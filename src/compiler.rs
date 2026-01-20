use crate::arena::{Arena, Node};
use crate::types::{NodeId, OpaqueValue};
use crate::symbol::{SymbolId, SymbolTable};
use crate::context::GlobalContext;
use crate::process::Process;


// Bracket Expression to handle intermediate compilation state
#[derive(Debug, Clone)]
enum BExpr {
    Var(SymbolId),
    Const(NodeId),
    App(Box<BExpr>, Box<BExpr>),
}

impl BExpr {
    fn occurs(&self, sym: SymbolId) -> bool {
        match self {
            BExpr::Var(s) => *s == sym,
            BExpr::Const(_) => false,
            BExpr::App(l, r) => l.occurs(sym) || r.occurs(sym),
        }
    }
}

pub struct Compiler<'a> {
    arena: &'a mut Arena,
    symbols: &'a SymbolTable,
    nil_node: NodeId,
}

impl<'a> Compiler<'a> {
    pub fn new(proc: &'a mut Process, ctx: &'a GlobalContext) -> Self {
        let nil_node = proc.make_nil();
        Self {
            arena: &mut proc.arena.inner,
            symbols: &ctx.symbols,
            nil_node,
        }
    }

    fn make_leaf(&mut self) -> NodeId {
        self.nil_node
    }

    fn make_app(&mut self, f: NodeId, a: NodeId) -> NodeId {
        self.arena.alloc(Node::Fork(f, a))
    }

    fn bexpr_i(&mut self) -> BExpr {
        // I = △ △
        // In search.rs: ((△ △) y) -> y
        let n = self.make_leaf();
        let nn = self.make_app(n, n);
        BExpr::Const(nn)
    }

    fn bexpr_k(&mut self, u: BExpr) -> BExpr {
        // K u = △ (△ u)
        // In search.rs: ((△ (△ u)) y) -> u
        let n = self.make_leaf();
        let n_node = BExpr::Const(n);
        // (△ u)
        let nu = BExpr::App(Box::new(n_node.clone()), Box::new(u));
        // (△ (△ u))
        BExpr::App(Box::new(n_node), Box::new(nu))
    }

    fn bexpr_s(&mut self, z: BExpr, w: BExpr) -> BExpr {
        // S z w = △ (△ z w) = △ ((△ z) w)
        // In search.rs: △ (△ z w) y -> ((z y) (w y))
        let n = self.make_leaf();
        let n_node = BExpr::Const(n);
        
        // (△ z)
        let nz = BExpr::App(Box::new(n_node.clone()), Box::new(z));
        // ((△ z) w)
        let nzw = BExpr::App(Box::new(nz), Box::new(w));
        // (△ ((△ z) w))
        let op = BExpr::App(Box::new(n_node), Box::new(nzw));
        op
    }

    fn abstract_var(&mut self, name: SymbolId, e: BExpr) -> BExpr {
        if !e.occurs(name) {
            self.bexpr_k(e)
        } else {
            match e {
                BExpr::Var(_) => self.bexpr_i(), // Must be the var itself if occurs
                BExpr::App(l, r) => {
                    // Optimization: eta-reduction \x. f x -> f if x not free in f
                    if let BExpr::Var(v_sym) = *r {
                        if v_sym == name && !l.occurs(name) {
                            return *l;
                        }
                    }
                    
                    let al = self.abstract_var(name, *l);
                    let ar = self.abstract_var(name, *r);
                    self.bexpr_s(al, ar)
                }
                BExpr::Const(_) => self.bexpr_k(e), // Should be covered by !occurs
            }
        }
    }

    // Convert an AST node (from eval) to BExpr
    fn compile_to_bexpr(&mut self, expr: NodeId, params: &[SymbolId]) -> Result<BExpr, String> {
        let node = self.arena.get_unchecked(expr).clone();
        match node {
            Node::Leaf(val) => {
                match val {
                    OpaqueValue::Symbol(id) => {
                        let sym_id = SymbolId(id);
                        if params.contains(&sym_id) {
                            Ok(BExpr::Var(sym_id))
                        } else {
                            // Free variable: resolve to value if possible, or keep as Const
                            // Global constants are resolved at runtime now.
                            Ok(BExpr::Const(expr))
                        }
                    }
                    _ => Ok(BExpr::Const(expr)),
                }
            }
            Node::Stem(_) => Ok(BExpr::Const(expr)),
            Node::Fork(_, _) => {
                // Check for LAMBDA special form
                let node_copy = self.arena.get_unchecked(expr).clone();
                if let Node::Fork(car, cdr) = node_copy {
                    if let Node::Leaf(OpaqueValue::Symbol(s)) = self.arena.get_unchecked(car) {
                        // Hardcoded check for LAMBDA symbol (SymbolId 1 is often nil, check ctx?)
                        // We need to look up LAMBDA symbol from context?
                        // But Compiler has &SymbolTable.
                        // We can internment check "LAMBDA".
                        if self.symbols.symbol_name(SymbolId(*s)).map(|n| n == "LAMBDA").unwrap_or(false) {
                             // (LAMBDA (params) body)
                             // Parse params
                             if let Node::Fork(params_node, body_rest) = self.arena.get_unchecked(cdr).clone() {
                                 let mut new_params = params.to_vec();
                                 let mut current = params_node;
                                 while let Node::Fork(p, rest) = self.arena.get_unchecked(current).clone() {
                                     if let Node::Leaf(OpaqueValue::Symbol(pid)) = self.arena.get_unchecked(p) {
                                         new_params.push(SymbolId(*pid));
                                     }
                                     current = rest;
                                 }
                                 
                                 // Parse body (assume single expression for now, or implicit progn)
                                 // If multiple body forms, we should wrap in PROGN?
                                 // For now, take first form.
                                 let body_node = if let Node::Fork(b, _) = self.arena.get_unchecked(body_rest).clone() {
                                     b
                                 } else {
                                     self.nil_node
                                 };
                                 
                                 // Recurse with new params
                                 let mut body_bexpr = self.compile_to_bexpr(body_node, &new_params)?;
                                 
                                 // Abstract over new parameters matches
                                 // We only abstract the variables introduced here
                                 // The `params` argument to `compile_to_bexpr` tracks ALL visible variables.
                                 // But abstract_var only abstracts the specific variable.
                                 
                                 // Wait, `new_params` contains outer + inner.
                                 // We need to abstract inner params from the body result to create the lambda term.
                                 // The result of `compile_to_bexpr` will have abstract placeholders for outer vars?
                                 // No, `BExpr::Var` uses SymbolId.
                                 // `abstract_var` converts `Var(id)` to S/K/I structure.
                                 
                                 // So we just need to abstract the *new* parameters in reverse order.
                                 let added_len = new_params.len() - params.len();
                                 let inner_params = &new_params[params.len()..];
                                 
                                 for &param in inner_params.iter().rev() {
                                     body_bexpr = self.abstract_var(param, body_bexpr);
                                 }
                                 
                                 return Ok(body_bexpr);
                             }
                        }
                    }
                }

                // Application (f x y ...) logic
                // Check for proper list arguments
                let mut items = Vec::new();
                let mut current = expr;
                while let Node::Fork(h, t) = self.arena.get_unchecked(current).clone() {
                    items.push(h);
                    current = t;
                }
                if let Node::Leaf(OpaqueValue::Nil) = self.arena.get_unchecked(current) {
                    if items.is_empty() {
                        return Ok(BExpr::Const(self.nil_node));
                    }
                    
                    // (f a b) -> ((f a) b)
                    let items_len = items.len();
                    if items_len > 0 {
                        let func_expr = items[0];
                        let mut curr_bexpr = self.compile_to_bexpr(func_expr, params)?;
                        
                        for arg in &items[1..] {
                            let arg_bexpr = self.compile_to_bexpr(*arg, params)?;
                            curr_bexpr = BExpr::App(Box::new(curr_bexpr), Box::new(arg_bexpr));
                        }
                        Ok(curr_bexpr)
                    } else {
                        Ok(BExpr::Const(self.nil_node))
                    }
                } else {
                     // Dotted list -> Treat as data constant?
                     // Or error? compile only supports standard code lists.
                     Ok(BExpr::Const(expr))
                }
            }
        }
    }

    fn bexpr_to_node(&mut self, e: BExpr) -> Result<NodeId, String> {
        match e {
            BExpr::Const(n) => Ok(n),
            BExpr::App(l, r) => {
                let ln = self.bexpr_to_node(*l)?;
                let rn = self.bexpr_to_node(*r)?;
                Ok(self.make_app(ln, rn))
            }
            BExpr::Var(sym) => Err(format!("Unbound variable remaining after compilation: {:?}", sym)),
        }
    }
    // Public API to compile an arbitrary expression (treating free variables as globals)
    pub fn compile_expr(&mut self, expr: NodeId) -> Result<NodeId, String> {
        let bexpr = self.compile_to_bexpr(expr, &[])?;
        self.bexpr_to_node(bexpr)
    }
}

pub fn compile_func(proc: &mut Process, ctx: &GlobalContext, params: &[SymbolId], body: NodeId) -> Result<NodeId, String> {
    let mut compiler = Compiler::new(proc, ctx);
    let mut bexpr = compiler.compile_to_bexpr(body, params)?;
    
    // Abstract variables in reverse order (inner to outer)
    for &param in params.iter().rev() {
        bexpr = compiler.abstract_var(param, bexpr);
    }
    
    compiler.bexpr_to_node(bexpr)
}
