use crate::arena::{Arena, Node};
use crate::types::{NodeId, OpaqueValue};
use crate::symbol::{SymbolId, SymbolTable};
use crate::eval::{Interpreter};


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
    pub fn new(interp: &'a mut Interpreter) -> Self {
        Self {
            arena: &mut interp.arena,
            symbols: &interp.symbols,
            nil_node: interp.nil_node,
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
                            if let Some(val) = self.symbols.symbol_value(sym_id) {
                                Ok(BExpr::Const(val))
                            } else {
                                Ok(BExpr::Const(expr))
                            }
                        }
                    }
                    _ => Ok(BExpr::Const(expr)),
                }
            }
            Node::Stem(_) => Ok(BExpr::Const(expr)),
            Node::Fork(_, _) => {
                // Application (f x y ...) logic
                // Check for proper list
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
                    let func_expr = items[0];
                    let mut curr_bexpr = self.compile_to_bexpr(func_expr, params)?;
                    
                    for arg in &items[1..] {
                        let arg_bexpr = self.compile_to_bexpr(*arg, params)?;
                        curr_bexpr = BExpr::App(Box::new(curr_bexpr), Box::new(arg_bexpr));
                    }
                    Ok(curr_bexpr)
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
}

pub fn compile_func(interp: &mut Interpreter, params: &[SymbolId], body: NodeId) -> Result<NodeId, String> {
    let mut compiler = Compiler::new(interp);
    let mut bexpr = compiler.compile_to_bexpr(body, params)?;
    
    // Abstract variables in reverse order (inner to outer)
    for &param in params.iter().rev() {
        bexpr = compiler.abstract_var(param, bexpr);
    }
    
    compiler.bexpr_to_node(bexpr)
}
