use crate::arena::{Arena, Node};
use crate::context::GlobalContext;
use crate::process::Process;
use crate::symbol::{SymbolId, SymbolTable};
use crate::types::{NodeId, OpaqueValue};
use crate::tree_calculus;

// Bracket Expression to handle intermediate compilation state
#[derive(Debug, Clone)]
enum BExpr {
    Var(SymbolId),
    Const(NodeId),
    App(Box<BExpr>, Box<BExpr>),
}

impl BExpr {
    #[allow(dead_code)]
    fn occurs(&self, sym: SymbolId) -> bool {
        let mut cache = std::collections::HashMap::new();
        self.occurs_cached(sym, &mut cache)
    }

    fn occurs_cached(
        &self,
        sym: SymbolId,
        cache: &mut std::collections::HashMap<(usize, SymbolId), bool>,
    ) -> bool {
        let key = (self as *const _ as usize, sym);
        if let Some(&res) = cache.get(&key) {
            return res;
        }
        let res = match self {
            BExpr::Var(s) => *s == sym,
            BExpr::Const(_) => false,
            BExpr::App(l, r) => l.occurs_cached(sym, cache) || r.occurs_cached(sym, cache),
        };
        cache.insert(key, res);
        res
    }
}

use std::sync::RwLock;

pub struct Compiler<'a> {
    arena: &'a mut Arena,
    symbols: &'a RwLock<SymbolTable>,
    primitives: &'a std::collections::HashMap<SymbolId, crate::context::PrimitiveFn>,
    nil_node: NodeId,
    k_node: NodeId,
    i_node: NodeId,
    s_node: NodeId,
    pure_only: bool,
}

impl<'a> Compiler<'a> {
    pub fn new(proc: &'a mut Process, ctx: &'a GlobalContext) -> Self {
        Self::new_with_mode(proc, ctx, true)
    }

    pub fn new_extended(proc: &'a mut Process, ctx: &'a GlobalContext) -> Self {
        Self::new_with_mode(proc, ctx, false)
    }

    fn new_with_mode(proc: &'a mut Process, ctx: &'a GlobalContext, pure_only: bool) -> Self {
        let nil_node = proc.make_nil();
        let k_node = tree_calculus::k(&mut proc.arena.inner);
        let i_node = tree_calculus::i(&mut proc.arena.inner);
        let s_node = tree_calculus::s(&mut proc.arena.inner);
        Self {
            arena: &mut proc.arena.inner,
            symbols: &ctx.symbols,
            primitives: &ctx.primitives,
            nil_node,
            k_node,
            i_node,
            s_node,
            pure_only,
        }
    }

    #[allow(dead_code)]
    fn make_leaf(&mut self) -> NodeId {
        self.nil_node
    }

    fn make_app(&mut self, f: NodeId, a: NodeId) -> NodeId {
        tree_calculus::app(self.arena, f, a)
    }

    fn is_pure_const(&self, root: NodeId) -> bool {
        let mut stack = vec![root];
        while let Some(id) = stack.pop() {
            match self.arena.get_unchecked(id) {
                Node::Leaf(val) => {
                    if !matches!(val, OpaqueValue::Nil) {
                        return false;
                    }
                }
                Node::Stem(child) => stack.push(*child),
                Node::Fork(left, right) => {
                    stack.push(*left);
                    stack.push(*right);
                }
            }
        }
        true
    }

    fn bexpr_i(&mut self) -> BExpr {
        BExpr::Const(self.i_node)
    }

    fn bexpr_k(&mut self, u: BExpr) -> BExpr {
        // K u
        BExpr::App(Box::new(BExpr::Const(self.k_node)), Box::new(u))
    }

    fn bexpr_s(&mut self, z: BExpr, w: BExpr) -> BExpr {
        // S z w
        let sz = BExpr::App(Box::new(BExpr::Const(self.s_node)), Box::new(z));
        BExpr::App(Box::new(sz), Box::new(w))
    }

    fn abstract_var(&mut self, name: SymbolId, e: &BExpr) -> BExpr {
        let mut occurs_cache = std::collections::HashMap::new();
        self.abstract_var_cached(name, e, &mut occurs_cache)
    }

    fn abstract_var_cached(
        &mut self,
        name: SymbolId,
        e: &BExpr,
        occurs_cache: &mut std::collections::HashMap<(usize, SymbolId), bool>,
    ) -> BExpr {
        if !e.occurs_cached(name, occurs_cache) {
            self.bexpr_k(e.clone())
        } else {
            match e {
                BExpr::Var(_) => self.bexpr_i(),
                BExpr::App(l, r) => {
                    // Optimization: eta-reduction \x. f x -> f if x not free in f
                    if let BExpr::Var(v_sym) = **r {
                        if v_sym == name && !l.occurs_cached(name, occurs_cache) {
                            return *l.clone();
                        }
                    }

                    let al = self.abstract_var_cached(name, l, occurs_cache);
                    let ar = self.abstract_var_cached(name, r, occurs_cache);
                    self.bexpr_s(al, ar)
                }
                BExpr::Const(_) => self.bexpr_k(e.clone()),
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
                        } else if !self.pure_only && self.primitives.contains_key(&sym_id) {
                            Ok(BExpr::Const(expr))
                        } else if !self.pure_only {
                            if let Some(pkg) = self
                                .symbols
                                .read()
                                .unwrap()
                                .get_package(crate::symbol::PackageId(1))
                            {
                                if let Some(sv_sym) = pkg.find_symbol("SYMBOL-VALUE") {
                                    let sv_leaf =
                                        self.arena.alloc(Node::Leaf(OpaqueValue::Symbol(sv_sym.0)));
                                    let sv_node = BExpr::Const(sv_leaf);
                                    let arg_node = BExpr::Const(expr);
                                    Ok(BExpr::App(Box::new(sv_node), Box::new(arg_node)))
                                } else {
                                    Ok(BExpr::Const(expr))
                                }
                            } else {
                                Ok(BExpr::Const(expr))
                            }
                        } else {
                            Err("Compilation is restricted to pure tree calculus terms; free symbols are not allowed".to_string())
                        }
                    }
                    OpaqueValue::Nil => Ok(BExpr::Const(expr)),
                    _ => {
                        if self.pure_only {
                            Err("Compilation is restricted to pure tree calculus terms; non-NIL literals are not allowed".to_string())
                        } else {
                            Ok(BExpr::Const(expr))
                        }
                    }
                }
            }
            Node::Stem(_) => {
                if !self.pure_only || self.is_pure_const(expr) {
                    Ok(BExpr::Const(expr))
                } else {
                    Err("Compilation is restricted to pure tree calculus terms; non-NIL literals are not allowed".to_string())
                }
            }
            Node::Fork(_, _) => {
                // Check for LAMBDA special form
                let node_copy = self.arena.get_unchecked(expr).clone();
                if let Node::Fork(car, cdr) = node_copy {
                    if let Node::Leaf(OpaqueValue::Symbol(s)) = self.arena.get_unchecked(car) {
                        // Hardcoded check for LAMBDA symbol (SymbolId 1 is often nil, check ctx?)
                        // We need to look up LAMBDA symbol from context?
                        // But Compiler has &SymbolTable.
                        // We can internment check "LAMBDA".
                        if self
                            .symbols
                            .read()
                            .unwrap()
                            .symbol_name(SymbolId(*s))
                            .map(|n| n == "LAMBDA")
                            .unwrap_or(false)
                        {
                            // (LAMBDA (params) body)
                            // Parse params
                            if let Node::Fork(params_node, body_rest) =
                                self.arena.get_unchecked(cdr).clone()
                            {
                                let mut new_params = params.to_vec();
                                let mut current = params_node;
                                while let Node::Fork(p, rest) =
                                    self.arena.get_unchecked(current).clone()
                                {
                                    if let Node::Leaf(OpaqueValue::Symbol(pid)) =
                                        self.arena.get_unchecked(p)
                                    {
                                        new_params.push(SymbolId(*pid));
                                    }
                                    current = rest;
                                }

                                // Parse body (assume single expression for now, or implicit progn)
                                // If multiple body forms, we should wrap in PROGN?
                                // For now, take first form.
                                let body_node = if let Node::Fork(b, _) =
                                    self.arena.get_unchecked(body_rest).clone()
                                {
                                    b
                                } else {
                                    self.nil_node
                                };

                                // Recurse with new params
                                let mut body_bexpr =
                                    self.compile_to_bexpr(body_node, &new_params)?;

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
                                let _added_len = new_params.len() - params.len();
                                let inner_params = &new_params[params.len()..];

                                for &param in inner_params.iter().rev() {
                                    body_bexpr = self.abstract_var(param, &body_bexpr);
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

                        // Handle 0-arity function calls (f) -> (f nil)
                        // In Tree Calculus, we must apply to something to trigger evaluation of the function
                        if items_len == 1 {
                            curr_bexpr = BExpr::App(
                                Box::new(curr_bexpr),
                                Box::new(BExpr::Const(self.nil_node)),
                            );
                        } else {
                            for arg in &items[1..] {
                                let arg_bexpr = self.compile_to_bexpr(*arg, params)?;
                                curr_bexpr = BExpr::App(Box::new(curr_bexpr), Box::new(arg_bexpr));
                            }
                        }
                        Ok(curr_bexpr)
                    } else {
                        Ok(BExpr::Const(self.nil_node))
                    }
                } else if !self.pure_only || self.is_pure_const(expr) {
                    Ok(BExpr::Const(expr))
                } else {
                    Err("Compilation is restricted to pure tree calculus terms; non-NIL literals are not allowed".to_string())
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
            BExpr::Var(sym) => Err(format!(
                "Unbound variable remaining after compilation: {:?}",
                sym
            )),
        }
    }
    // Public API to compile an arbitrary expression (treating free variables as globals)
    pub fn compile_expr(&mut self, expr: NodeId) -> Result<NodeId, String> {
        let bexpr = self.compile_to_bexpr(expr, &[])?;
        self.bexpr_to_node(bexpr)
    }
}

pub fn compile_func(
    proc: &mut Process,
    ctx: &GlobalContext,
    params: &[SymbolId],
    body: NodeId,
) -> Result<NodeId, String> {
    let mut compiler = Compiler::new(proc, ctx);
    let mut bexpr = compiler.compile_to_bexpr(body, params)?;

    // Abstract variables in reverse order (inner to outer)
    for &param in params.iter().rev() {
        bexpr = compiler.abstract_var(param, &bexpr);
    }

    compiler.bexpr_to_node(bexpr)
}

pub fn compile_func_extended(
    proc: &mut Process,
    ctx: &GlobalContext,
    params: &[SymbolId],
    body: NodeId,
) -> Result<NodeId, String> {
    let mut compiler = Compiler::new_extended(proc, ctx);
    let mut bexpr = compiler.compile_to_bexpr(body, params)?;

    for &param in params.iter().rev() {
        bexpr = compiler.abstract_var(param, &bexpr);
    }

    compiler.bexpr_to_node(bexpr)
}
