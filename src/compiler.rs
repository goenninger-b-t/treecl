use crate::arena::{Graph, NodeId};
use crate::arena::Node::{App, Leaf};
use smallvec::smallvec;

// Bracket Expression Types
#[derive(Debug, Clone)]
enum BExpr {
    Var(String),
    Const(NodeId),
    App(Box<BExpr>, Box<BExpr>),
}

// Constructors matching triage/core.clj logic



fn bexpr_k(g: &mut Graph, u: BExpr) -> BExpr {
    // K u = ((n n) u)
    // k_combinator = (n n)
    let n = g.add(Leaf);
    let nn = g.add(App { func: n, args: smallvec![n] });
    let k_node = BExpr::Const(nn);
    BExpr::App(Box::new(k_node), Box::new(u))
}

fn bexpr_s(g: &mut Graph, u: BExpr, v: BExpr) -> BExpr {
    // S u v = ((n (n v)) u)  -- Using D-rule: D v u = u (v)
    // D v u x = u x (v x) = S u v x
    let n = g.add(Leaf);
    let n_node = BExpr::Const(n);
    // (n v)
    let nv = BExpr::App(Box::new(n_node.clone()), Box::new(v));
    // (n (n v))
    let nnv = BExpr::App(Box::new(n_node), Box::new(nv));
    // ((n (n v)) u)
    BExpr::App(Box::new(nnv), Box::new(u))
}

fn bexpr_i(g: &mut Graph) -> BExpr {
    // I = S (n n) n
    let n = g.add(Leaf);
    let nn = g.add(App { func: n, args: smallvec![n] });
    let nn_expr = BExpr::Const(nn);
    let n_expr = BExpr::Const(n);
    bexpr_s(g, nn_expr, n_expr)
}

fn bexpr_occurs(name: &str, e: &BExpr) -> bool {
    match e {
        BExpr::Var(n) => n == name,
        BExpr::Const(_) => false,
        BExpr::App(l, r) => bexpr_occurs(name, l) || bexpr_occurs(name, r),
    }
}

fn bexpr_abstract(g: &mut Graph, name: &str, e: BExpr) -> BExpr {
    if !bexpr_occurs(name, &e) {
        bexpr_k(g, e)
    } else {
        match e {
            BExpr::Var(_) => bexpr_i(g), // If occurs, must be the var itself
            BExpr::App(l, r) => {
                // Optimization: eta-reduction-like check?
                // Clojure: if r is var and name==r.name and !occurs(name, l) -> l
                if let BExpr::Var(rn) = &*r {
                    if rn == name && !bexpr_occurs(name, &*l) {
                        return *l;
                    }
                }
                let al = bexpr_abstract(g, name, *l);
                let ar = bexpr_abstract(g, name, *r);
                bexpr_s(g, al, ar)
            }
            BExpr::Const(_) => bexpr_k(g, e), // Should be covered by !occurs
        }
    }
}

pub enum CompileTerm {
    Var(String),
    Const(NodeId),
    App(Box<CompileTerm>, Box<CompileTerm>),
    Lam(String, Box<CompileTerm>),
}

fn compile_to_bexpr(g: &mut Graph, t: CompileTerm) -> BExpr {
    match t {
        CompileTerm::Var(s) => BExpr::Var(s),
        CompileTerm::Const(n) => BExpr::Const(n),
        CompileTerm::App(f, a) => BExpr::App(
            Box::new(compile_to_bexpr(g, *f)),
            Box::new(compile_to_bexpr(g, *a))
        ),
        CompileTerm::Lam(name, body) => {
            let body_bexpr = compile_to_bexpr(g, *body);
            bexpr_abstract(g, &name, body_bexpr)
        }
    }
}

fn bexpr_to_node(g: &mut Graph, e: BExpr) -> Result<NodeId, String> {
    match e {
        BExpr::Const(n) => Ok(n),
        BExpr::App(l, r) => {
            let ln = bexpr_to_node(g, *l)?;
            let rn = bexpr_to_node(g, *r)?;
            Ok(g.add(App { func: ln, args: smallvec![rn] }))
        }
        BExpr::Var(name) => Err(format!("Unbound variable after compilation: {}", name)),
    }
}

pub fn compile(g: &mut Graph, t: CompileTerm) -> Result<NodeId, String> {
    let bexpr = compile_to_bexpr(g, t);
    bexpr_to_node(g, bexpr)
}
