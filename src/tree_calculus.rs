use crate::arena::{Arena, Node};
use crate::types::{NodeId, OpaqueValue};

pub fn delta(arena: &mut Arena) -> NodeId {
    arena.alloc(Node::Leaf(OpaqueValue::Nil))
}

pub fn app(arena: &mut Arena, f: NodeId, a: NodeId) -> NodeId {
    if is_delta(arena, f) {
        arena.alloc(Node::Stem(a))
    } else {
        arena.alloc(Node::Fork(f, a))
    }
}

pub fn is_delta(arena: &Arena, id: NodeId) -> bool {
    matches!(arena.get_unchecked(id), Node::Leaf(OpaqueValue::Nil))
}

pub fn k(arena: &mut Arena) -> NodeId {
    let d = delta(arena);
    app(arena, d, d)
}

pub fn i(arena: &mut Arena) -> NodeId {
    let d = delta(arena);
    let k_node = k(arena);
    let dk = app(arena, d, k_node);
    app(arena, dk, k_node)
}

pub fn d(arena: &mut Arena) -> NodeId {
    let d_node = delta(arena);
    let k_node = k(arena);
    let k4 = app(arena, k_node, d_node);
    let dk = app(arena, d_node, k_node);
    app(arena, dk, k4)
}

pub fn d_of(arena: &mut Arena, x: NodeId) -> NodeId {
    // d{x} = 4 (4 x)
    let d_node = delta(arena);
    let dx = app(arena, d_node, x);
    app(arena, d_node, dx)
}

pub fn s(arena: &mut Arena) -> NodeId {
    // S = d{K D}(d{K}(K D))
    let k_node = k(arena);
    let d_node = d(arena);
    let kd = app(arena, k_node, d_node);
    let d_kd = d_of(arena, kd);
    let d_k = d_of(arena, k_node);
    let d_k_kd = app(arena, d_k, kd);
    app(arena, d_kd, d_k_kd)
}

pub fn numeral(arena: &mut Arena, n: usize) -> NodeId {
    // Tree calculus numerals (Jay, §3.7): 0 = 4, succ n = K n.
    let mut node = delta(arena);
    if n == 0 {
        return node;
    }
    let k_node = k(arena);
    for _ in 0..n {
        node = app(arena, k_node, node);
    }
    node
}

pub fn encode_nat(arena: &mut Arena, n: u64) -> NodeId {
    numeral(arena, n as usize)
}

pub fn decode_nat(arena: &Arena, node: NodeId) -> Option<u64> {
    let mut count: u64 = 0;
    let mut curr = node;
    loop {
        match arena.get_unchecked(curr) {
            Node::Leaf(OpaqueValue::Nil) => return Some(count),
            Node::Fork(left, right) if is_k(arena, *left) => {
                count = count.checked_add(1)?;
                curr = *right;
            }
            // Backward compatibility with old unary-stem encoding.
            Node::Stem(child) => {
                count = count.checked_add(1)?;
                curr = *child;
            }
            Node::Fork(left, right) if is_delta(arena, *left) => {
                count = count.checked_add(1)?;
                curr = *right;
            }
            _ => return None,
        }
    }
}

fn is_k(arena: &Arena, node: NodeId) -> bool {
    match arena.get_unchecked(node) {
        Node::Stem(inner) => is_delta(arena, *inner),
        Node::Fork(left, right) => is_delta(arena, *left) && is_delta(arena, *right),
        _ => false,
    }
}

pub fn encode_list(arena: &mut Arena, elems: &[NodeId]) -> NodeId {
    let mut list = delta(arena);
    for &elem in elems.iter().rev() {
        let d_node = delta(arena);
        let pair = app(arena, d_node, elem);
        list = app(arena, pair, list);
    }
    list
}

pub fn encode_string(arena: &mut Arena, s: &str) -> NodeId {
    let mut list = delta(arena);
    for ch in s.chars().rev() {
        let code = ch as u32 as u64;
        let nat = encode_nat(arena, code);
        let d_node = delta(arena);
        let pair = app(arena, d_node, nat);
        list = app(arena, pair, list);
    }
    list
}

pub fn decode_string(arena: &Arena, node: NodeId) -> Option<String> {
    let mut out = String::new();
    let mut curr = node;
    loop {
        match arena.get_unchecked(curr) {
            Node::Leaf(OpaqueValue::Nil) => return Some(out),
            _ => {
                let (head, tail) = split_fork(arena, curr)?;
                let code = decode_nat(arena, head)?;
                let c = std::char::from_u32(code as u32)?;
                out.push(c);
                curr = tail;
            }
        }
    }
}

fn split_fork(arena: &Arena, node: NodeId) -> Option<(NodeId, NodeId)> {
    match arena.get_unchecked(node) {
        Node::Fork(left, right) => match arena.get_unchecked(*left) {
            Node::Stem(child) => Some((*child, *right)),
            Node::Fork(op, child) if is_delta(arena, *op) => Some((*child, *right)),
            _ => None,
        },
        _ => None,
    }
}

pub fn query(arena: &mut Arena, is0: NodeId, is1: NodeId, is2: NodeId) -> NodeId {
    let k_node = k(arena);
    let triage = triage_comb(arena);

    // triage {is0, λx.is1, λx.λy.is2}
    let f1 = app(arena, k_node, is1);
    let k_is2 = app(arena, k_node, is2);
    let f2 = app(arena, k_node, k_is2);
    let triage_f0 = app(arena, triage, is0);
    let triage_f0_f1 = app(arena, triage_f0, f1);
    app(arena, triage_f0_f1, f2)
}

pub fn is_leaf(arena: &mut Arena) -> NodeId {
    let k_node = k(arena);
    let i_node = i(arena);
    let k_i = app(arena, k_node, i_node);
    query(arena, k_node, k_i, k_i)
}

pub fn is_stem(arena: &mut Arena) -> NodeId {
    let k_node = k(arena);
    let i_node = i(arena);
    let k_i = app(arena, k_node, i_node);
    query(arena, k_i, k_node, k_i)
}

pub fn is_fork(arena: &mut Arena) -> NodeId {
    let k_node = k(arena);
    let i_node = i(arena);
    let k_i = app(arena, k_node, i_node);
    query(arena, k_i, k_i, k_node)
}

#[derive(Clone)]
enum BExpr {
    Var(u8),
    Const(NodeId),
    App(Box<BExpr>, Box<BExpr>),
}

fn expr_app(left: BExpr, right: BExpr) -> BExpr {
    BExpr::App(Box::new(left), Box::new(right))
}

impl BExpr {
    fn occurs(&self, var: u8) -> bool {
        match self {
            BExpr::Var(v) => *v == var,
            BExpr::Const(_) => false,
            BExpr::App(l, r) => l.occurs(var) || r.occurs(var),
        }
    }
}

fn abstract_var(var: u8, expr: BExpr, k_node: NodeId, s_node: NodeId, i_node: NodeId) -> BExpr {
    if !expr.occurs(var) {
        return expr_app(BExpr::Const(k_node), expr);
    }

    match expr {
        BExpr::Var(v) => {
            if v == var {
                BExpr::Const(i_node)
            } else {
                expr_app(BExpr::Const(k_node), BExpr::Var(v))
            }
        }
        BExpr::Const(_) => expr_app(BExpr::Const(k_node), expr),
        BExpr::App(l, r) => {
            if let BExpr::Var(v) = &*r {
                if *v == var && !l.occurs(var) {
                    return *l;
                }
            }
            let al = abstract_var(var, *l, k_node, s_node, i_node);
            let ar = abstract_var(var, *r, k_node, s_node, i_node);
            expr_app(expr_app(BExpr::Const(s_node), al), ar)
        }
    }
}

fn abstract_many(vars: &[u8], expr: BExpr, k_node: NodeId, s_node: NodeId, i_node: NodeId) -> BExpr {
    vars.iter()
        .rev()
        .fold(expr, |acc, &var| abstract_var(var, acc, k_node, s_node, i_node))
}

fn bexpr_to_node(arena: &mut Arena, expr: BExpr) -> NodeId {
    match expr {
        BExpr::Var(_) => panic!("unabstracted variable in BExpr"),
        BExpr::Const(node) => node,
        BExpr::App(l, r) => {
            let left = bexpr_to_node(arena, *l);
            let right = bexpr_to_node(arena, *r);
            app(arena, left, right)
        }
    }
}

pub fn is_stem2(arena: &mut Arena) -> NodeId {
    let k_node = k(arena);
    let s_node = s(arena);
    let i_node = i(arena);
    let d_node = delta(arena);
    let n2 = numeral(arena, 2);

    const VAR_Z: u8 = 0;

    let z = BExpr::Var(VAR_Z);
    let k2 = expr_app(BExpr::Const(k_node), BExpr::Const(n2));
    let k2_4 = expr_app(k2, BExpr::Const(d_node));
    let body = expr_app(
        expr_app(expr_app(BExpr::Const(d_node), z), BExpr::Const(d_node)),
        k2_4,
    );

    let comb = abstract_many(&[VAR_Z], body, k_node, s_node, i_node);
    bexpr_to_node(arena, comb)
}

pub fn is_fork2(arena: &mut Arena) -> NodeId {
    let k_node = k(arena);
    let s_node = s(arena);
    let i_node = i(arena);
    let d_node = delta(arena);

    const VAR_Z: u8 = 0;

    let z = BExpr::Var(VAR_Z);
    let k_k = expr_app(BExpr::Const(k_node), BExpr::Const(k_node));
    let k4 = expr_app(BExpr::Const(k_node), BExpr::Const(d_node));
    let k_k4 = expr_app(BExpr::Const(k_node), k4);
    let body = expr_app(
        expr_app(expr_app(BExpr::Const(d_node), z), k_k),
        k_k4,
    );

    let comb = abstract_many(&[VAR_Z], body, k_node, s_node, i_node);
    bexpr_to_node(arena, comb)
}

pub fn triage_comb(arena: &mut Arena) -> NodeId {
    let k_node = k(arena);
    let s_node = s(arena);
    let i_node = i(arena);
    let d_node = delta(arena);
    let is_stem2_node = is_stem2(arena);

    const VAR_F0: u8 = 0;
    const VAR_F1: u8 = 1;
    const VAR_F2: u8 = 2;
    const VAR_Z: u8 = 3;
    const VAR_X: u8 = 4;

    let f0 = BExpr::Var(VAR_F0);
    let f1 = BExpr::Var(VAR_F1);
    let f2 = BExpr::Var(VAR_F2);
    let z = BExpr::Var(VAR_Z);

    let is_stem2_z = expr_app(BExpr::Const(is_stem2_node), z.clone());
    let four_z_f0_f2 = expr_app(
        expr_app(expr_app(BExpr::Const(d_node), z.clone()), f0),
        f2,
    );

    let x_var = BExpr::Var(VAR_X);
    let f1_x = expr_app(f1.clone(), x_var);
    let k_f1_x = expr_app(BExpr::Const(k_node), f1_x);
    let k_k_f1_x = expr_app(BExpr::Const(k_node), k_f1_x);
    let k_k_k_f1_x = expr_app(BExpr::Const(k_node), k_k_f1_x);
    let lambda_x = abstract_many(&[VAR_X], k_k_k_f1_x, k_node, s_node, i_node);

    let z4 = expr_app(z, BExpr::Const(d_node));
    let four_z4_4_lambda = expr_app(
        expr_app(expr_app(BExpr::Const(d_node), z4), BExpr::Const(d_node)),
        lambda_x,
    );

    let body = expr_app(
        expr_app(
            expr_app(BExpr::Const(d_node), is_stem2_z),
            four_z_f0_f2,
        ),
        four_z4_4_lambda,
    );
    let comb = abstract_many(&[VAR_F0, VAR_F1, VAR_F2, VAR_Z], body, k_node, s_node, i_node);
    bexpr_to_node(arena, comb)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena::deep_equal;
    use crate::search::{reduce, EvalContext};

    fn apply(arena: &mut Arena, f: NodeId, a: NodeId) -> NodeId {
        app(arena, f, a)
    }

    #[test]
    fn test_triage_comb_leaf_stem_fork() {
        let mut arena = Arena::new();
        let mut ctx = EvalContext::default();
        ctx.max_steps = 100_000;

        let triage = triage_comb(&mut arena);
        let f0 = numeral(&mut arena, 2);
        let f1 = i(&mut arena);
        let f2 = k(&mut arena);

        let x = numeral(&mut arena, 3);
        let y = numeral(&mut arena, 4);

        let leaf = delta(&mut arena);
        let stem = {
            let d = delta(&mut arena);
            apply(&mut arena, d, x)
        };
        let fork = {
            let d = delta(&mut arena);
            let dx = apply(&mut arena, d, x);
            apply(&mut arena, dx, y)
        };

        let triage_f0 = apply(&mut arena, triage, f0);
        let triage_f0_f1 = apply(&mut arena, triage_f0, f1);
        let triage_f0_f1_f2 = apply(&mut arena, triage_f0_f1, f2);

        let leaf_term = apply(&mut arena, triage_f0_f1_f2, leaf);
        let stem_term = apply(&mut arena, triage_f0_f1_f2, stem);
        let fork_term = apply(&mut arena, triage_f0_f1_f2, fork);

        let leaf_res = reduce(&mut arena, leaf_term, &mut ctx);
        let stem_res = reduce(&mut arena, stem_term, &mut ctx);
        let fork_res = reduce(&mut arena, fork_term, &mut ctx);

        assert!(deep_equal(&arena, leaf_res, f0));
        assert!(deep_equal(&arena, stem_res, x));
        assert!(deep_equal(&arena, fork_res, x));
    }

    #[test]
    fn test_encode_decode_nat_roundtrip() {
        let mut arena = Arena::new();
        for n in [0u64, 1, 2, 3, 5, 10] {
            let encoded = encode_nat(&mut arena, n);
            let decoded = decode_nat(&arena, encoded);
            assert_eq!(decoded, Some(n));
        }
    }

    #[test]
    fn test_encode_decode_string_roundtrip() {
        let mut arena = Arena::new();
        let s = "abc";
        let encoded = encode_string(&mut arena, s);
        let decoded = decode_string(&arena, encoded);
        assert_eq!(decoded.as_deref(), Some(s));
    }

    #[test]
    fn test_abstraction_identity() {
        let mut arena = Arena::new();
        let mut ctx = EvalContext::default();

        let k_node = k(&mut arena);
        let s_node = s(&mut arena);
        let i_node = i(&mut arena);

        let expr = BExpr::Var(0);
        let comb = abstract_many(&[0], expr, k_node, s_node, i_node);
        let id = bexpr_to_node(&mut arena, comb);

        let arg = delta(&mut arena);
        let term = apply(&mut arena, id, arg);
        let res = reduce(&mut arena, term, &mut ctx);
        assert!(deep_equal(&arena, res, arg));
    }

    #[test]
    fn test_s_combinator() {
        let mut arena = Arena::new();
        let mut ctx = EvalContext::default();

        let s_node = s(&mut arena);
        let k_node = k(&mut arena);
        let i_node = i(&mut arena);
        let z = delta(&mut arena);

        let s_k = apply(&mut arena, s_node, k_node);
        let s_k_i = apply(&mut arena, s_k, i_node);
        let term = apply(&mut arena, s_k_i, z);

        let k_z = apply(&mut arena, k_node, z);
        let i_z = apply(&mut arena, i_node, z);
        let expected = apply(&mut arena, k_z, i_z);

        let res = reduce(&mut arena, term, &mut ctx);
        let expected_res = reduce(&mut arena, expected, &mut ctx);
        assert!(deep_equal(&arena, res, expected_res));
    }

    #[test]
    fn test_is_stem2_and_is_fork2_shapes() {
        let mut arena = Arena::new();
        let mut ctx = EvalContext::default();

        let leaf = delta(&mut arena);
        let stem = {
            let d = delta(&mut arena);
            apply(&mut arena, d, leaf)
        };
        let fork = {
            let d = delta(&mut arena);
            let dl = apply(&mut arena, d, leaf);
            apply(&mut arena, dl, leaf)
        };

        let is_stem2_node = is_stem2(&mut arena);
        let is_fork2_node = is_fork2(&mut arena);

        let stem2_leaf_term = apply(&mut arena, is_stem2_node, leaf);
        let stem2_stem_term = apply(&mut arena, is_stem2_node, stem);
        let stem2_fork_term = apply(&mut arena, is_stem2_node, fork);

        let stem2_leaf = reduce(&mut arena, stem2_leaf_term, &mut ctx);
        let stem2_stem = reduce(&mut arena, stem2_stem_term, &mut ctx);
        let stem2_fork = reduce(&mut arena, stem2_fork_term, &mut ctx);

        assert!(matches!(arena.get_unchecked(stem2_leaf), Node::Leaf(_)));
        assert!(matches!(arena.get_unchecked(stem2_stem), Node::Fork(_, _)));
        assert!(matches!(arena.get_unchecked(stem2_fork), Node::Leaf(_)));

        let fork2_leaf_term = apply(&mut arena, is_fork2_node, leaf);
        let fork2_stem_term = apply(&mut arena, is_fork2_node, stem);
        let fork2_fork_term = apply(&mut arena, is_fork2_node, fork);

        let fork2_leaf = reduce(&mut arena, fork2_leaf_term, &mut ctx);
        let fork2_stem = reduce(&mut arena, fork2_stem_term, &mut ctx);
        let fork2_fork = reduce(&mut arena, fork2_fork_term, &mut ctx);

        assert!(matches!(arena.get_unchecked(fork2_leaf), Node::Fork(_, _)));
        assert!(matches!(arena.get_unchecked(fork2_stem), Node::Fork(_, _)));
        assert!(matches!(arena.get_unchecked(fork2_fork), Node::Leaf(_)));
    }
}
