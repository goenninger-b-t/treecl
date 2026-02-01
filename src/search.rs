use crate::arena::{Arena, Node};
use crate::types::{NodeId, OpaqueValue};
use std::collections::HashMap;

pub struct EvalContext {
    pub steps: usize,
    pub max_steps: usize,
    exhausted: bool,
    cache_epoch: u64,
    purity_cache: HashMap<NodeId, bool>,
    whnf_cache: HashMap<NodeId, NodeId>,
    nf_cache: HashMap<NodeId, NodeId>,
}

impl Default for EvalContext {
    fn default() -> Self {
        Self {
            steps: 0,
            max_steps: 10000,
            exhausted: false,
            cache_epoch: 0,
            purity_cache: HashMap::new(),
            whnf_cache: HashMap::new(),
            nf_cache: HashMap::new(),
        }
    }
}

impl EvalContext {
    pub fn new() -> Self {
        Self::default()
    }

    fn sync_epoch(&mut self, arena: &Arena) {
        let epoch = arena.epoch();
        if self.cache_epoch != epoch {
            self.cache_epoch = epoch;
            self.purity_cache.clear();
            self.whnf_cache.clear();
            self.nf_cache.clear();
        }
    }

    fn reset_exhausted(&mut self) {
        self.exhausted = false;
    }
}

/// Perform reduction on the given root until normal form or step limit.
///
/// Implements canonical Tree Calculus reduction rules:
/// - △ △ y z → y                  (K rule)
/// - △ (△ x) y z → y z (x z)      (S rule)
/// - △ (△ w x) y z → z w x        (F rule)
///
/// The key insight: △ is the sole operator. It pattern-matches on its first argument
/// to decide which reduction rule applies. Reduction fires when △ has THREE arguments.
///
/// This reducer is strict about Tree Calculus structure: only Nil leaves are valid.
/// If any non-Nil leaf is present, no reduction is performed.
fn is_delta(arena: &Arena, id: NodeId) -> bool {
    matches!(arena.get_unchecked(id), Node::Leaf(OpaqueValue::Nil))
}

fn is_pure_tree(arena: &Arena, root: NodeId, cache: &mut HashMap<NodeId, bool>) -> bool {
    if let Some(&res) = cache.get(&root) {
        return res;
    }

    let mut stack: Vec<(NodeId, bool)> = vec![(root, false)];
    while let Some((id, visited)) = stack.pop() {
        if cache.contains_key(&id) {
            continue;
        }

        match arena.get_unchecked(id) {
            Node::Leaf(val) => {
                cache.insert(id, matches!(val, OpaqueValue::Nil));
            }
            Node::Stem(child) => {
                if visited {
                    let ok = cache.get(child).copied().unwrap_or(false);
                    cache.insert(id, ok);
                } else {
                    stack.push((id, true));
                    stack.push((*child, false));
                }
            }
            Node::Fork(left, right) => {
                if visited {
                    let ok_left = cache.get(left).copied().unwrap_or(false);
                    let ok_right = cache.get(right).copied().unwrap_or(false);
                    cache.insert(id, ok_left && ok_right);
                } else {
                    stack.push((id, true));
                    stack.push((*left, false));
                    stack.push((*right, false));
                }
            }
        }
    }

    cache.get(&root).copied().unwrap_or(false)
}

fn split_delta1(arena: &Arena, id: NodeId) -> Option<NodeId> {
    match arena.get_unchecked(id) {
        Node::Stem(x) => Some(*x),
        Node::Fork(op, x) if is_delta(arena, *op) => Some(*x),
        _ => None,
    }
}

fn split_delta2(arena: &Arena, id: NodeId) -> Option<(NodeId, NodeId)> {
    match arena.get_unchecked(id) {
        Node::Fork(left, y) => split_delta1(arena, *left).map(|x| (x, *y)),
        _ => None,
    }
}

fn alloc_app(arena: &mut Arena, f: NodeId, a: NodeId) -> NodeId {
    if is_delta(arena, f) {
        arena.alloc(Node::Stem(a))
    } else {
        arena.alloc(Node::Fork(f, a))
    }
}

pub fn reduce(arena: &mut Arena, root: NodeId, ctx: &mut EvalContext) -> NodeId {
    ctx.sync_epoch(arena);
    ctx.reset_exhausted();

    if !is_pure_tree(arena, root, &mut ctx.purity_cache) {
        return root;
    }

    reduce_nf_inner(arena, root, ctx)
}

/// Reduce to Weak Head Normal Form
/// Uses same rules as reduce but stops at head normal form.
pub fn reduce_whnf(arena: &mut Arena, root: NodeId, ctx: &mut EvalContext) -> NodeId {
    ctx.sync_epoch(arena);
    ctx.reset_exhausted();

    if !is_pure_tree(arena, root, &mut ctx.purity_cache) {
        return root;
    }

    reduce_whnf_inner(arena, root, ctx)
}

fn reduce_nf_inner(arena: &mut Arena, root: NodeId, ctx: &mut EvalContext) -> NodeId {
    if let Some(&cached) = ctx.nf_cache.get(&root) {
        return cached;
    }
    if ctx.steps >= ctx.max_steps {
        ctx.exhausted = true;
        return root;
    }

    let result = match arena.get_unchecked(root).clone() {
        Node::Leaf(_) => root,
        Node::Stem(inner) => {
            let reduced_inner = reduce_nf_inner(arena, inner, ctx);
            if reduced_inner != inner {
                arena.alloc(Node::Stem(reduced_inner))
            } else {
                root
            }
        }
        Node::Fork(left, z) => {
            let reduced_left = reduce_whnf_inner(arena, left, ctx);

            if let Some((x, y)) = split_delta2(arena, reduced_left) {
                let reduced_x = reduce_whnf_inner(arena, x, ctx);

                if is_delta(arena, reduced_x) {
                    ctx.steps += 1;
                    return reduce_nf_inner(arena, y, ctx);
                }

                if let Some(x_inner) = split_delta1(arena, reduced_x) {
                    ctx.steps += 1;
                    let yz = alloc_app(arena, y, z);
                    let xz = alloc_app(arena, x_inner, z);
                    let new_root = alloc_app(arena, yz, xz);
                    return reduce_nf_inner(arena, new_root, ctx);
                }

                if let Some((w, x_inner)) = split_delta2(arena, reduced_x) {
                    ctx.steps += 1;
                    let zw = alloc_app(arena, z, w);
                    let new_root = alloc_app(arena, zw, x_inner);
                    return reduce_nf_inner(arena, new_root, ctx);
                }
            }

            let new_left = reduce_nf_inner(arena, reduced_left, ctx);
            let new_right = reduce_nf_inner(arena, z, ctx);
            if new_left != reduced_left || new_right != z {
                alloc_app(arena, new_left, new_right)
            } else if reduced_left != left {
                alloc_app(arena, reduced_left, z)
            } else {
                root
            }
        }
    };

    if !ctx.exhausted {
        ctx.nf_cache.insert(root, result);
    }
    result
}

fn reduce_whnf_inner(arena: &mut Arena, root: NodeId, ctx: &mut EvalContext) -> NodeId {
    if let Some(&cached) = ctx.whnf_cache.get(&root) {
        return cached;
    }
    if ctx.steps >= ctx.max_steps {
        ctx.exhausted = true;
        return root;
    }

    let mut current = root;
    loop {
        if ctx.steps >= ctx.max_steps {
            ctx.exhausted = true;
            break;
        }

        match arena.get_unchecked(current).clone() {
            Node::Fork(left, z) => {
                let reduced_left = reduce_whnf_inner(arena, left, ctx);

                if let Some((x, y)) = split_delta2(arena, reduced_left) {
                    let reduced_x = reduce_whnf_inner(arena, x, ctx);

                    if is_delta(arena, reduced_x) {
                        ctx.steps += 1;
                        current = y;
                        continue;
                    }

                    if let Some(x_inner) = split_delta1(arena, reduced_x) {
                        ctx.steps += 1;
                        let yz = alloc_app(arena, y, z);
                        let xz = alloc_app(arena, x_inner, z);
                        current = alloc_app(arena, yz, xz);
                        continue;
                    }

                    if let Some((w, x_inner)) = split_delta2(arena, reduced_x) {
                        ctx.steps += 1;
                        let zw = alloc_app(arena, z, w);
                        current = alloc_app(arena, zw, x_inner);
                        continue;
                    }
                }

                if reduced_left != left {
                    current = alloc_app(arena, reduced_left, z);
                }
                break;
            }
            Node::Stem(_) | Node::Leaf(_) => break,
        }
    }

    if !ctx.exhausted {
        ctx.whnf_cache.insert(root, current);
    }
    current
}

// ============================================================================
// Primitive Operations for ANSI CL
// ============================================================================

/// Check if a node represents the boolean "true" (non-Nil Leaf or Fork)
pub fn is_truthy(arena: &Arena, id: NodeId) -> bool {
    match arena.get_unchecked(id) {
        Node::Leaf(OpaqueValue::Nil) => false,
        _ => true,
    }
}

/// Construct a cons cell (Fork)
pub fn cons(arena: &mut Arena, car: NodeId, cdr: NodeId) -> NodeId {
    arena.alloc(Node::Fork(car, cdr))
}

/// Get car of a cons cell
pub fn car(arena: &Arena, id: NodeId) -> Option<NodeId> {
    match arena.get_unchecked(id) {
        Node::Fork(left, _) => Some(*left),
        _ => None,
    }
}

/// Get cdr of a cons cell
pub fn cdr(arena: &Arena, id: NodeId) -> Option<NodeId> {
    match arena.get_unchecked(id) {
        Node::Fork(_, right) => Some(*right),
        _ => None,
    }
}

/// Create a Nil leaf
pub fn nil(arena: &mut Arena) -> NodeId {
    arena.alloc(Node::Leaf(OpaqueValue::Nil))
}

/// Create an integer leaf
pub fn integer(arena: &mut Arena, val: i64) -> NodeId {
    arena.alloc(Node::Leaf(OpaqueValue::Integer(val)))
}

/// Create a float leaf
pub fn float(arena: &mut Arena, val: f64) -> NodeId {
    arena.alloc(Node::Leaf(OpaqueValue::Float(val)))
}

/// Extract integer from a leaf
pub fn extract_int(arena: &Arena, id: NodeId) -> Option<i64> {
    match arena.get_unchecked(id) {
        Node::Leaf(OpaqueValue::Integer(n)) => Some(*n),
        _ => None,
    }
}

/// Extract float from a leaf
pub fn extract_float(arena: &Arena, id: NodeId) -> Option<f64> {
    match arena.get_unchecked(id) {
        Node::Leaf(OpaqueValue::Float(f)) => Some(*f),
        _ => None,
    }
}

// ============================================================================
// Arithmetic Primitives
// ============================================================================

pub fn add(arena: &mut Arena, a: NodeId, b: NodeId) -> Option<NodeId> {
    match (arena.get_unchecked(a), arena.get_unchecked(b)) {
        (Node::Leaf(OpaqueValue::Integer(x)), Node::Leaf(OpaqueValue::Integer(y))) => {
            Some(arena.alloc(Node::Leaf(OpaqueValue::Integer(x + y))))
        }
        (Node::Leaf(OpaqueValue::Float(x)), Node::Leaf(OpaqueValue::Float(y))) => {
            Some(arena.alloc(Node::Leaf(OpaqueValue::Float(x + y))))
        }
        (Node::Leaf(OpaqueValue::Integer(x)), Node::Leaf(OpaqueValue::Float(y))) => {
            Some(arena.alloc(Node::Leaf(OpaqueValue::Float(*x as f64 + y))))
        }
        (Node::Leaf(OpaqueValue::Float(x)), Node::Leaf(OpaqueValue::Integer(y))) => {
            Some(arena.alloc(Node::Leaf(OpaqueValue::Float(x + *y as f64))))
        }
        _ => None,
    }
}

pub fn sub(arena: &mut Arena, a: NodeId, b: NodeId) -> Option<NodeId> {
    match (arena.get_unchecked(a), arena.get_unchecked(b)) {
        (Node::Leaf(OpaqueValue::Integer(x)), Node::Leaf(OpaqueValue::Integer(y))) => {
            Some(arena.alloc(Node::Leaf(OpaqueValue::Integer(x - y))))
        }
        (Node::Leaf(OpaqueValue::Float(x)), Node::Leaf(OpaqueValue::Float(y))) => {
            Some(arena.alloc(Node::Leaf(OpaqueValue::Float(x - y))))
        }
        _ => None,
    }
}

pub fn mul(arena: &mut Arena, a: NodeId, b: NodeId) -> Option<NodeId> {
    match (arena.get_unchecked(a), arena.get_unchecked(b)) {
        (Node::Leaf(OpaqueValue::Integer(x)), Node::Leaf(OpaqueValue::Integer(y))) => {
            Some(arena.alloc(Node::Leaf(OpaqueValue::Integer(x * y))))
        }
        (Node::Leaf(OpaqueValue::Float(x)), Node::Leaf(OpaqueValue::Float(y))) => {
            Some(arena.alloc(Node::Leaf(OpaqueValue::Float(x * y))))
        }
        _ => None,
    }
}

pub fn div(arena: &mut Arena, a: NodeId, b: NodeId) -> Option<NodeId> {
    match (arena.get_unchecked(a), arena.get_unchecked(b)) {
        (Node::Leaf(OpaqueValue::Integer(x)), Node::Leaf(OpaqueValue::Integer(y))) if *y != 0 => {
            Some(arena.alloc(Node::Leaf(OpaqueValue::Integer(x / y))))
        }
        (Node::Leaf(OpaqueValue::Float(x)), Node::Leaf(OpaqueValue::Float(y))) => {
            Some(arena.alloc(Node::Leaf(OpaqueValue::Float(x / y))))
        }
        _ => None,
    }
}

// ============================================================================
// Comparison Primitives
// ============================================================================

pub fn eq(arena: &mut Arena, a: NodeId, b: NodeId) -> NodeId {
    let result = match (arena.get_unchecked(a), arena.get_unchecked(b)) {
        (Node::Leaf(OpaqueValue::Integer(x)), Node::Leaf(OpaqueValue::Integer(y))) => x == y,
        (Node::Leaf(OpaqueValue::Float(x)), Node::Leaf(OpaqueValue::Float(y))) => x == y,
        (Node::Leaf(OpaqueValue::Nil), Node::Leaf(OpaqueValue::Nil)) => true,
        _ => a == b, // Pointer equality for other cases
    };

    if result {
        // True: represented as (Stem Leaf) or Fork(Leaf, Leaf) per convention
        // Using Stem(Leaf) as K-combinator-like "true"
        let leaf = arena.alloc(Node::Leaf(OpaqueValue::Nil));
        arena.alloc(Node::Stem(leaf))
    } else {
        arena.alloc(Node::Leaf(OpaqueValue::Nil))
    }
}

pub fn lt(arena: &mut Arena, a: NodeId, b: NodeId) -> NodeId {
    let result = match (arena.get_unchecked(a), arena.get_unchecked(b)) {
        (Node::Leaf(OpaqueValue::Integer(x)), Node::Leaf(OpaqueValue::Integer(y))) => x < y,
        (Node::Leaf(OpaqueValue::Float(x)), Node::Leaf(OpaqueValue::Float(y))) => x < y,
        _ => false,
    };

    if result {
        let leaf = arena.alloc(Node::Leaf(OpaqueValue::Nil));
        arena.alloc(Node::Stem(leaf))
    } else {
        arena.alloc(Node::Leaf(OpaqueValue::Nil))
    }
}

// ============================================================================
// Pretty Printing
// ============================================================================

pub fn unparse(arena: &Arena, id: NodeId, depth: usize) -> String {
    if depth > 100 {
        return "...".to_string();
    }

    match arena.get_unchecked(id) {
        Node::Leaf(val) => match val {
            OpaqueValue::Nil => "nil".to_string(),
            OpaqueValue::Integer(n) => n.to_string(),
            OpaqueValue::Float(f) => format!("{:.6}", f),
            OpaqueValue::String(s) => format!("{:?}", s),
            OpaqueValue::VectorHandle(h) => format!("#<vector:{}>", h),
            OpaqueValue::ForeignPtr(p) => format!("#<foreign:{:?}>", p),
            OpaqueValue::Closure(id) => format!("#<closure:{}>", id),
            OpaqueValue::Generic(id) => format!("#<generic:{}>", id),
            OpaqueValue::Instance(id) => format!("#<instance:{}>", id),
            OpaqueValue::Class(id) => format!("#<class:{}>", id),
            OpaqueValue::Symbol(id) => format!("#<symbol:{}>", id),
            OpaqueValue::BigInt(n) => n.to_string(),
            OpaqueValue::StreamHandle(id) => format!("#<stream:{}>", id),
            OpaqueValue::Pid(pid) => format!("#<{}.{}.{}>", pid.node, pid.id, pid.serial),
            OpaqueValue::HashHandle(h) => format!("#<hash-table:{}>", h),
            OpaqueValue::Package(id) => format!("#<package:{}>", id),
            OpaqueValue::NextMethod(id) => format!("#<next-method:{}>", id),
            OpaqueValue::NextMethodP(id) => format!("#<next-method-p:{}>", id),
            OpaqueValue::CallMethod(id) => format!("#<call-method:{}>", id),
            OpaqueValue::MethodWrapper(a, b) => format!("#<method-wrapper:{}:{}>", a, b),
            OpaqueValue::Method(id) => format!("#<method:{}>", id),
        },
        Node::Stem(x) => format!("(Stem {})", unparse(arena, *x, depth + 1)),
        Node::Fork(l, r) => format!(
            "({} . {})",
            unparse(arena, *l, depth + 1),
            unparse(arena, *r, depth + 1)
        ),
    }
}

// ============================================================================
// Control Flow Structures
// ============================================================================

/// Control signals for non-local exits (tagbody/go, catch/throw)
pub enum ControlSignal {
    Go(u32),            // Jump to tag index
    Throw(NodeId),      // Throw with value
    ReturnFrom(NodeId), // Return from block
    Error(String),      // Runtime error
}

/// Frame for tagbody control construct
pub struct TagbodyFrame {
    pub tags: std::collections::HashMap<String, usize>,
    pub statements: Vec<NodeId>,
    pub pc: usize,
}

/// Control stack for managing non-local control flow
pub struct ControlStack {
    pub frames: Vec<ControlFrame>,
}

pub enum ControlFrame {
    Tagbody(TagbodyFrame),
    Catch { tag: NodeId },
    Block { name: NodeId },
}

impl ControlStack {
    pub fn new() -> Self {
        Self { frames: Vec::new() }
    }

    pub fn push(&mut self, frame: ControlFrame) {
        self.frames.push(frame);
    }

    pub fn pop(&mut self) -> Option<ControlFrame> {
        self.frames.pop()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena::deep_equal;
    use crate::tree_calculus as tc;

    // Helper: create △
    fn delta(arena: &mut Arena) -> NodeId {
        arena.alloc(Node::Leaf(OpaqueValue::Nil))
    }

    fn app(arena: &mut Arena, f: NodeId, x: NodeId) -> NodeId {
        if is_delta(arena, f) {
            arena.alloc(Node::Stem(x))
        } else {
            arena.alloc(Node::Fork(f, x))
        }
    }

    fn stem(arena: &mut Arena, x: NodeId) -> NodeId {
        arena.alloc(Node::Stem(x))
    }

    fn fork(arena: &mut Arena, l: NodeId, r: NodeId) -> NodeId {
        arena.alloc(Node::Fork(l, r))
    }

    #[test]
    fn test_k_rule() {
        // △ △ y z → y
        let mut arena = Arena::new();
        let mut ctx = EvalContext::default();

        let d = delta(&mut arena);
        let leaf = delta(&mut arena);
        let y = leaf;
        let z = stem(&mut arena, leaf);

        let k = app(&mut arena, d, d); // 4 4
        let k_y = app(&mut arena, k, y);
        let term = app(&mut arena, k_y, z);

        let result = reduce(&mut arena, term, &mut ctx);
        assert!(deep_equal(&arena, result, y));
    }

    #[test]
    fn test_s_rule() {
        // △ (△ x) y z → y z (x z)
        let mut arena = Arena::new();
        let mut ctx = EvalContext::default();

        let d = delta(&mut arena);
        let leaf = delta(&mut arena);
        let x = stem(&mut arena, leaf);
        let y = leaf;
        let z = fork(&mut arena, leaf, leaf);

        let stem_x = app(&mut arena, d, x); // 4 x
        let d_stem = app(&mut arena, d, stem_x);
        let d_stem_y = app(&mut arena, d_stem, y);
        let term = app(&mut arena, d_stem_y, z);

        let result = reduce(&mut arena, term, &mut ctx);

        // Expect ((y z) (x z))
        let yz = app(&mut arena, y, z);
        let xz = app(&mut arena, x, z);
        let expected = app(&mut arena, yz, xz);
        assert!(deep_equal(&arena, result, expected));
    }

    #[test]
    fn test_f_rule() {
        // △ (△ w x) y z → z w x
        let mut arena = Arena::new();
        let mut ctx = EvalContext::default();

        let d = delta(&mut arena);
        let leaf = delta(&mut arena);
        let w = stem(&mut arena, leaf);
        let x = fork(&mut arena, leaf, leaf);
        let y = stem(&mut arena, leaf);
        let z = leaf;

        let stem_w = arena.alloc(Node::Stem(w)); // Canonical stem for 4 w
        let fork = app(&mut arena, stem_w, x); // (4 w x)
        let d_fork = app(&mut arena, d, fork);
        let d_fork_y = app(&mut arena, d_fork, y);
        let term = app(&mut arena, d_fork_y, z);

        let result = reduce(&mut arena, term, &mut ctx);

        // Expect ((z w) x)
        let zw = app(&mut arena, z, w);
        let expected = app(&mut arena, zw, x);
        assert!(deep_equal(&arena, result, expected));
    }

    #[test]
    fn test_no_reduce_two_args() {
        // △ △ y should not reduce without third argument
        let mut arena = Arena::new();
        let mut ctx = EvalContext::default();

        let d = delta(&mut arena);
        let leaf = delta(&mut arena);
        let y = stem(&mut arena, leaf);

        let d_d = app(&mut arena, d, d);
        let term = app(&mut arena, d_d, y);
        let result = reduce(&mut arena, term, &mut ctx);
        assert_eq!(result, term);
    }

    #[test]
    fn test_stem_representation() {
        // Ensure Stem(x) is treated as (△ x) in the S rule.
        let mut arena = Arena::new();
        let mut ctx = EvalContext::default();

        let d = delta(&mut arena);
        let leaf = delta(&mut arena);
        let x = stem(&mut arena, leaf);
        let y = leaf;
        let z = fork(&mut arena, leaf, leaf);

        let stem_x = arena.alloc(Node::Stem(x));
        let d_stem = app(&mut arena, d, stem_x);
        let d_stem_y = app(&mut arena, d_stem, y);
        let term = app(&mut arena, d_stem_y, z);
        let result = reduce(&mut arena, term, &mut ctx);

        let yz = app(&mut arena, y, z);
        let xz = app(&mut arena, x, z);
        let expected = app(&mut arena, yz, xz);
        assert!(deep_equal(&arena, result, expected));
    }

    #[test]
    fn test_non_structural_leaf_blocks_reduction() {
        // Any non-Nil leaf should prevent reduction.
        let mut arena = Arena::new();
        let mut ctx = EvalContext::default();

        let d = delta(&mut arena);
        let y = arena.alloc(Node::Leaf(OpaqueValue::Integer(1)));
        let z = delta(&mut arena);

        let d_d = app(&mut arena, d, d);
        let d_d_y = app(&mut arena, d_d, y);
        let term = app(&mut arena, d_d_y, z);
        let result = reduce(&mut arena, term, &mut ctx);
        assert_eq!(result, term);
    }

    #[test]
    fn test_reduce_normalizes_inner_branch() {
        let mut arena = Arena::new();
        let mut ctx = EvalContext::default();

        let d = delta(&mut arena);
        let leaf = d;
        let left = stem(&mut arena, leaf);

        // redex: ((4 4) 4) 4 -> 4
        let k = app(&mut arena, d, d);
        let k_y = app(&mut arena, k, d);
        let redex = app(&mut arena, k_y, d);

        let term = app(&mut arena, left, redex);
        let result = reduce(&mut arena, term, &mut ctx);

        let expected = app(&mut arena, left, leaf);
        assert!(deep_equal(&arena, result, expected));
    }

    #[test]
    fn test_fundamental_queries() {
        let mut arena = Arena::new();
        let mut ctx = EvalContext::default();

        let leaf = tc::delta(&mut arena);
        let stem_node = arena.alloc(Node::Stem(leaf));
        let fork_left = arena.alloc(Node::Fork(leaf, leaf));
        let fork_node = arena.alloc(Node::Fork(fork_left, leaf));

        let k = tc::k(&mut arena);
        let i = tc::i(&mut arena);
        let k_i = tc::app(&mut arena, k, i);

        let is_leaf = tc::is_leaf(&mut arena);
        let is_stem = tc::is_stem(&mut arena);
        let is_fork = tc::is_fork(&mut arena);

        let leaf_app = app(&mut arena, is_leaf, leaf);
        let stem_app = app(&mut arena, is_leaf, stem_node);
        let fork_app = app(&mut arena, is_leaf, fork_node);
        let leaf_res = reduce(&mut arena, leaf_app, &mut ctx);
        let stem_res = reduce(&mut arena, stem_app, &mut ctx);
        let fork_res = reduce(&mut arena, fork_app, &mut ctx);
        assert!(
            deep_equal(&arena, leaf_res, k),
            "is_leaf on leaf -> {:?} (expected K {:?})",
            crate::printer::tree_format(&arena, leaf_res),
            crate::printer::tree_format(&arena, k)
        );
        assert!(deep_equal(&arena, stem_res, k_i));
        assert!(deep_equal(&arena, fork_res, k_i));

        let leaf_app = app(&mut arena, is_stem, leaf);
        let stem_app = app(&mut arena, is_stem, stem_node);
        let fork_app = app(&mut arena, is_stem, fork_node);
        let leaf_res = reduce(&mut arena, leaf_app, &mut ctx);
        let stem_res = reduce(&mut arena, stem_app, &mut ctx);
        let fork_res = reduce(&mut arena, fork_app, &mut ctx);
        assert!(deep_equal(&arena, leaf_res, k_i));
        assert!(deep_equal(&arena, stem_res, k));
        assert!(deep_equal(&arena, fork_res, k_i));

        let leaf_app = app(&mut arena, is_fork, leaf);
        let stem_app = app(&mut arena, is_fork, stem_node);
        let fork_app = app(&mut arena, is_fork, fork_node);
        let leaf_res = reduce(&mut arena, leaf_app, &mut ctx);
        let stem_res = reduce(&mut arena, stem_app, &mut ctx);
        let fork_res = reduce(&mut arena, fork_app, &mut ctx);
        assert!(deep_equal(&arena, leaf_res, k_i));
        assert!(deep_equal(&arena, stem_res, k_i));
        assert!(deep_equal(&arena, fork_res, k));
    }
}
