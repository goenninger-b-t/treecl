use crate::arena::{Arena, Node};
use crate::types::{NodeId, OpaqueValue};

pub struct EvalContext {
    pub steps: usize,
    pub max_steps: usize,
    pub depth: usize,
    pub stack: Vec<NodeId>,
}

impl Default for EvalContext {
    fn default() -> Self {
        Self {
            steps: 0,
            max_steps: 10000,
            depth: 0,
            stack: Vec::new(),
        }
    }
}

impl EvalContext {
    pub fn new() -> Self {
        Self::default()
    }
}

/// Perform reduction on the given root until normal form or step limit.
/// 
/// Implements canonical Tree Calculus reduction rules:
/// - △ △ y → y                    (leaf-leaf: identity/K behavior)
/// - △ (△ x) y → x                (leaf-stem: K combinator)
/// - △ (△ x z) y → ((x y) (z y))  (leaf-fork: S combinator)
/// 
/// The key insight: △ is the sole operator. It pattern-matches on its first argument
/// to decide which reduction rule applies. Reduction fires when △ has TWO arguments.
pub fn reduce(arena: &mut Arena, root: NodeId, ctx: &mut EvalContext) -> NodeId {
    let mut current = root;
    
    loop {
        if ctx.steps >= ctx.max_steps {
            return current;
        }
        
        match arena.get_unchecked(current).clone() {
            Node::Fork(left, y) => {
                // We have an application (left y)
                // Reduce left to WHNF first
                ctx.depth += 1;
                ctx.stack.push(left);
                let reduced_left = reduce_whnf(arena, left, ctx);
                ctx.stack.pop();
                ctx.depth -= 1;
                
                // Check if reduced_left is of form (△ x) = Fork(nil, x)
                if let Node::Fork(op, x) = arena.get_unchecked(reduced_left).clone() {
                    // Check if op is △ (nil)
                    if let Node::Leaf(OpaqueValue::Nil) = arena.get_unchecked(op) {
                        // We have ((△ x) y) - this is a redex!
                        // Dispatch based on structure of x
                        ctx.depth += 1;
                        ctx.stack.push(x);
                        let reduced_x = reduce_whnf(arena, x, ctx);
                        ctx.stack.pop();
                        ctx.depth -= 1;
                        
                        match arena.get_unchecked(reduced_x).clone() {
                            Node::Leaf(OpaqueValue::Nil) => {
                                // △ △ y → y
                                ctx.steps += 1;
                                current = y;
                                continue;
                            }
                            Node::Fork(a, b) => {
                                // Check if this is (△ z) pattern for K, or (△ z w) for S
                                if let Node::Leaf(OpaqueValue::Nil) = arena.get_unchecked(a) {
                                    // x = (△ b), so we have △ (△ b) y → b (K combinator)
                                    ctx.steps += 1;
                                    current = b;
                                    continue;
                                } else {
                                    // x = (a b) where a is not △
                                    // This is the S pattern: △ (a b) y → ((a y) (b y))
                                    // But wait - in canonical TC, first arg must be of form (△ z w)
                                    // Let's check if this should be S: △ (△ z w) y → ((z y) (w y))
                                    
                                    // x = Fork(a, b), we need a to be (△ z) = Fork(nil, z)
                                    if let Node::Fork(a_op, z) = arena.get_unchecked(a).clone() {
                                        if let Node::Leaf(OpaqueValue::Nil) = arena.get_unchecked(a_op) {
                                            // a = (△ z), so x = ((△ z) b) = (△ z b) in syntax
                                            // We have △ (△ z b) y → ((z y) (b y))
                                            ctx.steps += 1;
                                            let zy = arena.alloc(Node::Fork(z, y));
                                            let by = arena.alloc(Node::Fork(b, y));
                                            current = arena.alloc(Node::Fork(zy, by));
                                            continue;
                                        }
                                    }
                                    // Not a valid S pattern - no reduction
                                    return current;
                                }
                            }
                            Node::Stem(z) => {
                                // x is Stem(z) - this represents (△ z) in internal form
                                // △ (△ z) y → z (K combinator)
                                ctx.steps += 1;
                                current = z;
                                continue;
                            }
                            _ => {
                                // x is non-nil leaf - no reduction
                                return current;
                            }
                        }
                    }
                }
                
                // Not a redex - return with reduced left if different
                if reduced_left != left {
                    return arena.alloc(Node::Fork(reduced_left, y));
                }
                return current;
            }
            Node::Stem(inner) => {
                // Reduce inside Stem for full normalization
                // Reduce inside Stem for full normalization
                ctx.depth += 1;
                ctx.stack.push(inner);
                let reduced_inner = reduce(arena, inner, ctx);
                ctx.stack.pop();
                ctx.depth -= 1;
                if reduced_inner != inner {
                    return arena.alloc(Node::Stem(reduced_inner));
                }
                return current;
            }
            Node::Leaf(_) => return current, // Leaves are normal forms
        }
    }
}


/// Reduce to Weak Head Normal Form
/// Uses same rules as reduce but stops at head normal form.
pub fn reduce_whnf(arena: &mut Arena, root: NodeId, ctx: &mut EvalContext) -> NodeId {
    let mut current = root;
    
    loop {
        if ctx.steps >= ctx.max_steps { return current; }
        
        match arena.get_unchecked(current).clone() {
            Node::Fork(left, y) => {
                ctx.depth += 1;
                ctx.stack.push(left);
                let reduced_left = reduce_whnf(arena, left, ctx);
                ctx.stack.pop();
                ctx.depth -= 1;
                
                // Check if reduced_left is of form (△ x) = Fork(nil, x)
                if let Node::Fork(op, x) = arena.get_unchecked(reduced_left).clone() {
                    if let Node::Leaf(OpaqueValue::Nil) = arena.get_unchecked(op) {
                        // We have ((△ x) y) - check for redex
                        ctx.depth += 1;
                        ctx.stack.push(x);
                        let reduced_x = reduce_whnf(arena, x, ctx);
                        ctx.stack.pop();
                        ctx.depth -= 1;
                        
                        match arena.get_unchecked(reduced_x).clone() {
                            Node::Leaf(OpaqueValue::Nil) => {
                                // △ △ y → y
                                ctx.steps += 1;
                                current = y;
                                continue;
                            }
                            Node::Fork(a, b) => {
                                // Check K pattern: x = (△ b)
                                if let Node::Leaf(OpaqueValue::Nil) = arena.get_unchecked(a) {
                                    // △ (△ b) y → b
                                    ctx.steps += 1;
                                    current = b;
                                    continue;
                                }
                                // S-redex - in WHNF we stop here
                                return current;
                            }
                            Node::Stem(z) => {
                                // Stem form of K
                                ctx.steps += 1;
                                current = z;
                                continue;
                            }
                            _ => return current,
                        }
                    }
                }
                
                // Not a redex
                if reduced_left != left {
                    return arena.alloc(Node::Fork(reduced_left, y));
                }
                return current;
            }
            Node::Stem(_) | Node::Leaf(_) => return current,
        }
    }
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
        },
        Node::Stem(x) => format!("(Stem {})", unparse(arena, *x, depth + 1)),
        Node::Fork(l, r) => format!("({} . {})", 
            unparse(arena, *l, depth + 1), 
            unparse(arena, *r, depth + 1)),
    }
}

// ============================================================================
// Control Flow Structures
// ============================================================================

/// Control signals for non-local exits (tagbody/go, catch/throw)
pub enum ControlSignal {
    Go(u32),           // Jump to tag index
    Throw(NodeId),     // Throw with value
    ReturnFrom(NodeId), // Return from block
    Error(String),     // Runtime error
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
    
    // Helper: create nil (△)
    fn nil(arena: &mut Arena) -> NodeId {
        arena.alloc(Node::Leaf(OpaqueValue::Nil))
    }
    
    // Helper: create K = △ △
    fn k(arena: &mut Arena) -> NodeId {
        let n = nil(arena);
        arena.alloc(Node::Fork(n, n))
    }
    
    #[test]
    fn test_identity_rule() {
        // △ △ y → y
        let mut arena = Arena::new();
        let mut ctx = EvalContext::default();
        
        let n = nil(&mut arena);
        let y = arena.alloc(Node::Leaf(OpaqueValue::Integer(42)));
        
        // Build △ △: Fork(nil, nil)
        let nn = arena.alloc(Node::Fork(n, n));
        
        // Build (△ △) y: Fork(nn, y)
        let app = arena.alloc(Node::Fork(nn, y));
        
        let result = reduce(&mut arena, app, &mut ctx);
        assert_eq!(extract_int(&arena, result), Some(42));
    }
    
    #[test]
    fn test_k_combinator() {
        // △ (△ x) y → x
        let mut arena = Arena::new();
        let mut ctx = EvalContext::default();
        
        let n = nil(&mut arena);
        let x = arena.alloc(Node::Leaf(OpaqueValue::Integer(1)));
        let y = arena.alloc(Node::Leaf(OpaqueValue::Integer(2)));
        
        // Build △ x: Fork(nil, x)
        let nx = arena.alloc(Node::Fork(n, x));
        
        // Build △ (△ x): Fork(nil, nx) 
        let n_nx = arena.alloc(Node::Fork(n, nx));
        
        // Build (△ (△ x)) y: Fork(n_nx, y)
        let app = arena.alloc(Node::Fork(n_nx, y));
        
        let result = reduce(&mut arena, app, &mut ctx);
        assert_eq!(extract_int(&arena, result), Some(1));
    }
    
    #[test]
    fn test_s_combinator() {
        // S pattern: △ (△ x z) y → ((x y) (z y))
        // Use simple non-reducing integers for x and z
        // Then result is Fork(Fork(x,y), Fork(z,y)) which doesn't reduce further
        
        let mut arena = Arena::new();
        let mut ctx = EvalContext::default();
        
        let n = nil(&mut arena);
        let x = arena.alloc(Node::Leaf(OpaqueValue::Integer(1))); // Simple value, not △
        let z = arena.alloc(Node::Leaf(OpaqueValue::Integer(2))); // Simple value, not △
        let y = arena.alloc(Node::Leaf(OpaqueValue::Integer(3)));
        
        // Build △ x = Fork(nil, x)
        let nx = arena.alloc(Node::Fork(n, x));
        
        // Build (△ x) z = Fork(nx, z) = (△ x z)
        let nx_z = arena.alloc(Node::Fork(nx, z));
        
        // Build △ (△ x z) = Fork(nil, nx_z)
        let triage = arena.alloc(Node::Fork(n, nx_z));
        
        // Build (△ (△ x z)) y = Fork(triage, y)
        let app = arena.alloc(Node::Fork(triage, y));
        
        let result = reduce(&mut arena, app, &mut ctx);
        
        // S rule: △ (△ x z) y → ((x y) (z y))
        // = Fork(Fork(1, 3), Fork(2, 3))
        // Neither (1 3) nor (2 3) reduce because 1 and 2 are not △
        
        // Result should be Fork(Fork(1,3), Fork(2,3))
        match arena.get_unchecked(result) {
            Node::Fork(left, right) => {
                // Left should be Fork(1, 3)
                match arena.get_unchecked(*left) {
                    Node::Fork(a, b) => {
                        assert_eq!(extract_int(&arena, *a), Some(1));
                        assert_eq!(extract_int(&arena, *b), Some(3));
                    }
                    other => panic!("Expected Fork(1,3), got {:?}", other),
                }
                // Right should be Fork(2, 3)
                match arena.get_unchecked(*right) {
                    Node::Fork(c, d) => {
                        assert_eq!(extract_int(&arena, *c), Some(2));
                        assert_eq!(extract_int(&arena, *d), Some(3));
                    }
                    other => panic!("Expected Fork(2,3), got {:?}", other),
                }
            }
            other => panic!("Expected Fork(Fork(1,3), Fork(2,3)), got {:?}", other),
        }
    }
    
    #[test]
    fn test_i_combinator() {
        // I = K K = (△ △) (△ △)
        // But K = △ △ is already identity! So K x = x.
        // I = K K = (△ △) (△ △) → (△ △) by identity.
        // Then I x = K x = x. So I behaves like identity too.
        let mut arena = Arena::new();
        let mut ctx = EvalContext::default();
        
        let kk = k(&mut arena);
        let i = arena.alloc(Node::Fork(kk, kk)); // I = K K
        
        let x = arena.alloc(Node::Leaf(OpaqueValue::Integer(99)));
        
        // Build I x: Fork(i, x)
        let app = arena.alloc(Node::Fork(i, x));
        
        let result = reduce(&mut arena, app, &mut ctx);
        assert_eq!(extract_int(&arena, result), Some(99));
    }
    
    #[test]
    fn test_constant_combinator() {
        // The constant combinator: △ (△ x) y → x
        // This drops the second argument and returns the first
        let mut arena = Arena::new();
        let mut ctx = EvalContext::default();
        
        let n = nil(&mut arena);
        let x_val = arena.alloc(Node::Leaf(OpaqueValue::Integer(42)));
        let y_val = arena.alloc(Node::Leaf(OpaqueValue::Integer(99)));
        
        // Build △ x = Fork(nil, x)
        let nx = arena.alloc(Node::Fork(n, x_val));
        
        // Build △ (△ x) = Fork(nil, nx)
        let n_nx = arena.alloc(Node::Fork(n, nx));
        
        // Build (△ (△ x)) y = Fork(n_nx, y)
        let app = arena.alloc(Node::Fork(n_nx, y_val));
        
        let result = reduce(&mut arena, app, &mut ctx);
        // Should return x = 42, dropping y
        assert_eq!(extract_int(&arena, result), Some(42));
    }
}
