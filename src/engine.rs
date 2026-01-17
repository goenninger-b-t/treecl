use crate::arena::{Graph, Node, NodeId, Primitive};
use num_bigint::{BigUint, BigInt, Sign};
use num_traits::{Zero, One, Signed};
use smallvec::smallvec;

pub struct EvalContext {
    pub steps: u64,
    pub step_limit: u64,
}

impl Default for EvalContext {
    fn default() -> Self {
        Self {
            steps: 0,
            step_limit: 10_000_000,
        }
    }
}

// ZigZag Encoding for Signed Integers
//  0 -> 0
// -1 -> 1
//  1 -> 2
// -2 -> 3
//  2 -> 4
fn zigzag(n: &BigInt) -> BigUint {
    let _zero = BigInt::zero();
    let _one = BigInt::one();
    match n.sign() {
        Sign::NoSign => BigUint::zero(),
        Sign::Plus => {
            // n * 2
            n.to_biguint().unwrap() << 1
        }
        Sign::Minus => {
            // (-n * 2) - 1  => (abs(n) * 2) - 1
            let abs_n = n.abs().to_biguint().unwrap();
            (abs_n << 1) - BigUint::one()
        }
    }
}

fn unzigzag(n: &BigUint) -> BigInt {
    if n.is_zero() {
        BigInt::zero()
    } else {
        // if even -> positive: n / 2
        // if odd  -> negative: -(n + 1) / 2
        if n.bit(0) { // odd
            let val = (n + BigUint::one()) >> 1;
            BigInt::from(val) * -1
        } else { // even
            BigInt::from(n >> 1)
        }
    }
}

/// Helper: Encodes a raw BigUint (Natural Number) into the Triage graph.
fn encode_raw_nat(g: &mut Graph, n: &BigUint) -> NodeId {
    if n.is_zero() {
        return g.add(Node::Leaf);
    }
    
    // bit
    let bit_node = if n.bit(0) {
        // bit 1 = (n n)
        let leaf = g.add(Node::Leaf);
        g.add(Node::App {
            func: leaf,
            args: smallvec![leaf],
        })
    } else {
        // bit 0 = n
        g.add(Node::Leaf)
    };
    
    // rest = n >> 1
    let rest = encode_raw_nat(g, &(n >> 1));
    
    // ((n bit) rest)
    // First, construct (n bit)
    let leaf = g.add(Node::Leaf);
    let n_bit = g.add(Node::App {
        func: leaf,
        args: smallvec![bit_node],
    });
    
    // Then ((n bit) rest)
    g.add(Node::App {
        func: n_bit,
        args: smallvec![rest],
    })
}

/// Public: Encodes a BigInt using ZigZag encoding.
pub fn encode_int(g: &mut Graph, n: &BigInt) -> NodeId {
    let raw = zigzag(n);
    encode_raw_nat(g, &raw)
}

/// Backward compatibility for unsigned (literals in parser currently use u32 which is +)
/// Takes BigUint, treats as positive BigInt, encodes.
pub fn encode_nat(g: &mut Graph, n: &BigUint) -> NodeId {
    encode_int(g, &BigInt::from(n.clone()))
}




pub fn decode_raw_nat(g: &Graph, id: NodeId) -> Option<BigUint> {
    let node = g.get(g.resolve(id));
    match node {
        Node::Leaf => Some(BigUint::zero()),
        Node::Fork(bit, rest) => {
            let rest_val = decode_raw_nat(g, *rest)?;
            let b_val = match g.get(g.resolve(*bit)) {
                Node::Leaf => 0u8,
                Node::Stem(l) => {
                     if matches!(g.get(g.resolve(*l)), Node::Leaf) { 1u8 } else { return None; }
                }
                _ => return None,
            };
            let mut val = rest_val << 1;
            if b_val == 1 {
                val |= BigUint::one();
            }
            Some(val)
        }
        _ => None
    }
}

pub fn decode_int(g: &Graph, id: NodeId) -> Option<BigInt> {
    let raw = decode_raw_nat(g, id)?;
    Some(unzigzag(&raw))
}

pub fn decode_nat(g: &Graph, id: NodeId) -> Option<BigUint> {
    let i = decode_int(g, id)?;
    if i >= BigInt::zero() {
        i.to_biguint()
    } else {
        None
    }
}

pub fn make_tag(g: &mut Graph, tag_prim: Primitive, val: NodeId) -> NodeId {
    // Wrapper: App(Stem(tag), App(Stem(val), KK))
    // Canonicalizes to Fork(tag, Fork(val, KK))
    
    // 1. Tag Prim Node
    let t = g.add(Node::Prim(tag_prim));
    // 2. Stem(t)
    let dt = g.add(Node::Stem(t));
    
    // 3. Stem(val)
    let df = g.add(Node::Stem(val));
    
    // 4. KK = Fork(Leaf, Leaf)
    let leaf = g.add(Node::Leaf);
    let kk = g.add(Node::Fork(leaf, leaf));
    
    // 5. App(df, KK) -> Fork(val, KK) if canon
    let inner = g.add(Node::App { func: df, args: smallvec::smallvec![kk] });
    
    // 6. App(dt, inner) -> Fork(t, inner) if canon
    g.add(Node::App { func: dt, args: smallvec::smallvec![inner] })
}

pub fn encode_str(g: &mut Graph, s: &str) -> NodeId {
    // Fold right: Fork(char, rest). End with Leaf.
    let mut rest = g.add(Node::Leaf);
    for c in s.chars().rev() {
        let n = c as u32;
        use num_bigint::BigUint;
        let nat_node = encode_nat(g, &BigUint::from(n));
        
        // Wrap char in TagChar
        let char_node = make_tag(g, Primitive::TagChar, nat_node);
        
        rest = g.add(Node::Fork(char_node, rest));
    }
    
    // Wrap string in TagStr
    make_tag(g, Primitive::TagStr, rest)
}

pub fn decode_str(g: &Graph, id: NodeId) -> Option<String> {
    let (inner_id, _tag) = unwrap_data(g, id);
    // We strictly expect TagStr? Or lenient?
    // Let's be lenient for legacy/untagged lists, but if TagStr is present, it's fine.
    
    let mut s = String::new();
    let mut curr = inner_id;
    loop {
        // Resolve ind
        curr = g.resolve(curr);
        match g.get(curr) {
            Node::Leaf => return Some(s),
            Node::Fork(char_node, rest) => {
                // Decode char
                // Char might be tagged
                let (c_inner, _c_tag) = unwrap_data(g, *char_node);
                
                let code = decode_nat(g, c_inner)?;
                // code is BigUint. Convert to u32.
                use std::convert::TryInto;
                let u: u32 = code.try_into().ok()?;
                let c = std::char::from_u32(u)?;
                s.push(c);
                curr = *rest;
            }
            _ => return None,
        }
    }
}

pub fn decode_char(g: &Graph, id: NodeId) -> Option<char> {
    let (inner, tag) = unwrap_data(g, id);
    if matches!(tag, Some(Primitive::TagChar)) {
         use std::convert::TryInto;
         let n_uint = decode_nat(g, inner)?;
         let u: u32 = n_uint.try_into().ok()?;
         std::char::from_u32(u)
    } else {
        None
    }
}

pub fn node_depth(g: &Graph, id: NodeId) -> usize {
    // Iterative depth calculation to avoid stack overflow
    let mut stack = vec![(id, 0)]; // (node, current_depth)
    let mut max_depth = 0;
    
    // Safety check: if too many iterations, bail? No, strict DFS is fine for depth if cycle-free.
    // Triage is DAG.
    
    // Actually, simple DFS stack might just verify paths.
    // To get MAX depth, we need to visit all paths.
    // Standard DFS.
    
    while let Some((curr, d)) = stack.pop() {
        if d > max_depth { max_depth = d; }
        
        // Don't revisit nodes if we found a longer path? 
        // DAG depth is max length of any path. 
        // Memoization would help if DAG is re-entrant.
        // For now, let's just do simple DFS but checking visited to avoid cycles (if any) and repeated work.
        // Actually, for pure trees/DAGs, we just want max path.
        // Simple stack DFS.
        
        let curr = g.resolve(curr);
        match g.get(curr) {
            Node::Fork(a, b) => {
               // Push recursive children
               stack.push((*b, d + 1));
               stack.push((*a, d + 1));
            }
            Node::Stem(a) => {
                stack.push((*a, d + 1));
            }
            Node::App { func, args } => {
                // Depth is usually defined by tree structure (CONS/App)
                stack.push((*func, d + 1));
                for arg in args {
                    stack.push((*arg, d + 1));
                }
            }
            Node::Ind(a) => stack.push((*a, d)), // Ind doesn't add depth
            _ => {}
        }
    }
    max_depth
}

pub fn unparse(g: &Graph, id: NodeId) -> String {
    // Iterative unparse using explicit stack
    // We need to reconstruct the string post-order (sort of).
    // Actually, we can build it pre-order with holes? Or just recursively logic but on heap stack.
    
    // Trying heuristic first
    if let Some(s) = decode_str(g, id) {
        let printable = s.chars().all(|c| !c.is_control() || c.is_whitespace());
        if !s.is_empty() && printable {
             return format!("{:?}", s);
        }
    }

    enum Action {
        Visit(NodeId),
        EmitStr(String),
        EmitEndParams, // ')'
        EmitSpace,
    }
    
    let mut result = String::new();
    let mut stack = vec![Action::Visit(id)];
    
    // We need a smart way to handle parentheses.
    // (n a b)
    // Visit(App) -> Push Emit(')'); Push Visit(b); Push Space; Push Visit(a); Push Emit('('); ...
    
    while let Some(action) = stack.pop() {
        match action {
            Action::EmitStr(s) => result.push_str(&s),
            Action::EmitEndParams => result.push(')'),
            Action::EmitSpace => result.push(' '),
            Action::Visit(node_id) => {
                let curr = g.resolve(node_id);
                match g.get(curr) {
                    Node::Leaf => result.push('n'),
                    Node::Prim(op) => result.push_str(&format!("#<Prim:{:?}>", op)),
                    Node::Stem(x) => {
                        stack.push(Action::EmitEndParams); // )
                        stack.push(Action::Visit(*x));     // x
                        stack.push(Action::EmitSpace);     // space
                        stack.push(Action::EmitStr("(n".to_string())); // (n
                    }
                    Node::Fork(x, y) => {
                        stack.push(Action::EmitEndParams); // )
                        stack.push(Action::Visit(*y));     // y
                        stack.push(Action::EmitSpace);     // space
                        stack.push(Action::Visit(*x));     // x
                        stack.push(Action::EmitSpace);     // space
                         stack.push(Action::EmitStr("(n".to_string())); // (n
                    }
                    Node::App { func, args } => {
                        stack.push(Action::EmitEndParams); // )
                        // Args reverse order
                        for arg in args.iter().rev() {
                            stack.push(Action::Visit(*arg));
                            stack.push(Action::EmitSpace);
                        }
                        stack.push(Action::Visit(*func));
                        stack.push(Action::EmitStr("(".to_string()));
                    }
                    Node::Ind(x) => stack.push(Action::Visit(*x)),
                    Node::Float(f) => result.push_str(&format!("{}", f)),
                }
            }
        }
    }
    result
}

pub fn node_count(g: &Graph, id: NodeId) -> usize {
    let mut stack = vec![id];
    let mut count = 0;
    while let Some(curr) = stack.pop() {
        count += 1;
        match g.get(g.resolve(curr)) {
            Node::Stem(x) => stack.push(*x),
            Node::Fork(x, y) => {
                stack.push(*y);
                stack.push(*x);
            }
            Node::App { func, args } => {
                stack.push(*func);
                for arg in args {
                    stack.push(*arg);
                }
            }
            Node::Ind(x) => {
                count -= 1; 
                stack.push(*x);
            }
            Node::Float(_) => {}
            _ => {}
        }
    }
    count
}

pub fn is_true(g: &Graph, id: NodeId) -> bool {
    let node = g.get(g.resolve(id));
    if let Node::Fork(l, r) = node {
        let l_node = g.get(g.resolve(*l));
        let r_node = g.get(g.resolve(*r));
        matches!(l_node, Node::Leaf) && matches!(r_node, Node::Leaf)
    } else {
        false
    }
}

pub fn tree_contains(g: &Graph, root: NodeId, target: NodeId) -> bool {
    // Iterative search
    // We already resolved root/target in loop if needed?
    // Target is constant.
    let target = g.resolve(target);
    let mut stack = vec![g.resolve(root)];
    
    // We need to avoid cycles? Triage is DAG.
    // But duplicate visiting is waste.
    // Using simple stack.
    
    while let Some(curr) = stack.pop() {
        let curr = g.resolve(curr);
        if curr == target { return true; }
        
        match g.get(curr) {
            Node::Stem(x) => stack.push(*x),
            Node::Fork(x, y) => {
                stack.push(*y);
                stack.push(*x);
            }
            Node::App { func, args } => {
                stack.push(*func);
                for arg in args {
                    stack.push(*arg);
                }
            }
            // Ind resolved at loop start
            Node::Prim(_) | Node::Leaf | Node::Float(_) => {}
            _ => {} // Should be covered
        }
    }
    false
}

pub fn tree_match(g: &mut Graph, template: NodeId, target: NodeId, ctx: &mut EvalContext) -> bool {
    // Attempt to resolve/reduce if needed?
    // We try to match structure.
    // If we hit App, we should reduce it?
    // Only if the other side is NOT App?
    // If both are App, maybe we match structure of App?
    // Triage convention: Match is structural on VALUES.
    // So we force values.
    
    let mut t1 = g.resolve(template);
    let mut t2 = g.resolve(target);
    
    if t1 == t2 { return true; }
    
    // Check Any on t1
    if let Node::Prim(Primitive::Any) = g.get(t1) {
        return true;
    }
    
    // Check if we need to reduce
    if !g.is_value(t1) {
         if reduce_step(g, t1, ctx) {
             t1 = g.resolve(t1);
         }
    }
    if !g.is_value(t2) {
         if reduce_step(g, t2, ctx) {
             t2 = g.resolve(t2);
         }
    }
    
    // Re-resolve
    t1 = g.resolve(t1);
    t2 = g.resolve(t2);
    
    if t1 == t2 { return true; }

    // Clone to avoid borrow issues
    let n1 = g.get(t1).clone();
    let n2 = g.get(t2).clone();
    
    match (n1, n2) {
        (Node::Leaf, Node::Leaf) => true,
        (Node::Stem(x), Node::Stem(y)) => tree_match(g, x, y, ctx),
        (Node::Fork(x1, x2), Node::Fork(y1, y2)) => {
            tree_match(g, x1, y1, ctx) && tree_match(g, x2, y2, ctx)
        },
        (Node::App { func: f1, args: a1 }, Node::App { func: f2, args: a2 }) => {
             // If we are here, neither reduced to Value (or both are stuck Apps).
             // Match structure.
             if !tree_match(g, f1, f2, ctx) { return false; }
             if a1.len() != a2.len() { return false; }
             for (arg1, arg2) in a1.iter().zip(a2.iter()) {
                 if !tree_match(g, *arg1, *arg2, ctx) { return false; }
             }
             true
        }
        (Node::Prim(p1), Node::Prim(p2)) => p1 == p2,
        (Node::Float(f1), Node::Float(f2)) => f1.to_bits() == f2.to_bits(),
        _ => false
    }
}

pub fn get_tagged_prim(g: &Graph, id: NodeId) -> Option<Primitive> {
    let node = g.get(g.resolve(id));
    
    // Tag structure usually canonicalizes to Fork(t, inner)
    // inner canonicalizes to Fork(p, KK)
    // So Tag = Fork(t, Fork(p, KK))
    
    if let Node::Fork(_t, inner) = node {
        let inner_node = g.get(g.resolve(*inner));
        if let Node::Fork(p, _kk) = inner_node {
             let p_val = g.get(g.resolve(*p));
             if let Node::Prim(op) = p_val {
                 return Some(*op);
             }
        }
    }
    
    // Fallback: Check App structure (if canonicalization didn't happen for some reason)
    if let Node::App { func: outer_func, args: outer_args } = node {
        if outer_args.len() == 1 {
             let of_val = g.get(g.resolve(*outer_func));
             if let Node::Stem(_t) = of_val {
                 let inner_node = g.get(g.resolve(outer_args[0]));
                 // Handle inner being Fork (likely) or App
                 if let Node::Fork(p, _kk) = inner_node {
                      let p_val = g.get(g.resolve(*p));
                      if let Node::Prim(op) = p_val { return Some(*op); }
                 }
                 if let Node::App { func: inner_func, args: inner_args } = inner_node {
                     if inner_args.len() == 1 {
                         let if_val = g.get(g.resolve(*inner_func));
                         if let Node::Stem(p) = if_val {
                             let p_val = g.get(g.resolve(*p));
                             if let Node::Prim(op) = p_val { return Some(*op); }
                         }
                     }
                 }
             }
        }
    }
    None
}

pub fn unwrap_data(g: &Graph, id: NodeId) -> (NodeId, Option<Primitive>) {
    let node = g.get(g.resolve(id));
    // Check for Tag signature: Fork(t, Fork(v, KK))
    if let Node::Fork(t, inner) = node {
        let t_val = g.get(g.resolve(*t));
        if let Node::Prim(op) = t_val {
             match op {
                 Primitive::TagStr | Primitive::TagChar => {
                     let inner_node = g.get(g.resolve(*inner));
                     // Expect Fork(v, KK)
                     if let Node::Fork(v, _kk) = inner_node {
                         return (*v, Some(*op));
                     }
                 }
                 _ => {}
             }
        }
    }
    (id, None)
}

pub fn reduce_step(g: &mut Graph, root: NodeId, ctx: &mut EvalContext) -> bool {
    // Iterative spine unwinding to prevent stack overflow
    // We unwind the spine of App nodes to find the leftmost function ‘head’.
    // The spine is App( ... App(head, arg1), arg2 ... )
    // We collect the App nodes in a stack: [App1, App2, ...] where App1 is top-level.
    
    let mut stack = Vec::new();
    let mut curr = root;
    
    // 1. Unwind
    loop {
        // Resolve Ind if any
        curr = g.resolve(curr); // This resolves Ind to target
        
        let node = g.get(curr).clone();
        if let Node::App { func, .. } = node {
             stack.push(curr); // Push the App node ID
             curr = func;      // Descend
        } else {
             break; // Found head (Leaf, Stem, Fork, or Prim)
        }
    }
    
    // 2. Reduce Top-Down (Prioritize Flattening)
    // Stack contains [App_Top, ..., App_Bottom]
    for &app_id in &stack {
        // app_id is an App node.
        // We need to resolve its function to pass as 'head' to attempt_reduction.
        let app_node = g.get(app_id).clone();
        
        let (func, args) = if let Node::App { func, args } = app_node {
            (func, args)
        } else {
            continue;
        };
        
        // We don't resolve func deeply here because attempt_reduction handles resolving?
        // Actually attempt_reduction resolves head.
        // Func might be the next App in the stack (if nested) OR the ultimate head.
        // This is exactly what we want.
        
        let reduced = attempt_reduction(g, app_id, func, &args, ctx);
        if reduced {
            return true;
        }
    }
        
    
    false
}

// Helper to encapsulate the reduction logic for a single level
fn attempt_reduction(g: &mut Graph, root: NodeId, head: NodeId, args: &[NodeId], ctx: &mut EvalContext) -> bool {
    let head_node = g.get(g.resolve(head)).clone(); // Resolve head just in case
    
    match head_node {
        Node::Leaf => {
             if args.len() >= 3 {
                 try_reduce_rule(g, root, args[0], args[1], args[2], &args[3..], ctx)
             } else if args.len() == 2 {
                 g.set(root, Node::Fork(args[0], args[1]));
                 true
             } else if args.len() == 1 {
                 g.set(root, Node::Stem(args[0]));
                 true
             } else {
                 false
             }
        }
        Node::Stem(p) => {
             if args.len() >= 2 {
                 try_reduce_rule(g, root, p, args[0], args[1], &args[2..], ctx)
             } else {
                 false
             }
        }
        Node::Fork(p, q) => {
             // Check tags
             if let Some(op) = get_tagged_prim(g, head) {
                  let prim_node = g.add(Node::Prim(op));
                  use smallvec::SmallVec;
                  let new_args: SmallVec<[NodeId; 3]> = args.iter().cloned().collect();
                  
                  let new_app = g.add(Node::App {
                      func: prim_node,
                      args: new_args
                  });
                  g.set(root, Node::Ind(new_app));
                  return true;
             }
             
             if args.len() >= 1 {
                 try_reduce_rule(g, root, p, q, args[0], &args[1..], ctx)
             } else {
                 false
             }
        }
        Node::App { func: f_inner, args: inner_args } => {
            // Check Tagged Primitive in App structure ((TagStr ...) ...)
            if let Some(op) = get_tagged_prim(g, head) {
                 let prim_node = g.add(Node::Prim(op));
                 use smallvec::SmallVec;
                 let new_args: SmallVec<[NodeId; 3]> = args.iter().cloned().collect();
                 
                 let new_app = g.add(Node::App {
                     func: prim_node,
                     args: new_args
                 });
                 g.set(root, Node::Ind(new_app));
                 return true;
            }

            // Flatten ((f a) b) -> (f a b)
            let mut new_args = inner_args.clone();
            new_args.extend(args.iter().cloned());
            
            let new_app = g.add(Node::App {
                func: f_inner,
                args: new_args
            });
            
            g.set(root, Node::Ind(new_app));
            true
        }
        Node::Prim(op) => {
            let _spine_args = args;

                    // Primitive Application
                    let needed = match op {
                        Primitive::Add | Primitive::Sub | Primitive::Mul | Primitive::Div | Primitive::Mod | Primitive::Eq | Primitive::Cons | Primitive::Contains | Primitive::Match => 2,
                        Primitive::First | Primitive::Rest | Primitive::IsNum | Primitive::IsStr | Primitive::IsChar | Primitive::IsProg | Primitive::IsNeg | Primitive::IsPrim | Primitive::Size | Primitive::TagStr | Primitive::TagChar => 1,
                        
                        // Float Arity 1
                        Primitive::IntToFloat | Primitive::FloatToInt | Primitive::IsFloat | Primitive::Floor | Primitive::Ceil | Primitive::Sqrt | Primitive::Sin | Primitive::Cos | Primitive::Tan | Primitive::Abs => 1,
                        
                        Primitive::SearchStep => 4,
                        Primitive::Any => 0,
                        Primitive::Identity => 1,
                    };
                    
                    if args.len() >= needed {
                        if op == Primitive::Identity {
                             g.set(root, Node::Ind(args[0]));
                             return true;
                        }
                        // Pre-process args: Unwrap data if necessary
                        let needs_unwrap = matches!(op, 
                            Primitive::First | Primitive::Rest | Primitive::Size |
                            Primitive::Add | Primitive::Sub | Primitive::Mul | Primitive::Div | Primitive::Mod | 
                            Primitive::IsNeg | Primitive::SearchStep
                        );

                        let raw_arg1 = args[0];
                        let (arg1, _val_tag1) = if needs_unwrap { unwrap_data(g, raw_arg1) } else { (raw_arg1, None) };
                        
                        let raw_arg2 = if needed >= 2 { Some(args[1]) } else { None };
                        let arg2 = if let Some(a2) = raw_arg2 {
                            let (v, _t) = if matches!(op, Primitive::Add | Primitive::Sub | Primitive::Mul | Primitive::Div | Primitive::Mod) {
                                unwrap_data(g, a2)
                            } else {
                                (a2, None)
                            };
                            Some(v)
                        } else { None };
                        
                        // List Ops
                        if op == Primitive::Cons {
                             if let Some(a2) = arg2 {
                                let fork = g.add(Node::Fork(arg1, a2));
                                let mut final_res = fork;
                                for &arg in &args[needed..] {
                                    final_res = g.add(Node::App {
                                        func: final_res,
                                        args: smallvec![arg]
                                    });
                                }
                                if final_res != root {
                                    g.set(root, Node::Ind(final_res));
                                }
                                return true;
                             }
                        }
                        
                        if op == Primitive::First || op == Primitive::Rest {
                             if !g.is_value(arg1) {
                                // println!("Debug First/Rest: arg1 not value: {}", unparse(g, arg1));
                                return reduce_step(g, arg1, ctx);
                             }
                             if let Node::Fork(u, v) = g.get(g.resolve(arg1)) {
                                let res_node = if op == Primitive::First { *u } else { *v };
                                let mut final_res = res_node;
                                for &arg in &args[needed..] {
                                    final_res = g.add(Node::App {
                                        func: final_res,
                                        args: smallvec![arg]
                                    });
                                }
                                if final_res != root {
                                    g.set(root, Node::Ind(final_res));
                                }
                                return true;
                             } else {
                                 // Stuck?
                                 return false;
                             }
                        }
                        


                        if op == Primitive::TagStr || op == Primitive::TagChar {
                             if !g.is_value(arg1) { return reduce_step(g, arg1, ctx); }
                             let res = make_tag(g, op, arg1);
                             // Result is canonical tag structure
                             // But root is App(p, x) or Fork(p, x).
                             // We want to replace root with res.
                             // But res is NodeId.
                             // Current root might be App. res is likely Fork.
                             // set(root, Ind(res)) is safe.
                             if res != root {
                                 g.set(root, Node::Ind(res));
                             }
                             return true;
                        }

                        if matches!(op, Primitive::IsNum | Primitive::IsStr | Primitive::IsChar | Primitive::IsProg | Primitive::IsNeg | Primitive::IsPrim) {
                            if !g.is_value(arg1) {
                                return reduce_step(g, arg1, ctx);
                            }
                            
                            let (unwrapped_arg1, tag_opt) = unwrap_data(g, raw_arg1);

                            let val_bool = match op {
                                Primitive::IsNum => {
                                    // Check Int OR Float
                                    if decode_int_forced(g, unwrapped_arg1, ctx).is_some() && tag_opt.is_none() { true }
                                    else { matches!(g.get(g.resolve(unwrapped_arg1)), Node::Float(_)) }
                                },
                                Primitive::IsStr => matches!(tag_opt, Some(Primitive::TagStr)),
                                Primitive::IsChar => matches!(tag_opt, Some(Primitive::TagChar)),
                                Primitive::IsProg => true,
                                Primitive::IsNeg => {
                                    if let Some(i) = decode_int_forced(g, arg1, ctx) {
                                        i < BigInt::zero()
                                    } else if let Node::Float(f) = g.get(g.resolve(arg1)) {
                                        *f < 0.0
                                    } else { false }
                                }
                                Primitive::IsPrim => {
                                    // Check for Node::Prim OR Tagged Primitive
                                    let node = g.get(g.resolve(arg1));
                                    if let Node::Prim(_) = node { true }
                                    else if let Some(_) = get_tagged_prim(g, arg1) { true }
                                    else { false }
                                }
                                _ => false,
                            };
                            
                            let res_node = if val_bool {
                                 let leaf = g.add(Node::Leaf);
                                 g.add(Node::Fork(leaf, leaf))
                            } else {
                                 g.add(Node::Leaf)
                            };
                            
                            let mut final_res = res_node;
                            for &arg in &args[needed..] {
                                final_res = g.add(Node::App {
                                    func: final_res,
                                    args: smallvec![arg],
                                });
                            }
                            if final_res != root {
                                g.set(root, Node::Ind(final_res));
                            }
                            return true;
                        }

                        if op == Primitive::Size {
                            if !g.is_value(arg1) {
                                return reduce_step(g, arg1, ctx);
                            }
                            let c = node_count(g, arg1);
                            let res_node = encode_int(g, &BigInt::from(c));
                            
                            let mut final_res = res_node;
                            for &arg in &args[needed..] {
                                final_res = g.add(Node::App {
                                    func: final_res,
                                    args: smallvec![arg],
                                });
                            }
                            if final_res != root {
                                g.set(root, Node::Ind(final_res));
                            }
                            return true;
                        }

                        if op == Primitive::Contains {
                             if let Some(a2) = arg2 {
                                 if !g.is_value(arg1) {
                                     return reduce_step(g, arg1, ctx);
                                 }
                                 // Target (a2) should also be a value? Usually yes.
                                 if !g.is_value(a2) {
                                     return reduce_step(g, a2, ctx);
                                 }
                                 
                                 let found = tree_contains(g, arg1, a2);
                                 let res_node = if found {
                                      let leaf = g.add(Node::Leaf);
                                      g.add(Node::Fork(leaf, leaf))
                                 } else {
                                      g.add(Node::Leaf)
                                 };
                                 
                                 let mut final_res = res_node;
                                 for &arg in &args[needed..] {
                                     final_res = g.add(Node::App {
                                         func: final_res,
                                         args: smallvec![arg],
                                     });
                                 }
                                 if final_res != root {
                                     g.set(root, Node::Ind(final_res));
                                 }
                                 return true;
                             }
                        }

                        if op == Primitive::Match {
                             if let Some(a2) = arg2 {
                                 // Tree Match with Reduction
                                 let matches = tree_match(g, arg1, a2, ctx);
                                 let res_node = if matches {
                                      let leaf = g.add(Node::Leaf);
                                      g.add(Node::Fork(leaf, leaf))
                                 } else {
                                      g.add(Node::Leaf)
                                 };
                                 
                                 let mut final_res = res_node;
                                 for &arg in &args[needed..] {
                                     final_res = g.add(Node::App {
                                         func: final_res,
                                         args: smallvec![arg],
                                     });
                                 }
                                 if final_res != root {
                                     g.set(root, Node::Ind(final_res));
                                 }
                                 return true;
                             }
                        }

                        if op == Primitive::SearchStep {
                             // Args: data, scorer, population, steps
                             // arg1 is data (unwrapped if needed/possible? data is usually list, not tagged, so raw is fine)
                             // arg2 is scorer
                             // args[2] is population
                             // args[3] is steps
                             
                             let steps_arg = args[3];
                             // Steps must be plain integer
                             if !g.is_value(steps_arg) { return reduce_step(g, steps_arg, ctx); }
                             
                             let steps_val = decode_int(g, steps_arg);
                             use num_traits::cast::ToPrimitive;
                             let steps_usize = steps_val.and_then(|bg| bg.to_usize());
                             
                             if let Some(steps) = steps_usize {
                                 // Check population
                                 let pop_arg = args[2];
                                 // Population might be partial? reduce it?
                                 // usage: (search-step ... pop ...)
                                 // pop is usually a Value (List).
                                 // But if it's a thunk, we should reduce it?
                                 // Let's assume strictness for population too.
                                 if !g.is_value(pop_arg) { return reduce_step(g, pop_arg, ctx); }
                                 
                                 // Data and Scorer can be anything?
                                 // Scorer is code. Data is list.
                                 // Let's rely on extract_list to traverse.
                                 
                                 // Extract tasks
                                 // println!("DEBUG: SearchStep data = {}", unparse(g, arg1));
                                 let mut tasks = Vec::new();
                                 if let Some(items) = crate::search::extract_list(g, arg1) {
                                     let mut multi_task_success = false;
                                      /* Multi-task detection disabled due to ambiguity with Integers/Lists
                                       if !items.is_empty() && crate::search::extract_list(g, items[0]).is_some() {
                                          let mut current_tasks = Vec::new();
                                          let mut all_valid = true;
                                          for item in &items {
                                              if let Some(pairs) = crate::search::extract_pairs(g, *item) {
                                                  if !pairs.is_empty() {
                                                      current_tasks.push(pairs);
                                                  } else {
                                                      all_valid = false;
                                                      break;
                                                  }
                                              } else {
                                                  all_valid = false;
                                                  break;
                                              }
                                          }
                                          
                                          if all_valid && !current_tasks.is_empty() {
                                              tasks = current_tasks;
                                              multi_task_success = true;
                                          }
                                      } 
                                      */ 
                                      
                                      if !multi_task_success {
                                          if let Some(pairs) = crate::search::extract_pairs(g, arg1) {
                                              if !pairs.is_empty() {
                                                  tasks.push(pairs);
                                              }
                                          }
                                      }
                                 }
                                 
                                 // Extract Population
                                 let mut seeds = Vec::new();
                                 if let Some(items) = crate::search::extract_list(g, pop_arg) {
                                     seeds = items;
                                 } else {
                                     // Maybe single seed?
                                     seeds.push(pop_arg);
                                 }
                                 
                                 // Config
                                 let pop_size = if seeds.is_empty() { 5 } else { seeds.len() };
                                 let raw_scorer = arg2.unwrap();
                                 let scorer_node = if matches!(g.get(g.resolve(raw_scorer)), Node::Leaf) {
                                     None
                                 } else {
                                     Some(raw_scorer)
                                 };
                                 
                                 // Run Generation (Iterated / OOPS)
                                 let new_pop = crate::search::run_generation_iterated(g, &tasks, scorer_node, steps, seeds, pop_size);
                                 
                                 // Convert Result Vec -> Triage List
                                 // (cons p1 (cons p2 ... n))
                                 let cons_prim = g.add(Node::Prim(Primitive::Cons));
                                 let nil = g.add(Node::Leaf);
                                 let mut list_node = nil;
                                 for &p in new_pop.iter().rev() {
                                     // cons p list_node
                                     let c1 = g.add(Node::App { func: cons_prim, args: smallvec![p] });
                                     list_node = g.add(Node::App { func: c1, args: smallvec![list_node] });
                                 }
                                 
                                 let mut final_res = list_node;
                                 for &arg in &args[needed..] {
                                     final_res = g.add(Node::App {
                                         func: final_res,
                                         args: smallvec![arg],
                                     });
                                 }
                                 if final_res != root {
                                     g.set(root, Node::Ind(final_res));
                                 }
                                 return true;
                             }
                        }

                        
                        if op == Primitive::Eq {
                             if let Some(a2) = arg2 {
                                 if !g.is_value(arg1) {
                                     return reduce_step(g, arg1, ctx);
                                 }
                                 if !g.is_value(a2) {
                                     return reduce_step(g, a2, ctx);
                                 }
                                 
                                 // Compare node IDs
                                 let id1 = g.resolve(arg1);
                                 let id2 = g.resolve(a2);
                                 
                                 let is_equal = id1 == id2;
                                 
                                 // true -> (n n) [Fork(n, n)], false -> n [Leaf] (Church Booleans / Triage Booleans)
                                 // Triage false is n. Triage true is usually (n n) or similar.
                                 // In parser.rs: "(def true (n n))", "(def false n)".
                                 
                                 let res_node = if is_equal {
                                     let leaf = g.add(Node::Leaf);
                                     g.add(Node::Fork(leaf, leaf)) // (n n)
                                 } else {
                                     g.add(Node::Leaf) // n
                                 };
                                 
                                 let mut final_res = res_node;
                                 for &arg in &args[needed..] {
                                     final_res = g.add(Node::App {
                                         func: final_res,
                                         args: smallvec![arg],
                                     });
                                 }
                                 if final_res != root {
                                     g.set(root, Node::Ind(final_res));
                                 }
                                 return true;
                             }
                        }



                        // Polymorphic Arithmetic
                        if args.len() >= 2 && matches!(op, Primitive::Add | Primitive::Sub | Primitive::Mul | Primitive::Div | Primitive::Mod) {
                             // Check if first arg is value
                             if !g.is_value(arg1) { return reduce_step(g, arg1, ctx); }
                             
                             enum Nu { I(BigInt), F(f64) }
                             
                             let decode_num = |g: &Graph, id: NodeId| -> Option<Nu> {
                                 // Try int
                                 if let Some(i) = decode_int(g, id) { return Some(Nu::I(i)); }
                                 // Try float
                                 let node = g.get(g.resolve(id));
                                 if let Node::Float(f) = node { return Some(Nu::F(*f)); }
                                 None
                             };
                             
                             let val1 = decode_num(g, arg1);
                             if val1.is_none() { return false; } 
                             
                             let mut params = Vec::with_capacity(args.len());
                             params.push(val1.unwrap());
                             
                             let mut any_float = matches!(params[0], Nu::F(_));

                             for i in 1..args.len() {
                                 let arg_i = args[i];
                                 if !g.is_value(arg_i) { return reduce_step(g, arg_i, ctx); }
                                 
                                 if let Some(n) = decode_num(g, arg_i) {
                                     if let Nu::F(_) = n { any_float = true; }
                                     params.push(n);
                                 } else {
                                     return false; // Non-numeric arg
                                 }
                             }
                             
                             // Calculate
                             let res_node = if any_float {
                                 let mut acc = match &params[0] { Nu::I(i) => num_traits::cast::ToPrimitive::to_f64(i).unwrap_or(0.0), Nu::F(f) => *f };
                                 for val in &params[1..] {
                                     let v = match val { Nu::I(i) => num_traits::cast::ToPrimitive::to_f64(i).unwrap_or(0.0), Nu::F(f) => *f };
                                     acc = match op {
                                         Primitive::Add => acc + v,
                                         Primitive::Sub => acc - v,
                                         Primitive::Mul => acc * v,
                                         Primitive::Div => acc / v,
                                         Primitive::Mod => acc % v,
                                         _ => acc,
                                     };
                                 }
                                 g.add(Node::Float(acc))
                             } else {
                                 let mut acc = match &params[0] { Nu::I(i) => i.clone(), _ => unreachable!() };
                                 for val in &params[1..] {
                                     let v = match val { Nu::I(i) => i, _ => unreachable!() };
                                     acc = match op {
                                         Primitive::Add => acc + v,
                                         Primitive::Sub => acc - v,
                                         Primitive::Mul => acc * v,
                                         Primitive::Div => if v.is_zero() { BigInt::zero() } else { acc / v },
                                         Primitive::Mod => if v.is_zero() { BigInt::zero() } else { acc % v },
                                         _ => acc,
                                     };
                                 }
                                 encode_int(g, &acc)
                             };
                             
                             if res_node != root {
                                 g.set(root, Node::Ind(res_node));
                             }
                             return true;
                        }
                        
                        // New Float Primitives
                        if matches!(op, Primitive::IntToFloat | Primitive::FloatToInt | Primitive::IsFloat | Primitive::Floor | Primitive::Ceil | Primitive::Sqrt | Primitive::Sin | Primitive::Cos | Primitive::Tan | Primitive::Abs) {
                             if !g.is_value(arg1) { return reduce_step(g, arg1, ctx); }
                             match op {
                                 Primitive::IntToFloat => {
                                     if let Some(i) = decode_int(g, arg1) {
                                         let f = num_traits::cast::ToPrimitive::to_f64(&i).unwrap_or(0.0);
                                         let float_node = g.add(Node::Float(f));
                                         g.set(root, Node::Ind(float_node));
                                         return true;
                                     }
                                 },
                                 Primitive::FloatToInt => {
                                      if let Node::Float(f) = g.get(g.resolve(arg1)) {
                                          let i = BigInt::from(*f as i64); // Simple truncation? or use round?
                                          // Typically floor or round?
                                          // Let's use truncation as standard cast.
                                          let res = encode_int(g, &i);
                                          g.set(root, Node::Ind(res));
                                          return true;
                                      }
                                 },
                                 Primitive::IsFloat => {
                                      let is_f = matches!(g.get(g.resolve(arg1)), Node::Float(_));
                                      let res = if is_f { 
                                          let leaf1 = g.add(Node::Leaf);
                                          let leaf2 = g.add(Node::Leaf);
                                          g.add(Node::Fork(leaf1, leaf2)) 
                                      } else { 
                                          g.add(Node::Leaf) 
                                      }; // True/False
                                      g.set(root, Node::Ind(res));
                                      return true;
                                 },
                                 Primitive::Abs => {
                                     // Polymorphic Abs
                                     if let Some(i) = decode_int(g, arg1) {
                                         let res = encode_int(g, &i.abs());
                                         g.set(root, Node::Ind(res));
                                         return true;
                                     } else if let Node::Float(f) = g.get(g.resolve(arg1)) {
                                         let float_node = g.add(Node::Float(f.abs()));
                                         g.set(root, Node::Ind(float_node));
                                         return true;
                                     }
                                 },
                                 Primitive::Floor | Primitive::Ceil | Primitive::Sqrt | Primitive::Sin | Primitive::Cos | Primitive::Tan => {
                                     if let Node::Float(f) = g.get(g.resolve(arg1)) {
                                         let val = match op {
                                             Primitive::Floor => f.floor(),
                                             Primitive::Ceil => f.ceil(),
                                             Primitive::Sqrt => f.sqrt(),
                                             Primitive::Sin => f.sin(),
                                             Primitive::Cos => f.cos(),
                                             Primitive::Tan => f.tan(),
                                             _ => *f,
                                         };
                                         let float_node = g.add(Node::Float(val));
                                         g.set(root, Node::Ind(float_node));
                                         return true;
                                     }
                                 }
                                 _ => {}
                             }
                        }
                    }
                    false
                }
                
        _ => false,
    }
}
fn try_reduce_rule(g: &mut Graph, root: NodeId, p: NodeId, q: NodeId, r: NodeId, rest: &[NodeId], ctx: &mut EvalContext) -> bool {
    // STRICTNESS CHECK: Only p needs to be a value
    if !g.is_value(p) {
        return reduce_step(g, p, ctx);
    }

    // p is Value. Check Rules.
    let p_node = g.get(g.resolve(p)).clone();
    
    let res = match p_node {
        // Rule 1: n (n) q r -> q
        Node::Leaf => {
             Some(q)
        }
        
        // Rule 2 (D-Rule): n (n x) q r -> q r (x r)
        Node::Stem(x) => {
            let xr = g.add(Node::App { func: x, args: smallvec![r] });
            let qr = g.add(Node::App { func: q, args: smallvec![r] });
            // D x q r = q r (x r)
            Some(g.add(Node::App { func: qr, args: smallvec![xr] }))
        }
        
        // Rule 3: n (n w x) q r -> ...
        Node::Fork(w, x) => {
             // Check z=r
             // For Rule 3, we often need structural check on z.
             // If z is NOT a value, we must reduce it?
             // Actually Rule 3 says "n (n w x) q z".
             // We need to match z.
             if !g.is_value(r) {
                 // Force z
                 // Return result of reducing z (tracing that we did work)
                 // Wait, we need to return 'true' if we reduce z.
                 // We can recursively reduce z here.
                 // But we are deep in logic.
                 return reduce_step(g, r, ctx);
             }
             
             let z_node = g.get(g.resolve(r)).clone();
             match z_node {
                 // 3a: z=n -> w
                 Node::Leaf => Some(w),
                 
                 // 3b: z=(n u) -> x u
                 Node::Stem(u) => {
                     Some(g.add(Node::App { func: x, args: smallvec![u] }))
                 }
                 
                 // 3c: z=(n u v) -> q u v
                 Node::Fork(u, v) => {
                     Some(g.add(Node::App { 
                         func: q, 
                         args: smallvec![u, v] 
                     }))
                 }
                 
                 _ => None // z is not Leaf/Stem/Fork? impossible if is_value
             }
        }
        
        _ => None
    };
    
    if let Some(mut result) = res {
        // Apply remaining args if any (n p q r s...)
        for &arg in rest {
             result = g.add(Node::App {
                 func: result,
                 args: smallvec![arg],
             });
        }
        
        // Update root
        if result != root {
            g.set(root, Node::Ind(result));
        }
        true
    } else {
        false
    }
}

pub fn reduce(g: &mut Graph, root: NodeId, ctx: &mut EvalContext) -> NodeId {
    let mut root = root;
    loop {
        if ctx.steps >= ctx.step_limit {
            // Timeout: return nil (Leaf)
            return g.add(Node::Leaf);
        }
        if reduce_step(g, root, ctx) {
            ctx.steps += 1;
            root = g.resolve(root); 
        } else {
            break;
        }
    }
    root
}


pub fn decode_raw_nat_forced(g: &mut Graph, id: NodeId, ctx: &mut EvalContext) -> Option<BigUint> {
    let root = reduce(g, id, ctx);
    match g.get(g.resolve(root)).clone() {
        Node::Leaf => Some(BigUint::zero()),
        Node::Fork(b, r) => {
             let b_val = reduce(g, b, ctx);
             let bit = match g.get(g.resolve(b_val)) {
                 Node::Leaf => 0,
                 Node::Stem(x) => {
                     let x_val = reduce(g, *x, ctx);
                     if matches!(g.get(g.resolve(x_val)), Node::Leaf) { 1 } else { return None; }
                 }
                 _ => return None
             };
             let rest = decode_raw_nat_forced(g, r, ctx)?;
             
             let mut val = rest << 1;
             if bit == 1 { val |= BigUint::one(); }
             Some(val)
        }
        _ => None
    }
}

pub fn decode_int_forced(g: &mut Graph, id: NodeId, ctx: &mut EvalContext) -> Option<BigInt> {
    let raw = decode_raw_nat_forced(g, id, ctx)?;
    Some(unzigzag(&raw))
}


pub fn decode_str_forced(g: &mut Graph, id: NodeId, ctx: &mut EvalContext) -> Option<String> {
     let mut s = String::new();
     let mut curr = id;
     loop {
         let root = reduce(g, curr, ctx);
         match g.get(g.resolve(root)).clone() {
             Node::Leaf => return Some(s),
             Node::Fork(c, r) => {
                 let n = decode_raw_nat_forced(g, c, ctx)?;
                 use num_traits::cast::ToPrimitive;
                 let u: u32 = n.to_u32()?;
                 let char = std::char::from_u32(u)?;
                 s.push(char);
                 curr = r;
             }
             _ => return None
         }
     }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_nat() {
        let mut g = Graph::new();
        // 0 -> Leaf
        let zero = encode_nat(&mut g, &BigUint::from(0u32));
        assert!(matches!(g.get(zero), Node::Leaf));
        
        let one = encode_nat(&mut g, &BigUint::from(1u32));
        
        // Use round-trip to verify instead of fragile structural checks
        // since encoding might change (ZigZag vs direct).
        let decoded = decode_nat(&g, one).expect("Failed to decode 1");
        assert_eq!(decoded, BigUint::from(1u32));
        
        // Test 99
        let ninety_nine = encode_nat(&mut g, &BigUint::from(99u32));
        let decoded_99 = decode_nat(&g, ninety_nine).expect("Failed to decode 99");
        assert_eq!(decoded_99, BigUint::from(99u32));
        
        let big = BigUint::parse_bytes(b"12345678901234567890", 10).unwrap();
        let big_node = encode_nat(&mut g, &big);
        let big_decoded = decode_nat(&g, big_node).expect("Failed to decode big");
        assert_eq!(big, big_decoded);
    }

    #[test]
    fn test_primitives() {
        let mut g = Graph::new();
        let mut ctx = EvalContext::default();
        
        // Helper to run code
        let run = |g: &mut Graph, code: &str| -> NodeId {
            // Minimal parser for test args would be nice, but we can construct manually or use tiny parser if available.
            // Since we are in engine.rs, we don't have easy access to Parser (in parser.rs).
            // We'll construct nodes manually.
            NodeId::NULL
        };
        
        // Test Add: (+ 2 3)
        let add = g.add(Node::Prim(Primitive::Add));
        let n2 = encode_int(&mut g, &BigInt::from(2));
        let n3 = encode_int(&mut g, &BigInt::from(3));
        
        // App(App(+, 2), 3) -> (+ 2 3)
        let app1 = g.add(Node::App { func: add, args: smallvec![n2] });
        let app2 = g.add(Node::App { func: app1, args: smallvec![n3] });
        
        let res = reduce(&mut g, app2, &mut ctx);
        let val = decode_int(&g, res).expect("Result should be int");
        assert_eq!(val, BigInt::from(5));
        
        // Test List: (first (cons 1 2))
        let cons = g.add(Node::Prim(Primitive::Cons));
        let first = g.add(Node::Prim(Primitive::First));
        let n1 = encode_int(&mut g, &BigInt::from(1));
        
        // (cons 1 2)
        // App(App(cons, 1), 2)
        let c1 = g.add(Node::App { func: cons, args: smallvec![n1] });
        let c2 = g.add(Node::App { func: c1, args: smallvec![n2] });
        
        // (first (cons 1 2))
        let f1 = g.add(Node::App { func: first, args: smallvec![c2] });
        let res_f = reduce(&mut g, f1, &mut ctx);
        
        let val_f = decode_int(&g, res_f).expect("First should be 1");
        assert_eq!(val_f, BigInt::from(1));
    }
    
    #[test]
    fn test_reduce_rule1() {
        // Rule 1: n n y z -> y
        let mut g = Graph::new();
        let y = g.add(Node::Leaf); // usually y would be unique to distinguish
        let z = g.add(Node::Leaf);
        
        // Construct (n n) -> Stem(Leaf)
        let n = g.add(Node::Leaf);
        let nn = g.add(Node::Stem(n));
        
        // Construct application (nn y z)
        let app = g.add(Node::App { 
            func: nn, 
            args: smallvec![y, z] 
        });
        
        let mut ctx = EvalContext::default();
        let reduced = reduce(&mut g, app, &mut ctx);
        
        // Should be y (Leaf)
        // Note: Graph adds 'y' as Leaf. Reduced returns 'y'.
        assert_eq!(reduced, y);
    }
    
    #[test]
    fn test_reduce_rule2() {
        // Rule 2: n (n x) y z -> x z (y z)
        let mut g = Graph::new();
        let n = g.add(Node::Leaf);
        let x = g.add(Node::Leaf); // x
        let y = g.add(Node::Leaf); // y
        let z = g.add(Node::Leaf); // z
        
        // n (n x) -> Stem(Stem(x))? 
        // No. (n x) = Stem(x).
        // n (n x) = App(Leaf, Stem(x)) -> Stem(Stem(x)).
        // So p = Stem(x).
        let nx = g.add(Node::Stem(x));
        let p = g.add(Node::Stem(nx));
        
        // App(p, y, z)
        let app = g.add(Node::App {
            func: p,
            args: smallvec![y, z]
        });
        
        let mut ctx = EvalContext::default();
        let reduced = reduce(&mut g, app, &mut ctx);
        
        // Result: App(App(x, z), App(y, z))
        // Canonicalization:
        // App(x, z) -> App(Leaf, z) -> Stem(z).
        // App(y, z) -> App(Leaf, z) -> Stem(z).
        // Result: App(Stem(z), Stem(z)).
        // Canonicalization: App(Stem(u), v) -> Fork(u, v).
        // So Fork(z, Stem(z)).
        
        let r_node = g.get(reduced);
        if let Node::Fork(u, v) = r_node {
            // u should be z
            assert_eq!(*u, z);
            // v should be Stem(z)
            match g.get(*v) {
                Node::Stem(s) => assert_eq!(*s, z),
                _ => panic!("Expected Stem(z) in Fork, got {:?}", g.get(*v)),
            }
        } else {
            panic!("Expected Fork, got {:?}", r_node);
        }
    }
}

pub struct Copier {
    map: std::collections::HashMap<NodeId, NodeId>,
}

impl Copier {
    pub fn new() -> Self {
        Self {
            map: std::collections::HashMap::with_capacity(1024),
        }
    }

    pub fn clear(&mut self) {
        self.map.clear();
    }

    pub fn copy(&mut self, src: &Graph, dst: &mut Graph, node: NodeId) -> NodeId {
        if let Some(&mapped) = self.map.get(&node) {
            return mapped;
        }

        // Must extract node info first to avoid borrowing `src` while borrowing `self` 
        // (though self is just map here) and mutating `dst`.
        // Actually, `src` is immutable reference. `dst` is mutable.
        // Copying requires reading `src.get(node)`.
        
        // Resolve indirections first?
        // Usually we want to preserve structure, but Indirections are irrelevant for logic.
        // However, `Graph.get` might not resolve Indirections automatically if they are distinct variants?
        // `Graph::get` returns `&Node`.
        // If `Node` has Indirection variant, we should follow it.
        // Assuming `src.get` returns raw node.
        
        let new_id = match src.get(node) {
            Node::Leaf => dst.add(Node::Leaf),
            Node::Stem(s) => {
                let new_s = self.copy(src, dst, *s);
                dst.add(Node::Stem(new_s))
            },
            Node::Fork(a, b) => {
                let new_a = self.copy(src, dst, *a);
                let new_b = self.copy(src, dst, *b);
                dst.add(Node::Fork(new_a, new_b))
            },
            Node::Prim(p) => dst.add(Node::Prim(*p)),
            Node::App { func, args } => {
                let new_func = self.copy(src, dst, *func);
                let mut new_args = smallvec::SmallVec::new();
                for &arg in args {
                    new_args.push(self.copy(src, dst, arg));
                }
                dst.add(Node::App { func: new_func, args: new_args })
            },
            Node::Ind(target) => {
                // Skip indirection node, point directly to target
                self.copy(src, dst, *target)
            },
            Node::Float(f) => dst.add(Node::Float(*f)),
        };

        self.map.insert(node, new_id);
        new_id
    }
}
