use crate::types::{NodeId, OpaqueValue, SourceLocation};

#[derive(Debug, Clone, PartialEq)]
pub enum Node {
    Leaf(OpaqueValue),
    Stem(NodeId),
    Fork(NodeId, NodeId),
}

enum Entry {
    Occupied(Node),
    Free { next: Option<u32> },
}

/// Statistics about Arena memory usage
#[derive(Debug, Clone)]
pub struct ArenaStats {
    pub total_slots: usize,
    pub free_slots: usize,
    pub allocs_since_gc: usize,
}

pub struct Arena {
    pub nodes: Vec<Entry>, // Made public for easier access if needed, or keep private? The planned use might valid.
    source_map: Vec<Option<SourceLocation>>,
    free_head: Option<u32>,
    allocs_since_gc: usize,
}

impl Arena {
    pub fn new() -> Self {
        Self {
            nodes: Vec::with_capacity(1024),
            source_map: Vec::with_capacity(1024),
            free_head: None,
            allocs_since_gc: 0,
        }
    }

    pub fn alloc(&mut self, node: Node) -> NodeId {
        self.alloc_with_location(node, None)
    }

    pub fn alloc_with_location(&mut self, node: Node, loc: Option<SourceLocation>) -> NodeId {
        match self.free_head {
            Some(idx) => {
                let entry = &mut self.nodes[idx as usize];
                let next_free = match entry {
                    Entry::Free { next } => *next,
                    _ => panic!("Corrupt free list"),
                };
                self.free_head = next_free;
                *entry = Entry::Occupied(node);
                
                // Ensure source_map is large enough (it should be, but safe to check?)
                // It should be parallel.
                if idx as usize >= self.source_map.len() {
                    self.source_map.resize(idx as usize + 1, None);
                }
                self.source_map[idx as usize] = loc;

                self.allocs_since_gc += 1;
                NodeId(idx)
            }
            None => {
                let idx = self.nodes.len() as u32;
                self.nodes.push(Entry::Occupied(node));
                self.source_map.push(loc);
                self.allocs_since_gc += 1;
                NodeId(idx)
            }
        }
    }

    pub fn get_location(&self, id: NodeId) -> Option<&SourceLocation> {
        self.source_map.get(id.0 as usize).and_then(|opt| opt.as_ref())
    }

    pub fn overwrite(&mut self, id: NodeId, node: Node) {
        let idx = id.0 as usize;
        if idx < self.nodes.len() {
            // Ensure slot is occupied? Or force?
            // Safe to force.
            self.nodes[idx] = Entry::Occupied(node);
        } else {
             panic!("Arena overwrite out of bounds");
        }
    }

    pub fn get(&self, id: NodeId) -> Option<&Node> {
        match self.nodes.get(id.0 as usize) {
            Some(Entry::Occupied(node)) => Some(node),
            _ => None,
        }
    }
    
    pub fn get_unchecked(&self, id: NodeId) -> &Node {
        match &self.nodes[id.0 as usize] {
            Entry::Occupied(node) => node,
            _ => panic!("Accessing freed node or out of bounds"),
        }
    }

    /// Sweep phase of GC.
    /// Reclaims all Occupied nodes whose indices are NOT in the `marked` set.
    /// Returns the number of nodes freed.
    pub fn sweep(&mut self, marked: &std::collections::HashSet<u32>) -> usize {
        let mut freed_count = 0;
        for idx in 0..self.nodes.len() {
            let u_idx = idx as u32;
            // If node is NOT marked and IS occupied, free it.
            if !marked.contains(&u_idx) {
                if let Entry::Occupied(_) = self.nodes[idx] {
                     // Convert to Free entry pointing to current free_head
                     self.nodes[idx] = Entry::Free { next: self.free_head };
                     self.free_head = Some(u_idx);
                     freed_count += 1;
                }
            }
        }
        freed_count
    }
    
    pub fn len(&self) -> usize {
        self.nodes.len()
    }
    
    /// Get allocation count since last GC and reset it
    pub fn reset_alloc_count(&mut self) -> usize {
        let count = self.allocs_since_gc;
        self.allocs_since_gc = 0;
        count
    }
    
    /// Get allocation count since last GC (without reset)
    pub fn allocs_since_gc(&self) -> usize {
        self.allocs_since_gc
    }
    
    /// Get memory statistics
    pub fn stats(&self) -> ArenaStats {
        // Count free list length
        let mut free_count = 0;
        let mut current = self.free_head;
        while let Some(idx) = current {
            free_count += 1;
            if let Entry::Free { next } = &self.nodes[idx as usize] {
                current = *next;
            } else {
                break;
            }
        }
        
        ArenaStats {
            total_slots: self.nodes.len(),
            free_slots: free_count,
            allocs_since_gc: self.allocs_since_gc,
        }
    }
}

/// Deep copy a tree from one arena to another
/// Returns the new NodeId in the destination arena.
/// Preserves structure (DAGs) using a memoization map.
pub fn deep_copy(src_arena: &Arena, src_root: NodeId, dest_arena: &mut Arena) -> NodeId {
    // Memoization map: Source NodeId -> Dest NodeId
    let mut copied = std::collections::HashMap::new();
    
    // Stack for iterative traversal
    // (Source Node, Parent's Slot to update) - simplified recursive logic
    // Actually, iterative deep copy of DAG is tricky without recursion.
    // Let's use recursion for now, assuming modest depth for messages.
    // If strict no-recursion needed, we need a fancier topological copy or 2-pass.
    // Let's stick to recursion for simplicity and clarity in this phase, 
    // unless the tree is huge. TreeCL stacks are managed, but Rust stack is finite.
    // "Files" had node_depth using stack.
    
    deep_copy_recursive(src_arena, src_root, dest_arena, &mut copied)
}

fn deep_copy_recursive(
    src_arena: &Arena, 
    src_id: NodeId, 
    dest_arena: &mut Arena, 
    copied: &mut std::collections::HashMap<NodeId, NodeId>
) -> NodeId {
    if let Some(&dest_id) = copied.get(&src_id) {
        return dest_id;
    }
    
    let node = src_arena.get_unchecked(src_id);
    let new_id = match node {
        Node::Leaf(val) => {
            // Value types are cloned. 
            // Note: Handles (e.g. VectorHandle) are copied as indices. 
            // This assumes shared global heaps for Vectors/Classes, or that handles are invalid.
            // For Integers/Floats/Nil/Strings it is safe.
            dest_arena.alloc(Node::Leaf(val.clone()))
        }
        Node::Stem(child) => {
            // Reserve slot first? No, we need child internal structure.
            // But if cycle? 
            // Cycle handling requires reserving slot before recursing.
            // But we can't reserve in this Arena impl easily without putting a dummy.
            // Let's insert dummy, recurse, then update?
            // Or just fail on cycles for now (ITC is usually acyclic for data).
            // Let's support DAGs without cycles first.
            let new_child = deep_copy_recursive(src_arena, *child, dest_arena, copied);
            dest_arena.alloc(Node::Stem(new_child))
        }
        Node::Fork(left, right) => {
            let nl = deep_copy_recursive(src_arena, *left, dest_arena, copied);
            let nr = deep_copy_recursive(src_arena, *right, dest_arena, copied);
            dest_arena.alloc(Node::Fork(nl, nr))
        }
    };
    
    copied.insert(src_id, new_id);
    new_id
}

/// Deep equality check for pattern matching
pub fn deep_equal(arena: &Arena, a: NodeId, b: NodeId) -> bool {
    if a == b { return true; }
    match (arena.get_unchecked(a), arena.get_unchecked(b)) {
         (Node::Leaf(v1), Node::Leaf(v2)) => v1 == v2,
         (Node::Stem(c1), Node::Stem(c2)) => deep_equal(arena, *c1, *c2),
         (Node::Fork(l1, r1), Node::Fork(l2, r2)) => {
             deep_equal(arena, *l1, *l2) && deep_equal(arena, *r1, *r2)
         }
         _ => false
    }
}
