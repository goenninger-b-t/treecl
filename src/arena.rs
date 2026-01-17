use crate::types::{NodeId, OpaqueValue};

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
    nodes: Vec<Entry>,
    free_head: Option<u32>,
    allocs_since_gc: usize,
}

impl Arena {
    pub fn new() -> Self {
        Self {
            nodes: Vec::with_capacity(1024),
            free_head: None,
            allocs_since_gc: 0,
        }
    }

    pub fn alloc(&mut self, node: Node) -> NodeId {
        match self.free_head {
            Some(idx) => {
                let entry = &mut self.nodes[idx as usize];
                let next_free = match entry {
                    Entry::Free { next } => *next,
                    _ => panic!("Corrupt free list"),
                };
                self.free_head = next_free;
                *entry = Entry::Occupied(node);
                self.allocs_since_gc += 1;
                NodeId(idx)
            }
            None => {
                let idx = self.nodes.len() as u32;
                self.nodes.push(Entry::Occupied(node));
                self.allocs_since_gc += 1;
                NodeId(idx)
            }
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
