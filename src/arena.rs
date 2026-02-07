use crate::types::{NodeId, OpaqueValue};
use rayon::prelude::*;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeGeneration {
    Young,
    Old,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SweepMode {
    Minor,
    Major,
}

#[derive(Debug, Clone, Default)]
pub struct SweepReport {
    pub freed: usize,
    pub promoted: usize,
    pub examined: usize,
    pub workers: usize,
}

/// Statistics about Arena memory usage
#[derive(Debug, Clone)]
pub struct ArenaStats {
    pub total_slots: usize,
    pub free_slots: usize,
    pub allocs_since_gc: usize,
    pub allocs_since_major_gc: usize,
    pub young_live_slots: usize,
    pub old_live_slots: usize,
    pub remembered_set_size: usize,
    pub dirty_card_count: usize,
}

pub struct Arena {
    nodes: Vec<Entry>,
    free_head: Option<u32>,
    allocs_since_gc: usize,
    allocs_since_major_gc: usize,
    generations: Vec<NodeGeneration>,
    survivor_ages: Vec<u8>,
    remembered_set: crate::fastmap::HashSet<u32>,
    dirty_cards: crate::fastmap::HashSet<u32>,
    promote_age: u8,
    epoch: u64,
}

impl Arena {
    pub fn new() -> Self {
        Self {
            nodes: Vec::with_capacity(1024),
            free_head: None,
            allocs_since_gc: 0,
            allocs_since_major_gc: 0,
            generations: Vec::with_capacity(1024),
            survivor_ages: Vec::with_capacity(1024),
            remembered_set: crate::fastmap::HashSet::default(),
            dirty_cards: crate::fastmap::HashSet::default(),
            promote_age: 2,
            epoch: 0,
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
                self.generations[idx as usize] = NodeGeneration::Young;
                self.survivor_ages[idx as usize] = 0;
                self.remembered_set.remove(&idx);
                self.dirty_cards.remove(&idx);
                self.allocs_since_gc += 1;
                self.allocs_since_major_gc += 1;
                NodeId(idx)
            }
            None => {
                let idx = self.nodes.len() as u32;
                self.nodes.push(Entry::Occupied(node));
                self.generations.push(NodeGeneration::Young);
                self.survivor_ages.push(0);
                self.allocs_since_gc += 1;
                self.allocs_since_major_gc += 1;
                NodeId(idx)
            }
        }
    }

    pub fn overwrite(&mut self, id: NodeId, node: Node) {
        let idx = id.0 as usize;
        if idx < self.nodes.len() {
            if matches!(self.nodes[idx], Entry::Occupied(_))
                && self.generations[idx] == NodeGeneration::Old
            {
                // Coarse write barrier: treat any old-node mutation as potentially
                // introducing an old->young edge; track at card/node granularity.
                self.remembered_set.insert(id.0);
                self.dirty_cards.insert(id.0);
            }
            // Ensure slot is occupied? Or force?
            // Safe to force.
            self.nodes[idx] = Entry::Occupied(node);
            self.epoch = self.epoch.wrapping_add(1);
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
    pub fn sweep(&mut self, marked: &crate::fastmap::HashSet<u32>) -> usize {
        self.sweep_generation(marked, SweepMode::Major).freed
    }

    pub fn sweep_generation(
        &mut self,
        marked: &crate::fastmap::HashSet<u32>,
        mode: SweepMode,
    ) -> SweepReport {
        #[derive(Default)]
        struct LocalSweep {
            freed: Vec<u32>,
            promoted: usize,
            examined: usize,
        }

        let mark_bits: Vec<bool> = (0..self.nodes.len())
            .map(|idx| marked.contains(&(idx as u32)))
            .collect();
        let workers = rayon::current_num_threads().max(1);
        let promote_age = self.promote_age;

        let mut local = self
            .nodes
            .par_iter_mut()
            .zip(self.generations.par_iter_mut())
            .zip(self.survivor_ages.par_iter_mut())
            .enumerate()
            .map(|(idx, ((entry, generation), age))| {
                let mut out = LocalSweep::default();
                if !matches!(entry, Entry::Occupied(_)) {
                    return out;
                }
                out.examined += 1;

                let marked_here = mark_bits[idx];
                match mode {
                    SweepMode::Minor => {
                        if *generation == NodeGeneration::Young {
                            if marked_here {
                                *age = age.saturating_add(1);
                                if *age >= promote_age {
                                    *generation = NodeGeneration::Old;
                                    *age = 0;
                                    out.promoted += 1;
                                }
                            } else {
                                *entry = Entry::Free { next: None };
                                *generation = NodeGeneration::Young;
                                *age = 0;
                                out.freed.push(idx as u32);
                            }
                        }
                    }
                    SweepMode::Major => {
                        if marked_here {
                            if *generation == NodeGeneration::Young {
                                *age = age.saturating_add(1);
                                if *age >= promote_age {
                                    *generation = NodeGeneration::Old;
                                    *age = 0;
                                    out.promoted += 1;
                                }
                            }
                        } else {
                            *entry = Entry::Free { next: None };
                            *generation = NodeGeneration::Young;
                            *age = 0;
                            out.freed.push(idx as u32);
                        }
                    }
                }
                out
            })
            .reduce(LocalSweep::default, |mut a, mut b| {
                a.freed.append(&mut b.freed);
                a.promoted += b.promoted;
                a.examined += b.examined;
                a
            });

        let freed_count = local.freed.len();
        for idx in local.freed.drain(..) {
            self.nodes[idx as usize] = Entry::Free { next: self.free_head };
            self.free_head = Some(idx);
            self.remembered_set.remove(&idx);
            self.dirty_cards.remove(&idx);
        }

        if matches!(mode, SweepMode::Major) {
            self.remembered_set.clear();
            self.dirty_cards.clear();
        } else {
            self.remembered_set
                .retain(|idx| matches!(self.generations.get(*idx as usize), Some(NodeGeneration::Old)));
            self.dirty_cards
                .retain(|idx| matches!(self.generations.get(*idx as usize), Some(NodeGeneration::Old)));
        }

        if freed_count > 0 || local.promoted > 0 {
            self.epoch = self.epoch.wrapping_add(1);
        }

        SweepReport {
            freed: freed_count,
            promoted: local.promoted,
            examined: local.examined,
            workers,
        }
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

    /// Get allocation count since last MAJOR GC and reset it
    pub fn reset_major_alloc_count(&mut self) -> usize {
        let count = self.allocs_since_major_gc;
        self.allocs_since_major_gc = 0;
        count
    }
    
    /// Get allocation count since last GC (without reset)
    pub fn allocs_since_gc(&self) -> usize {
        self.allocs_since_gc
    }

    /// Get allocation count since last MAJOR GC (without reset)
    pub fn allocs_since_major_gc(&self) -> usize {
        self.allocs_since_major_gc
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

        let mut young_live = 0usize;
        let mut old_live = 0usize;
        for (idx, entry) in self.nodes.iter().enumerate() {
            if matches!(entry, Entry::Occupied(_)) {
                match self.generations[idx] {
                    NodeGeneration::Young => young_live += 1,
                    NodeGeneration::Old => old_live += 1,
                }
            }
        }
        
        ArenaStats {
            total_slots: self.nodes.len(),
            free_slots: free_count,
            allocs_since_gc: self.allocs_since_gc,
            allocs_since_major_gc: self.allocs_since_major_gc,
            young_live_slots: young_live,
            old_live_slots: old_live,
            remembered_set_size: self.remembered_set.len(),
            dirty_card_count: self.dirty_cards.len(),
        }
    }

    /// Mutation epoch, increments on overwrite/sweep to invalidate caches.
    pub fn epoch(&self) -> u64 {
        self.epoch
    }

    /// Total heap size in bytes for arena node storage.
    pub fn total_bytes(&self) -> usize {
        self.nodes.len().saturating_mul(std::mem::size_of::<Entry>())
    }

    pub fn remembered_set_size(&self) -> usize {
        self.remembered_set.len()
    }

    pub fn dirty_card_count(&self) -> usize {
        self.dirty_cards.len()
    }
}

/// Deep copy a tree from one arena to another
/// Returns the new NodeId in the destination arena.
/// Preserves structure (DAGs) using a memoization map.
pub fn deep_copy(src_arena: &Arena, src_root: NodeId, dest_arena: &mut Arena) -> NodeId {
    // Memoization map: Source NodeId -> Dest NodeId
    let mut copied = crate::fastmap::HashMap::default();
    
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
    copied: &mut crate::fastmap::HashMap<NodeId, NodeId>
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
