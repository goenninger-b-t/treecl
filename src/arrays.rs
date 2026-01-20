// TreeCL Arrays - Dynamic Vector Storage
//
// Separated from Arena to enable O(1) indexing and efficient storage.

use crate::types::NodeId;

/// Handle to a vector (index into ArrayStore)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VectorId(pub u32);

/// Storage for vectors
pub struct ArrayStore {
    vectors: Vec<Vec<NodeId>>,
    free_indices: Vec<u32>,
}

impl ArrayStore {
    pub fn new() -> Self {
        Self {
            vectors: Vec::new(),
            free_indices: Vec::new(),
        }
    }

    /// Allocate a new vector with given size and initial element
    pub fn alloc(&mut self, size: usize, initial_element: NodeId) -> VectorId {
        let vec = vec![initial_element; size];
        
        if let Some(idx) = self.free_indices.pop() {
            self.vectors[idx as usize] = vec;
            VectorId(idx)
        } else {
            let idx = self.vectors.len() as u32;
            self.vectors.push(vec);
            VectorId(idx)
        }
    }

    /// Allocate a vector from existing content
    pub fn alloc_from_vec(&mut self, content: Vec<NodeId>) -> VectorId {
        if let Some(idx) = self.free_indices.pop() {
            self.vectors[idx as usize] = content;
            VectorId(idx)
        } else {
            let idx = self.vectors.len() as u32;
            self.vectors.push(content);
            VectorId(idx)
        }
    }

    /// Get a reference to a vector
    pub fn get(&self, id: VectorId) -> Option<&Vec<NodeId>> {
        self.vectors.get(id.0 as usize)
    }

    /// Get a mutable reference to a vector
    pub fn get_mut(&mut self, id: VectorId) -> Option<&mut Vec<NodeId>> {
        self.vectors.get_mut(id.0 as usize)
    }

    /// Get element at index
    pub fn aref(&self, id: VectorId, index: usize) -> Option<NodeId> {
        self.vectors.get(id.0 as usize).and_then(|v| v.get(index).copied())
    }

    /// Set element at index
    pub fn set_aref(&mut self, id: VectorId, index: usize, value: NodeId) -> bool {
        if let Some(v) = self.vectors.get_mut(id.0 as usize) {
            if index < v.len() {
                v[index] = value;
                return true;
            }
        }
        false
    }
    
    /// Length of vector
    pub fn length(&self, id: VectorId) -> Option<usize> {
        self.vectors.get(id.0 as usize).map(|v| v.len())
    }
    
    /// For GC: Iterate over all occupied vectors
    /// Returns iterator of (VectorId, &Vec<NodeId>)
    /// Note: This iterates potentially free slots too if they are not cleared.
    /// We should probably track liveness or just iterate all.
    /// Since we use free_indices, we can check if index is valid?
    /// Actually, if GC marks reachable vectors, we only need to traverse those.
    /// But wait, we need to traverse FROM the vectors to find reachable nodes.
    /// So we need `get` enabled.
    /// 
    /// The Sweep phase needs to know which ones are NOT marked to free them.
    pub fn sweep(&mut self, marked: &std::collections::HashSet<u32>) -> usize {
        let mut freed_count = 0;
        for i in 0..self.vectors.len() {
            let idx = i as u32;
            if !marked.contains(&idx) {
                // If it's not already free (how do we know? We don't distinguish Occupied/Free in Vec directly unless we use an Enum or check free_indices)
                // Optimization: We can just clear the vector to save memory, and add to free_indices if not already there.
                // But `free_indices` logic requires us to know if it was ALREADY free.
                
                // Simpler: Use Option<Vec> in storage?
                // Let's change implementation slightly for robustness if needed.
                // For now, let's assume if it's not marked and it HAS capacity, we free it.
                if !self.vectors[i].is_empty() {
                    self.vectors[i].clear(); // Reclaim memory
                    self.free_indices.push(idx);
                    freed_count += 1;
                }
            }
        }
        freed_count
    }
    
    /// Get number of vectors (including freed slots)
    pub fn len(&self) -> usize {
        self.vectors.len()
    }
    
    /// Get number of active vectors
    pub fn active_count(&self) -> usize {
        self.vectors.len() - self.free_indices.len()
    }
    
    /// Get total elements across all vectors
    pub fn total_elements(&self) -> usize {
        self.vectors.iter().map(|v| v.len()).sum()
    }
    /// Trace nodes in a specific vector
    pub fn trace_vector(&self, id: VectorId, marked: &mut std::collections::HashSet<u32>) {
        if let Some(vec) = self.vectors.get(id.0 as usize) {
            for &node in vec {
                marked.insert(node.0);
            }
        }
    }
}
