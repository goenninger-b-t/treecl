// TreeCL Arrays - Dynamic Array Storage
//
// Provides basic array metadata (dimensions, element type, fill pointers)
// with flat row-major storage for elements.

use crate::types::NodeId;

/// Handle to an array (index into ArrayStore)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VectorId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArrayElementType {
    T,
    Bit,
    Character,
}

impl ArrayElementType {
    pub fn is_bit(self) -> bool {
        matches!(self, ArrayElementType::Bit)
    }

    pub fn is_character(self) -> bool {
        matches!(self, ArrayElementType::Character)
    }
}

#[derive(Debug, Clone)]
pub struct ArrayObject {
    pub elements: Vec<NodeId>,
    pub dimensions: Vec<usize>,
    pub element_type: ArrayElementType,
    pub fill_pointer: Option<usize>,
}

impl ArrayObject {
    fn total_size_from_dims(dims: &[usize]) -> usize {
        if dims.is_empty() {
            1
        } else {
            dims.iter().product()
        }
    }

    pub fn total_size(&self) -> usize {
        Self::total_size_from_dims(&self.dimensions)
    }

    pub fn rank(&self) -> usize {
        self.dimensions.len()
    }

    pub fn is_simple_vector(&self) -> bool {
        self.rank() == 1 && self.element_type == ArrayElementType::T && self.fill_pointer.is_none()
    }

    pub fn is_simple_bit_vector(&self) -> bool {
        self.rank() == 1 && self.element_type.is_bit() && self.fill_pointer.is_none()
    }

    pub fn vector_length(&self) -> Option<usize> {
        if self.rank() != 1 {
            return None;
        }
        if let Some(fp) = self.fill_pointer {
            Some(fp)
        } else {
            Some(self.dimensions[0])
        }
    }

    pub fn elements_for_sequence(&self) -> Vec<NodeId> {
        if self.rank() == 1 {
            let limit = self.fill_pointer.unwrap_or(self.elements.len());
            self.elements.iter().take(limit).copied().collect()
        } else {
            self.elements.clone()
        }
    }
}

/// Storage for arrays
pub struct ArrayStore {
    arrays: Vec<ArrayObject>,
    free_indices: Vec<u32>,
}

impl ArrayStore {
    pub fn new() -> Self {
        Self {
            arrays: Vec::new(),
            free_indices: Vec::new(),
        }
    }

    /// Allocate a new simple vector with given size and initial element
    pub fn alloc(&mut self, size: usize, initial_element: NodeId) -> VectorId {
        let elements = vec![initial_element; size];
        let dims = vec![size];
        self.alloc_array(dims, elements, ArrayElementType::T, None)
    }

    /// Allocate a simple vector from existing content
    pub fn alloc_from_vec(&mut self, content: Vec<NodeId>) -> VectorId {
        let dims = vec![content.len()];
        self.alloc_array(dims, content, ArrayElementType::T, None)
    }

    /// Allocate an array with explicit metadata
    pub fn alloc_array(
        &mut self,
        dimensions: Vec<usize>,
        elements: Vec<NodeId>,
        element_type: ArrayElementType,
        fill_pointer: Option<usize>,
    ) -> VectorId {
        let obj = ArrayObject {
            elements,
            dimensions,
            element_type,
            fill_pointer,
        };

        if let Some(idx) = self.free_indices.pop() {
            self.arrays[idx as usize] = obj;
            VectorId(idx)
        } else {
            let idx = self.arrays.len() as u32;
            self.arrays.push(obj);
            VectorId(idx)
        }
    }

    /// Get a reference to an array
    pub fn get(&self, id: VectorId) -> Option<&ArrayObject> {
        self.arrays.get(id.0 as usize)
    }

    /// Get a mutable reference to an array
    pub fn get_mut(&mut self, id: VectorId) -> Option<&mut ArrayObject> {
        self.arrays.get_mut(id.0 as usize)
    }

    /// Get element at row-major index
    pub fn aref(&self, id: VectorId, index: usize) -> Option<NodeId> {
        self.arrays
            .get(id.0 as usize)
            .and_then(|a| a.elements.get(index).copied())
    }

    /// Set element at row-major index
    pub fn set_aref(&mut self, id: VectorId, index: usize, value: NodeId) -> bool {
        if let Some(a) = self.arrays.get_mut(id.0 as usize) {
            if index < a.elements.len() {
                a.elements[index] = value;
                return true;
            }
        }
        false
    }

    /// Length of vector (rank 1 arrays)
    pub fn length(&self, id: VectorId) -> Option<usize> {
        self.arrays.get(id.0 as usize).and_then(|a| a.vector_length())
    }

    /// For GC: Iterate over all occupied arrays
    pub fn sweep(&mut self, marked: &std::collections::HashSet<u32>) -> usize {
        let mut freed_count = 0;
        for i in 0..self.arrays.len() {
            let idx = i as u32;
            if !marked.contains(&idx) {
                if !self.arrays[i].elements.is_empty() {
                    self.arrays[i].elements.clear();
                    self.arrays[i].dimensions.clear();
                    self.free_indices.push(idx);
                    freed_count += 1;
                }
            }
        }
        freed_count
    }

    /// Get number of arrays (including freed slots)
    pub fn len(&self) -> usize {
        self.arrays.len()
    }

    /// Get number of active arrays
    pub fn active_count(&self) -> usize {
        self.arrays.len() - self.free_indices.len()
    }

    /// Get total elements across all arrays
    pub fn total_elements(&self) -> usize {
        self.arrays.iter().map(|a| a.elements.len()).sum()
    }

    /// Trace nodes in a specific array (for GC)
    pub fn trace_vector(&self, id: VectorId, marked: &mut std::collections::HashSet<u32>) {
        if let Some(arr) = self.arrays.get(id.0 as usize) {
            for &node in &arr.elements {
                marked.insert(node.0);
            }
        }
    }
}
