use crate::types::NodeId;

#[derive(Debug, Clone, PartialEq)]
pub enum TestMode {
    Eq,
    Eql,
    Equal,
    Equalp,
}

#[derive(Debug, Clone)]
pub struct HashTable {
    pub test_mode: TestMode,
    pub entries: Vec<(NodeId, NodeId)>, // Linear scan for now to support 'equal' without complex hashing
}

impl HashTable {
    pub fn new(test_mode: TestMode) -> Self {
        Self {
            test_mode,
            entries: Vec::new(),
        }
    }

    pub fn get(&self, key: NodeId, arena: &crate::arena::Arena, mode: TestMode) -> Option<NodeId> {
        // Implement lookup based on mode
        for (k, v) in &self.entries {
            if Self::compare(*k, key, arena, &mode) {
                return Some(*v);
            }
        }
        None
    }

    pub fn insert(&mut self, key: NodeId, value: NodeId, arena: &crate::arena::Arena) {
        // Check if exists
        let mode = self.test_mode.clone(); // Clone mode to avoid borrow conflict
        for (k, v) in &mut self.entries {
            if Self::compare(*k, key, arena, &mode) {
                *v = value;
                return;
            }
        }
        self.entries.push((key, value));
    }

    pub fn remove(&mut self, key: NodeId, arena: &crate::arena::Arena) -> bool {
        let mode = self.test_mode.clone();
        if let Some(pos) = self
            .entries
            .iter()
            .position(|(k, _)| Self::compare(*k, key, arena, &mode))
        {
            self.entries.remove(pos);
            true
        } else {
            false
        }
    }

    pub fn clear(&mut self) {
        self.entries.clear();
    }

    pub fn count(&self) -> usize {
        self.entries.len()
    }

    fn compare(a: NodeId, b: NodeId, arena: &crate::arena::Arena, mode: &TestMode) -> bool {
        match mode {
            TestMode::Eq => a == b,
            TestMode::Eql => Self::eql(a, b, arena),
            TestMode::Equal => Self::equal(a, b, arena),
            TestMode::Equalp => Self::equalp(a, b, arena),
        }
    }

    fn eql(a: NodeId, b: NodeId, arena: &crate::arena::Arena) -> bool {
        if a == b {
            return true;
        }
        use crate::arena::Node;
        use crate::types::OpaqueValue;

        let node_a = arena.get_unchecked(a);
        let node_b = arena.get_unchecked(b);

        match (node_a, node_b) {
            (Node::Leaf(OpaqueValue::Integer(x)), Node::Leaf(OpaqueValue::Integer(y))) => x == y,
            (Node::Leaf(OpaqueValue::Float(x)), Node::Leaf(OpaqueValue::Float(y))) => x == y,
            (Node::Leaf(OpaqueValue::String(x)), Node::Leaf(OpaqueValue::String(y))) => x == y,
            _ => false,
        }
    }

    fn equal(a: NodeId, b: NodeId, arena: &crate::arena::Arena) -> bool {
        if Self::eql(a, b, arena) {
            return true;
        }

        use crate::arena::Node;
        use crate::types::OpaqueValue;

        let node_a = arena.get_unchecked(a);
        let node_b = arena.get_unchecked(b);

        match (node_a, node_b) {
            (Node::Fork(la, ra), Node::Fork(lb, rb)) => {
                Self::equal(*la, *lb, arena) && Self::equal(*ra, *rb, arena)
            }
            (Node::Leaf(OpaqueValue::String(s1)), Node::Leaf(OpaqueValue::String(s2))) => s1 == s2,
            _ => false,
        }
    }

    fn equalp(a: NodeId, b: NodeId, arena: &crate::arena::Arena) -> bool {
        if Self::equal(a, b, arena) {
            return true;
        }
        // Case insensitive strings, etc.
        // For now, fallback to equal
        Self::equal(a, b, arena)
    }
}

pub struct HashTableStore {
    tables: Vec<HashTable>,
    free_list: Vec<usize>,
}

impl HashTableStore {
    pub fn new() -> Self {
        Self {
            tables: Vec::new(),
            free_list: Vec::new(),
        }
    }

    pub fn alloc(&mut self, table: HashTable) -> crate::types::HashHandle {
        if let Some(idx) = self.free_list.pop() {
            self.tables[idx] = table;
            crate::types::HashHandle(idx as u32)
        } else {
            let idx = self.tables.len();
            self.tables.push(table);
            crate::types::HashHandle(idx as u32)
        }
    }

    pub fn get(&self, handle: crate::types::HashHandle) -> Option<&HashTable> {
        self.tables.get(handle.0 as usize)
    }

    pub fn get_mut(&mut self, handle: crate::types::HashHandle) -> Option<&mut HashTable> {
        self.tables.get_mut(handle.0 as usize)
    }
}
