use crate::types::NodeId;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::OnceLock;

#[derive(Default, Debug, Clone)]
pub struct HashCounters {
    pub get_calls: u64,
    pub set_calls: u64,
    pub rem_calls: u64,
    pub clr_calls: u64,
    pub maphash_calls: u64,
}

static COUNTERS_ENABLED: OnceLock<bool> = OnceLock::new();
static COUNTERS_FORCE_ENABLE: AtomicBool = AtomicBool::new(false);
static GET_CALLS: AtomicU64 = AtomicU64::new(0);
static SET_CALLS: AtomicU64 = AtomicU64::new(0);
static REM_CALLS: AtomicU64 = AtomicU64::new(0);
static CLR_CALLS: AtomicU64 = AtomicU64::new(0);
static MAPHASH_CALLS: AtomicU64 = AtomicU64::new(0);

fn counters_enabled() -> bool {
    if COUNTERS_FORCE_ENABLE.load(Ordering::Relaxed) {
        return true;
    }
    *COUNTERS_ENABLED.get_or_init(|| std::env::var("TREECL_DEBUG_COUNTERS").is_ok())
}

pub fn record_get() {
    if counters_enabled() {
        GET_CALLS.fetch_add(1, Ordering::Relaxed);
    }
}

pub fn record_set() {
    if counters_enabled() {
        SET_CALLS.fetch_add(1, Ordering::Relaxed);
    }
}

pub fn record_rem() {
    if counters_enabled() {
        REM_CALLS.fetch_add(1, Ordering::Relaxed);
    }
}

pub fn record_clr() {
    if counters_enabled() {
        CLR_CALLS.fetch_add(1, Ordering::Relaxed);
    }
}

pub fn record_maphash() {
    if counters_enabled() {
        MAPHASH_CALLS.fetch_add(1, Ordering::Relaxed);
    }
}

pub fn snapshot_counters() -> HashCounters {
    HashCounters {
        get_calls: GET_CALLS.load(Ordering::Relaxed),
        set_calls: SET_CALLS.load(Ordering::Relaxed),
        rem_calls: REM_CALLS.load(Ordering::Relaxed),
        clr_calls: CLR_CALLS.load(Ordering::Relaxed),
        maphash_calls: MAPHASH_CALLS.load(Ordering::Relaxed),
    }
}

pub fn reset_counters() {
    GET_CALLS.store(0, Ordering::Relaxed);
    SET_CALLS.store(0, Ordering::Relaxed);
    REM_CALLS.store(0, Ordering::Relaxed);
    CLR_CALLS.store(0, Ordering::Relaxed);
    MAPHASH_CALLS.store(0, Ordering::Relaxed);
}

#[cfg(test)]
fn force_enable_counters() {
    COUNTERS_FORCE_ENABLE.store(true, Ordering::Relaxed);
}

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
    buckets: Vec<Vec<(NodeId, NodeId)>>,
    count: usize,
}

impl HashTable {
    pub fn new(test_mode: TestMode) -> Self {
        Self {
            test_mode,
            buckets: vec![Vec::new(); 64],
            count: 0,
        }
    }

    pub fn get(&self, key: NodeId, arena: &crate::arena::Arena, mode: TestMode) -> Option<NodeId> {
        let idx = self.bucket_index(key, arena, &mode);
        for (k, v) in &self.buckets[idx] {
            if Self::compare(*k, key, arena, &mode) {
                return Some(*v);
            }
        }
        None
    }

    pub fn insert(&mut self, key: NodeId, value: NodeId, arena: &crate::arena::Arena) {
        let mode = self.test_mode.clone(); // Clone mode to avoid borrow conflict
        let idx = self.bucket_index(key, arena, &mode);
        for (k, v) in &mut self.buckets[idx] {
            if Self::compare(*k, key, arena, &mode) {
                *v = value;
                return;
            }
        }
        self.buckets[idx].push((key, value));
        self.count += 1;
        if self.count > self.buckets.len() * 4 {
            self.rehash(arena);
        }
    }

    pub fn remove(&mut self, key: NodeId, arena: &crate::arena::Arena) -> bool {
        let mode = self.test_mode.clone();
        let idx = self.bucket_index(key, arena, &mode);
        if let Some(pos) = self.buckets[idx]
            .iter()
            .position(|(k, _)| Self::compare(*k, key, arena, &mode))
        {
            self.buckets[idx].remove(pos);
            self.count = self.count.saturating_sub(1);
            return true;
        }
        false
    }

    pub fn clear(&mut self) {
        for bucket in &mut self.buckets {
            bucket.clear();
        }
        self.count = 0;
    }

    pub fn count(&self) -> usize {
        self.count
    }

    pub fn entries(&self) -> Vec<(NodeId, NodeId)> {
        let mut out = Vec::with_capacity(self.count);
        for bucket in &self.buckets {
            for (k, v) in bucket {
                out.push((*k, *v));
            }
        }
        out
    }

    fn rehash(&mut self, arena: &crate::arena::Arena) {
        let new_size = (self.buckets.len() * 2).max(64);
        let mut new_buckets: Vec<Vec<(NodeId, NodeId)>> = vec![Vec::new(); new_size];
        let mode = self.test_mode.clone();
        for bucket in self.buckets.drain(..) {
            for (k, v) in bucket {
                let idx = (Self::hash_key(k, arena, &mode) as usize) % new_size;
                new_buckets[idx].push((k, v));
            }
        }
        self.buckets = new_buckets;
    }

    fn bucket_index(&self, key: NodeId, arena: &crate::arena::Arena, mode: &TestMode) -> usize {
        (Self::hash_key(key, arena, mode) as usize) % self.buckets.len()
    }

    fn hash_key(a: NodeId, arena: &crate::arena::Arena, mode: &TestMode) -> u64 {
        match mode {
            TestMode::Eq => a.0 as u64,
            TestMode::Eql => Self::hash_eql(a, arena),
            TestMode::Equal => Self::hash_equal(a, arena, false, 0),
            TestMode::Equalp => Self::hash_equal(a, arena, true, 0),
        }
    }

    fn hash_eql(a: NodeId, arena: &crate::arena::Arena) -> u64 {
        use crate::arena::Node;
        use crate::types::OpaqueValue;

        match arena.get_unchecked(a) {
            Node::Leaf(OpaqueValue::Integer(n)) => (*n as u64).wrapping_mul(0x9e3779b97f4a7c15),
            Node::Leaf(OpaqueValue::Float(f)) => f.to_bits().wrapping_mul(0x9e3779b97f4a7c15),
            Node::Leaf(OpaqueValue::Char(c)) => (*c as u32 as u64).wrapping_mul(0x27d4eb2d),
            Node::Leaf(OpaqueValue::String(s)) => {
                let mut h: u64 = 0xcbf29ce484222325;
                for b in s.bytes() {
                    h ^= b as u64;
                    h = h.wrapping_mul(0x100000001b3);
                }
                h
            }
            Node::Leaf(OpaqueValue::Symbol(id)) => (*id as u64).wrapping_mul(0x9e3779b97f4a7c15),
            _ => a.0 as u64,
        }
    }

    fn hash_equal(a: NodeId, arena: &crate::arena::Arena, case_fold: bool, depth: usize) -> u64 {
        if depth > 32 {
            return a.0 as u64;
        }

        use crate::arena::Node;
        use crate::types::OpaqueValue;

        match arena.get_unchecked(a) {
            Node::Leaf(OpaqueValue::Nil) => 0x9e3779b97f4a7c15,
            Node::Leaf(OpaqueValue::Unbound) => 0x85ebca6b,
            Node::Leaf(OpaqueValue::Integer(n)) => (*n as u64).wrapping_mul(0x9e3779b97f4a7c15),
            Node::Leaf(OpaqueValue::Float(f)) => f.to_bits().wrapping_mul(0x9e3779b97f4a7c15),
            Node::Leaf(OpaqueValue::Char(c)) => (*c as u32 as u64).wrapping_mul(0x27d4eb2d),
            Node::Leaf(OpaqueValue::String(s)) => {
                let mut h: u64 = 0xcbf29ce484222325;
                if case_fold {
                    for b in s.bytes().map(|b| b.to_ascii_lowercase()) {
                        h ^= b as u64;
                        h = h.wrapping_mul(0x100000001b3);
                    }
                } else {
                    for b in s.bytes() {
                        h ^= b as u64;
                        h = h.wrapping_mul(0x100000001b3);
                    }
                }
                h
            }
            Node::Leaf(OpaqueValue::Symbol(id)) => (*id as u64).wrapping_mul(0x9e3779b97f4a7c15),
            Node::Leaf(OpaqueValue::BigInt(bi)) => {
                use num_traits::ToPrimitive;
                bi.to_u64().unwrap_or(a.0 as u64)
            }
            Node::Leaf(OpaqueValue::Ratio(num, den)) => {
                use num_traits::ToPrimitive;
                let n = num.to_u64().unwrap_or(0);
                let d = den.to_u64().unwrap_or(0);
                n.wrapping_mul(0x9e3779b97f4a7c15) ^ d
            }
            Node::Fork(car, cdr) => {
                let h1 = Self::hash_equal(*car, arena, case_fold, depth + 1);
                let h2 = Self::hash_equal(*cdr, arena, case_fold, depth + 1);
                h1 ^ h2.wrapping_mul(0x9e3779b97f4a7c15).wrapping_add(0x85ebca6b)
            }
            _ => a.0 as u64,
        }
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
            (Node::Leaf(OpaqueValue::Symbol(a_id)), Node::Leaf(OpaqueValue::Symbol(b_id))) => {
                a_id == b_id
            }
            (Node::Leaf(OpaqueValue::Char(a_ch)), Node::Leaf(OpaqueValue::Char(b_ch))) => {
                a_ch == b_ch
            }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena::{Arena, Node};
    use crate::types::OpaqueValue;

    #[test]
    fn hash_eql_matches_numeric_value() {
        let mut arena = Arena::new();
        let mut table = HashTable::new(TestMode::Eql);

        let key_a = arena.alloc(Node::Leaf(OpaqueValue::Integer(42)));
        let key_b = arena.alloc(Node::Leaf(OpaqueValue::Integer(42)));
        let value = arena.alloc(Node::Leaf(OpaqueValue::Integer(7)));

        table.insert(key_a, value, &arena);
        assert_eq!(table.get(key_b, &arena, TestMode::Eql), Some(value));
    }

    #[test]
    fn hash_equal_matches_cons_structure() {
        let mut arena = Arena::new();
        let mut table = HashTable::new(TestMode::Equal);

        let nil = arena.alloc(Node::Leaf(OpaqueValue::Nil));
        let one_a = arena.alloc(Node::Leaf(OpaqueValue::Integer(1)));
        let two_a = arena.alloc(Node::Leaf(OpaqueValue::Integer(2)));
        let list_a_tail = arena.alloc(Node::Fork(two_a, nil));
        let list_a = arena.alloc(Node::Fork(one_a, list_a_tail));

        let one_b = arena.alloc(Node::Leaf(OpaqueValue::Integer(1)));
        let two_b = arena.alloc(Node::Leaf(OpaqueValue::Integer(2)));
        let list_b_tail = arena.alloc(Node::Fork(two_b, nil));
        let list_b = arena.alloc(Node::Fork(one_b, list_b_tail));

        let value = arena.alloc(Node::Leaf(OpaqueValue::Integer(99)));
        table.insert(list_a, value, &arena);

        assert_eq!(table.get(list_b, &arena, TestMode::Equal), Some(value));
    }

    #[test]
    fn hash_counters_increment() {
        force_enable_counters();
        reset_counters();

        record_get();
        record_set();
        record_rem();
        record_clr();
        record_maphash();

        let counters = snapshot_counters();
        assert_eq!(counters.get_calls, 1);
        assert_eq!(counters.set_calls, 1);
        assert_eq!(counters.rem_calls, 1);
        assert_eq!(counters.clr_calls, 1);
        assert_eq!(counters.maphash_calls, 1);
    }
}
