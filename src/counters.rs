use crate::fastmap::HashMap;
use std::sync::{Mutex, OnceLock};

#[derive(Default, Debug, Clone)]
pub struct LoadCounters {
    pub loads: u64,
    pub elapsed_ns: u64,
    pub find_package_calls: u64,
    pub find_package_ns: u64,
    pub find_symbol_calls: u64,
    pub find_symbol_ns: u64,
    pub intern_calls: u64,
    pub gethash_calls: u64,
    pub sethash_calls: u64,
    pub remhash_calls: u64,
    pub clrhash_calls: u64,
    pub maphash_calls: u64,
}

impl LoadCounters {
    pub fn add(&mut self, other: &LoadCounters) {
        self.loads = self.loads.saturating_add(other.loads);
        self.elapsed_ns = self.elapsed_ns.saturating_add(other.elapsed_ns);
        self.find_package_calls = self
            .find_package_calls
            .saturating_add(other.find_package_calls);
        self.find_package_ns = self
            .find_package_ns
            .saturating_add(other.find_package_ns);
        self.find_symbol_calls = self
            .find_symbol_calls
            .saturating_add(other.find_symbol_calls);
        self.find_symbol_ns = self
            .find_symbol_ns
            .saturating_add(other.find_symbol_ns);
        self.intern_calls = self.intern_calls.saturating_add(other.intern_calls);
        self.gethash_calls = self.gethash_calls.saturating_add(other.gethash_calls);
        self.sethash_calls = self.sethash_calls.saturating_add(other.sethash_calls);
        self.remhash_calls = self.remhash_calls.saturating_add(other.remhash_calls);
        self.clrhash_calls = self.clrhash_calls.saturating_add(other.clrhash_calls);
        self.maphash_calls = self.maphash_calls.saturating_add(other.maphash_calls);
    }

    pub fn total_hash_calls(&self) -> u64 {
        self.gethash_calls
            .saturating_add(self.sethash_calls)
            .saturating_add(self.remhash_calls)
            .saturating_add(self.clrhash_calls)
            .saturating_add(self.maphash_calls)
    }
}

static LOAD_COUNTERS: OnceLock<Mutex<HashMap<String, LoadCounters>>> = OnceLock::new();

fn load_map() -> &'static Mutex<HashMap<String, LoadCounters>> {
    LOAD_COUNTERS.get_or_init(|| Mutex::new(HashMap::default()))
}

pub fn record_load(path: &str, delta: &LoadCounters) {
    let mut map = load_map().lock().unwrap();
    let entry = map.entry(path.to_string()).or_insert_with(LoadCounters::default);
    entry.add(delta);
}

pub fn snapshot_loads() -> Vec<(String, LoadCounters)> {
    let map = load_map().lock().unwrap();
    map.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
}

pub fn reset_load_counters() {
    let mut map = load_map().lock().unwrap();
    map.clear();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn load_counters_accumulate() {
        reset_load_counters();
        let mut delta = LoadCounters::default();
        delta.loads = 1;
        delta.elapsed_ns = 10;
        delta.find_symbol_calls = 2;
        record_load("a.lsp", &delta);
        record_load("a.lsp", &delta);

        let entries = snapshot_loads();
        let found = entries.iter().find(|(k, _)| k == "a.lsp").unwrap();
        assert_eq!(found.1.loads, 2);
        assert_eq!(found.1.elapsed_ns, 20);
        assert_eq!(found.1.find_symbol_calls, 4);
    }
}
