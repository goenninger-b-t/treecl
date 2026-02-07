// TreeCL Symbol Table and Package System
//
// Implements ANSI CL symbol/package semantics with O(1) comparison.

use crate::fastmap::HashMap;
use dashmap::DashMap;
use std::borrow::Cow;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::OnceLock;
use std::time::Instant;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FindSymbolStatus {
    Internal,
    External,
    Inherited,
}

/// Unique identifier for a symbol (index into symbol table)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolId(pub u32);

/// Unique identifier for a package
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PackageId(pub u32);

/// A Common Lisp symbol (Immutable Metadata only)
#[derive(Debug, Clone)]
pub struct Symbol {
    /// The symbol's name (e.g., "CAR", "MY-VAR")
    pub name: String,
    /// The home package (None for uninterned symbols)
    pub package: Option<PackageId>,
    /// Protected status (cannot be redefined, uninterned, or set)
    pub is_protected: bool,
    // Removed: value, function, plist (Moved to ProcessDictionary)
}

impl Symbol {
    pub fn new(name: String, package: Option<PackageId>) -> Self {
        Self {
            name,
            package,
            is_protected: false,
        }
    }

    /// Check if symbol is a keyword
    pub fn is_keyword(&self) -> bool {
        self.package == Some(PackageId(0)) // KEYWORD is package 0
    }
}

/// A Common Lisp package
#[derive(Debug, Clone)]
pub struct Package {
    /// Package name (e.g., "COMMON-LISP", "KEYWORD")
    pub name: String,
    /// Nicknames for the package
    pub nicknames: Vec<String>,
    /// Internal symbols (not exported)
    internal: HashMap<String, SymbolId>,
    /// External (exported) symbols
    external: HashMap<String, SymbolId>,
    /// List of used packages
    use_list: Vec<PackageId>,
    /// Packages that use this package
    used_by_list: Vec<PackageId>,
    /// Shadowing symbols by name
    shadowing: HashMap<String, SymbolId>,
    /// Documentation string
    documentation: Option<String>,
    /// Deleted flag (name/nicknames removed from registry)
    deleted: bool,
    // Shadowing symbols
    // Shadowing symbols - REMOVING field to avoid dead code warning for now
    // shadowing: Vec<SymbolId>,
}

#[derive(Default, Debug, Clone)]
pub struct SymbolCounters {
    pub find_package_calls: u64,
    pub find_package_ns: u64,
    pub find_symbol_calls: u64,
    pub find_symbol_ns: u64,
    pub intern_calls: u64,
}

#[derive(Debug)]
struct LookupCacheBucket {
    gen: u64,
    map: HashMap<String, Option<(SymbolId, FindSymbolStatus)>>,
}

impl LookupCacheBucket {
    fn new(gen: u64) -> Self {
        Self {
            gen,
            map: HashMap::default(),
        }
    }
}

static COUNTERS_ENABLED: OnceLock<bool> = OnceLock::new();
static COUNTERS_FORCE_ENABLE: AtomicBool = AtomicBool::new(false);
static FIND_PACKAGE_CALLS: AtomicU64 = AtomicU64::new(0);
static FIND_PACKAGE_NS: AtomicU64 = AtomicU64::new(0);
static FIND_SYMBOL_CALLS: AtomicU64 = AtomicU64::new(0);
static FIND_SYMBOL_NS: AtomicU64 = AtomicU64::new(0);
static INTERN_CALLS: AtomicU64 = AtomicU64::new(0);

fn counters_enabled() -> bool {
    if COUNTERS_FORCE_ENABLE.load(Ordering::Relaxed) {
        return true;
    }
    *COUNTERS_ENABLED.get_or_init(|| std::env::var("TREECL_DEBUG_COUNTERS").is_ok())
}

pub fn snapshot_counters() -> SymbolCounters {
    SymbolCounters {
        find_package_calls: FIND_PACKAGE_CALLS.load(Ordering::Relaxed),
        find_package_ns: FIND_PACKAGE_NS.load(Ordering::Relaxed),
        find_symbol_calls: FIND_SYMBOL_CALLS.load(Ordering::Relaxed),
        find_symbol_ns: FIND_SYMBOL_NS.load(Ordering::Relaxed),
        intern_calls: INTERN_CALLS.load(Ordering::Relaxed),
    }
}

pub fn reset_counters() {
    FIND_PACKAGE_CALLS.store(0, Ordering::Relaxed);
    FIND_PACKAGE_NS.store(0, Ordering::Relaxed);
    FIND_SYMBOL_CALLS.store(0, Ordering::Relaxed);
    FIND_SYMBOL_NS.store(0, Ordering::Relaxed);
    INTERN_CALLS.store(0, Ordering::Relaxed);
}

#[cfg(test)]
fn force_enable_counters() {
    COUNTERS_FORCE_ENABLE.store(true, Ordering::Relaxed);
}

impl Package {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_uppercase(),
            nicknames: Vec::new(),
            internal: HashMap::default(),
            external: HashMap::default(),
            use_list: Vec::new(),
            used_by_list: Vec::new(),
            shadowing: HashMap::default(),
            documentation: None,
            deleted: false,
        }
    }

    pub fn is_deleted(&self) -> bool {
        self.deleted
    }

    pub fn mark_deleted(&mut self) {
        self.deleted = true;
    }

    /// Add a package to the use-list
    pub fn use_package(&mut self, pkg: PackageId) {
        if !self.use_list.contains(&pkg) {
            self.use_list.push(pkg);
        }
    }

    pub fn unuse_package(&mut self, pkg: PackageId) -> bool {
        if let Some(pos) = self.use_list.iter().position(|p| *p == pkg) {
            self.use_list.remove(pos);
            return true;
        }
        false
    }

    pub fn add_used_by(&mut self, pkg: PackageId) {
        if !self.used_by_list.contains(&pkg) {
            self.used_by_list.push(pkg);
        }
    }

    pub fn remove_used_by(&mut self, pkg: PackageId) -> bool {
        if let Some(pos) = self.used_by_list.iter().position(|p| *p == pkg) {
            self.used_by_list.remove(pos);
            return true;
        }
        false
    }

    pub fn used_by_list(&self) -> &[PackageId] {
        &self.used_by_list
    }

    pub fn use_list(&self) -> &[PackageId] {
        &self.use_list
    }

    /// Export a symbol
    pub fn export(&mut self, name: &str, sym: SymbolId) {
        self.external.insert(name.to_string(), sym);
        self.internal.remove(name);
    }

    /// Unexport a symbol (move to internal if present)
    pub fn unexport(&mut self, name: &str, sym: SymbolId) -> bool {
        if self.external.remove(name).is_some() {
            self.internal.insert(name.to_string(), sym);
            return true;
        }
        false
    }

    /// Find an external symbol
    pub fn find_external(&self, name: &str) -> Option<SymbolId> {
        self.external.get(name).copied()
    }

    /// Find any symbol (internal or external)
    pub fn find_symbol(&self, name: &str) -> Option<SymbolId> {
        self.external
            .get(name)
            .or_else(|| self.internal.get(name))
            .copied()
    }

    pub fn insert_internal(&mut self, name: &str, sym: SymbolId) {
        self.internal.insert(name.to_string(), sym);
    }

    pub fn remove_symbol(&mut self, name: &str) -> bool {
        let mut removed = false;
        if self.internal.remove(name).is_some() {
            removed = true;
        }
        if self.external.remove(name).is_some() {
            removed = true;
        }
        self.shadowing.remove(name);
        removed
    }

    pub fn shadowing_symbol(&self, name: &str) -> Option<SymbolId> {
        self.shadowing.get(name).copied()
    }

    pub fn add_shadowing(&mut self, name: &str, sym: SymbolId) {
        self.shadowing.insert(name.to_string(), sym);
    }

    pub fn remove_shadowing(&mut self, name: &str) {
        self.shadowing.remove(name);
    }

    pub fn shadowing_symbols(&self) -> impl Iterator<Item = SymbolId> + '_ {
        self.shadowing.values().copied()
    }

    pub fn internal_symbols(&self) -> impl Iterator<Item = (&String, SymbolId)> + '_ {
        self.internal.iter().map(|(k, v)| (k, *v))
    }

    pub fn external_symbols(&self) -> impl Iterator<Item = (&String, SymbolId)> + '_ {
        self.external.iter().map(|(k, v)| (k, *v))
    }

    pub fn set_documentation(&mut self, doc: Option<String>) {
        self.documentation = doc;
    }

    pub fn documentation(&self) -> Option<&str> {
        self.documentation.as_deref()
    }
}

/// The global symbol table
#[derive(Debug)]
pub struct SymbolTable {
    /// All symbols indexed by SymbolId
    symbols: Vec<Symbol>,
    /// All packages indexed by PackageId
    packages: Vec<Package>,
    /// Package name -> PackageId lookup
    package_names: HashMap<String, PackageId>,
    /// Current package (*package*)
    current_package: PackageId,
    lookup_gen: AtomicU64,
    lookup_cache: DashMap<PackageId, LookupCacheBucket>,
}

impl SymbolTable {
    pub fn new() -> Self {
        let mut table = Self {
            symbols: Vec::new(),
            packages: Vec::new(),
            package_names: HashMap::default(),
            current_package: PackageId(1), // CL-USER by default
            lookup_gen: AtomicU64::new(0),
            lookup_cache: DashMap::new(),
        };

        // Create standard packages
        table.create_package("KEYWORD"); // PackageId(0)
        table.create_package("COMMON-LISP"); // PackageId(1)
        table.create_package("COMMON-LISP-USER"); // PackageId(2)

        // CL-USER uses COMMON-LISP
        table.packages[2].use_package(PackageId(1));
        table.packages[1].add_used_by(PackageId(2));

        // Set current package to COMMON-LISP-USER
        table.current_package = PackageId(2);

        table
    }

    /// Get mutable symbol data (INTERNAL USE ONLY)
    // Protected symbols should typically not be mutated, but we might need
    // to separate this text later.
    pub fn get_mut(&mut self, id: SymbolId) -> Option<&mut Symbol> {
        self.symbols.get_mut(id.0 as usize)
    }

    /// Mark a symbol as protected
    pub fn protect_symbol(&mut self, id: SymbolId) {
        if let Some(sym) = self.symbols.get_mut(id.0 as usize) {
            sym.is_protected = true;
        }
    }

    /// Check if a symbol is protected
    pub fn is_protected(&self, id: SymbolId) -> bool {
        self.get_symbol(id).map(|s| s.is_protected).unwrap_or(false)
    }

    /// Create a new package
    pub fn create_package(&mut self, name: &str) -> PackageId {
        let id = PackageId(self.packages.len() as u32);
        let mut pkg = Package::new(name);

        // Add standard nicknames
        match name.to_uppercase().as_str() {
            "COMMON-LISP" => pkg.nicknames.push("CL".to_string()),
            "COMMON-LISP-USER" => pkg.nicknames.push("CL-USER".to_string()),
            _ => {}
        }

        self.package_names.insert(name.to_uppercase(), id);
        for i in 0..pkg.nicknames.len() {
            let nick = pkg.nicknames[i].clone();
            self.package_names.insert(nick, id);
        }

        self.packages.push(pkg);
        id
    }

    fn normalize_package_name(name: &str) -> String {
        name.to_uppercase()
    }

    fn normalize_package_lookup(name: &str) -> Cow<'_, str> {
        if name
            .bytes()
            .all(|b| !b.is_ascii_lowercase())
        {
            Cow::Borrowed(name)
        } else {
            Cow::Owned(name.to_ascii_uppercase())
        }
    }

    fn lookup_gen(&self) -> u64 {
        self.lookup_gen.load(Ordering::Relaxed)
    }

    fn bump_lookup_gen(&self) {
        self.lookup_gen.fetch_add(1, Ordering::Relaxed);
    }

    fn lookup_cache_get(
        &self,
        pkg_id: PackageId,
        name: &str,
    ) -> Option<Option<(SymbolId, FindSymbolStatus)>> {
        let gen = self.lookup_gen();
        if let Some(bucket) = self.lookup_cache.get(&pkg_id) {
            if bucket.gen == gen {
                if let Some(value) = bucket.map.get(name) {
                    return Some(*value);
                }
            }
        }
        None
    }

    fn lookup_cache_insert(
        &self,
        pkg_id: PackageId,
        name: &str,
        value: Option<(SymbolId, FindSymbolStatus)>,
    ) {
        let gen = self.lookup_gen();
        if let Some(mut bucket) = self.lookup_cache.get_mut(&pkg_id) {
            if bucket.gen != gen {
                bucket.gen = gen;
                bucket.map.clear();
            }
            bucket.map.insert(name.to_string(), value);
            return;
        }

        let mut bucket = LookupCacheBucket::new(gen);
        bucket.map.insert(name.to_string(), value);
        self.lookup_cache.insert(pkg_id, bucket);
    }

    pub fn make_package(
        &mut self,
        name: &str,
        nicknames: Vec<String>,
        use_list: Vec<PackageId>,
        documentation: Option<String>,
    ) -> Result<PackageId, String> {
        let name_norm = Self::normalize_package_name(name);
        if self.package_names.contains_key(&name_norm) {
            return Err(format!("Package already exists: {}", name_norm));
        }

        let mut pkg = Package::new(&name_norm);
        pkg.set_documentation(documentation);

        for nick in nicknames {
            let nick_norm = Self::normalize_package_name(&nick);
            if self.package_names.contains_key(&nick_norm) {
                return Err(format!("Package nickname already exists: {}", nick_norm));
            }
            pkg.nicknames.push(nick_norm.clone());
        }

        let id = PackageId(self.packages.len() as u32);
        self.package_names.insert(name_norm.clone(), id);
        for nick in &pkg.nicknames {
            self.package_names.insert(nick.clone(), id);
        }

        self.packages.push(pkg);

        for used in use_list {
            self.use_package(id, used)?;
        }

        Ok(id)
    }

    pub fn delete_package(&mut self, id: PackageId) -> Result<bool, String> {
        let (name, nicknames, used, used_by) = {
            let pkg = self
                .packages
                .get_mut(id.0 as usize)
                .ok_or_else(|| "Unknown package".to_string())?;

            if pkg.is_deleted() {
                return Ok(false);
            }

            (
                pkg.name.clone(),
                pkg.nicknames.clone(),
                pkg.use_list.clone(),
                pkg.used_by_list.clone(),
            )
        };

        let mut keys = vec![name];
        keys.extend(nicknames);
        for key in keys {
            self.package_names.remove(&Self::normalize_package_name(&key));
        }

        // Remove from used-by lists in used packages
        for used_id in used {
            if let Some(used_pkg) = self.packages.get_mut(used_id.0 as usize) {
                used_pkg.remove_used_by(id);
            }
        }

        // Remove from use-lists in packages that used this package
        for user_id in used_by {
            if let Some(user_pkg) = self.packages.get_mut(user_id.0 as usize) {
                user_pkg.unuse_package(id);
            }
        }

        // Unintern home symbols by clearing their home package
        for sym in self.symbols.iter_mut() {
            if sym.package == Some(id) {
                sym.package = None;
            }
        }

        if let Some(pkg) = self.packages.get_mut(id.0 as usize) {
            pkg.mark_deleted();
        }
        self.bump_lookup_gen();
        Ok(true)
    }

    /// Find a package by name
    pub fn find_package(&self, name: &str) -> Option<PackageId> {
        let enabled = counters_enabled();
        let start = if enabled { Some(Instant::now()) } else { None };
        if enabled {
            FIND_PACKAGE_CALLS.fetch_add(1, Ordering::Relaxed);
        }

        let key = Self::normalize_package_lookup(name);
        let result = self.package_names.get(key.as_ref()).copied();

        if let Some(start) = start {
            let elapsed = start.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
            FIND_PACKAGE_NS.fetch_add(elapsed, Ordering::Relaxed);
        }

        result
    }

    /// Get the current package
    pub fn current_package(&self) -> PackageId {
        self.current_package
    }

    /// Set the current package
    pub fn set_current_package(&mut self, pkg: PackageId) {
        self.current_package = pkg;
    }

    /// Get a package by ID
    pub fn get_package(&self, id: PackageId) -> Option<&Package> {
        self.packages.get(id.0 as usize)
    }

    /// Get a mutable package by ID
    pub fn get_package_mut(&mut self, id: PackageId) -> Option<&mut Package> {
        self.packages.get_mut(id.0 as usize)
    }

    /// Get a symbol by ID
    pub fn get_symbol(&self, id: SymbolId) -> Option<&Symbol> {
        self.symbols.get(id.0 as usize)
    }

    pub fn iter_symbols(&self) -> impl Iterator<Item = &Symbol> {
        self.symbols.iter()
    }

    /// Get the total number of symbols
    pub fn symbol_count(&self) -> usize {
        self.symbols.len()
    }

    /// Get the total number of packages
    pub fn package_count(&self) -> usize {
        self.packages.len()
    }

    /// Get a mutable symbol by ID
    pub fn get_symbol_mut(&mut self, id: SymbolId) -> Option<&mut Symbol> {
        self.symbols.get_mut(id.0 as usize)
    }

    /// Intern a symbol in the current package
    pub fn intern(&mut self, name: &str) -> SymbolId {
        self.intern_in(name, self.current_package)
    }

    /// Intern a symbol in a specific package
    pub fn intern_in(&mut self, name: &str, pkg_id: PackageId) -> SymbolId {
        self.intern_in_with_status(name, pkg_id).0
    }

    pub fn intern_in_with_status(
        &mut self,
        name: &str,
        pkg_id: PackageId,
    ) -> (SymbolId, Option<FindSymbolStatus>) {
        if counters_enabled() {
            INTERN_CALLS.fetch_add(1, Ordering::Relaxed);
        }
        if let Some((sym, status)) = self.find_symbol_in_package(pkg_id, name) {
            return (sym, Some(status));
        }

        let name = name.to_string();
        let sym_id = SymbolId(self.symbols.len() as u32);
        let symbol = Symbol::new(name.clone(), Some(pkg_id));
        self.symbols.push(symbol);

        if let Some(pkg) = self.packages.get_mut(pkg_id.0 as usize) {
            if pkg_id == PackageId(0) {
                pkg.export(&name, sym_id);
            } else {
                pkg.insert_internal(&name, sym_id);
            }
            self.bump_lookup_gen();
        }

        (sym_id, None)
    }

    pub fn create_symbol_in_package(&mut self, name: &str, pkg_id: PackageId) -> SymbolId {
        let sym_id = SymbolId(self.symbols.len() as u32);
        let symbol = Symbol::new(name.to_string(), Some(pkg_id));
        self.symbols.push(symbol);
        if let Some(pkg) = self.get_package_mut(pkg_id) {
            if pkg_id == PackageId(0) {
                pkg.export(name, sym_id);
            } else {
                pkg.insert_internal(name, sym_id);
            }
            self.bump_lookup_gen();
        }
        sym_id
    }

    /// Intern a keyword (in KEYWORD package)
    pub fn intern_keyword(&mut self, name: &str) -> SymbolId {
        self.intern_in(name, PackageId(0))
    }

    /// Create an uninterned symbol (gensym)
    pub fn make_symbol(&mut self, name: &str) -> SymbolId {
        let sym_id = SymbolId(self.symbols.len() as u32);
        let symbol = Symbol::new(name.to_string(), None);
        self.symbols.push(symbol);
        sym_id
    }

    /// Get the name of a symbol
    pub fn symbol_name(&self, id: SymbolId) -> Option<&str> {
        self.get_symbol(id).map(|s| s.name.as_str())
    }

    /// Get the package of a symbol
    pub fn symbol_package(&self, id: SymbolId) -> Option<PackageId> {
        self.get_symbol(id).and_then(|s| s.package)
    }

    /// Export a symbol from its home package
    pub fn export_symbol(&mut self, id: SymbolId) {
        let mut did_export = false;
        if let Some(sym) = self.get_symbol(id) {
            if let Some(pkg_id) = sym.package {
                let name = sym.name.clone();
                if let Some(pkg) = self.get_package_mut(pkg_id) {
                    pkg.export(&name, id);
                    did_export = true;
                }
            }
        }
        if did_export {
            self.bump_lookup_gen();
        }
    }

    pub fn export_in_package(
        &mut self,
        pkg_id: PackageId,
        sym_id: SymbolId,
    ) -> Result<(), String> {
        let sym_name = self
            .symbol_name(sym_id)
            .ok_or_else(|| "Unknown symbol".to_string())?
            .to_string();
        let pkg = self
            .get_package_mut(pkg_id)
            .ok_or_else(|| "Unknown package".to_string())?;
        if pkg.is_deleted() {
            return Err("Package deleted".into());
        }
        pkg.export(&sym_name, sym_id);
        self.bump_lookup_gen();
        Ok(())
    }

    pub fn unexport_in_package(
        &mut self,
        pkg_id: PackageId,
        sym_id: SymbolId,
    ) -> Result<bool, String> {
        let sym_name = self
            .symbol_name(sym_id)
            .ok_or_else(|| "Unknown symbol".to_string())?
            .to_string();
        let pkg = self
            .get_package_mut(pkg_id)
            .ok_or_else(|| "Unknown package".to_string())?;
        if pkg.is_deleted() {
            return Ok(false);
        }
        let removed = pkg.unexport(&sym_name, sym_id);
        if removed {
            self.bump_lookup_gen();
        }
        Ok(removed)
    }

    pub fn import_into_package(
        &mut self,
        pkg_id: PackageId,
        sym_id: SymbolId,
    ) -> Result<(), String> {
        let sym_name = self
            .symbol_name(sym_id)
            .ok_or_else(|| "Unknown symbol".to_string())?
            .to_string();
        let pkg = self
            .get_package_mut(pkg_id)
            .ok_or_else(|| "Unknown package".to_string())?;
        if pkg.is_deleted() {
            return Err("Package deleted".into());
        }
        pkg.insert_internal(&sym_name, sym_id);
        self.bump_lookup_gen();
        Ok(())
    }

    pub fn unintern_from_package(
        &mut self,
        pkg_id: PackageId,
        sym_id: SymbolId,
    ) -> Result<bool, String> {
        let sym_name = self
            .symbol_name(sym_id)
            .ok_or_else(|| "Unknown symbol".to_string())?
            .to_string();
        let pkg = self
            .get_package_mut(pkg_id)
            .ok_or_else(|| "Unknown package".to_string())?;
        if pkg.is_deleted() {
            return Ok(false);
        }
        let removed = pkg.remove_symbol(&sym_name);
        if removed {
            self.bump_lookup_gen();
        }
        Ok(removed)
    }

    pub fn add_shadowing_symbol(
        &mut self,
        pkg_id: PackageId,
        sym_id: SymbolId,
    ) -> Result<(), String> {
        let sym_name = self
            .symbol_name(sym_id)
            .ok_or_else(|| "Unknown symbol".to_string())?
            .to_string();
        let pkg = self
            .get_package_mut(pkg_id)
            .ok_or_else(|| "Unknown package".to_string())?;
        if pkg.is_deleted() {
            return Err("Package deleted".into());
        }
        pkg.add_shadowing(&sym_name, sym_id);
        self.bump_lookup_gen();
        Ok(())
    }

    pub fn find_symbol_in_package(
        &self,
        pkg_id: PackageId,
        name: &str,
    ) -> Option<(SymbolId, FindSymbolStatus)> {
        let enabled = counters_enabled();
        let start = if enabled { Some(Instant::now()) } else { None };
        if enabled {
            FIND_SYMBOL_CALLS.fetch_add(1, Ordering::Relaxed);
        }

        let cached = self.lookup_cache_get(pkg_id, name);
        let result = if let Some(cached) = cached {
            cached
        } else {
            let result = if let Some(pkg) = self.packages.get(pkg_id.0 as usize) {
                if pkg.is_deleted() {
                    None
                } else if let Some(sym) = pkg.find_external(name) {
                    Some((sym, FindSymbolStatus::External))
                } else if let Some(sym) = pkg.find_symbol(name) {
                    Some((sym, FindSymbolStatus::Internal))
                } else {
                    let mut inherited = None;
                    for &used_id in pkg.use_list() {
                        if let Some(used_pkg) = self.packages.get(used_id.0 as usize) {
                            if used_pkg.is_deleted() {
                                continue;
                            }
                            if let Some(sym) = used_pkg.find_external(name) {
                                inherited = Some((sym, FindSymbolStatus::Inherited));
                                break;
                            }
                        }
                    }
                    inherited
                }
            } else {
                None
            };
            self.lookup_cache_insert(pkg_id, name, result);
            result
        };
        if let Some(start) = start {
            let elapsed = start.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
            FIND_SYMBOL_NS.fetch_add(elapsed, Ordering::Relaxed);
        }
        result
    }

    pub fn use_package(&mut self, pkg_id: PackageId, use_pkg: PackageId) -> Result<(), String> {
        if pkg_id == use_pkg {
            return Ok(());
        }

        let (pkg_use_list, shadowing) = {
            let pkg = self
                .get_package(pkg_id)
                .ok_or_else(|| "Unknown package".to_string())?;
            if pkg.is_deleted() {
                return Err("Package deleted".into());
            }
            (pkg.use_list().to_vec(), pkg.shadowing.clone())
        };

        if pkg_use_list.contains(&use_pkg) {
            return Ok(());
        }

        let used_pkg = self
            .get_package(use_pkg)
            .ok_or_else(|| "Unknown package".to_string())?;
        if used_pkg.is_deleted() {
            return Err("Package deleted".into());
        }

        // Conflict check
        for (name, sym) in used_pkg.external.iter() {
            if shadowing.contains_key(name) {
                continue;
            }
            if let Some((existing, _)) = self.find_symbol_in_package(pkg_id, name) {
                if existing != *sym {
                    return Err(format!("Name conflict on {}", name));
                }
            }
        }

        if let Some(pkg) = self.get_package_mut(pkg_id) {
            pkg.use_package(use_pkg);
        }
        if let Some(used) = self.get_package_mut(use_pkg) {
            used.add_used_by(pkg_id);
        }
        self.bump_lookup_gen();
        Ok(())
    }

    pub fn unuse_package(&mut self, pkg_id: PackageId, use_pkg: PackageId) -> Result<bool, String> {
        let mut removed = false;
        if let Some(pkg) = self.get_package_mut(pkg_id) {
            removed = pkg.unuse_package(use_pkg);
        }
        if removed {
            if let Some(used) = self.get_package_mut(use_pkg) {
                used.remove_used_by(pkg_id);
            }
            self.bump_lookup_gen();
        }
        Ok(removed)
    }

    pub fn rename_package(
        &mut self,
        pkg_id: PackageId,
        new_name: &str,
        new_nicknames: Option<Vec<String>>,
    ) -> Result<(), String> {
        let name_norm = Self::normalize_package_name(new_name);
        if let Some(existing) = self.package_names.get(&name_norm) {
            if *existing != pkg_id {
                return Err(format!("Package name already in use: {}", name_norm));
            }
        }

        let (old_name, old_nicknames) = {
            let pkg = self
                .get_package(pkg_id)
                .ok_or_else(|| "Unknown package".to_string())?;
            if pkg.is_deleted() {
                return Err("Package deleted".into());
            }
            (pkg.name.clone(), pkg.nicknames.clone())
        };

        // Remove old name/nicknames
        let mut keys = vec![old_name];
        keys.extend(old_nicknames.clone());
        for key in keys {
            self.package_names.remove(&Self::normalize_package_name(&key));
        }

        let new_nicks_norm = if let Some(nicks) = new_nicknames {
            nicks
                .into_iter()
                .map(|n| Self::normalize_package_name(&n))
                .collect()
        } else {
            old_nicknames
        };

        if let Some(pkg) = self.get_package_mut(pkg_id) {
            pkg.name = name_norm.clone();
            pkg.nicknames = new_nicks_norm.clone();
        }

        self.package_names.insert(name_norm.clone(), pkg_id);
        for nick in &new_nicks_norm {
            self.package_names.insert(nick.clone(), pkg_id);
        }

        Ok(())
    }
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_package() {
        let table = SymbolTable::new();
        let pkg = table.find_package("COMMON-LISP");
        assert!(pkg.is_some());
        assert_eq!(table.find_package("CL"), pkg); // Nickname
    }

    #[test]
    fn test_intern_symbol() {
        let mut table = SymbolTable::new();
        let sym1 = table.intern("FOO");
        let sym2 = table.intern("FOO");
        assert_eq!(sym1, sym2); // Same symbol

        let sym3 = table.intern("BAR");
        assert_ne!(sym1, sym3); // Different symbols
    }

    #[test]
    fn test_keyword() {
        let mut table = SymbolTable::new();
        let kw = table.intern_keyword("TEST");
        let sym = table.get_symbol(kw).unwrap();
        assert!(sym.is_keyword());
    }

    #[test]
    fn test_uninterned() {
        let mut table = SymbolTable::new();
        let sym = table.make_symbol("G123");
        let s = table.get_symbol(sym).unwrap();
        assert!(s.package.is_none()); // Uninterned
    }
    #[test]
    fn test_inheritance() {
        let mut table = SymbolTable::new();
        // Switch to CL (1)
        table.set_current_package(PackageId(1));
        let foo_cl = table.intern("FOO");
        table.export_symbol(foo_cl);

        // Switch to CL-USER (2)
        // CL-USER uses CL.
        table.set_current_package(PackageId(2));

        // Should find inherited FOO
        let foo_user = table.intern("FOO");

        assert_eq!(foo_cl, foo_user, "FOO should be inherited from CL");

        // Verify via intern_in
        let foo_user_2 = table.intern_in("FOO", PackageId(2));
        assert_eq!(foo_cl, foo_user_2, "FOO via intern_in should be inherited");
    }

    #[test]
    fn test_symbol_counters_increment() {
        force_enable_counters();
        reset_counters();

        let mut table = SymbolTable::new();
        let _ = table.find_package("CL");
        let _ = table.intern_in("CAR", PackageId(1));
        let _ = table.find_symbol_in_package(PackageId(1), "CAR");
        let _ = table.intern("FOO");

        let counters = snapshot_counters();
        assert!(counters.find_package_calls >= 1);
        assert!(counters.find_symbol_calls >= 1);
        assert!(counters.intern_calls >= 1);
    }

    #[test]
    fn test_find_symbol_cache_invalidation_after_intern() {
        let mut table = SymbolTable::new();
        let pkg = PackageId(2);

        let miss = table.find_symbol_in_package(pkg, "CACHE-MISS-1");
        assert!(miss.is_none());

        let sym = table.intern_in("CACHE-MISS-1", pkg);
        let found = table.find_symbol_in_package(pkg, "CACHE-MISS-1");
        assert_eq!(found, Some((sym, FindSymbolStatus::Internal)));
    }
}
