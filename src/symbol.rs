// TreeCL Symbol Table and Package System
//
// Implements ANSI CL symbol/package semantics with O(1) comparison.

use std::collections::HashMap;

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

impl Package {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_uppercase(),
            nicknames: Vec::new(),
            internal: HashMap::new(),
            external: HashMap::new(),
            use_list: Vec::new(),
            used_by_list: Vec::new(),
            shadowing: HashMap::new(),
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
}

impl SymbolTable {
    pub fn new() -> Self {
        let mut table = Self {
            symbols: Vec::new(),
            packages: Vec::new(),
            package_names: HashMap::new(),
            current_package: PackageId(1), // CL-USER by default
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
        Ok(true)
    }

    /// Find a package by name
    pub fn find_package(&self, name: &str) -> Option<PackageId> {
        self.package_names
            .get(&Self::normalize_package_name(name))
            .copied()
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
        let name = name.to_string();

        if let Some((sym, status)) = self.find_symbol_in_package(pkg_id, &name) {
            return (sym, Some(status));
        }

        let sym_id = SymbolId(self.symbols.len() as u32);
        let symbol = Symbol::new(name.clone(), Some(pkg_id));
        self.symbols.push(symbol);

        if let Some(pkg) = self.packages.get_mut(pkg_id.0 as usize) {
            if pkg_id == PackageId(0) {
                pkg.export(&name, sym_id);
            } else {
                pkg.insert_internal(&name, sym_id);
            }
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
        if let Some(sym) = self.get_symbol(id) {
            if let Some(pkg_id) = sym.package {
                let name = sym.name.clone();
                if let Some(pkg) = self.get_package_mut(pkg_id) {
                    pkg.export(&name, id);
                }
            }
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
        Ok(pkg.unexport(&sym_name, sym_id))
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
        Ok(pkg.remove_symbol(&sym_name))
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
        Ok(())
    }

    pub fn find_symbol_in_package(
        &self,
        pkg_id: PackageId,
        name: &str,
    ) -> Option<(SymbolId, FindSymbolStatus)> {
        let pkg = self.packages.get(pkg_id.0 as usize)?;
        if pkg.is_deleted() {
            return None;
        }

        if let Some(sym) = pkg.find_external(name) {
            return Some((sym, FindSymbolStatus::External));
        }
        if let Some(sym) = pkg.find_symbol(name) {
            return Some((sym, FindSymbolStatus::Internal));
        }

        for &used_id in pkg.use_list() {
            let used_pkg = self.packages.get(used_id.0 as usize)?;
            if used_pkg.is_deleted() {
                continue;
            }
            if let Some(sym) = used_pkg.find_external(name) {
                return Some((sym, FindSymbolStatus::Inherited));
            }
        }
        None
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
}
