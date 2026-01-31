// TreeCL Symbol Table and Package System
//
// Implements ANSI CL symbol/package semantics with O(1) comparison.

use std::collections::HashMap;

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
            // shadowing: Vec::new(),
        }
    }

    /// Add a package to the use-list
    pub fn use_package(&mut self, pkg: PackageId) {
        if !self.use_list.contains(&pkg) {
            self.use_list.push(pkg);
        }
    }

    /// Export a symbol
    pub fn export(&mut self, name: &str, sym: SymbolId) {
        self.external.insert(name.to_uppercase(), sym);
    }

    /// Find an external symbol
    pub fn find_external(&self, name: &str) -> Option<SymbolId> {
        self.external.get(&name.to_uppercase()).copied()
    }

    /// Find any symbol (internal or external)
    pub fn find_symbol(&self, name: &str) -> Option<SymbolId> {
        let upper = name.to_uppercase();
        self.external
            .get(&upper)
            .or_else(|| self.internal.get(&upper))
            .copied()
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
        table.create_package("CL-USER"); // PackageId(2)

        // CL-USER uses COMMON-LISP
        table.packages[2].use_package(PackageId(1));

        // Set current package to CL-USER
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

    /// Find a package by name
    pub fn find_package(&self, name: &str) -> Option<PackageId> {
        self.package_names.get(&name.to_uppercase()).copied()
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
        let upper = name.to_uppercase();

        // Check if already exists in package
        if let Some(pkg) = self.packages.get(pkg_id.0 as usize) {
            if let Some(sym) = pkg.find_symbol(&upper) {
                return sym;
            }

            // Check used packages for external symbol
            for &used_id in &pkg.use_list.clone() {
                if let Some(used_pkg) = self.packages.get(used_id.0 as usize) {
                    if let Some(sym) = used_pkg.find_external(&upper) {
                        return sym;
                    }
                }
            }
        }

        // Create new symbol
        let sym_id = SymbolId(self.symbols.len() as u32);
        let symbol = Symbol::new(upper.clone(), Some(pkg_id));
        self.symbols.push(symbol);

        // Add to package
        if let Some(pkg) = self.packages.get_mut(pkg_id.0 as usize) {
            // Keywords are automatically external
            if pkg_id == PackageId(0) {
                pkg.external.insert(upper, sym_id);
            } else {
                pkg.internal.insert(upper, sym_id);
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
        let symbol = Symbol::new(name.to_uppercase(), None);
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
