use crate::eval::{EvalResult, SpecialForms};
use crate::process::Process;
use crate::symbol::{PackageId, SymbolId, SymbolTable};
use crate::types::NodeId;
use std::collections::HashMap;

/// Type for primitive functions
/// Note: Signature changed to take Process context
pub type PrimitiveFn = fn(&mut Process, &GlobalContext, &[NodeId]) -> EvalResult;

use std::sync::RwLock;

pub struct GlobalContext {
    pub symbols: RwLock<SymbolTable>, // Interner (Names)
    pub special_forms: SpecialForms,  // IDs of special forms
    pub primitives: HashMap<SymbolId, PrimitiveFn>,

    // cached standard symbols
    pub t_sym: SymbolId,
    pub nil_sym: SymbolId,
    pub package_sym: SymbolId,
}

impl GlobalContext {
    pub fn new() -> Self {
        let mut symbols = SymbolTable::new();
        let special_forms = SpecialForms::new(&mut symbols);

        let nil_sym = symbols.intern_in("NIL", PackageId(1));
        let t_sym = symbols.intern_in("T", PackageId(1));
        let package_sym = symbols.intern_in("*PACKAGE*", PackageId(1));

        // Export NIL and T
        symbols.export_symbol(nil_sym);
        symbols.export_symbol(t_sym);
        symbols.export_symbol(package_sym);

        // Ensure CALL-NEXT-METHOD/NEXT-METHOD-P are in COMMON-LISP so reader resolves them consistently.
        let cnm_sym = symbols.intern_in("CALL-NEXT-METHOD", PackageId(1));
        symbols.export_symbol(cnm_sym);
        let nmp_sym = symbols.intern_in("NEXT-METHOD-P", PackageId(1));
        symbols.export_symbol(nmp_sym);

        // Register Protected Combinator Keywords
        let kw = PackageId(0); // KEYWORD
        let s_comb = symbols.intern_in("S-COMBINATOR", kw);
        symbols.protect_symbol(s_comb);

        let k_comb = symbols.intern_in("K-COMBINATOR", kw);
        symbols.protect_symbol(k_comb);

        let i_comb = symbols.intern_in("I-COMBINATOR", kw);
        symbols.protect_symbol(i_comb);

        let triage_comb = symbols.intern_in("TRIAGE-COMBINATOR", kw);
        symbols.protect_symbol(triage_comb);

        Self {
            symbols: RwLock::new(symbols),
            special_forms,
            primitives: HashMap::new(),
            t_sym,
            nil_sym,
            package_sym,
        }
    }

    pub fn register_primitive(&mut self, name: &str, pkg: PackageId, func: PrimitiveFn) {
        let mut symbols = self.symbols.write().unwrap();
        let sym = symbols.intern_in(name, pkg);
        symbols.export_symbol(sym);
        self.primitives.insert(sym, func);
    }
}
