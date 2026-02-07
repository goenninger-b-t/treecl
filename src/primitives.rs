// TreeCL Primitives - Built-in Functions
//
// Implements core CL primitives in Rust.

use crate::arena::{Arena, Node};
use crate::context::PrimitiveFn;
use crate::eval::{Closure, ControlSignal, Environment, EvalResult, Interpreter, ParsedLambdaList};
use crate::counters::LoadCounters;
use crate::hashtables::{HashTable, TestMode};
use crate::process::Process;
use crate::readtable::{ReadtableCase, ReadtableId};
use crate::symbol::{PackageId, SymbolId};
use crate::syscall::SysCall;
use crate::types::{NodeId, OpaqueValue};
use crate::pathname::Pathname;
use crate::tree_calculus;
use crate::clos::GenericName;
use libc;
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive};
use crate::fastmap::HashMap;

fn err_helper(msg: &str) -> EvalResult {
    Err(ControlSignal::Error(msg.to_string()))
}

fn set_multiple_values(proc: &mut Process, mut values: Vec<NodeId>) -> NodeId {
    proc.values_are_set = true;
    proc.values.clear();
    proc.values.append(&mut values);
    proc.values
        .first()
        .copied()
        .unwrap_or_else(|| proc.make_nil())
}

fn node_to_symbol(proc: &Process, node: NodeId) -> Option<SymbolId> {
    if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(node) {
        Some(SymbolId(*id))
    } else {
        None
    }
}

fn node_is_nil(proc: &Process, node: NodeId) -> bool {
    matches!(
        proc.arena.inner.get_unchecked(node),
        Node::Leaf(OpaqueValue::Nil)
    )
}

fn node_to_hash_handle(proc: &Process, node: NodeId) -> Option<crate::types::HashHandle> {
    if let Node::Leaf(OpaqueValue::HashHandle(id)) = proc.arena.inner.get_unchecked(node) {
        Some(crate::types::HashHandle(*id))
    } else {
        None
    }
}

fn node_to_char(
    proc: &Process,
    ctx: &crate::context::GlobalContext,
    node: NodeId,
) -> Option<char> {
    match proc.arena.inner.get_unchecked(node) {
        Node::Leaf(OpaqueValue::Char(c)) => Some(*c),
        Node::Leaf(OpaqueValue::Integer(n)) => std::char::from_u32(*n as u32),
        Node::Leaf(OpaqueValue::String(s)) => s.chars().next(),
        Node::Leaf(OpaqueValue::Symbol(id)) => ctx
            .symbols
            .read()
            .unwrap()
            .symbol_name(SymbolId(*id))
            .and_then(|s| s.chars().next()),
        _ => None,
    }
}

fn list_to_vec_opt(proc: &Process, list: NodeId) -> Option<Vec<NodeId>> {
    let mut out = Vec::new();
    let mut cur = list;
    loop {
        match proc.arena.inner.get_unchecked(cur) {
            Node::Leaf(OpaqueValue::Nil) => break,
            Node::Fork(car, cdr) => {
                out.push(*car);
                cur = *cdr;
            }
            _ => return None,
        }
    }
    Some(out)
}

fn path_from_designator(
    proc: &Process,
    ctx: &crate::context::GlobalContext,
    node: NodeId,
    label: &str,
) -> Result<String, ControlSignal> {
    string_from_designator(proc, ctx, node)
        .ok_or_else(|| ControlSignal::Error(format!("{}: invalid pathspec", label)))
}

fn alloc_string(proc: &mut Process, value: String) -> NodeId {
    proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(value)))
}

fn alloc_pathname(proc: &mut Process, pathname: Pathname) -> NodeId {
    proc.arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Pathname(pathname)))
}

fn node_to_pathname(proc: &Process, node: NodeId) -> Option<Pathname> {
    match proc.arena.inner.get_unchecked(node) {
        Node::Leaf(OpaqueValue::Pathname(p)) => Some(p.clone()),
        _ => None,
    }
}

fn pathname_from_designator(
    proc: &Process,
    ctx: &crate::context::GlobalContext,
    node: NodeId,
    label: &str,
) -> Result<Pathname, ControlSignal> {
    if let Some(pn) = node_to_pathname(proc, node) {
        return Ok(pn);
    }
    let s = path_from_designator(proc, ctx, node, label)?;
    Ok(Pathname::from_namestring(&s))
}

fn path_is_absolute(path: &str) -> bool {
    if std::path::Path::new(path).is_absolute() {
        return true;
    }
    let bytes = path.as_bytes();
    bytes.len() >= 2 && bytes[1] == b':' && bytes[0].is_ascii_alphabetic()
        || {
            let colon = path.find(':');
            let sep = path.find(|c| c == '/' || c == '\\');
            colon.is_some()
                && !(colon == Some(1)
                    && bytes.get(0).map(|b| b.is_ascii_alphabetic()) == Some(true))
                && (sep.is_none() || colon.unwrap() < sep.unwrap())
        }
}

fn glob_match(pattern: &str, text: &str) -> bool {
    let p = pattern.as_bytes();
    let s = text.as_bytes();
    let mut pi = 0usize;
    let mut si = 0usize;
    let mut star_idx: Option<usize> = None;
    let mut match_idx = 0usize;

    while si < s.len() {
        if pi < p.len() && (p[pi] == b'?' || p[pi] == s[si]) {
            pi += 1;
            si += 1;
        } else if pi < p.len() && p[pi] == b'*' {
            star_idx = Some(pi);
            match_idx = si;
            pi += 1;
        } else if let Some(star) = star_idx {
            pi = star + 1;
            match_idx += 1;
            si = match_idx;
        } else {
            return false;
        }
    }

    while pi < p.len() && p[pi] == b'*' {
        pi += 1;
    }

    pi == p.len()
}

fn is_wild_component(text: &str) -> bool {
    text.eq_ignore_ascii_case("WILD")
        || text.eq_ignore_ascii_case("WILD-INFERIORS")
        || text.contains('*')
        || text.contains('?')
}

fn component_matches(actual: &str, pattern: &str) -> bool {
    if pattern.eq_ignore_ascii_case("WILD") {
        return true;
    }
    if pattern.contains('*') || pattern.contains('?') {
        return glob_match(pattern, actual);
    }
    actual == pattern
}

fn directory_matches(
    actual: Option<crate::pathname::PathnameDirectory>,
    pattern: Option<crate::pathname::PathnameDirectory>,
) -> bool {
    let Some(pattern) = pattern else {
        return actual
            .as_ref()
            .map(|d| d.components.is_empty())
            .unwrap_or(true);
    };
    let Some(actual) = actual else {
        return false;
    };
    if pattern.absolute != actual.absolute {
        return false;
    }

    let pcomps = pattern.components;
    let acomps = actual.components;

    if let Some(idx) = pcomps
        .iter()
        .position(|c| c.eq_ignore_ascii_case("WILD-INFERIORS"))
    {
        for (a, p) in acomps.iter().zip(pcomps.iter().take(idx)) {
            if !component_matches(a, p) {
                return false;
            }
        }
        let suffix = &pcomps[idx + 1..];
        if suffix.is_empty() {
            return true;
        }
        if acomps.len() < idx + suffix.len() {
            return false;
        }
        let start = acomps.len() - suffix.len();
        for (a, p) in acomps[start..].iter().zip(suffix.iter()) {
            if !component_matches(a, p) {
                return false;
            }
        }
        return true;
    }

    if acomps.len() != pcomps.len() {
        return false;
    }
    for (a, p) in acomps.iter().zip(pcomps.iter()) {
        if !component_matches(a, p) {
            return false;
        }
    }
    true
}

fn string_from_designator(
    proc: &Process,
    ctx: &crate::context::GlobalContext,
    node: NodeId,
) -> Option<String> {
    match proc.arena.inner.get_unchecked(node) {
        Node::Leaf(OpaqueValue::String(s)) => Some(s.clone()),
        Node::Leaf(OpaqueValue::Pathname(p)) => Some(p.namestring().to_string()),
        Node::Leaf(OpaqueValue::Char(c)) => Some(c.to_string()),
        Node::Leaf(OpaqueValue::Integer(_)) => node_to_char(proc, ctx, node).map(|c| c.to_string()),
        Node::Leaf(OpaqueValue::Symbol(id)) => ctx
            .symbols
            .read()
            .unwrap()
            .symbol_name(SymbolId(*id))
            .map(|s| s.to_string()),
        Node::Leaf(OpaqueValue::VectorHandle(id)) => {
            let arr = proc.arrays.get(crate::arrays::VectorId(*id))?;
            if !arr.element_type.is_character() {
                return None;
            }
            let mut out = String::new();
            for item in arr.elements_for_sequence() {
                let ch = node_to_char(proc, ctx, item)?;
                out.push(ch);
            }
            Some(out)
        }
        _ => None,
    }
}

fn string_from_sequence(
    proc: &Process,
    ctx: &crate::context::GlobalContext,
    node: NodeId,
) -> Option<String> {
    if let Some(s) = string_from_designator(proc, ctx, node) {
        return Some(s);
    }

    match proc.arena.inner.get_unchecked(node) {
        Node::Leaf(OpaqueValue::VectorHandle(id)) => {
            let arr = proc.arrays.get(crate::arrays::VectorId(*id))?;
            if !arr.element_type.is_character() {
                return None;
            }
            let mut out = String::new();
            for item in arr.elements_for_sequence() {
                let ch = node_to_char(proc, ctx, item)?;
                out.push(ch);
            }
            Some(out)
        }
        Node::Fork(_, _) => {
            let items = list_to_vec_opt(proc, node)?;
            let mut out = String::new();
            for item in items {
                let ch = node_to_char(proc, ctx, item)?;
                out.push(ch);
            }
            Some(out)
        }
        _ => None,
    }
}

fn current_package_id(
    proc: &Process,
    ctx: &crate::context::GlobalContext,
) -> crate::symbol::PackageId {
    if let Some(val) = proc.get_value(ctx.package_sym) {
        if let Node::Leaf(OpaqueValue::Package(id)) = proc.arena.inner.get_unchecked(val) {
            return crate::symbol::PackageId(*id);
        }
    }
    ctx.symbols.read().unwrap().current_package()
}

fn package_id_from_designator_opt(
    proc: &Process,
    ctx: &crate::context::GlobalContext,
    node: NodeId,
) -> Option<crate::symbol::PackageId> {
    match proc.arena.inner.get_unchecked(node) {
        Node::Leaf(OpaqueValue::Package(id)) => Some(crate::symbol::PackageId(*id)),
        Node::Leaf(OpaqueValue::Symbol(id)) => ctx
            .symbols
            .read()
            .unwrap()
            .symbol_name(SymbolId(*id))
            .and_then(|name| ctx.symbols.read().unwrap().find_package(name)),
        Node::Leaf(OpaqueValue::String(s)) => ctx.symbols.read().unwrap().find_package(s),
        Node::Leaf(OpaqueValue::Char(c)) => ctx
            .symbols
            .read()
            .unwrap()
            .find_package(&c.to_string()),
        Node::Leaf(OpaqueValue::Integer(_)) => {
            node_to_char(proc, ctx, node)
                .and_then(|c| ctx.symbols.read().unwrap().find_package(&c.to_string()))
        }
        Node::Leaf(OpaqueValue::VectorHandle(_)) => {
            let s = string_from_sequence(proc, ctx, node)?;
            ctx.symbols.read().unwrap().find_package(&s)
        }
        _ => None,
    }
}

fn package_id_from_designator(
    proc: &Process,
    ctx: &crate::context::GlobalContext,
    node: NodeId,
) -> Result<crate::symbol::PackageId, ControlSignal> {
    package_id_from_designator_opt(proc, ctx, node)
        .ok_or_else(|| ControlSignal::Error("Invalid package designator".into()))
}

/// Registry of primitive functions
pub struct Primitives {
    functions: HashMap<SymbolId, PrimitiveFn>,
}

impl Primitives {
    pub fn new() -> Self {
        Self {
            functions: HashMap::default(),
        }
    }

    pub fn register(&mut self, sym: SymbolId, func: PrimitiveFn) {
        self.functions.insert(sym, func);
    }

    pub fn get(&self, sym: SymbolId) -> Option<PrimitiveFn> {
        self.functions.get(&sym).copied()
    }
}

/// Register all standard primitives
pub fn register_primitives(globals: &mut crate::context::GlobalContext) {
    let cl = PackageId(1);

    // Arithmetic
    globals.register_primitive("+", cl, prim_add);
    globals.register_primitive("-", cl, prim_sub);
    globals.register_primitive("*", cl, prim_mul);
    globals.register_primitive("/", cl, prim_div);
    globals.register_primitive("1+", cl, prim_1plus);
    globals.register_primitive("1-", cl, prim_1minus);
    globals.register_primitive("MOD", cl, prim_mod);

    // Comparison
    globals.register_primitive("=", cl, prim_num_eq);
    globals.register_primitive("<", cl, prim_lt);
    globals.register_primitive(">", cl, prim_gt);
    globals.register_primitive("<=", cl, prim_le);
    globals.register_primitive(">=", cl, prim_ge);

    // List operations
    globals.register_primitive("CONS", cl, prim_cons);
    globals.register_primitive("CAR", cl, prim_car);
    globals.register_primitive("CDR", cl, prim_cdr);
    globals.register_primitive("LIST", cl, prim_list);
    globals.register_primitive("LENGTH", cl, prim_length);
    globals.register_primitive("APPEND", cl, prim_append);
    globals.register_primitive("REVERSE", cl, prim_reverse);
    globals.register_primitive("NTH", cl, prim_nth);
    globals.register_primitive("RPLACA", cl, prim_rplaca);
    globals.register_primitive("RPLACD", cl, prim_rplacd);
    globals.register_primitive("VALUES", cl, prim_values);
    globals.register_primitive("VALUES-LIST", cl, prim_values_list);

    // Predicates
    globals.register_primitive("NULL", cl, prim_null);
    globals.register_primitive("ATOM", cl, prim_atom);
    globals.register_primitive("CONSP", cl, prim_consp);
    globals.register_primitive("LISTP", cl, prim_listp);
    globals.register_primitive("NUMBERP", cl, prim_numberp);
    globals.register_primitive("CHARACTERP", cl, prim_characterp);
    globals.register_primitive("STRINGP", cl, prim_stringp);
    globals.register_primitive("CHARACTER", cl, prim_character);
    globals.register_primitive("CHAR-CODE", cl, prim_char_code);
    globals.register_primitive("CODE-CHAR", cl, prim_code_char);
    globals.register_primitive("CHAR-NAME", cl, prim_char_name);
    globals.register_primitive("NAME-CHAR", cl, prim_name_char);
    globals.register_primitive("CHAR-UPCASE", cl, prim_char_upcase);
    globals.register_primitive("CHAR-DOWNCASE", cl, prim_char_downcase);
    globals.register_primitive("UPPER-CASE-P", cl, prim_upper_case_p);
    globals.register_primitive("LOWER-CASE-P", cl, prim_lower_case_p);
    globals.register_primitive("BOTH-CASE-P", cl, prim_both_case_p);
    globals.register_primitive("ALPHANUMERICP", cl, prim_alphanumericp);
    globals.register_primitive("DIGIT-CHAR", cl, prim_digit_char);
    globals.register_primitive("DIGIT-CHAR-P", cl, prim_digit_char_p);
    globals.register_primitive("SYMBOLP", cl, prim_symbolp);
    globals.register_primitive("FUNCTIONP", cl, prim_functionp);
    globals.register_primitive("EQ", cl, prim_eq);
    globals.register_primitive("EQL", cl, prim_eql);
    globals.register_primitive("EQUAL", cl, prim_equal);
    globals.register_primitive("TYPEP", cl, prim_typep);
    globals.register_primitive("SYMBOL-VALUE", cl, prim_symbol_value);
    globals.register_primitive("ASSOC", cl, prim_assoc);
    globals.register_primitive("RASSOC", cl, prim_rassoc);
    globals.register_primitive("GENSYM", cl, prim_gensym);
    globals.register_primitive("GENTEMP", cl, prim_gentemp);
    globals.register_primitive("MAKE-SYMBOL", cl, prim_make_symbol);
    globals.register_primitive("INTERN", cl, prim_intern);
    globals.register_primitive("FIND-SYMBOL", cl, prim_find_symbol);
    globals.register_primitive("FIND-ALL-SYMBOLS", cl, prim_find_all_symbols);
    globals.register_primitive("EXPORT", cl, prim_export);
    globals.register_primitive("UNEXPORT", cl, prim_unexport);
    globals.register_primitive("IMPORT", cl, prim_import);
    globals.register_primitive("SHADOW", cl, prim_shadow);
    globals.register_primitive("SHADOWING-IMPORT", cl, prim_shadowing_import);
    globals.register_primitive("UNINTERN", cl, prim_unintern);
    globals.register_primitive("USE-PACKAGE", cl, prim_use_package);
    globals.register_primitive("UNUSE-PACKAGE", cl, prim_unuse_package);
    globals.register_primitive("MAKE-PACKAGE", cl, prim_make_package);
    globals.register_primitive("DELETE-PACKAGE", cl, prim_delete_package);
    globals.register_primitive("RENAME-PACKAGE", cl, prim_rename_package);
    globals.register_primitive("PACKAGEP", cl, prim_packagep);
    globals.register_primitive("PACKAGE-NICKNAMES", cl, prim_package_nicknames);
    globals.register_primitive("PACKAGE-USE-LIST", cl, prim_package_use_list);
    globals.register_primitive("PACKAGE-USED-BY-LIST", cl, prim_package_used_by_list);
    globals.register_primitive("PACKAGE-SHADOWING-SYMBOLS", cl, prim_package_shadowing_symbols);
    globals.register_primitive("SYS-DEFPACKAGE", cl, prim_sys_defpackage);
    globals.register_primitive(
        "SYS-PACKAGE-ITERATOR-ENTRIES",
        cl,
        prim_sys_package_iterator_entries,
    );

    // Logic
    globals.register_primitive("NOT", cl, prim_not);

    // I/O
    globals.register_primitive("PRINT", cl, prim_print);
    globals.register_primitive("PRINC", cl, prim_princ);
    globals.register_primitive("TERPRI", cl, prim_terpri);
    globals.register_primitive("FORMAT", cl, prim_format);
    globals.register_primitive("READ", cl, prim_read);
    globals.register_primitive(
        "READ-PRESERVING-WHITESPACE",
        cl,
        prim_read_preserving_whitespace,
    );
    globals.register_primitive("READ-FROM-STRING", cl, prim_read_from_string);
    globals.register_primitive("READ-DELIMITED-LIST", cl, prim_read_delimited_list);
    globals.register_primitive("READ-CHAR", cl, prim_read_char);
    globals.register_primitive("UNREAD-CHAR", cl, prim_unread_char);
    globals.register_primitive("READ-LINE", cl, prim_read_line);

    // Strings & Characters
    globals.register_primitive("STRING", cl, prim_string);
    globals.register_primitive("STRING=", cl, prim_string_eq);
    globals.register_primitive("STRING-UPCASE", cl, prim_string_upcase);
    globals.register_primitive("STRING-DOWNCASE", cl, prim_string_downcase);
    globals.register_primitive("STRING-CAPITALIZE", cl, prim_string_capitalize);
    globals.register_primitive("STRING-TRIM", cl, prim_string_trim);
    globals.register_primitive("MAKE-STRING", cl, prim_make_string);
    globals.register_primitive("CONCATENATE", cl, prim_concatenate);
    globals.register_primitive("COERCE", cl, prim_coerce);
    globals.register_primitive("SUBSEQ", cl, prim_subseq);

    // Arrays
    globals.register_primitive("ARRAYP", cl, prim_arrayp);
    globals.register_primitive("VECTORP", cl, prim_vectorp);
    globals.register_primitive("SIMPLE-VECTOR-P", cl, prim_simple_vector_p);
    globals.register_primitive("SIMPLE-BIT-VECTOR-P", cl, prim_simple_bit_vector_p);
    globals.register_primitive("ARRAY-RANK", cl, prim_array_rank);
    globals.register_primitive("ARRAY-DIMENSIONS", cl, prim_array_dimensions);
    globals.register_primitive("ARRAY-TOTAL-SIZE", cl, prim_array_total_size);
    globals.register_primitive("ARRAY-HAS-FILL-POINTER-P", cl, prim_array_has_fill_pointer_p);
    globals.register_primitive("ARRAY-ELEMENT-TYPE", cl, prim_array_element_type);
    globals.register_primitive(
        "UPGRADED-ARRAY-ELEMENT-TYPE",
        cl,
        prim_upgraded_array_element_type,
    );
    globals.register_primitive("ROW-MAJOR-AREF", cl, prim_row_major_aref);
    globals.register_primitive("COMPLEX", cl, prim_complex);
    globals.register_primitive("SYS-MAKE-STRUCT", cl, prim_sys_make_struct);
    globals.register_primitive("SYS-STRUCT-REF", cl, prim_sys_struct_ref);
    globals.register_primitive("SYS-STRUCT-P", cl, prim_sys_struct_p);

    // Hash Tables
    globals.register_primitive("MAKE-HASH-TABLE", cl, prim_make_hash_table);
    globals.register_primitive("GETHASH", cl, prim_gethash);
    globals.register_primitive("SET-GETHASH", cl, prim_set_gethash);
    globals.register_primitive("REMHASH", cl, prim_remhash);
    globals.register_primitive("CLRHASH", cl, prim_clrhash);
    globals.register_primitive("MAPHASH", cl, prim_maphash);

    // CLOS
    globals.register_primitive("FIND-CLASS", cl, prim_find_class);
    globals.register_primitive("MAKE-INSTANCE", cl, prim_make_instance);
    globals.register_primitive("CLASS-OF", cl, prim_class_of);
    globals.register_primitive("SLOT-VALUE", cl, prim_slot_value);
    globals.register_primitive("SET-SLOT-VALUE", cl, prim_set_slot_value);
    globals.register_primitive("SLOT-BOUNDP", cl, prim_slot_boundp);
    globals.register_primitive("SLOT-EXISTS-P", cl, prim_slot_exists_p);
    globals.register_primitive("SLOT-MAKUNBOUND", cl, prim_slot_makunbound);
    globals.register_primitive("SLOT-VALUE-USING-CLASS", cl, prim_slot_value_using_class);
    globals.register_primitive(
        "SET-SLOT-VALUE-USING-CLASS",
        cl,
        prim_set_slot_value_using_class,
    );
    globals.register_primitive("SLOT-BOUNDP-USING-CLASS", cl, prim_slot_boundp_using_class);
    globals.register_primitive(
        "SLOT-MAKUNBOUND-USING-CLASS",
        cl,
        prim_slot_makunbound_using_class,
    );
    globals.register_primitive(
        "SLOT-EXISTS-P-USING-CLASS",
        cl,
        prim_slot_exists_p_using_class,
    );
    globals.register_primitive("ENSURE-CLASS", cl, prim_ensure_class);
    globals.register_primitive("SYS-ENSURE-CLASS", cl, prim_ensure_class);
    globals.register_primitive(
        "ENSURE-CLASS-USING-CLASS",
        cl,
        prim_ensure_class_using_class,
    );
    globals.register_primitive("VALIDATE-SUPERCLASS", cl, prim_validate_superclass);
    globals.register_primitive("CHANGE-CLASS", cl, prim_change_class);
    globals.register_primitive(
        "UPDATE-INSTANCE-FOR-REDEFINED-CLASS",
        cl,
        prim_update_instance_for_redefined_class,
    );
    globals.register_primitive("REINITIALIZE-INSTANCE", cl, prim_reinitialize_instance);
    globals.register_primitive("ENSURE-GENERIC-FUNCTION", cl, prim_ensure_generic_function);
    globals.register_primitive(
        "ENSURE-GENERIC-FUNCTION-USING-CLASS",
        cl,
        prim_ensure_generic_function_using_class,
    );
    globals.register_primitive(
        "SET-FUNCALLABLE-INSTANCE-FUNCTION",
        cl,
        prim_set_funcallable_instance_function,
    );
    globals.register_primitive(
        "FUNCALLABLE-STANDARD-INSTANCE-ACCESS",
        cl,
        prim_funcallable_standard_instance_access,
    );
    globals.register_primitive(
        "SET-FUNCALLABLE-STANDARD-INSTANCE-ACCESS",
        cl,
        prim_set_funcallable_standard_instance_access,
    );
    globals.register_primitive("ENSURE-METHOD", cl, prim_ensure_method);
    globals.register_primitive(
        "REGISTER-METHOD-COMBINATION",
        cl,
        prim_register_method_combination,
    );
    globals.register_primitive("METHOD-QUALIFIERS", cl, prim_method_qualifiers);
    globals.register_primitive("METHOD-SPECIALIZERS", cl, prim_method_specializers);
    globals.register_primitive("METHOD-LAMBDA-LIST", cl, prim_method_lambda_list);
    globals.register_primitive("METHOD-GENERIC-FUNCTION", cl, prim_method_generic_function);
    globals.register_primitive("METHOD-BODY", cl, prim_method_body);
    globals.register_primitive("INTERN-EQL-SPECIALIZER", cl, prim_intern_eql_specializer);
    globals.register_primitive(
        "SYS-EQL-SPECIALIZER-OBJECT",
        cl,
        prim_sys_eql_specializer_object,
    );
    globals.register_primitive("SYS-MAKE-METHOD", cl, prim_sys_make_method);
    globals.register_primitive("CLASS-NAME", cl, prim_class_name);
    globals.register_primitive(
        "CLASS-DIRECT-SUPERCLASSES",
        cl,
        prim_class_direct_superclasses,
    );
    globals.register_primitive(
        "CLASS-DIRECT-SUBCLASSES",
        cl,
        prim_class_direct_subclasses,
    );
    globals.register_primitive("CLASS-DIRECT-SLOTS", cl, prim_class_direct_slots);
    globals.register_primitive("CLASS-SLOTS", cl, prim_class_slots);
    globals.register_primitive(
        "SYS-CLASS-DIRECT-METHODS",
        cl,
        prim_sys_class_direct_methods,
    );
    globals.register_primitive(
        "SYS-CLASS-DIRECT-GENERIC-FUNCTIONS",
        cl,
        prim_sys_class_direct_generic_functions,
    );
    globals.register_primitive(
        "SYS-SPECIALIZER-DIRECT-METHODS",
        cl,
        prim_sys_specializer_direct_methods,
    );
    globals.register_primitive(
        "SYS-SPECIALIZER-DIRECT-GENERIC-FUNCTIONS",
        cl,
        prim_sys_specializer_direct_generic_functions,
    );
    globals.register_primitive("CLASS-PRECEDENCE-LIST", cl, prim_class_precedence_list);
    globals.register_primitive("CLASS-FINALIZED-P", cl, prim_class_finalized_p);
    globals.register_primitive("CLASS-PROTOTYPE", cl, prim_class_prototype);
    globals.register_primitive(
        "CLASS-DIRECT-DEFAULT-INITARGS",
        cl,
        prim_class_direct_default_initargs,
    );
    globals.register_primitive("CLASS-DEFAULT-INITARGS", cl, prim_class_default_initargs);
    globals.register_primitive("FINALIZE-INHERITANCE", cl, prim_finalize_inheritance);
    globals.register_primitive("SYS-FINALIZE-INHERITANCE", cl, prim_finalize_inheritance);
    globals.register_primitive("SYS-CHANGE-CLASS", cl, prim_change_class);
    globals.register_primitive(
        "SYS-UPDATE-INSTANCE-FOR-REDEFINED-CLASS",
        cl,
        prim_update_instance_for_redefined_class,
    );
    globals.register_primitive("SYS-REINITIALIZE-INSTANCE", cl, prim_reinitialize_instance);
    globals.register_primitive("SYS-ADD-DEPENDENT", cl, prim_sys_add_dependent);
    globals.register_primitive("SYS-REMOVE-DEPENDENT", cl, prim_sys_remove_dependent);
    globals.register_primitive("SYS-MAP-DEPENDENTS", cl, prim_sys_map_dependents);
    globals.register_primitive(
        "COMPUTE-CLASS-PRECEDENCE-LIST",
        cl,
        prim_compute_class_precedence_list,
    );
    globals.register_primitive("COMPUTE-SLOTS", cl, prim_compute_slots);
    globals.register_primitive(
        "COMPUTE-EFFECTIVE-SLOT-DEFINITION",
        cl,
        prim_compute_effective_slot_definition,
    );
    globals.register_primitive(
        "GENERIC-FUNCTION-NAME",
        cl,
        prim_generic_function_name,
    );
    globals.register_primitive(
        "GENERIC-FUNCTION-LAMBDA-LIST",
        cl,
        prim_generic_function_lambda_list,
    );
    globals.register_primitive(
        "GENERIC-FUNCTION-METHODS",
        cl,
        prim_generic_function_methods,
    );
    globals.register_primitive(
        "GENERIC-FUNCTION-METHOD-COMBINATION",
        cl,
        prim_generic_function_method_combination,
    );
    globals.register_primitive(
        "SYS-GENERIC-FUNCTION-ARGUMENT-PRECEDENCE-ORDER",
        cl,
        prim_sys_generic_function_argument_precedence_order,
    );
    globals.register_primitive("SYS-DISPATCH-GENERIC", cl, prim_sys_dispatch_generic);
    globals.register_primitive(
        "SYS-APPLY-EFFECTIVE-METHOD",
        cl,
        prim_sys_apply_effective_method,
    );
    globals.register_primitive("SLOT-DEFINITION-NAME", cl, prim_slot_definition_name);
    globals.register_primitive("SLOT-DEFINITION-INITFORM", cl, prim_slot_definition_initform);
    globals.register_primitive(
        "SLOT-DEFINITION-INITFUNCTION",
        cl,
        prim_slot_definition_initfunction,
    );
    globals.register_primitive("SLOT-DEFINITION-INITARGS", cl, prim_slot_definition_initargs);
    globals.register_primitive("SLOT-DEFINITION-READERS", cl, prim_slot_definition_readers);
    globals.register_primitive("SLOT-DEFINITION-WRITERS", cl, prim_slot_definition_writers);
    globals.register_primitive(
        "SLOT-DEFINITION-ALLOCATION",
        cl,
        prim_slot_definition_allocation,
    );
    globals.register_primitive("SLOT-DEFINITION-TYPE", cl, prim_slot_definition_type);
    globals.register_primitive("SLOT-DEFINITION-LOCATION", cl, prim_slot_definition_location);
    globals.register_primitive(
        "SYS-MAKE-DIRECT-SLOT-DEFINITION",
        cl,
        prim_make_direct_slot_definition,
    );
    globals.register_primitive(
        "SYS-MAKE-EFFECTIVE-SLOT-DEFINITION",
        cl,
        prim_make_effective_slot_definition,
    );
    globals.register_primitive("COMPUTE-APPLICABLE-METHODS", cl, prim_compute_applicable_methods);
    globals.register_primitive(
        "COMPUTE-APPLICABLE-METHODS-USING-CLASSES",
        cl,
        prim_compute_applicable_methods_using_classes,
    );
    globals.register_primitive("FIND-METHOD", cl, prim_find_method);

    // Error handling
    globals.register_primitive("ERROR", cl, prim_error);

    // System
    globals.register_primitive("GC", cl, prim_gc);
    globals.register_primitive("ROOM", cl, prim_room);
    globals.register_primitive(
        "LOAD-AND-COMPILE-MINIMAL",
        cl,
        prim_load_and_compile_minimal,
    );

    // Arrays
    globals.register_primitive("MAKE-ARRAY", cl, prim_make_array);
    globals.register_primitive("AREF", cl, prim_aref);
    globals.register_primitive("SET-AREF", cl, prim_set_aref);

    // Readtable
    globals.register_primitive("SET-MACRO-CHARACTER", cl, prim_set_macro_character);
    globals.register_primitive("GET-MACRO-CHARACTER", cl, prim_get_macro_character);
    globals.register_primitive("SET-SYNTAX-FROM-CHAR", cl, prim_set_syntax_from_char);
    globals.register_primitive("READTABLEP", cl, prim_readtablep);
    globals.register_primitive("COPY-READTABLE", cl, prim_copy_readtable);
    globals.register_primitive("READTABLE-CASE", cl, prim_readtable_case);
    globals.register_primitive("SET-READTABLE-CASE", cl, prim_set_readtable_case);
    globals.register_primitive(
        "MAKE-DISPATCH-MACRO-CHARACTER",
        cl,
        prim_make_dispatch_macro_character,
    );
    globals.register_primitive(
        "SET-DISPATCH-MACRO-CHARACTER",
        cl,
        prim_set_dispatch_macro_character,
    );
    globals.register_primitive(
        "GET-DISPATCH-MACRO-CHARACTER",
        cl,
        prim_get_dispatch_macro_character,
    );

    // Tools
    globals.register_primitive("COMPILE", cl, prim_compile);
    globals.register_primitive("COMPILE-LISP", cl, prim_compile_lisp);
    globals.register_primitive("TREE-STRING", cl, prim_tree_string);
    globals.register_primitive("TREE-TO-DOT", cl, prim_tree_to_dot);
    globals.register_primitive("SAVE-TREE-PDF", cl, prim_save_tree_pdf);
    globals.register_primitive("TREE-TO-PDF", cl, prim_tree_to_pdf);

    // Tree Calculus (pure encoding helpers)
    globals.register_primitive("TC-ENCODE-NAT", cl, prim_tc_encode_nat);
    globals.register_primitive("TC-DECODE-NAT", cl, prim_tc_decode_nat);
    globals.register_primitive("TC-ENCODE-STRING", cl, prim_tc_encode_string);
    globals.register_primitive("TC-DECODE-STRING", cl, prim_tc_decode_string);
    globals.register_primitive("TC-SUCC", cl, prim_tc_succ);
    globals.register_primitive("TC-ADD", cl, prim_tc_add);
    globals.register_primitive("TC-EQUAL", cl, prim_tc_equal);
    globals.register_primitive("TC-TRIAGE", cl, prim_tc_triage);
    globals.register_primitive("FUNCALL", cl, prim_funcall);
    globals.register_primitive("EVAL", cl, prim_eval);
    globals.register_primitive("APPLY", cl, prim_apply);
    globals.register_primitive("SYS-ALLOCATE-INSTANCE", cl, prim_sys_allocate_instance);
    globals.register_primitive("SYS-SHARED-INITIALIZE-PRIM", cl, prim_shared_initialize);
    globals.register_primitive("APROPOS", cl, prim_apropos);

    // Streams
    globals.register_primitive(
        "MAKE-STRING-OUTPUT-STREAM",
        cl,
        prim_make_string_output_stream,
    );
    globals.register_primitive(
        "GET-OUTPUT-STREAM-STRING",
        cl,
        prim_get_output_stream_string,
    );
    globals.register_primitive(
        "MAKE-STRING-INPUT-STREAM",
        cl,
        prim_make_string_input_stream,
    );
    globals.register_primitive("MAKE-TWO-WAY-STREAM", cl, prim_make_two_way_stream);
    globals.register_primitive("MAKE-BROADCAST-STREAM", cl, prim_make_broadcast_stream);
    globals.register_primitive("CLOSE", cl, prim_close);
    globals.register_primitive("WRITE-STRING", cl, prim_write_string);
    globals.register_primitive("WRITE-CHAR", cl, prim_write_char);
    globals.register_primitive("FRESH-LINE", cl, prim_fresh_line);
    globals.register_primitive("SYS-TIME-EVAL", cl, prim_sys_time_eval);

    // Concurrency
    globals.register_primitive("SPAWN", cl, prim_spawn);
    globals.register_primitive("SEND", cl, prim_send);
    globals.register_primitive("RECEIVE", cl, prim_receive);

    globals.register_primitive("SELF", cl, prim_self);
    globals.register_primitive("SLEEP", cl, prim_sleep);

    // File System & Loading
    globals.register_primitive("LOAD", cl, prim_load);
    globals.register_primitive("MAPC", cl, prim_mapc);
    globals.register_primitive("MAKE-PATHNAME", cl, prim_make_pathname);
    globals.register_primitive("PATHNAME-DIRECTORY", cl, prim_pathname_directory);
    globals.register_primitive("PATHNAME-NAME", cl, prim_pathname_name);
    globals.register_primitive("PATHNAME-TYPE", cl, prim_pathname_type);
    globals.register_primitive("PATHNAME-HOST", cl, prim_pathname_host);
    globals.register_primitive("PATHNAME-DEVICE", cl, prim_pathname_device);
    globals.register_primitive("PATHNAME-VERSION", cl, prim_pathname_version);
    globals.register_primitive("PARSE-NAMESTRING", cl, prim_parse_namestring);
    globals.register_primitive("PATHNAME-MATCH-P", cl, prim_pathname_match_p);
    globals.register_primitive("WILD-PATHNAME-P", cl, prim_wild_pathname_p);
    globals.register_primitive("PATHNAMEP", cl, prim_pathnamep);
    globals.register_primitive("DIRECTORY", cl, prim_directory);
    globals.register_primitive("DELETE-FILE", cl, prim_delete_file);
    globals.register_primitive("PROBE-FILE", cl, prim_probe_file);
    globals.register_primitive("RENAME-FILE", cl, prim_rename_file);
    globals.register_primitive("ENSURE-DIRECTORIES-EXIST", cl, prim_ensure_directories_exist);
    globals.register_primitive("FILE-NAMESTRING", cl, prim_file_namestring);
    globals.register_primitive("DIRECTORY-NAMESTRING", cl, prim_directory_namestring);
    globals.register_primitive("TRUENAME", cl, prim_truename);
    globals.register_primitive("COMPILE-FILE-PATHNAME", cl, prim_compile_file_pathname);
    globals.register_primitive("LOGICAL-PATHNAME", cl, prim_logical_pathname);
    globals.register_primitive("TRANSLATE-LOGICAL-PATHNAME", cl, prim_translate_logical_pathname);
    globals.register_primitive("TRANSLATE-PATHNAME", cl, prim_translate_pathname);
    globals.register_primitive(
        "LOGICAL-PATHNAME-TRANSLATIONS",
        cl,
        prim_logical_pathname_translations,
    );
    globals.register_primitive(
        "SET-LOGICAL-PATHNAME-TRANSLATIONS",
        cl,
        prim_set_logical_pathname_translations,
    );
    globals.register_primitive(
        "LOAD-LOGICAL-PATHNAME-TRANSLATIONS",
        cl,
        prim_load_logical_pathname_translations,
    );
    globals.register_primitive("STRING-EQUAL", cl, prim_string_equal);
    globals.register_primitive("ASSERT", cl, prim_assert);

    globals.register_primitive("MERGE-PATHNAMES", cl, prim_merge_pathnames);
    globals.register_primitive("PATHNAME", cl, prim_pathname);
    globals.register_primitive("NAMESTRING", cl, prim_namestring);

    // Symbols
    globals.register_primitive("SYMBOL-NAME", cl, prim_symbol_name);
    globals.register_primitive("SYMBOL-PACKAGE", cl, prim_symbol_package);
    globals.register_primitive("SYMBOL-PLIST", cl, prim_symbol_plist);
    globals.register_primitive("GET", cl, prim_get);
    globals.register_primitive("PUT", cl, prim_put); // Internal use
    globals.register_primitive("REMPROP", cl, prim_remprop);

    globals.register_primitive("BOUNDP", cl, prim_boundp);
    globals.register_primitive("MAKUNBOUND", cl, prim_makunbound);
    globals.register_primitive("SET", cl, prim_set);

    globals.register_primitive("SYMBOL-FUNCTION", cl, prim_symbol_function);
    globals.register_primitive("SET-SYMBOL-FUNCTION", cl, prim_set_symbol_function);
    globals.register_primitive("FBOUNDP", cl, prim_fboundp);
    globals.register_primitive("FMAKUNBOUND", cl, prim_fmakunbound);
    globals.register_primitive("FIND-PACKAGE", cl, prim_find_package);
    globals.register_primitive("IN-PACKAGE", cl, prim_in_package);
    globals.register_primitive("KEYWORDP", cl, prim_keywordp);
    globals.register_primitive("COPY-SYMBOL", cl, prim_copy_symbol);
    globals.register_primitive("PACKAGE-NAME", cl, prim_package_name);
    globals.register_primitive("LIST-ALL-PACKAGES", cl, prim_list_all_packages);
    globals.register_primitive("MACROEXPAND-1", cl, prim_macroexpand_1);
}

// ============================================================================
// File System Primitives
// ============================================================================

fn prim_symbol_name(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Some(sym_id) = node_to_symbol(proc, arg) {
            let name = ctx
                .symbols
                .read()
                .unwrap()
                .symbol_name(sym_id)
                .unwrap_or("NIL")
                .to_string();
            return Ok(proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::String(name))));
        }
    }
    Ok(proc.make_nil())
}

fn prim_symbol_package(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Some(sym_id) = node_to_symbol(proc, arg) {
            let pkg_id = ctx.symbols.read().unwrap().symbol_package(sym_id);

            if let Some(id) = pkg_id {
                if let Some(pkg) = ctx.symbols.read().unwrap().get_package(id) {
                    if !pkg.is_deleted() {
                        return Ok(proc
                            .arena
                            .inner
                            .alloc(Node::Leaf(OpaqueValue::Package(id.0))));
                    }
                }
            }
        }
    }
    Ok(proc.make_nil())
}

fn prim_symbol_plist(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Some(sym_id) = node_to_symbol(proc, arg) {
            // Check process dictionary for plist
            if let Some(binding) = proc.dictionary.get(&sym_id) {
                if let Some(plist) = binding.plist {
                    return Ok(plist);
                }
            }
        }
    }
    Ok(proc.make_nil())
}

fn prim_get(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return err_helper("GET: too few arguments");
    }

    let sym_node = args[0];
    let indicator = args[1];
    let default = if args.len() > 2 {
        args[2]
    } else {
        proc.make_nil()
    };

    if let Some(sym_id) = node_to_symbol(proc, sym_node) {
        if let Some(binding) = proc.dictionary.get(&sym_id) {
            if let Some(plist_id) = binding.plist {
                // Traverse plist
                let mut current = plist_id;
                loop {
                    match proc.arena.inner.get_unchecked(current) {
                        Node::Fork(ind_node, rest1) => {
                            // Check indicator
                            if crate::arena::deep_equal(&proc.arena.inner, indicator, *ind_node) {
                                // Found! Get value
                                match proc.arena.inner.get_unchecked(*rest1) {
                                    Node::Fork(val_node, _) => return Ok(*val_node),
                                    _ => return Ok(proc.make_nil()), // Malformed
                                }
                            }
                            // Advance (skip value)
                            match proc.arena.inner.get_unchecked(*rest1) {
                                Node::Fork(_, rest2) => current = *rest2,
                                _ => break,
                            }
                        }
                        _ => break,
                    }
                }
            }
        }
    }

    Ok(default)
}

fn prim_put(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 3 {
        return err_helper("PUT: too few arguments");
    }

    let sym_node = args[0];
    let indicator = args[1];
    let value = args[2];

    if let Some(sym_id) = node_to_symbol(proc, sym_node) {
        // Read-Modify-Write
        let mut new_plist_nodes = Vec::new();
        let mut found = false;

        let binding = proc.dictionary.entry(sym_id).or_default();
        if let Some(plist_id) = binding.plist {
            let mut current = plist_id;
            loop {
                match proc.arena.inner.get_unchecked(current) {
                    Node::Fork(ind_node, rest1) => {
                        if !found
                            && crate::arena::deep_equal(&proc.arena.inner, indicator, *ind_node)
                        {
                            found = true;
                            // Replace value
                            new_plist_nodes.push(*ind_node);
                            new_plist_nodes.push(value);

                            // Skip old value
                            match proc.arena.inner.get_unchecked(*rest1) {
                                Node::Fork(_, rest2) => current = *rest2,
                                _ => break,
                            }
                        } else {
                            // Copy pair
                            new_plist_nodes.push(*ind_node);
                            match proc.arena.inner.get_unchecked(*rest1) {
                                Node::Fork(val_node, rest2) => {
                                    new_plist_nodes.push(*val_node);
                                    current = *rest2;
                                }
                                _ => break, // Malformed
                            }
                        }
                    }
                    _ => break,
                }
            }
        }

        if !found {
            // Append new pair
            new_plist_nodes.push(indicator);
            new_plist_nodes.push(value);
        }

        let new_plist = proc.make_list(&new_plist_nodes);
        proc.dictionary.entry(sym_id).or_default().plist = Some(new_plist);
        return Ok(value);
    }

    Ok(proc.make_nil())
}

fn prim_remprop(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return err_helper("REMPROP: too few arguments");
    }

    let sym_node = args[0];
    let indicator = args[1];

    if let Some(sym_id) = node_to_symbol(proc, sym_node) {
        // We need to mutate the plist.
        // Read-Modify-Write
        let mut new_plist_nodes = Vec::new();
        let mut found = false;

        if let Some(binding) = proc.dictionary.get(&sym_id) {
            if let Some(plist_id) = binding.plist {
                let mut current = plist_id;
                loop {
                    match proc.arena.inner.get_unchecked(current) {
                        Node::Fork(ind_node, rest1) => {
                            if !found
                                && crate::arena::deep_equal(&proc.arena.inner, indicator, *ind_node)
                            {
                                found = true;
                                // Skip this pair
                                match proc.arena.inner.get_unchecked(*rest1) {
                                    Node::Fork(_, rest2) => current = *rest2,
                                    _ => break,
                                }
                            } else {
                                // Copy pair
                                new_plist_nodes.push(*ind_node);
                                match proc.arena.inner.get_unchecked(*rest1) {
                                    Node::Fork(val_node, rest2) => {
                                        new_plist_nodes.push(*val_node);
                                        current = *rest2;
                                    }
                                    _ => break, // Malformed
                                }
                            }
                        }
                        _ => break,
                    }
                }
            }
        }

        if found {
            let new_plist = proc.make_list(&new_plist_nodes);
            proc.dictionary.entry(sym_id).or_default().plist = Some(new_plist);
            return Ok(proc.make_t(ctx));
        }
    }

    Ok(proc.make_nil())
}

fn prim_boundp(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Some(sym_id) = node_to_symbol(proc, arg) {
            if sym_id == ctx.t_sym || sym_id == ctx.nil_sym {
                return Ok(proc.make_t(ctx));
            }
            if let Some(sym) = ctx.symbols.read().unwrap().get_symbol(sym_id) {
                if sym.is_keyword() {
                    return Ok(proc.make_t(ctx));
                }
            }
            if let Some(binding) = proc.dictionary.get(&sym_id) {
                if binding.value.is_some() {
                    return Ok(proc.make_t(ctx));
                }
            }
        }
    }
    Ok(proc.make_nil())
}

fn prim_makunbound(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Some(sym_id) = node_to_symbol(proc, arg) {
            proc.unbind_value(sym_id);
            return Ok(arg);
        }
    }
    // Should error if not symbol?
    Ok(proc.make_nil())
}

fn prim_set(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return err_helper("SET: too few arguments");
    }
    let sym_node = args[0];
    let val_node = args[1];

    if let Some(sym_id) = node_to_symbol(proc, sym_node) {
        proc.set_value(sym_id, val_node);
        if sym_id == ctx.package_sym {
            if let Some(pkg_id) = package_id_from_designator_opt(proc, ctx, val_node) {
                ctx.symbols.write().unwrap().set_current_package(pkg_id);
            }
        }
        Ok(val_node)
    } else {
        err_helper("SET: first argument must be a symbol")
    }
}

fn prim_symbol_function(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Some(sym_id) = node_to_symbol(proc, arg) {
            if let Some(func) = proc.get_function(sym_id) {
                return Ok(func);
            } else if ctx.primitives.contains_key(&sym_id) {
                // For now, return the symbol itself as a placeholder for primitive?
                // Or error nicely.
                // Ideally we return a wrapped primitive.
                // Let's return the symbol, assuming caller knows?
                // No, usually (funcall (symbol-function 'car) ...) works.
                // Eval applies symbol by looking up.
                // So returning symbol works for funcall.
                return Ok(arg);
            } else {
                return err_helper(&format!("Undefined function: {:?}", sym_id));
            }
        }
        if let Some(sym_id) = setf_function_name_from_node(proc, arg) {
            if let Some(func) = proc.get_setf_function(sym_id) {
                return Ok(func);
            }
            if let Some(gid) = proc.mop.find_setf_generic(sym_id) {
                return Ok(proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Generic(gid.0))));
            }
            return err_helper("Undefined SETF function");
        }
    }
    err_helper("SYMBOL-FUNCTION: invalid argument")
}

fn prim_fboundp(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Some(sym_id) = node_to_symbol(proc, arg) {
            if proc.get_function(sym_id).is_some()
                || proc.macros.contains_key(&sym_id)
                || ctx.primitives.contains_key(&sym_id)
            {
                return Ok(proc.make_t(ctx));
            }
        } else if let Some(sym_id) = setf_function_name_from_node(proc, arg) {
            if proc.get_setf_function(sym_id).is_some()
                || proc.mop.find_setf_generic(sym_id).is_some()
            {
                return Ok(proc.make_t(ctx));
            }
        }
    }
    Ok(proc.make_nil())
}

fn prim_fmakunbound(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Some(sym_id) = node_to_symbol(proc, arg) {
            if let Some(binding) = proc.dictionary.get_mut(&sym_id) {
                binding.function = None;
            }
            return Ok(arg);
        } else if let Some(sym_id) = setf_function_name_from_node(proc, arg) {
            proc.clear_setf_function(sym_id);
            return Ok(arg);
        }
    }
    Ok(proc.make_nil())
}

fn prim_find_package(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if matches!(proc.arena.inner.get_unchecked(arg), Node::Leaf(OpaqueValue::Package(_))) {
            return Ok(arg);
        }
        if let Some(pkg_id) = package_id_from_designator_opt(proc, ctx, arg) {
            return Ok(proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Package(pkg_id.0))));
        }
    }
    Ok(proc.make_nil())
}

fn prim_keywordp(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Some(sym_id) = node_to_symbol(proc, arg) {
            if let Some(sym) = ctx.symbols.read().unwrap().get_symbol(sym_id) {
                if sym.is_keyword() {
                    return Ok(proc.make_t(ctx));
                }
            }
        }
    }
    Ok(proc.make_nil())
}

fn prim_copy_symbol(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 2 {
        return err_helper("COPY-SYMBOL requires 1 or 2 arguments");
    }

    let sym_id = node_to_symbol(proc, args[0])
        .ok_or_else(|| ControlSignal::Error("COPY-SYMBOL: argument must be a symbol".into()))?;

    let copy_plist = if args.len() == 2 {
        !matches!(proc.arena.inner.get_unchecked(args[1]), Node::Leaf(OpaqueValue::Nil))
    } else {
        false
    };

    let name = _ctx
        .symbols
        .read()
        .unwrap()
        .symbol_name(sym_id)
        .unwrap_or("G")
        .to_string();
    let new_sym_id = _ctx.symbols.write().unwrap().make_symbol(&name);

    if copy_plist {
        let mut new_binding = crate::process::SymbolBindings::default();
        let (plist_opt, value_opt, func_opt) = if let Some(binding) = proc.dictionary.get(&sym_id)
        {
            (binding.plist, binding.value, binding.function)
        } else {
            (None, None, None)
        };

        if let Some(plist) = plist_opt {
            fn copy_list(proc: &mut Process, list: NodeId) -> NodeId {
                match proc.arena.inner.get_unchecked(list).clone() {
                    Node::Leaf(OpaqueValue::Nil) => proc.make_nil(),
                    Node::Fork(car, cdr) => {
                        let tail = copy_list(proc, cdr);
                        proc.arena.inner.alloc(Node::Fork(car, tail))
                    }
                    _ => list,
                }
            }
            new_binding.plist = Some(copy_list(proc, plist));
        }
        if let Some(val) = value_opt {
            new_binding.value = Some(val);
        }
        if let Some(func) = func_opt {
            new_binding.function = Some(func);
        }
        proc.dictionary.insert(new_sym_id, new_binding);
    }

    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(new_sym_id.0))))
}

fn prim_in_package(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "IN-PACKAGE requires exactly 1 argument".to_string(),
        ));
    }

    let pkg_id = package_id_from_designator(proc, ctx, args[0])
        .map_err(|_| ControlSignal::Error("IN-PACKAGE: unknown package".to_string()))?;

    ctx.symbols.write().unwrap().set_current_package(pkg_id);
    let pkg_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Package(pkg_id.0)));
    proc.set_value(ctx.package_sym, pkg_node);
    Ok(pkg_node)
}

fn prim_package_name(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Some(pkg_id) = package_id_from_designator_opt(proc, ctx, arg) {
            if let Some(pkg) = ctx.symbols.read().unwrap().get_package(pkg_id) {
                if !pkg.is_deleted() {
                    return Ok(proc
                        .arena
                        .inner
                        .alloc(Node::Leaf(OpaqueValue::String(pkg.name.clone()))));
                }
            }
        }
    }
    Ok(proc.make_nil())
}

fn prim_list_all_packages(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    _args: &[NodeId],
) -> EvalResult {
    let count = ctx.symbols.read().unwrap().package_count();
    let mut list = proc.make_nil();

    // Iterate backwards to preserve order in list construction if we pushed front,
    // but here order doesn't strictly matter.
    for i in (0..count).rev() {
        let pkg_id = crate::symbol::PackageId(i as u32);
        if let Some(pkg) = ctx.symbols.read().unwrap().get_package(pkg_id) {
            if pkg.is_deleted() {
                continue;
            }
        }
        let pkg_node = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Package(i as u32)));
        list = proc.arena.inner.alloc(Node::Fork(pkg_node, list));
    }

    Ok(list)
}

fn prim_macroexpand_1(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&form) = args.first() {
        // Reuse Interpreter logic?
        // Accessing macros directly
        if let Node::Fork(op, args_node) = proc.arena.inner.get_unchecked(form).clone() {
            if let Some(sym_id) = node_to_symbol(proc, op) {
                if let Some(&macro_idx) = proc.macros.get(&sym_id) {
                    if let Some(closure) = proc.closures.get(macro_idx).cloned() {
                        // We need to invoke the macro.
                        // Since we are in a primitive, we don't have an Interpreter instance handy.
                        // But _apply_macro is on Interpreter.
                        // Re-instantiate a temporary Interpreter?
                        // Interpreter::new(proc, ctx) takes mutable proc.
                        // But we are in a primitive which has `&mut proc`.
                        // So yes, we can create a temporary interpreter.
                        let mut interpreter = Interpreter::new(proc, ctx);
                        let expanded = interpreter._apply_macro(&closure, args_node)?;

                        let t_val = interpreter.process.make_t(ctx);
                        let primary = set_multiple_values(proc, vec![expanded, t_val]);
                        return Ok(primary);
                    }
                }
            }
        }
        // Not a macro form or not a cons
        let nil_val = proc.make_nil();
        let primary = set_multiple_values(proc, vec![form, nil_val]);
        Ok(primary)
    } else {
        err_helper("MACROEXPAND-1: missing argument")
    }
}

fn prim_load(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        let mut filename = path_from_designator(proc, ctx, arg, "LOAD")?;
        filename = translate_logical_path_minimal(proc, &filename)?;

        // If relative with no explicit directory, try default pathname defaults or load pathname.
        if !filename.contains('/') && !filename.contains('\\') {
            let default_sym = {
                let mut symbols = ctx.symbols.write().unwrap();
                let sym = symbols.intern_in(
                    "*DEFAULT-PATHNAME-DEFAULTS*",
                    crate::symbol::PackageId(1),
                );
                symbols.export_symbol(sym);
                sym
            };
            if let Some(base_node) = proc.get_value(default_sym) {
                if let Some(base_str) = string_from_designator(proc, ctx, base_node) {
                    let candidate = std::path::Path::new(&base_str).join(&filename);
                    filename = candidate.to_string_lossy().to_string();
                }
            } else {
                let load_pn_sym = ctx
                    .symbols
                    .write()
                    .unwrap()
                    .intern_in("*LOAD-PATHNAME*", crate::symbol::PackageId(1));
                if let Some(base_node) = proc.get_value(load_pn_sym) {
                    if let Some(base_str) = string_from_designator(proc, ctx, base_node) {
                        if let Some(parent) = std::path::Path::new(&base_str).parent() {
                            let candidate = parent.join(&filename);
                            filename = candidate.to_string_lossy().to_string();
                        }
                    }
                }
            }
        }

        let path = std::path::Path::new(&filename);
        if !path.exists() {
            // Try appending .lisp or .lsp if not found
            let extensions = ["lisp", "lsp", "cl"];
            for ext in extensions {
                let path_ext = std::path::Path::new(&filename).with_extension(ext);
                if path_ext.exists() {
                    let new_arg = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(
                        path_ext.to_string_lossy().to_string(),
                    )));
                    return prim_load(proc, ctx, &[new_arg]);
                }
            }

            return err_helper(&format!("LOAD: file not found: {}", filename));
        }

        let full_path = std::fs::canonicalize(path).unwrap_or(path.to_path_buf());
        let full_path_str = full_path.to_string_lossy().into_owned();

        // Bind *LOAD-PATHNAME* and *LOAD-TRUENAME*
        let (load_pn_sym, load_tn_sym) = {
            let mut symbols = ctx.symbols.write().unwrap();
            let pn = symbols.intern_in("*LOAD-PATHNAME*", crate::symbol::PackageId(1));
            let tn = symbols.intern_in("*LOAD-TRUENAME*", crate::symbol::PackageId(1));
            symbols.export_symbol(pn);
            symbols.export_symbol(tn);
            (pn, tn)
        };

        let old_pn = proc.get_value(load_pn_sym);
        let old_tn = proc.get_value(load_tn_sym);

        let pn_node = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String(filename.clone())));
        let tn_node = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String(full_path_str.clone())));

        proc.set_value(load_pn_sym, pn_node);
        proc.set_value(load_tn_sym, tn_node);

        let load_start = std::time::Instant::now();
        let content = std::fs::read_to_string(path)
            .map_err(|e| ControlSignal::Error(format!("LOAD: io error: {}", e)))?;

        let debug_counters = std::env::var("TREECL_DEBUG_COUNTERS").is_ok();
        let debug_load_file_timing = std::env::var("TREECL_DEBUG_LOAD_FILE_TIMING").is_ok();
        let counters_base = if debug_counters && std::env::var("TREECL_DEBUG_COUNTERS_RESET").is_ok() {
            Some((
                crate::symbol::snapshot_counters(),
                crate::hashtables::snapshot_counters(),
            ))
        } else {
            None
        };

        let debug_load = std::env::var("TREECL_DEBUG_LOAD").is_ok();
        let debug_load_match = std::env::var("TREECL_DEBUG_LOAD_MATCH").ok();
        let debug_load_this_file = if let Some(pattern) = debug_load_match.as_ref() {
            full_path_str.contains(pattern) || filename.contains(pattern)
        } else {
            true
        };
        let debug_load_timing = std::env::var("TREECL_DEBUG_LOAD_TIMING").is_ok();
        let debug_load_timing_this_file = debug_load_timing && debug_load_this_file;

        // Parse and Eval loop
        // We need to use Reader and Interpreter
        let env = crate::eval::Environment::new();

        // Preserve caller state so LOAD doesn't clobber it.
        let saved_program = proc.program;
        let saved_mode = proc.execution_mode.clone();
        let saved_env = proc.current_env.clone();
        let saved_stack = std::mem::take(&mut proc.continuation_stack);
        let saved_pending = proc.pending_redex;
        let saved_next_methods = std::mem::take(&mut proc.next_method_states);

        let eval_result = (|| {
            let mut input = crate::reader::ReaderInput::new(&content);
            // Enable read-time eval for #. while loading
            crate::reader::set_read_eval_context(Some(crate::reader::ReadEvalContext {
                proc_ptr: proc as *mut _,
                globals_ptr: ctx as *const _,
                env_ptr: &env as *const _,
            }));

            let mut form_index: usize = 0;
            loop {
                let form_total_start = std::time::Instant::now();
                let options = build_reader_options(proc, ctx, false);
                let rt_id = current_readtable_id(proc, ctx);
                let readtable = proc
                    .readtable_by_id(rt_id)
                    .expect("readtable missing")
                    .clone();
                let mut symbols_guard = ctx.symbols.write().unwrap();
                let mut reader = crate::reader::Reader::new_with_options_from_input(
                    input,
                    &mut proc.arena.inner,
                    &mut *symbols_guard,
                    &readtable,
                    Some(&mut proc.arrays),
                    options,
                );

                let read_start = std::time::Instant::now();
                let read_result = reader.read();
                let needs_read_eval = reader.read_eval_hit();
                let pos = reader.position();
                let read_elapsed = read_start.elapsed();
                input = reader.into_input();
                drop(symbols_guard);

                let expr = match read_result {
                    Ok(expr) => expr,
                    Err(crate::reader::ReaderError::UnexpectedEof) => break,
                    Err(e) => {
                        return Err(ControlSignal::Error(format!(
                            "LOAD: read error at byte {}: {}",
                            pos, e
                        )));
                    }
                };

                let expr = if needs_read_eval {
                    resolve_read_eval(proc, ctx, &env, expr)?
                } else {
                    expr
                };
                form_index = form_index.saturating_add(1);
                if debug_load_timing_this_file {
                    eprintln!(
                        "LOAD DEBUG TIMING [{} #{} READ]: {:.3}ms at-byte={}",
                        filename,
                        form_index,
                        read_elapsed.as_secs_f64() * 1000.0,
                        pos
                    );
                }
                let mut interpreter = Interpreter::new(proc, ctx);
                if debug_load && debug_load_this_file {
                    let symbols = ctx.symbols.read().unwrap();
                    let printed =
                        crate::printer::print_to_string(&interpreter.process.arena.inner, &symbols, expr);
                    eprintln!("LOAD DEBUG [{} #{}]: {}", filename, form_index, printed);
                }
                let eval_start = std::time::Instant::now();
                interpreter.eval(expr, &env)?;
                if debug_load_timing_this_file {
                    let eval_elapsed = eval_start.elapsed();
                    let total_elapsed = form_total_start.elapsed();
                    eprintln!(
                        "LOAD DEBUG TIMING [{} #{} EVAL]: {:.3}ms total={:.3}ms",
                        filename,
                        form_index,
                        eval_elapsed.as_secs_f64() * 1000.0,
                        total_elapsed.as_secs_f64() * 1000.0
                    );
                }
            }
            Ok::<(), ControlSignal>(())
        })();
        crate::reader::set_read_eval_context(None);

        proc.program = saved_program;
        proc.execution_mode = saved_mode;
        proc.current_env = saved_env;
        proc.continuation_stack = saved_stack;
        proc.pending_redex = saved_pending;
        proc.next_method_states = saved_next_methods;

        eval_result?;

        let elapsed_ns = load_start.elapsed().as_nanos().min(u128::from(u64::MAX)) as u64;
        let elapsed_ms = elapsed_ns as f64 / 1_000_000.0;

        let mut delta = LoadCounters::default();
        delta.loads = 1;
        delta.elapsed_ns = elapsed_ns;

        if debug_counters {
            let sym_now = crate::symbol::snapshot_counters();
            let hash_now = crate::hashtables::snapshot_counters();
            let (sym, hash) = if let Some((sym_base, hash_base)) = counters_base {
                (
                    crate::symbol::SymbolCounters {
                        find_package_calls: sym_now
                            .find_package_calls
                            .saturating_sub(sym_base.find_package_calls),
                        find_package_ns: sym_now
                            .find_package_ns
                            .saturating_sub(sym_base.find_package_ns),
                        find_symbol_calls: sym_now
                            .find_symbol_calls
                            .saturating_sub(sym_base.find_symbol_calls),
                        find_symbol_ns: sym_now
                            .find_symbol_ns
                            .saturating_sub(sym_base.find_symbol_ns),
                        intern_calls: sym_now.intern_calls.saturating_sub(sym_base.intern_calls),
                    },
                    crate::hashtables::HashCounters {
                        get_calls: hash_now.get_calls.saturating_sub(hash_base.get_calls),
                        set_calls: hash_now.set_calls.saturating_sub(hash_base.set_calls),
                        rem_calls: hash_now.rem_calls.saturating_sub(hash_base.rem_calls),
                        clr_calls: hash_now.clr_calls.saturating_sub(hash_base.clr_calls),
                        maphash_calls: hash_now
                            .maphash_calls
                            .saturating_sub(hash_base.maphash_calls),
                    },
                )
            } else {
                (sym_now, hash_now)
            };
            let pkg_ms = sym.find_package_ns as f64 / 1_000_000.0;
            let sym_ms = sym.find_symbol_ns as f64 / 1_000_000.0;
            eprintln!(
                "LOAD COUNTERS [{}]: find_package={} ({:.2}ms) find_symbol={} ({:.2}ms) intern={} gethash={} sethash={} remhash={} clrhash={} maphash={}",
                filename,
                sym.find_package_calls,
                pkg_ms,
                sym.find_symbol_calls,
                sym_ms,
                sym.intern_calls,
                hash.get_calls,
                hash.set_calls,
                hash.rem_calls,
                hash.clr_calls,
                hash.maphash_calls
            );
            delta.find_package_calls = sym.find_package_calls;
            delta.find_package_ns = sym.find_package_ns;
            delta.find_symbol_calls = sym.find_symbol_calls;
            delta.find_symbol_ns = sym.find_symbol_ns;
            delta.intern_calls = sym.intern_calls;
            delta.gethash_calls = hash.get_calls;
            delta.sethash_calls = hash.set_calls;
            delta.remhash_calls = hash.rem_calls;
            delta.clrhash_calls = hash.clr_calls;
            delta.maphash_calls = hash.maphash_calls;
        }

        if debug_load_file_timing {
            eprintln!("LOAD FILE TIMING [{}]: {:.2}ms", filename, elapsed_ms);
        }

        if debug_counters || debug_load_file_timing {
            crate::counters::record_load(&full_path_str, &delta);
        }

        // Restore bindings
        if let Some(v) = old_pn {
            proc.set_value(load_pn_sym, v);
        } else {
            proc.unbind_value(load_pn_sym);
        }
        if let Some(v) = old_tn {
            proc.set_value(load_tn_sym, v);
        } else {
            proc.unbind_value(load_tn_sym);
        }

        Ok(proc.make_t(ctx))
    } else {
        err_helper("LOAD: missing argument")
    }
}

#[derive(Default, Clone)]
struct DirectoryMatchCaptures {
    singles: Vec<String>,
    inferiors: Vec<String>,
}

#[derive(Default, Clone)]
struct PathnameMatchCaptures {
    host: Option<String>,
    device: Option<String>,
    directory: DirectoryMatchCaptures,
    name: Option<String>,
    type_: Option<String>,
    version: Option<String>,
}

fn normalize_logical_host(host: &str) -> String {
    host.trim().trim_end_matches(':').to_uppercase()
}

fn logical_wild_token(text: &str) -> bool {
    text == "*" || text.eq_ignore_ascii_case("WILD")
}

fn logical_wild_inferiors_token(text: &str) -> bool {
    text == "**" || text.eq_ignore_ascii_case("WILD-INFERIORS")
}

fn glob_match_case(pattern: &str, text: &str, case_insensitive: bool) -> bool {
    if case_insensitive {
        glob_match(&pattern.to_uppercase(), &text.to_uppercase())
    } else {
        glob_match(pattern, text)
    }
}

fn match_component_capture(
    actual: Option<&str>,
    pattern: Option<&str>,
    case_insensitive: bool,
) -> Option<Option<String>> {
    let Some(pattern) = pattern else {
        return if actual.is_none() { Some(None) } else { None };
    };

    if logical_wild_token(pattern) {
        return Some(actual.map(|s| s.to_string()));
    }
    if logical_wild_inferiors_token(pattern) {
        return Some(actual.map(|s| s.to_string()));
    }
    let Some(actual) = actual else {
        return None;
    };
    if pattern.contains('*') || pattern.contains('?') {
        return if glob_match_case(pattern, actual, case_insensitive) {
            Some(Some(actual.to_string()))
        } else {
            None
        };
    }

    let matched = if case_insensitive {
        actual.eq_ignore_ascii_case(pattern)
    } else {
        actual == pattern
    };
    if matched {
        Some(None)
    } else {
        None
    }
}

fn match_directory_component(
    actual: &str,
    pattern: &str,
    case_insensitive: bool,
) -> Option<Option<String>> {
    if logical_wild_token(pattern) || logical_wild_inferiors_token(pattern) {
        return Some(Some(actual.to_string()));
    }
    if pattern.contains('*') || pattern.contains('?') {
        return if glob_match_case(pattern, actual, case_insensitive) {
            Some(Some(actual.to_string()))
        } else {
            None
        };
    }
    let matched = if case_insensitive {
        actual.eq_ignore_ascii_case(pattern)
    } else {
        actual == pattern
    };
    if matched {
        Some(None)
    } else {
        None
    }
}

fn match_directory_capture(
    actual: Option<&crate::pathname::PathnameDirectory>,
    pattern: Option<&crate::pathname::PathnameDirectory>,
    case_insensitive: bool,
) -> Option<DirectoryMatchCaptures> {
    let Some(pattern) = pattern else {
        return if actual.is_none() || actual.is_some_and(|d| d.components.is_empty()) {
            Some(DirectoryMatchCaptures::default())
        } else {
            None
        };
    };

    let actual_absolute = actual.map(|d| d.absolute).unwrap_or(false);
    if actual_absolute != pattern.absolute {
        return None;
    }

    let empty = Vec::new();
    let actual_components = actual.map(|d| &d.components).unwrap_or(&empty);
    let pattern_components = &pattern.components;
    let mut captures = DirectoryMatchCaptures::default();

    if let Some(idx) = pattern_components
        .iter()
        .position(|c| logical_wild_inferiors_token(c))
    {
        let prefix = &pattern_components[..idx];
        let suffix = &pattern_components[idx + 1..];
        if actual_components.len() < prefix.len() + suffix.len() {
            return None;
        }

        for (actual_comp, pattern_comp) in actual_components.iter().zip(prefix.iter()) {
            let capture = match_directory_component(actual_comp, pattern_comp, case_insensitive)?;
            if let Some(c) = capture {
                captures.singles.push(c);
            }
        }

        let suffix_start = actual_components.len() - suffix.len();
        captures
            .inferiors
            .extend(actual_components[prefix.len()..suffix_start].iter().cloned());

        for (actual_comp, pattern_comp) in actual_components[suffix_start..]
            .iter()
            .zip(suffix.iter())
        {
            let capture = match_directory_component(actual_comp, pattern_comp, case_insensitive)?;
            if let Some(c) = capture {
                captures.singles.push(c);
            }
        }

        return Some(captures);
    }

    if actual_components.len() != pattern_components.len() {
        return None;
    }

    for (actual_comp, pattern_comp) in actual_components.iter().zip(pattern_components.iter()) {
        let capture = match_directory_component(actual_comp, pattern_comp, case_insensitive)?;
        if let Some(c) = capture {
            captures.singles.push(c);
        }
    }
    Some(captures)
}

fn apply_component_template(template: Option<&String>, capture: &Option<String>) -> Option<String> {
    let Some(template) = template else {
        return None;
    };

    if logical_wild_token(template) || logical_wild_inferiors_token(template) {
        return capture.clone();
    }

    if template.contains('*') {
        if let Some(cap) = capture {
            return Some(template.replace('*', cap));
        }
    }

    Some(template.clone())
}

fn apply_directory_template(
    template: Option<&crate::pathname::PathnameDirectory>,
    captures: &DirectoryMatchCaptures,
) -> Option<crate::pathname::PathnameDirectory> {
    let Some(template) = template else {
        return None;
    };

    let mut components = Vec::new();
    let mut next_single = 0usize;
    for comp in &template.components {
        if logical_wild_inferiors_token(comp) {
            components.extend(captures.inferiors.iter().cloned());
            continue;
        }

        if logical_wild_token(comp) {
            if let Some(c) = captures.singles.get(next_single) {
                components.push(c.clone());
                next_single += 1;
                continue;
            }
        } else if comp.contains('*') {
            if let Some(c) = captures.singles.get(next_single) {
                components.push(comp.replace('*', c));
                next_single += 1;
                continue;
            }
        }
        components.push(comp.clone());
    }

    if components.is_empty() && !template.absolute {
        None
    } else {
        Some(crate::pathname::PathnameDirectory {
            absolute: template.absolute,
            components,
        })
    }
}

fn build_namestring_from_components(
    host: Option<&String>,
    directory: Option<&crate::pathname::PathnameDirectory>,
    name: Option<&String>,
    type_: Option<&String>,
    version: Option<&String>,
) -> String {
    if host.is_some() {
        let mut out = String::new();
        if let Some(host) = host {
            out.push_str(host);
        }
        out.push(':');

        if let Some(dir) = directory {
            if dir.absolute {
                out.push(';');
            }
            for comp in &dir.components {
                out.push_str(comp);
                out.push(';');
            }
        }

        if let Some(name) = name {
            out.push_str(name);
        }
        if let Some(type_) = type_ {
            if name.is_some() {
                out.push('.');
            } else {
                out.push_str("*.");
            }
            out.push_str(type_);
        }
        if let Some(version) = version {
            if name.is_some() || type_.is_some() {
                out.push('.');
            } else {
                out.push_str("*.*.");
            }
            out.push_str(version);
        }
        return out;
    }

    let sep = std::path::MAIN_SEPARATOR;
    let mut out = String::new();
    if let Some(dir) = directory {
        if dir.absolute {
            out.push(sep);
        }
        if !dir.components.is_empty() {
            out.push_str(&dir.components.join(&sep.to_string()));
        }
    }

    let mut file = String::new();
    if let Some(name) = name {
        file.push_str(name);
    }
    if let Some(type_) = type_ {
        if !file.is_empty() {
            file.push('.');
        }
        file.push_str(type_);
    }
    if let Some(version) = version {
        if !file.is_empty() {
            file.push('.');
        }
        file.push_str(version);
    }

    if !file.is_empty() {
        if !out.is_empty() && !out.ends_with(sep) {
            out.push(sep);
        }
        out.push_str(&file);
    } else if out.is_empty() {
        out.push('.');
    }

    out
}

fn translate_pathname_with_wildcards(
    source: &Pathname,
    from_wildname: &Pathname,
    to_wildname: &Pathname,
) -> Option<Pathname> {
    let case_insensitive = source.host.is_some() || from_wildname.host.is_some();
    let mut captures = PathnameMatchCaptures::default();

    captures.host = match_component_capture(
        source.host.as_deref(),
        from_wildname.host.as_deref(),
        true,
    )?;
    captures.device = match_component_capture(
        source.device.as_deref(),
        from_wildname.device.as_deref(),
        case_insensitive,
    )?;
    captures.directory = match_directory_capture(
        source.directory.as_ref(),
        from_wildname.directory.as_ref(),
        case_insensitive,
    )?;
    captures.name = match_component_capture(
        source.name.as_deref(),
        from_wildname.name.as_deref(),
        case_insensitive,
    )?;
    captures.type_ = match_component_capture(
        source.type_.as_deref(),
        from_wildname.type_.as_deref(),
        case_insensitive,
    )?;
    captures.version = match_component_capture(
        source.version.as_deref(),
        from_wildname.version.as_deref(),
        case_insensitive,
    )?;

    let host = apply_component_template(to_wildname.host.as_ref(), &captures.host)
        .map(|s| normalize_logical_host(&s));
    let device = apply_component_template(to_wildname.device.as_ref(), &captures.device);
    let directory = apply_directory_template(to_wildname.directory.as_ref(), &captures.directory);
    let name = apply_component_template(to_wildname.name.as_ref(), &captures.name);
    let type_ = apply_component_template(to_wildname.type_.as_ref(), &captures.type_);
    let version = apply_component_template(to_wildname.version.as_ref(), &captures.version);

    let namestring = build_namestring_from_components(
        host.as_ref(),
        directory.as_ref(),
        name.as_ref(),
        type_.as_ref(),
        version.as_ref(),
    );
    let mut pn = Pathname::from_namestring(&namestring);
    pn.host = host;
    pn.device = device;
    pn.directory = directory;
    pn.name = name;
    pn.type_ = type_;
    pn.version = version;
    Some(pn)
}

fn make_builtin_translation_rule(host: &str, from: &str, to: &str) -> (Pathname, Pathname) {
    let mut from_pn = Pathname::from_namestring(from);
    from_pn.host = Some(host.to_string());
    let to_pn = Pathname::from_namestring(to);
    (from_pn, to_pn)
}

fn builtin_logical_pathname_translations(host: &str) -> Option<Vec<(Pathname, Pathname)>> {
    match host {
        "ANSI-TESTS" => Some(vec![
            make_builtin_translation_rule("ANSI-TESTS", "AUX;**;*.*.*", "tests/ansi-test/auxiliary/**/*.*"),
            make_builtin_translation_rule("ANSI-TESTS", "**;*.*.*", "tests/ansi-test/**/*.*"),
        ]),
        "CLTESTROOT" => Some(vec![make_builtin_translation_rule(
            "CLTESTROOT",
            "**;*.*.*",
            "tests/ansi-test/**/*.*",
        )]),
        "CLTEST" => Some(vec![make_builtin_translation_rule(
            "CLTEST",
            "**;*.*.*",
            "tests/ansi-test/sandbox/**/*.*",
        )]),
        _ => None,
    }
}

fn ensure_logical_translations_loaded(
    proc: &mut Process,
    host: &str,
) -> Result<(), ControlSignal> {
    if proc.logical_pathname_translations.contains_key(host) {
        return Ok(());
    }
    if let Some(rules) = builtin_logical_pathname_translations(host) {
        proc.logical_pathname_translations
            .insert(host.to_string(), rules);
        return Ok(());
    }
    Err(ControlSignal::Error(
        "LOAD-LOGICAL-PATHNAME-TRANSLATIONS: no translations found for host".to_string(),
    ))
}

fn translate_logical_pathname_with_tables(
    proc: &mut Process,
    pathname: &Pathname,
    depth: usize,
) -> Result<Pathname, ControlSignal> {
    if depth > 16 {
        return Err(ControlSignal::Error(
            "TRANSLATE-LOGICAL-PATHNAME: translation recursion limit exceeded".to_string(),
        ));
    }

    let Some(host_raw) = pathname.host.as_ref() else {
        return Ok(pathname.clone());
    };
    let host = normalize_logical_host(host_raw);
    ensure_logical_translations_loaded(proc, &host).map_err(|_| {
        ControlSignal::Error("TRANSLATE-LOGICAL-PATHNAME: no translation defined for host".to_string())
    })?;

    let rules = proc
        .logical_pathname_translations
        .get(&host)
        .cloned()
        .unwrap_or_default();

    for (from_wildname, to_wildname) in rules {
        if let Some(mapped) = translate_pathname_with_wildcards(pathname, &from_wildname, &to_wildname) {
            if mapped.host.is_some() {
                if mapped.host.as_ref().is_some_and(|h| normalize_logical_host(h) == host)
                    && mapped.namestring() == pathname.namestring()
                {
                    return Err(ControlSignal::Error(
                        "TRANSLATE-LOGICAL-PATHNAME: translation cycle detected".to_string(),
                    ));
                }
                return translate_logical_pathname_with_tables(proc, &mapped, depth + 1);
            }
            return Ok(mapped);
        }
    }

    Err(ControlSignal::Error(
        "TRANSLATE-LOGICAL-PATHNAME: no translation defined for host".to_string(),
    ))
}

fn translate_logical_path_minimal(
    proc: &mut Process,
    path: &str,
) -> Result<String, ControlSignal> {
    if !Pathname::has_logical_syntax(path) {
        return Ok(path.to_string());
    }
    let pathname = Pathname::from_namestring(path);
    if pathname.host.is_none() {
        return Ok(path.to_string());
    }
    let translated = translate_logical_pathname_with_tables(proc, &pathname, 0)?;
    if translated.host.is_some() {
        return Err(ControlSignal::Error(
            "Logical pathname translation did not produce a physical pathname".to_string(),
        ));
    }
    Ok(translated.namestring().to_string())
}

fn prim_load_and_compile_minimal(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return err_helper("LOAD-AND-COMPILE-MINIMAL requires a pathspec");
    }

    let mut path = string_from_designator(proc, ctx, args[0]).ok_or_else(|| {
        ControlSignal::Error("LOAD-AND-COMPILE-MINIMAL: invalid pathspec".to_string())
    })?;

    path = translate_logical_path_minimal(proc, &path)?;

    if !path.contains('/') && !path.contains('\\') {
        let load_pn_sym = ctx
            .symbols
            .write()
            .unwrap()
            .intern_in("*LOAD-PATHNAME*", crate::symbol::PackageId(1));
        if let Some(base_node) = proc.get_value(load_pn_sym) {
            if let Some(base_str) = string_from_designator(proc, ctx, base_node) {
                if let Some(parent) = std::path::Path::new(&base_str).parent() {
                    path = parent.join(&path).to_string_lossy().to_string();
                }
            }
        }
    }

    let path_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::String(path)));
    prim_load(proc, ctx, &[path_node])
}

fn build_reader_options(
    proc: &crate::process::Process,
    ctx: &crate::context::GlobalContext,
    preserve_whitespace: bool,
) -> crate::reader::ReaderOptions {
    let mut opts = crate::reader::ReaderOptions::default();
    opts.preserve_whitespace = preserve_whitespace;

    let get_sym = |name: &str| -> crate::symbol::SymbolId {
        ctx.symbols
            .write()
            .unwrap()
            .intern_in(name, crate::symbol::PackageId(1))
    };

    let lookup_env_or_global = |sym: crate::symbol::SymbolId| -> Option<NodeId> {
        if let Some(env) = &proc.current_env {
            if let Some(val) = env.lookup(sym) {
                return Some(val);
            }
        }
        proc.get_value(sym)
    };

    let read_base_sym = get_sym("*READ-BASE*");
    if let Some(val) = lookup_env_or_global(read_base_sym) {
        if let Node::Leaf(OpaqueValue::Integer(n)) = proc.arena.inner.get_unchecked(val) {
            if *n >= 2 && *n <= 36 {
                opts.read_base = *n as u32;
            }
        }
    }

    let read_eval_sym = get_sym("*READ-EVAL*");
    if let Some(val) = lookup_env_or_global(read_eval_sym) {
        opts.read_eval = !matches!(proc.arena.inner.get_unchecked(val), Node::Leaf(OpaqueValue::Nil));
    }

    let read_suppress_sym = get_sym("*READ-SUPPRESS*");
    if let Some(val) = lookup_env_or_global(read_suppress_sym) {
        opts.read_suppress =
            !matches!(proc.arena.inner.get_unchecked(val), Node::Leaf(OpaqueValue::Nil));
    }

    let features_sym = get_sym("*FEATURES*");
    if let Some(val) = lookup_env_or_global(features_sym) {
        let mut feats = Vec::new();
        let mut cur = val;
        while let Node::Fork(car, cdr) = proc.arena.inner.get_unchecked(cur) {
            if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(*car) {
                if let Some(name) = ctx
                    .symbols
                    .read()
                    .unwrap()
                    .symbol_name(crate::symbol::SymbolId(*id))
                {
                    feats.push(name.to_uppercase());
                }
            }
            cur = *cdr;
        }
        opts.features = feats;
    }

    opts
}

fn prim_mapc(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return err_helper("MAPC: too few arguments");
    }

    let func = args[0];
    let lists = &args[1..];

    // Validate lists and collect lengths?
    // MAPC terminates when shortest list runs out.
    // And returns the FIRST list.

    let result_list = lists[0];
    let mut current_nodes: Vec<NodeId> = lists.to_vec();

    let mut interpreter = Interpreter::new(proc, ctx);
    let env = crate::eval::Environment::new();

    loop {
        // Collect args for this iteration: (car list1) (car list2) ...
        let mut apply_args = Vec::new();
        let mut next_nodes = Vec::new();

        for &node in &current_nodes {
            match interpreter.process.arena.inner.get_unchecked(node) {
                Node::Fork(car, cdr) => {
                    apply_args.push(*car);
                    next_nodes.push(*cdr);
                }
                _ => {
                    // End of list (or dotted). Terminate.
                    return Ok(result_list);
                }
            }
        }

        // Apply function
        let args_list = interpreter.list(&apply_args);
        interpreter.apply_function(func, args_list, &env)?;

        current_nodes = next_nodes;
    }
}

fn prim_make_pathname(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    // Minimal pathname constructor: combines :directory, :name, :type with optional :defaults.
    let mut name: Option<String> = None;
    let mut type_ext: Option<String> = None;
    let mut directory: Option<String> = None;
    let mut defaults: Option<String> = None;

    let mut i = 0;
    while i < args.len() {
        if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(args[i]) {
            if let Some(s) = ctx.symbols.read().unwrap().symbol_name(SymbolId(*id)) {
                if i + 1 < args.len() {
                    let value = args[i + 1];
                    match s {
                        "NAME" => {
                            if !node_is_nil(proc, value) {
                                name = string_from_designator(proc, ctx, value);
                            }
                            i += 2;
                            continue;
                        }
                        "TYPE" => {
                            if !node_is_nil(proc, value) {
                                type_ext = string_from_designator(proc, ctx, value);
                            }
                            i += 2;
                            continue;
                        }
                        "DIRECTORY" => {
                            if node_is_nil(proc, value) {
                                directory = None;
                            } else if let Some(sval) = string_from_designator(proc, ctx, value) {
                                directory = Some(sval);
                            } else if let Some(items) = list_to_vec_opt(proc, value) {
                                let mut iter = items.into_iter();
                                let mut absolute = false;
                                let mut parts: Vec<String> = Vec::new();
                                if let Some(first) = iter.next() {
                                    if let Some(sym) = node_to_symbol(proc, first)
                                        .and_then(|sym| ctx.symbols.read().unwrap().symbol_name(sym).map(|s| s.to_string()))
                                    {
                                        if sym == "ABSOLUTE" {
                                            absolute = true;
                                        } else if sym == "RELATIVE" {
                                            absolute = false;
                                        } else if let Some(sval) = string_from_designator(proc, ctx, first) {
                                            parts.push(sval);
                                        }
                                    } else if let Some(sval) = string_from_designator(proc, ctx, first) {
                                        parts.push(sval);
                                    }
                                }
                                for item in iter {
                                    if let Some(sym) = node_to_symbol(proc, item)
                                        .and_then(|sym| ctx.symbols.read().unwrap().symbol_name(sym).map(|s| s.to_string()))
                                    {
                                        if sym == "BACK" || sym == "UP" {
                                            parts.push("..".to_string());
                                            continue;
                                        }
                                        if sym == "CURRENT" {
                                            parts.push(".".to_string());
                                            continue;
                                        }
                                    }
                                    if let Some(sval) = string_from_designator(proc, ctx, item) {
                                        parts.push(sval);
                                    }
                                }
                                let mut buf = if absolute {
                                    std::path::PathBuf::from(std::path::MAIN_SEPARATOR.to_string())
                                } else {
                                    std::path::PathBuf::new()
                                };
                                for part in parts {
                                    buf.push(part);
                                }
                                directory = Some(buf.to_string_lossy().to_string());
                            }
                            i += 2;
                            continue;
                        }
                        "DEFAULTS" => {
                            if !node_is_nil(proc, value) {
                                defaults = string_from_designator(proc, ctx, value);
                            }
                            i += 2;
                            continue;
                        }
                        _ => {}
                    }
                }
            }
        }
        i += 1;
    }

    let defaults_path = defaults.as_ref().map(std::path::Path::new);
    if name.is_none() {
        if let Some(p) = defaults_path {
            if let Some(stem) = p.file_stem() {
                name = Some(stem.to_string_lossy().to_string());
            }
        }
    }
    if type_ext.is_none() {
        if let Some(p) = defaults_path {
            if let Some(ext) = p.extension() {
                type_ext = Some(ext.to_string_lossy().to_string());
            }
        }
    }
    if directory.is_none() {
        if let Some(p) = defaults_path {
            let dir = if p.is_dir() {
                Some(p.to_path_buf())
            } else {
                p.parent().map(|d| d.to_path_buf())
            };
            if let Some(dir) = dir {
                directory = Some(dir.to_string_lossy().to_string());
            }
        }
    }

    let mut file = String::new();
    if let Some(name) = name {
        file = name;
        if let Some(ext) = type_ext {
            if !ext.is_empty() {
                file.push('.');
                file.push_str(&ext);
            }
        }
    }

    let res = if let Some(dir) = directory {
        if file.is_empty() {
            dir
        } else {
            std::path::Path::new(&dir)
                .join(file)
                .to_string_lossy()
                .to_string()
        }
    } else {
        file
    };

    Ok(alloc_pathname(proc, Pathname::from_namestring(&res)))
}

fn prim_pathname_directory(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("PATHNAME-DIRECTORY requires exactly 1 argument");
    }
    let pn = pathname_from_designator(proc, ctx, args[0], "PATHNAME-DIRECTORY")?;
    let Some(dir) = pn.directory else {
        return Ok(proc.make_nil());
    };

    let mut kw = |name: &str| -> NodeId {
        let sym = ctx.symbols.write().unwrap().intern_keyword(name);
        proc.arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(sym.0)))
    };

    let mut parts: Vec<NodeId> = Vec::new();
    parts.push(kw(if dir.absolute { "ABSOLUTE" } else { "RELATIVE" }));
    for comp in dir.components {
        parts.push(alloc_string(proc, comp));
    }

    let mut list = proc.make_nil();
    for node in parts.into_iter().rev() {
        list = proc.arena.inner.alloc(Node::Fork(node, list));
    }
    Ok(list)
}

fn prim_merge_pathnames(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return Ok(proc.make_nil());
    }
    let specified = path_from_designator(proc, ctx, args[0], "MERGE-PATHNAMES")?;
    let mut defaults = None;
    if args.len() > 1 {
        defaults = Some(path_from_designator(proc, ctx, args[1], "MERGE-PATHNAMES")?);
    } else {
        let sym = ctx
            .symbols
            .write()
            .unwrap()
            .intern_in("*DEFAULT-PATHNAME-DEFAULTS*", PackageId(1));
        if let Some(val) = proc.get_value(sym) {
            defaults = string_from_designator(proc, ctx, val);
        }
    }

    let merged = if path_is_absolute(&specified) || defaults.is_none() {
        specified
    } else {
        let defaults = defaults.unwrap();
        let base = std::path::Path::new(&defaults);
        let dir = if base.is_dir() {
            base.to_path_buf()
        } else {
            base.parent().unwrap_or(base).to_path_buf()
        };
        dir.join(&specified).to_string_lossy().to_string()
    };
    Ok(alloc_pathname(proc, Pathname::from_namestring(&merged)))
}

fn prim_pathname(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        let pn = pathname_from_designator(proc, ctx, arg, "PATHNAME")?;
        Ok(alloc_pathname(proc, pn))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_namestring(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        let path = path_from_designator(proc, ctx, arg, "NAMESTRING")?;
        Ok(alloc_string(proc, path))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_logical_pathname(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("LOGICAL-PATHNAME requires exactly 1 argument");
    }
    let mut pn = pathname_from_designator(proc, ctx, args[0], "LOGICAL-PATHNAME")?;
    if pn.host.is_none() || pn.namestring.contains('%') {
        return Err(ControlSignal::Error(
            "LOGICAL-PATHNAME: argument is not a logical pathname designator".to_string(),
        ));
    }
    if let Some(host) = pn.host.as_ref() {
        pn.host = Some(normalize_logical_host(host));
    }
    Ok(alloc_pathname(proc, pn))
}

fn logical_host_from_designator(
    proc: &Process,
    ctx: &crate::context::GlobalContext,
    node: NodeId,
    label: &str,
) -> Result<String, ControlSignal> {
    let host = string_from_designator(proc, ctx, node).ok_or_else(|| {
        ControlSignal::Error(format!("{}: host must be a string designator", label))
    })?;
    let normalized = normalize_logical_host(&host);
    if normalized.is_empty() {
        return Err(ControlSignal::Error(format!("{}: invalid host designator", label)));
    }
    Ok(normalized)
}

fn parse_allow_other_keys_tail(
    proc: &Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
    label: &str,
) -> Result<(), ControlSignal> {
    let mut allow_other_keys = false;
    let mut unknown_key_seen = false;
    if args.is_empty() {
        return Ok(());
    }
    if args.len() % 2 != 0 {
        return Err(ControlSignal::Error(format!(
            "{}: odd number of keyword arguments",
            label
        )));
    }
    for pair in args.chunks(2) {
        let key_sym = node_to_symbol(proc, pair[0]).ok_or_else(|| {
            ControlSignal::Error(format!("{}: keyword must be a symbol", label))
        })?;
        let key_name = ctx
            .symbols
            .read()
            .unwrap()
            .symbol_name(key_sym)
            .unwrap_or("")
            .to_uppercase();
        if key_name == "ALLOW-OTHER-KEYS" {
            if !allow_other_keys {
                allow_other_keys = !node_is_nil(proc, pair[1]);
            }
        } else {
            unknown_key_seen = true;
        }
    }
    if unknown_key_seen && !allow_other_keys {
        return Err(ControlSignal::Error(format!(
            "{}: invalid keyword argument",
            label
        )));
    }
    Ok(())
}

fn parse_logical_translation_rules(
    proc: &Process,
    ctx: &crate::context::GlobalContext,
    host: &str,
    value: NodeId,
) -> Result<Vec<(Pathname, Pathname)>, ControlSignal> {
    if node_is_nil(proc, value) {
        return Ok(Vec::new());
    }
    let rows = list_to_vec_opt(proc, value).ok_or_else(|| {
        ControlSignal::Error(
            "LOGICAL-PATHNAME-TRANSLATIONS: value must be a list of translation pairs".to_string(),
        )
    })?;

    let mut out = Vec::new();
    for row in rows {
        let pair = list_to_vec_opt(proc, row).ok_or_else(|| {
            ControlSignal::Error(
                "LOGICAL-PATHNAME-TRANSLATIONS: each translation must be a proper list".to_string(),
            )
        })?;
        if pair.len() < 2 {
            return Err(ControlSignal::Error(
                "LOGICAL-PATHNAME-TRANSLATIONS: each translation must have FROM and TO".to_string(),
            ));
        }

        let mut from = pathname_from_designator(
            proc,
            ctx,
            pair[0],
            "LOGICAL-PATHNAME-TRANSLATIONS",
        )?;
        if from.host.is_none() {
            from.host = Some(host.to_string());
        } else if from
            .host
            .as_ref()
            .is_some_and(|h| normalize_logical_host(h) != host)
        {
            return Err(ControlSignal::Error(
                "LOGICAL-PATHNAME-TRANSLATIONS: FROM host does not match table host".to_string(),
            ));
        } else {
            from.host = Some(host.to_string());
        }

        let to = pathname_from_designator(
            proc,
            ctx,
            pair[1],
            "LOGICAL-PATHNAME-TRANSLATIONS",
        )?;
        out.push((from, to));
    }
    Ok(out)
}

fn logical_translation_rules_to_list(
    proc: &mut Process,
    rules: &[(Pathname, Pathname)],
) -> NodeId {
    let mut list = proc.make_nil();
    for (from, to) in rules.iter().rev() {
        let from_node = alloc_pathname(proc, from.clone());
        let to_node = alloc_pathname(proc, to.clone());
        let pair = proc.make_list(&[from_node, to_node]);
        list = proc.arena.inner.alloc(Node::Fork(pair, list));
    }
    list
}

fn prim_logical_pathname_translations(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("LOGICAL-PATHNAME-TRANSLATIONS requires exactly 1 argument");
    }
    let host = logical_host_from_designator(proc, ctx, args[0], "LOGICAL-PATHNAME-TRANSLATIONS")?;
    ensure_logical_translations_loaded(proc, &host).map_err(|_| {
        ControlSignal::Error(
            "LOGICAL-PATHNAME-TRANSLATIONS: no translations found for host".to_string(),
        )
    })?;
    let rules = proc
        .logical_pathname_translations
        .get(&host)
        .cloned()
        .unwrap_or_default();
    Ok(logical_translation_rules_to_list(proc, &rules))
}

fn prim_set_logical_pathname_translations(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return err_helper("SET-LOGICAL-PATHNAME-TRANSLATIONS requires host and new table");
    }
    let host = logical_host_from_designator(
        proc,
        ctx,
        args[0],
        "LOGICAL-PATHNAME-TRANSLATIONS",
    )?;
    let rules = parse_logical_translation_rules(proc, ctx, &host, args[1])?;
    proc.logical_pathname_translations.insert(host, rules);
    Ok(args[1])
}

fn prim_translate_pathname(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 3 {
        return err_helper("TRANSLATE-PATHNAME requires at least 3 arguments");
    }
    parse_allow_other_keys_tail(proc, ctx, &args[3..], "TRANSLATE-PATHNAME")?;

    let source = pathname_from_designator(proc, ctx, args[0], "TRANSLATE-PATHNAME")?;
    let from_wildname = pathname_from_designator(proc, ctx, args[1], "TRANSLATE-PATHNAME")?;
    let to_wildname = pathname_from_designator(proc, ctx, args[2], "TRANSLATE-PATHNAME")?;
    let translated = translate_pathname_with_wildcards(&source, &from_wildname, &to_wildname)
        .ok_or_else(|| ControlSignal::Error("TRANSLATE-PATHNAME: source does not match FROM-WILDNAME".to_string()))?;
    Ok(alloc_pathname(proc, translated))
}

fn prim_translate_logical_pathname(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return err_helper("TRANSLATE-LOGICAL-PATHNAME requires at least 1 argument");
    }
    parse_allow_other_keys_tail(
        proc,
        ctx,
        &args[1..],
        "TRANSLATE-LOGICAL-PATHNAME",
    )?;

    // Keep object identity for physical pathname objects.
    if let Some(pn) = node_to_pathname(proc, args[0]) {
        if pn.host.is_none() {
            return Ok(args[0]);
        }
    }

    let pn = pathname_from_designator(proc, ctx, args[0], "TRANSLATE-LOGICAL-PATHNAME")?;
    if pn.host.is_none() {
        return Ok(alloc_pathname(proc, pn));
    }

    let mapped = translate_logical_pathname_with_tables(proc, &pn, 0)?;
    Ok(alloc_pathname(proc, mapped))
}

fn prim_load_logical_pathname_translations(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("LOAD-LOGICAL-PATHNAME-TRANSLATIONS requires exactly 1 argument");
    }
    let host = logical_host_from_designator(
        proc,
        ctx,
        args[0],
        "LOAD-LOGICAL-PATHNAME-TRANSLATIONS",
    )?;
    ensure_logical_translations_loaded(proc, &host)?;
    Ok(proc.make_nil())
}

fn prim_pathname_name(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("PATHNAME-NAME requires exactly 1 argument");
    }
    let pn = pathname_from_designator(proc, ctx, args[0], "PATHNAME-NAME")?;
    if let Some(name) = pn.name {
        Ok(alloc_string(proc, name))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_pathname_type(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("PATHNAME-TYPE requires exactly 1 argument");
    }
    let pn = pathname_from_designator(proc, ctx, args[0], "PATHNAME-TYPE")?;
    if let Some(ty) = pn.type_ {
        Ok(alloc_string(proc, ty))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_pathname_host(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("PATHNAME-HOST requires exactly 1 argument");
    }
    let pn = pathname_from_designator(proc, ctx, args[0], "PATHNAME-HOST")?;
    if let Some(host) = pn.host {
        Ok(alloc_string(proc, host))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_pathname_device(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("PATHNAME-DEVICE requires exactly 1 argument");
    }
    let pn = pathname_from_designator(proc, ctx, args[0], "PATHNAME-DEVICE")?;
    if let Some(device) = pn.device {
        Ok(alloc_string(proc, device))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_pathname_version(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("PATHNAME-VERSION requires exactly 1 argument");
    }
    let pn = pathname_from_designator(proc, ctx, args[0], "PATHNAME-VERSION")?;
    if let Some(version) = pn.version {
        Ok(alloc_string(proc, version))
    } else {
        Ok(proc.make_nil())
    }
}

fn slice_by_char_indices(s: &str, start: usize, end: usize) -> Option<String> {
    let chars: Vec<char> = s.chars().collect();
    if start > chars.len() || end > chars.len() || start > end {
        return None;
    }
    Some(chars[start..end].iter().collect())
}

#[derive(Debug, Default)]
struct ParseNamestringOptions {
    start: Option<usize>,
    end: Option<usize>,
    junk_allowed: bool,
    junk_allowed_set: bool,
}

fn parse_namestring_kwargs(
    proc: &Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> Result<ParseNamestringOptions, ControlSignal> {
    let mut opts = ParseNamestringOptions::default();

    if args.is_empty() {
        return Ok(opts);
    }
    if args.len() % 2 != 0 {
        return Err(ControlSignal::Error(
            "PARSE-NAMESTRING: odd number of keyword arguments".to_string(),
        ));
    }

    let syms = ctx.symbols.read().unwrap();
    let keyword_pkg = syms.get_package(PackageId(0));
    let kw_start = keyword_pkg.and_then(|p| p.find_external("START"));
    let kw_end = keyword_pkg.and_then(|p| p.find_external("END"));
    let kw_junk = keyword_pkg.and_then(|p| p.find_external("JUNK-ALLOWED"));

    for pair in args.chunks(2) {
        let key_node = pair[0];
        let val_node = pair[1];
        let key_sym = node_to_symbol(proc, key_node).ok_or_else(|| {
            ControlSignal::Error("PARSE-NAMESTRING: keyword must be a symbol".to_string())
        })?;

        if Some(key_sym) == kw_start {
            if opts.start.is_none() {
                if let Node::Leaf(OpaqueValue::Integer(n)) =
                    proc.arena.inner.get_unchecked(val_node)
                {
                    if *n >= 0 {
                        opts.start = Some(*n as usize);
                    }
                } else {
                    return Err(ControlSignal::Error(
                        "PARSE-NAMESTRING: :start must be an integer".to_string(),
                    ));
                }
            }
            continue;
        }
        if Some(key_sym) == kw_end {
            if opts.end.is_none() {
                if let Node::Leaf(OpaqueValue::Integer(n)) =
                    proc.arena.inner.get_unchecked(val_node)
                {
                    if *n >= 0 {
                        opts.end = Some(*n as usize);
                    }
                } else {
                    return Err(ControlSignal::Error(
                        "PARSE-NAMESTRING: :end must be an integer".to_string(),
                    ));
                }
            }
            continue;
        }
        if Some(key_sym) == kw_junk {
            if !opts.junk_allowed_set {
                opts.junk_allowed = !node_is_nil(proc, val_node);
                opts.junk_allowed_set = true;
            }
            continue;
        }

        return Err(ControlSignal::Error(
            "PARSE-NAMESTRING: invalid keyword argument".to_string(),
        ));
    }

    Ok(opts)
}

fn prim_parse_namestring(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return err_helper("PARSE-NAMESTRING requires at least 1 argument");
    }

    if let Some(pn) = node_to_pathname(proc, args[0]) {
        let idx = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Integer(pn.namestring.chars().count() as i64)));
        let pn_node = alloc_pathname(proc, pn);
        return Ok(set_multiple_values(proc, vec![pn_node, idx]));
    }

    let raw = path_from_designator(proc, ctx, args[0], "PARSE-NAMESTRING")?;
    let host_node = args.get(1).copied();
    let defaults_node = args.get(2).copied();
    let kw_start = if args.len() > 3 { 3 } else { args.len() };
    let opts = parse_namestring_kwargs(proc, ctx, &args[kw_start..])?;

    let mut start = opts.start.unwrap_or(0);
    let mut end = opts.end.unwrap_or_else(|| raw.chars().count());
    let mut slice = slice_by_char_indices(&raw, start, end)
        .ok_or_else(|| ControlSignal::Error("PARSE-NAMESTRING: invalid bounds".to_string()))?;

    if let Some(idx) = slice
        .chars()
        .position(|c| c.is_whitespace())
    {
        if opts.junk_allowed {
            slice = slice_by_char_indices(&slice, 0, idx)
                .unwrap_or_else(|| "".to_string());
            end = start + idx;
        } else {
            return Err(ControlSignal::Error(
                "PARSE-NAMESTRING: junk at end of namestring".to_string(),
            ));
        }
    }

    let mut merged = slice.clone();
    let defaults = if let Some(node) = defaults_node {
        if node_is_nil(proc, node) {
            None
        } else {
            Some(pathname_from_designator(proc, ctx, node, "PARSE-NAMESTRING")?)
        }
    } else {
        None
    };

    if let Some(defaults_pn) = &defaults {
        if merged.is_empty() {
            merged = defaults_pn.namestring().to_string();
        } else if !path_is_absolute(&merged) {
            let base = std::path::Path::new(defaults_pn.namestring());
            let dir = if base.is_dir() {
                base.to_path_buf()
            } else {
                base.parent().unwrap_or(base).to_path_buf()
            };
            merged = dir.join(&merged).to_string_lossy().to_string();
        }
    }

    let mut pn = Pathname::from_namestring(&merged);
    if pn.host.is_none() {
        if let Some(node) = host_node {
            if !node_is_nil(proc, node) {
                if let Some(host) = string_from_designator(proc, ctx, node) {
                    pn.host = Some(host);
                }
            }
        }
    }
    if pn.host.is_none() {
        if let Some(defaults_pn) = &defaults {
            if let Some(host) = defaults_pn.host.clone() {
                pn.host = Some(host);
            }
        }
    }

    let idx = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Integer(end as i64)));
    let pn_node = alloc_pathname(proc, pn);
    Ok(set_multiple_values(proc, vec![pn_node, idx]))
}

fn prim_pathnamep(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("PATHNAMEP requires exactly 1 argument");
    }
    let is_pathname = matches!(
        proc.arena.inner.get_unchecked(args[0]),
        Node::Leaf(OpaqueValue::Pathname(_))
    );
    if is_pathname {
        Ok(proc.make_t(_ctx))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_wild_pathname_p(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 2 {
        return err_helper("WILD-PATHNAME-P requires 1 or 2 arguments");
    }
    let pn = pathname_from_designator(proc, ctx, args[0], "WILD-PATHNAME-P")?;

    let key = if args.len() == 2 { args[1] } else { proc.make_nil() };
    let key_name = if node_is_nil(proc, key) {
        None
    } else {
        node_to_symbol(proc, key)
            .and_then(|sym| ctx.symbols.read().unwrap().symbol_name(sym).map(|s| s.to_string()))
    };

    let is_wild = |text: &Option<String>| text.as_ref().map(|s| is_wild_component(s)).unwrap_or(false);
    let dir_wild = pn.directory.as_ref().map(|d| {
        d.components
            .iter()
            .any(|c| c.eq_ignore_ascii_case("WILD") || c.eq_ignore_ascii_case("WILD-INFERIORS"))
    }).unwrap_or(false);

    let result = match key_name.as_deref() {
        None => {
            dir_wild
                || is_wild(&pn.name)
                || is_wild(&pn.type_)
                || is_wild(&pn.version)
                || is_wild(&pn.host)
                || is_wild(&pn.device)
        }
        Some("HOST") => is_wild(&pn.host),
        Some("DEVICE") => is_wild(&pn.device),
        Some("DIRECTORY") => dir_wild,
        Some("NAME") => is_wild(&pn.name),
        Some("TYPE") => is_wild(&pn.type_),
        Some("VERSION") => is_wild(&pn.version),
        _ => {
            return Err(ControlSignal::Error(
                "WILD-PATHNAME-P: invalid key".to_string(),
            ))
        }
    };

    if result {
        Ok(proc.make_t(ctx))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_pathname_match_p(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return err_helper("PATHNAME-MATCH-P requires exactly 2 arguments");
    }
    let path = pathname_from_designator(proc, ctx, args[0], "PATHNAME-MATCH-P")?;
    let pattern = pathname_from_designator(proc, ctx, args[1], "PATHNAME-MATCH-P")?;

    let host_ok = match &pattern.host {
        None => true,
        Some(host) if is_wild_component(host) => true,
        Some(host) => path.host.as_deref() == Some(host.as_str()),
    };
    let device_ok = match &pattern.device {
        None => true,
        Some(dev) if is_wild_component(dev) => true,
        Some(dev) => path.device.as_deref() == Some(dev.as_str()),
    };
    let dir_ok = directory_matches(path.directory.clone(), pattern.directory.clone());

    let name_ok = match &pattern.name {
        None => path.name.is_none(),
        Some(pat) if is_wild_component(pat) => {
            if let Some(actual) = &path.name {
                component_matches(actual, pat)
            } else {
                false
            }
        }
        Some(pat) => path.name.as_deref() == Some(pat.as_str()),
    };

    let type_ok = match &pattern.type_ {
        None => path.type_.is_none(),
        Some(pat) if is_wild_component(pat) => {
            if let Some(actual) = &path.type_ {
                component_matches(actual, pat)
            } else {
                false
            }
        }
        Some(pat) => path.type_.as_deref() == Some(pat.as_str()),
    };

    let version_ok = match &pattern.version {
        None => path.version.is_none(),
        Some(pat) if is_wild_component(pat) => true,
        Some(pat) => path.version.as_deref() == Some(pat.as_str()),
    };

    let result = host_ok && device_ok && dir_ok && name_ok && type_ok && version_ok;
    if result {
        Ok(proc.make_t(ctx))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_directory(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("DIRECTORY requires exactly 1 argument");
    }
    let mut path = path_from_designator(proc, ctx, args[0], "DIRECTORY")?;
    path = translate_logical_path_minimal(proc, &path)?;

    let has_wildcards = path.contains('*') || path.contains('?');
    let mut entries: Vec<String> = Vec::new();

    if has_wildcards {
        let pattern_path = std::path::Path::new(&path);
        let dir = pattern_path.parent().unwrap_or_else(|| std::path::Path::new("."));
        let pattern = pattern_path
            .file_name()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_else(|| "*".to_string());
        if let Ok(read_dir) = std::fs::read_dir(dir) {
            for entry in read_dir.flatten() {
                let file_name = entry.file_name().to_string_lossy().to_string();
                if glob_match(&pattern, &file_name) {
                    let full = entry.path().to_string_lossy().to_string();
                    entries.push(full);
                }
            }
        }
    } else {
        let path_buf = std::path::Path::new(&path);
        match std::fs::metadata(path_buf) {
            Ok(meta) if meta.is_dir() => {
                if let Ok(read_dir) = std::fs::read_dir(path_buf) {
                    for entry in read_dir.flatten() {
                        entries.push(entry.path().to_string_lossy().to_string());
                    }
                }
            }
            Ok(_) => entries.push(path),
            Err(_) => {}
        }
    }

    entries.sort();
    let mut list = proc.make_nil();
    for entry in entries.into_iter().rev() {
        let node = alloc_pathname(proc, Pathname::from_namestring(&entry));
        list = proc.arena.inner.alloc(Node::Fork(node, list));
    }
    Ok(list)
}

fn prim_delete_file(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("DELETE-FILE requires exactly 1 argument");
    }
    let mut path = path_from_designator(proc, ctx, args[0], "DELETE-FILE")?;
    path = translate_logical_path_minimal(proc, &path)?;
    std::fs::remove_file(&path)
        .map_err(|e| ControlSignal::Error(format!("DELETE-FILE: {}", e)))?;
    Ok(proc.make_t(ctx))
}

fn prim_probe_file(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("PROBE-FILE requires exactly 1 argument");
    }
    let mut path = path_from_designator(proc, ctx, args[0], "PROBE-FILE")?;
    path = translate_logical_path_minimal(proc, &path)?;
    if std::fs::metadata(&path).is_ok() {
        if let Ok(full) = std::fs::canonicalize(&path) {
            let full_str = full.to_string_lossy().to_string();
            return Ok(alloc_pathname(proc, Pathname::from_namestring(&full_str)));
        }
        return Ok(alloc_pathname(proc, Pathname::from_namestring(&path)));
    }
    Ok(proc.make_nil())
}

fn prim_truename(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("TRUENAME requires exactly 1 argument");
    }
    let mut path = path_from_designator(proc, ctx, args[0], "TRUENAME")?;
    path = translate_logical_path_minimal(proc, &path)?;
    let full = std::fs::canonicalize(&path)
        .map_err(|e| ControlSignal::Error(format!("TRUENAME: {}", e)))?;
    let full_str = full.to_string_lossy().to_string();
    Ok(alloc_pathname(proc, Pathname::from_namestring(&full_str)))
}

fn prim_rename_file(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return err_helper("RENAME-FILE requires exactly 2 arguments");
    }
    let defaulted_new_name = pathname_from_designator(proc, ctx, args[1], "RENAME-FILE")?;
    let mut from = path_from_designator(proc, ctx, args[0], "RENAME-FILE")?;
    let mut to = path_from_designator(proc, ctx, args[1], "RENAME-FILE")?;
    from = translate_logical_path_minimal(proc, &from)?;
    to = translate_logical_path_minimal(proc, &to)?;
    std::fs::rename(&from, &to)
        .map_err(|e| ControlSignal::Error(format!("RENAME-FILE: {}", e)))?;

    let old_true = std::fs::canonicalize(&to)
        .unwrap_or_else(|_| std::path::PathBuf::from(&to))
        .to_string_lossy()
        .to_string();
    let new_node = alloc_pathname(proc, defaulted_new_name);
    let old_node = alloc_pathname(proc, Pathname::from_namestring(&old_true));
    let new_true_node = alloc_pathname(proc, Pathname::from_namestring(&old_true));
    Ok(set_multiple_values(proc, vec![new_node, old_node, new_true_node]))
}

fn prim_ensure_directories_exist(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("ENSURE-DIRECTORIES-EXIST requires exactly 1 argument");
    }
    let mut path = path_from_designator(proc, ctx, args[0], "ENSURE-DIRECTORIES-EXIST")?;
    path = translate_logical_path_minimal(proc, &path)?;
    let path_buf = std::path::Path::new(&path);
    let has_trailing_sep = path.ends_with(std::path::MAIN_SEPARATOR);
    let is_dir = path_buf.is_dir();
    let is_file_hint = path_buf.extension().is_some() && !has_trailing_sep;
    let dir = if has_trailing_sep || is_dir || !is_file_hint {
        path_buf
    } else {
        path_buf.parent().unwrap_or(path_buf)
    };
    let existed = dir.exists();
    std::fs::create_dir_all(dir)
        .map_err(|e| ControlSignal::Error(format!("ENSURE-DIRECTORIES-EXIST: {}", e)))?;
    let path_node = alloc_pathname(proc, Pathname::from_namestring(&path));
    let created_node = if existed { proc.make_nil() } else { proc.make_t(ctx) };
    Ok(set_multiple_values(proc, vec![path_node, created_node]))
}

fn prim_compile_file_pathname(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    _args: &[NodeId],
) -> EvalResult {
    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Pathname(Pathname::from_namestring(
            "out.fasl",
        )))))
}

fn prim_file_namestring(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("FILE-NAMESTRING requires exactly 1 argument");
    }
    let path = path_from_designator(proc, ctx, args[0], "FILE-NAMESTRING")?;
    let path = std::path::Path::new(&path);
    if let Some(name) = path.file_name() {
        Ok(alloc_string(proc, name.to_string_lossy().to_string()))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_directory_namestring(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("DIRECTORY-NAMESTRING requires exactly 1 argument");
    }
    let path = path_from_designator(proc, ctx, args[0], "DIRECTORY-NAMESTRING")?;
    let path = std::path::Path::new(&path);
    let dir = if path.is_dir() {
        path
    } else {
        path.parent().unwrap_or(path)
    };
    let mut out = dir.to_string_lossy().to_string();
    if !out.ends_with(std::path::MAIN_SEPARATOR) && !out.is_empty() {
        out.push(std::path::MAIN_SEPARATOR);
    }
    Ok(alloc_string(proc, out))
}

fn prim_string(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("STRING requires exactly 1 argument");
    }
    let s = string_from_designator(proc, ctx, args[0])
        .ok_or_else(|| ControlSignal::Error("STRING: invalid designator".to_string()))?;
    Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(s))))
}

fn prim_string_eq(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return Ok(proc.make_t(ctx));
    }
    let s1 = string_from_designator(proc, ctx, args[0])
        .ok_or_else(|| ControlSignal::Error("STRING=: invalid string designator".to_string()))?;
    let s2 = string_from_designator(proc, ctx, args[1])
        .ok_or_else(|| ControlSignal::Error("STRING=: invalid string designator".to_string()))?;
    Ok(if s1 == s2 { proc.make_t(ctx) } else { proc.make_nil() })
}

fn prim_string_equal(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return Ok(proc.make_t(ctx));
    }
    let s1 = string_from_designator(proc, ctx, args[0])
        .ok_or_else(|| ControlSignal::Error("STRING-EQUAL: invalid designator".to_string()))?;
    let s2 = string_from_designator(proc, ctx, args[1])
        .ok_or_else(|| ControlSignal::Error("STRING-EQUAL: invalid designator".to_string()))?;
    Ok(if s1.eq_ignore_ascii_case(&s2) {
        proc.make_t(ctx)
    } else {
        proc.make_nil()
    })
}

fn prim_string_upcase(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("STRING-UPCASE requires exactly 1 argument");
    }
    let s = string_from_designator(proc, ctx, args[0])
        .ok_or_else(|| ControlSignal::Error("STRING-UPCASE: invalid designator".to_string()))?;
    let out: String = s.chars().flat_map(|c| c.to_uppercase()).collect();
    Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(out))))
}

fn prim_string_downcase(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("STRING-DOWNCASE requires exactly 1 argument");
    }
    let s = string_from_designator(proc, ctx, args[0])
        .ok_or_else(|| ControlSignal::Error("STRING-DOWNCASE: invalid designator".to_string()))?;
    let out: String = s.chars().flat_map(|c| c.to_lowercase()).collect();
    Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(out))))
}

fn prim_string_capitalize(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("STRING-CAPITALIZE requires exactly 1 argument");
    }
    let s = string_from_designator(proc, ctx, args[0])
        .ok_or_else(|| ControlSignal::Error("STRING-CAPITALIZE: invalid designator".to_string()))?;
    let mut out = String::with_capacity(s.len());
    let mut at_word_start = true;
    for ch in s.chars() {
        if ch.is_alphanumeric() {
            if at_word_start {
                out.extend(ch.to_uppercase());
                at_word_start = false;
            } else {
                out.extend(ch.to_lowercase());
            }
        } else {
            at_word_start = true;
            out.push(ch);
        }
    }
    Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(out))))
}

fn prim_string_trim(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return err_helper("STRING-TRIM requires exactly 2 arguments");
    }
    let bag = string_from_designator(proc, ctx, args[0])
        .ok_or_else(|| ControlSignal::Error("STRING-TRIM: invalid bag".to_string()))?;
    let s = string_from_designator(proc, ctx, args[1])
        .ok_or_else(|| ControlSignal::Error("STRING-TRIM: invalid string".to_string()))?;
    let bag_chars: Vec<char> = bag.chars().collect();
    let mut start = 0usize;
    let mut end = s.chars().count();
    let chars: Vec<char> = s.chars().collect();
    while start < end && bag_chars.contains(&chars[start]) {
        start += 1;
    }
    while end > start && bag_chars.contains(&chars[end - 1]) {
        end -= 1;
    }
    let out: String = chars[start..end].iter().collect();
    Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(out))))
}

fn prim_make_string(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return err_helper("MAKE-STRING requires at least 1 argument");
    }
    let len = match extract_number(&proc.arena.inner, args[0]) {
        NumVal::Int(n) if n >= 0 => n as usize,
        _ => return err_helper("MAKE-STRING: length must be a non-negative integer"),
    };
    let mut initial = ' ';
    let mut i = 1;
    while i + 1 < args.len() {
        let key = args[i];
        let val = args[i + 1];
        if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(key) {
            let name = ctx
                .symbols
                .read()
                .unwrap()
                .symbol_name(SymbolId(*id))
                .unwrap_or("")
                .to_uppercase();
            if name == "INITIAL-ELEMENT" {
                if let Some(ch) = node_to_char(proc, ctx, val) {
                    initial = ch;
                }
            }
        }
        i += 2;
    }
    let out: String = std::iter::repeat(initial).take(len).collect();
    Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(out))))
}

fn prim_concatenate(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return err_helper("CONCATENATE requires at least 1 argument");
    }
    let type_spec = args[0];
    let type_name = match proc.arena.inner.get_unchecked(type_spec) {
        Node::Leaf(OpaqueValue::Symbol(id)) => ctx
            .symbols
            .read()
            .unwrap()
            .symbol_name(SymbolId(*id))
            .unwrap_or("")
            .to_uppercase(),
        _ => "".to_string(),
    };
    if !matches!(
        type_name.as_str(),
        "STRING" | "SIMPLE-STRING" | "BASE-STRING" | "SIMPLE-BASE-STRING"
    ) {
        return err_helper("CONCATENATE: only string result supported");
    }
    let mut out = String::new();
    for &arg in &args[1..] {
        let part = string_from_sequence(proc, ctx, arg)
            .ok_or_else(|| ControlSignal::Error("CONCATENATE: invalid sequence".to_string()))?;
        out.push_str(&part);
    }
    Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(out))))
}

fn prim_coerce(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return err_helper("COERCE requires exactly 2 arguments");
    }
    let obj = args[0];
    let type_spec = args[1];
    let type_name = match proc.arena.inner.get_unchecked(type_spec) {
        Node::Leaf(OpaqueValue::Symbol(id)) => ctx
            .symbols
            .read()
            .unwrap()
            .symbol_name(SymbolId(*id))
            .unwrap_or("")
            .to_uppercase(),
        _ => "".to_string(),
    };
    match type_name.as_str() {
        "STRING" | "SIMPLE-STRING" | "BASE-STRING" | "SIMPLE-BASE-STRING" => {
            let s = string_from_sequence(proc, ctx, obj)
                .ok_or_else(|| ControlSignal::Error("COERCE: invalid string source".to_string()))?;
            Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(s))))
        }
        "SHORT-FLOAT" | "SINGLE-FLOAT" | "DOUBLE-FLOAT" | "LONG-FLOAT" | "FLOAT" => {
            let num = extract_number(&proc.arena.inner, obj);
            match num {
                NumVal::Int(n) => Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Float(n as f64)))),
                NumVal::Big(n) => Ok(proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Float(n.to_f64().unwrap_or(0.0))))),
                NumVal::Float(f) => Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Float(f)))),
                _ => err_helper("COERCE: cannot convert to float"),
            }
        }
        _ => err_helper("COERCE: unsupported target type"),
    }
}

fn prim_subseq(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 || args.len() > 3 {
        return err_helper("SUBSEQ requires 2 or 3 arguments");
    }
    let s = string_from_designator(proc, ctx, args[0])
        .ok_or_else(|| ControlSignal::Error("SUBSEQ: only strings supported".to_string()))?;
    let start = match extract_number(&proc.arena.inner, args[1]) {
        NumVal::Int(n) if n >= 0 => n as usize,
        _ => return err_helper("SUBSEQ: start must be non-negative integer"),
    };
    let end = if args.len() == 3 {
        match extract_number(&proc.arena.inner, args[2]) {
            NumVal::Int(n) if n >= 0 => n as usize,
            _ => return err_helper("SUBSEQ: end must be non-negative integer"),
        }
    } else {
        s.chars().count()
    };
    let chars: Vec<char> = s.chars().collect();
    if start > end || end > chars.len() {
        return err_helper("SUBSEQ: invalid bounds");
    }
    let out: String = chars[start..end].iter().collect();
    Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(out))))
}

fn prim_arrayp(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        match proc.arena.inner.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::VectorHandle(_)) | Node::Leaf(OpaqueValue::String(_)) => {
                Ok(proc.make_t(ctx))
            }
            _ => Ok(proc.make_nil()),
        }
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_vectorp(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        match proc.arena.inner.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::String(_)) => Ok(proc.make_t(ctx)),
            Node::Leaf(OpaqueValue::VectorHandle(id)) => {
                if let Some(arr) = proc.arrays.get(crate::arrays::VectorId(*id)) {
                    if arr.rank() == 1 {
                        return Ok(proc.make_t(ctx));
                    }
                }
                Ok(proc.make_nil())
            }
            _ => Ok(proc.make_nil()),
        }
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_simple_vector_p(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        match proc.arena.inner.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::VectorHandle(id)) => {
                if let Some(arr) = proc.arrays.get(crate::arrays::VectorId(*id)) {
                    if arr.is_simple_vector() {
                        return Ok(proc.make_t(ctx));
                    }
                }
                Ok(proc.make_nil())
            }
            _ => Ok(proc.make_nil()),
        }
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_simple_bit_vector_p(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        match proc.arena.inner.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::VectorHandle(id)) => {
                if let Some(arr) = proc.arrays.get(crate::arrays::VectorId(*id)) {
                    if arr.is_simple_bit_vector() {
                        return Ok(proc.make_t(ctx));
                    }
                }
                Ok(proc.make_nil())
            }
            _ => Ok(proc.make_nil()),
        }
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_array_rank(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("ARRAY-RANK requires exactly 1 argument");
    }
    match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::String(_)) => Ok(proc.make_integer(1)),
        Node::Leaf(OpaqueValue::VectorHandle(id)) => {
            if let Some(arr) = proc.arrays.get(crate::arrays::VectorId(*id)) {
                Ok(proc.make_integer(arr.rank() as i64))
            } else {
                err_helper("ARRAY-RANK: invalid array")
            }
        }
        _ => err_helper("ARRAY-RANK: not an array"),
    }
}

fn prim_array_dimensions(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("ARRAY-DIMENSIONS requires exactly 1 argument");
    }
    let dims: Vec<usize> = match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::String(s)) => vec![s.chars().count()],
        Node::Leaf(OpaqueValue::VectorHandle(id)) => {
            if let Some(arr) = proc.arrays.get(crate::arrays::VectorId(*id)) {
                arr.dimensions.clone()
            } else {
                return err_helper("ARRAY-DIMENSIONS: invalid array");
            }
        }
        _ => return err_helper("ARRAY-DIMENSIONS: not an array"),
    };
    let mut list = proc.make_nil();
    for d in dims.into_iter().rev() {
        let node = proc.make_integer(d as i64);
        list = proc.arena.inner.alloc(Node::Fork(node, list));
    }
    Ok(list)
}

fn prim_array_total_size(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("ARRAY-TOTAL-SIZE requires exactly 1 argument");
    }
    match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::String(s)) => Ok(proc.make_integer(s.chars().count() as i64)),
        Node::Leaf(OpaqueValue::VectorHandle(id)) => {
            if let Some(arr) = proc.arrays.get(crate::arrays::VectorId(*id)) {
                Ok(proc.make_integer(arr.total_size() as i64))
            } else {
                err_helper("ARRAY-TOTAL-SIZE: invalid array")
            }
        }
        _ => err_helper("ARRAY-TOTAL-SIZE: not an array"),
    }
}

fn prim_array_has_fill_pointer_p(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("ARRAY-HAS-FILL-POINTER-P requires exactly 1 argument");
    }
    match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::String(_)) => Ok(proc.make_nil()),
        Node::Leaf(OpaqueValue::VectorHandle(id)) => {
            if let Some(arr) = proc.arrays.get(crate::arrays::VectorId(*id)) {
                if arr.fill_pointer.is_some() {
                    Ok(proc.make_t(ctx))
                } else {
                    Ok(proc.make_nil())
                }
            } else {
                err_helper("ARRAY-HAS-FILL-POINTER-P: invalid array")
            }
        }
        _ => err_helper("ARRAY-HAS-FILL-POINTER-P: not an array"),
    }
}

fn array_element_type_symbol_id(
    ctx: &crate::context::GlobalContext,
    element_type: crate::arrays::ArrayElementType,
) -> SymbolId {
    let name = match element_type {
        crate::arrays::ArrayElementType::Bit => "BIT",
        crate::arrays::ArrayElementType::Character => "CHARACTER",
        crate::arrays::ArrayElementType::T => "T",
    };
    ctx
        .symbols
        .write()
        .unwrap()
        .intern_in(name, PackageId(1))
}

fn prim_array_element_type(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("ARRAY-ELEMENT-TYPE requires exactly 1 argument");
    }
    match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::String(_)) => {
            let sym = array_element_type_symbol_id(ctx, crate::arrays::ArrayElementType::Character);
            Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Symbol(sym.0))))
        }
        Node::Leaf(OpaqueValue::VectorHandle(id)) => {
            if let Some(arr) = proc.arrays.get(crate::arrays::VectorId(*id)) {
                let sym = array_element_type_symbol_id(ctx, arr.element_type);
                Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Symbol(sym.0))))
            } else {
                err_helper("ARRAY-ELEMENT-TYPE: invalid array")
            }
        }
        _ => err_helper("ARRAY-ELEMENT-TYPE: not an array"),
    }
}

fn prim_upgraded_array_element_type(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("UPGRADED-ARRAY-ELEMENT-TYPE requires exactly 1 argument");
    }
    let elem_type = match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::Symbol(id)) => {
            let name = ctx
                .symbols
                .read()
                .unwrap()
                .symbol_name(SymbolId(*id))
                .unwrap_or("")
                .to_uppercase();
            match name.as_str() {
                "BIT" => crate::arrays::ArrayElementType::Bit,
                "CHARACTER" | "BASE-CHAR" => crate::arrays::ArrayElementType::Character,
                _ => crate::arrays::ArrayElementType::T,
            }
        }
        Node::Fork(car, _) => {
            if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(*car) {
                let name = ctx
                    .symbols
                    .read()
                    .unwrap()
                    .symbol_name(SymbolId(*id))
                    .unwrap_or("")
                    .to_uppercase();
                if name == "UNSIGNED-BYTE" || name == "SIGNED-BYTE" {
                    crate::arrays::ArrayElementType::T
                } else {
                    crate::arrays::ArrayElementType::T
                }
            } else {
                crate::arrays::ArrayElementType::T
            }
        }
        _ => crate::arrays::ArrayElementType::T,
    };
    let sym = array_element_type_symbol_id(ctx, elem_type);
    Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Symbol(sym.0))))
}

fn prim_row_major_aref(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return err_helper("ROW-MAJOR-AREF requires exactly 2 arguments");
    }
    let index = match extract_number(&proc.arena.inner, args[1]) {
        NumVal::Int(n) if n >= 0 => n as usize,
        _ => return err_helper("ROW-MAJOR-AREF: index must be non-negative integer"),
    };
    match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::String(s)) => {
            let ch = s.chars().nth(index).ok_or_else(|| {
                ControlSignal::Error("ROW-MAJOR-AREF: index out of bounds".to_string())
            })?;
            Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Char(ch))))
        }
        Node::Leaf(OpaqueValue::VectorHandle(id)) => {
            let vec_id = crate::arrays::VectorId(*id);
            if let Some(val) = proc.arrays.aref(vec_id, index) {
                Ok(val)
            } else {
                err_helper("ROW-MAJOR-AREF: index out of bounds")
            }
        }
        _ => err_helper("ROW-MAJOR-AREF: not an array"),
    }
}

fn prim_complex(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 2 {
        return err_helper("COMPLEX requires 1 or 2 arguments");
    }
    let real = args[0];
    let imag = if args.len() == 2 { args[1] } else { proc.make_integer(0) };
    let is_zero = match proc.arena.inner.get_unchecked(imag) {
        Node::Leaf(OpaqueValue::Integer(n)) => *n == 0,
        Node::Leaf(OpaqueValue::BigInt(n)) => n == &num_bigint::BigInt::from(0),
        Node::Leaf(OpaqueValue::Float(f)) => *f == 0.0,
        _ => false,
    };
    if is_zero {
        return Ok(real);
    }
    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Complex(real, imag))))
}

fn prim_typep(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return err_helper("TYPEP requires exactly 2 arguments");
    }
    let obj = args[0];
    let type_spec = args[1];

    let type_name = match proc.arena.inner.get_unchecked(type_spec) {
        Node::Leaf(OpaqueValue::Symbol(id)) => ctx
            .symbols
            .read()
            .unwrap()
            .symbol_name(SymbolId(*id))
            .unwrap_or("")
            .to_uppercase(),
        Node::Fork(car, _) => {
            if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(*car) {
                ctx.symbols
                    .read()
                    .unwrap()
                    .symbol_name(SymbolId(*id))
                    .unwrap_or("")
                    .to_uppercase()
            } else {
                "".to_string()
            }
        }
        _ => "".to_string(),
    };

    let result = match type_name.as_str() {
        "T" => true,
        "NIL" => false,
        "SYMBOL" => matches!(
            proc.arena.inner.get_unchecked(obj),
            Node::Leaf(OpaqueValue::Symbol(_)) | Node::Leaf(OpaqueValue::Nil)
        ),
        "INTEGER" => matches!(
            proc.arena.inner.get_unchecked(obj),
            Node::Leaf(OpaqueValue::Integer(_)) | Node::Leaf(OpaqueValue::BigInt(_))
        ),
        "RATIONAL" => matches!(
            proc.arena.inner.get_unchecked(obj),
            Node::Leaf(OpaqueValue::Integer(_))
                | Node::Leaf(OpaqueValue::BigInt(_))
                | Node::Leaf(OpaqueValue::Ratio(_, _))
        ),
        "RATIO" => matches!(
            proc.arena.inner.get_unchecked(obj),
            Node::Leaf(OpaqueValue::Ratio(_, _))
        ),
        "REAL" => matches!(
            proc.arena.inner.get_unchecked(obj),
            Node::Leaf(OpaqueValue::Integer(_))
                | Node::Leaf(OpaqueValue::BigInt(_))
                | Node::Leaf(OpaqueValue::Ratio(_, _))
                | Node::Leaf(OpaqueValue::Float(_))
        ),
        "FLOAT" | "SHORT-FLOAT" | "SINGLE-FLOAT" | "DOUBLE-FLOAT" | "LONG-FLOAT" => {
            matches!(proc.arena.inner.get_unchecked(obj), Node::Leaf(OpaqueValue::Float(_)))
        }
        "NUMBER" => matches!(
            proc.arena.inner.get_unchecked(obj),
            Node::Leaf(OpaqueValue::Integer(_))
                | Node::Leaf(OpaqueValue::BigInt(_))
                | Node::Leaf(OpaqueValue::Ratio(_, _))
                | Node::Leaf(OpaqueValue::Float(_))
                | Node::Leaf(OpaqueValue::Complex(_, _))
        ),
        "COMPLEX" => matches!(
            proc.arena.inner.get_unchecked(obj),
            Node::Leaf(OpaqueValue::Complex(_, _))
        ),
        "CHARACTER" | "BASE-CHAR" => {
            matches!(proc.arena.inner.get_unchecked(obj), Node::Leaf(OpaqueValue::Char(_)))
        }
        "STRING" | "SIMPLE-STRING" | "BASE-STRING" | "SIMPLE-BASE-STRING" => {
            matches!(proc.arena.inner.get_unchecked(obj), Node::Leaf(OpaqueValue::String(_)))
        }
        "PATHNAME" => matches!(
            proc.arena.inner.get_unchecked(obj),
            Node::Leaf(OpaqueValue::Pathname(_))
        ),
        "LOGICAL-PATHNAME" => match proc.arena.inner.get_unchecked(obj) {
            Node::Leaf(OpaqueValue::Pathname(pn)) => pn.host.is_some(),
            _ => false,
        },
        "ARRAY" | "SIMPLE-ARRAY" => matches!(
            proc.arena.inner.get_unchecked(obj),
            Node::Leaf(OpaqueValue::VectorHandle(_)) | Node::Leaf(OpaqueValue::String(_))
        ),
        "VECTOR" => {
            if let Node::Leaf(OpaqueValue::String(_)) = proc.arena.inner.get_unchecked(obj) {
                true
            } else if let Node::Leaf(OpaqueValue::VectorHandle(id)) =
                proc.arena.inner.get_unchecked(obj)
            {
                proc.arrays
                    .get(crate::arrays::VectorId(*id))
                    .map(|a| a.rank() == 1)
                    .unwrap_or(false)
            } else {
                false
            }
        }
        "SIMPLE-VECTOR" => {
            if let Node::Leaf(OpaqueValue::VectorHandle(id)) = proc.arena.inner.get_unchecked(obj) {
                proc.arrays
                    .get(crate::arrays::VectorId(*id))
                    .map(|a| a.is_simple_vector())
                    .unwrap_or(false)
            } else {
                false
            }
        }
        "BIT-VECTOR" | "SIMPLE-BIT-VECTOR" => {
            if let Node::Leaf(OpaqueValue::VectorHandle(id)) = proc.arena.inner.get_unchecked(obj) {
                proc.arrays
                    .get(crate::arrays::VectorId(*id))
                    .map(|a| a.is_simple_bit_vector())
                    .unwrap_or(false)
            } else {
                false
            }
        }
        "READTABLE" => matches!(
            proc.arena.inner.get_unchecked(obj),
            Node::Leaf(OpaqueValue::Readtable(_))
        ),
        other => {
            // Structure types: vector with tag symbol in slot 0
            if let Node::Leaf(OpaqueValue::VectorHandle(id)) = proc.arena.inner.get_unchecked(obj) {
                if let Some(arr) = proc.arrays.get(crate::arrays::VectorId(*id)) {
                    if let Some(first) = arr.elements.first() {
                        if let Node::Leaf(OpaqueValue::Symbol(sym_id)) =
                            proc.arena.inner.get_unchecked(*first)
                        {
                            if let Some(name) = ctx
                                .symbols
                                .read()
                                .unwrap()
                                .symbol_name(SymbolId(*sym_id))
                            {
                                return Ok(if name.eq_ignore_ascii_case(other) {
                                    proc.make_t(ctx)
                                } else {
                                    proc.make_nil()
                                });
                            }
                        }
                    }
                }
            }
            false
        }
    };

    Ok(if result {
        proc.make_t(ctx)
    } else {
        proc.make_nil()
    })
}

fn prim_sys_make_struct(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return err_helper("SYS-MAKE-STRUCT requires type and slot list");
    }
    let type_sym = match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::Symbol(id)) => SymbolId(*id),
        _ => return err_helper("SYS-MAKE-STRUCT: type must be a symbol"),
    };

    let slot_nodes = list_to_vec_opt(proc, args[1])
        .ok_or_else(|| ControlSignal::Error("SYS-MAKE-STRUCT: invalid slot list".into()))?;
    let mut slot_names: Vec<String> = Vec::new();
    for node in &slot_nodes {
        match proc.arena.inner.get_unchecked(*node) {
            Node::Leaf(OpaqueValue::Symbol(id)) => {
                let name = ctx
                    .symbols
                    .read()
                    .unwrap()
                    .symbol_name(SymbolId(*id))
                    .unwrap_or("")
                    .to_uppercase();
                slot_names.push(name);
            }
            _ => return err_helper("SYS-MAKE-STRUCT: slot name must be a symbol"),
        }
    }

    let mut allow_other_keys = false;
    if (args.len() - 2) % 2 != 0 {
        return err_helper("SYS-MAKE-STRUCT: odd number of initargs");
    }
    let mut i = 2;
    while i + 1 < args.len() {
        if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(args[i]) {
            let name = ctx
                .symbols
                .read()
                .unwrap()
                .symbol_name(SymbolId(*id))
                .unwrap_or("")
                .to_uppercase();
            if name == "ALLOW-OTHER-KEYS"
                && !matches!(
                    proc.arena.inner.get_unchecked(args[i + 1]),
                    Node::Leaf(OpaqueValue::Nil)
                )
            {
                allow_other_keys = true;
            }
        }
        i += 2;
    }

    let type_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(type_sym.0)));
    let mut elements = vec![proc.make_nil(); slot_names.len() + 1];
    elements[0] = type_node;
    let mut set_flags = vec![false; slot_names.len()];

    i = 2;
    while i + 1 < args.len() {
        let key = args[i];
        let val = args[i + 1];
        let key_name = if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(key)
        {
            ctx.symbols
                .read()
                .unwrap()
                .symbol_name(SymbolId(*id))
                .unwrap_or("")
                .to_uppercase()
        } else {
            String::new()
        };

        if key_name == "ALLOW-OTHER-KEYS" {
            i += 2;
            continue;
        }

        if let Some(pos) = slot_names.iter().position(|s| s == &key_name) {
            if !set_flags[pos] {
                elements[pos + 1] = val;
                set_flags[pos] = true;
            }
        } else if !allow_other_keys {
            return err_helper("SYS-MAKE-STRUCT: invalid initarg");
        }

        i += 2;
    }

    let vec_id = proc.arrays.alloc_array(
        vec![elements.len()],
        elements,
        crate::arrays::ArrayElementType::T,
        None,
    );
    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::VectorHandle(vec_id.0))))
}

fn prim_sys_struct_ref(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 3 {
        return err_helper("SYS-STRUCT-REF requires object, index, type");
    }
    let obj = args[0];
    let idx = match extract_number(&proc.arena.inner, args[1]) {
        NumVal::Int(n) if n >= 0 => n as usize,
        _ => return err_helper("SYS-STRUCT-REF: invalid index"),
    };
    let type_sym = match proc.arena.inner.get_unchecked(args[2]) {
        Node::Leaf(OpaqueValue::Symbol(id)) => SymbolId(*id),
        _ => return err_helper("SYS-STRUCT-REF: invalid type"),
    };

    let vec_id = match proc.arena.inner.get_unchecked(obj) {
        Node::Leaf(OpaqueValue::VectorHandle(id)) => crate::arrays::VectorId(*id),
        _ => return err_helper("SYS-STRUCT-REF: not a structure"),
    };
    let arr = proc
        .arrays
        .get(vec_id)
        .ok_or_else(|| ControlSignal::Error("SYS-STRUCT-REF: invalid structure".into()))?;
    if arr.elements.is_empty() {
        return err_helper("SYS-STRUCT-REF: invalid structure");
    }
    if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(arr.elements[0])
    {
        if *id != type_sym.0 {
            let symbols = ctx.symbols.read().unwrap();
            let expected = symbols.symbol_name(type_sym).unwrap_or("");
            let actual = symbols.symbol_name(SymbolId(*id)).unwrap_or("");
            if !actual.eq_ignore_ascii_case(expected) {
                return err_helper("SYS-STRUCT-REF: type mismatch");
            }
        }
    }
    let slot_index = idx + 1;
    if slot_index >= arr.elements.len() {
        return err_helper("SYS-STRUCT-REF: slot index out of bounds");
    }
    Ok(arr.elements[slot_index])
}

fn prim_sys_struct_p(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return err_helper("SYS-STRUCT-P requires object and type");
    }
    let type_name = match proc.arena.inner.get_unchecked(args[1]) {
        Node::Leaf(OpaqueValue::Symbol(id)) => ctx
            .symbols
            .read()
            .unwrap()
            .symbol_name(SymbolId(*id))
            .unwrap_or("")
            .to_uppercase(),
        _ => return err_helper("SYS-STRUCT-P: invalid type"),
    };
    if let Node::Leaf(OpaqueValue::VectorHandle(id)) = proc.arena.inner.get_unchecked(args[0]) {
        if let Some(arr) = proc.arrays.get(crate::arrays::VectorId(*id)) {
            if let Some(first) = arr.elements.first() {
                if let Node::Leaf(OpaqueValue::Symbol(sym_id)) =
                    proc.arena.inner.get_unchecked(*first)
                {
                    if let Some(name) = ctx
                        .symbols
                        .read()
                        .unwrap()
                        .symbol_name(SymbolId(*sym_id))
                    {
                        return Ok(if name.eq_ignore_ascii_case(&type_name) {
                            proc.make_t(ctx)
                        } else {
                            proc.make_nil()
                        });
                    }
                }
            }
        }
    }
    Ok(proc.make_nil())
}

fn parse_hash_test_mode(
    proc: &crate::process::Process,
    ctx: &crate::context::GlobalContext,
    node: NodeId,
) -> TestMode {
    let mut name: Option<String> = None;
    match proc.arena.inner.get_unchecked(node) {
        Node::Leaf(OpaqueValue::Symbol(id)) => {
            name = ctx
                .symbols
                .read()
                .unwrap()
                .symbol_name(SymbolId(*id))
                .map(|s| s.to_string());
        }
        Node::Leaf(OpaqueValue::String(s)) => {
            name = Some(s.clone());
        }
        _ => {}
    }

    match name.unwrap_or_default().to_uppercase().as_str() {
        "EQL" => TestMode::Eql,
        "EQUAL" => TestMode::Equal,
        "EQUALP" => TestMode::Equalp,
        "EQ" => TestMode::Eq,
        _ => TestMode::Eq,
    }
}

fn prim_make_hash_table(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    let mut test_mode = TestMode::Eq;

    if args.len() % 2 != 0 {
        return err_helper("MAKE-HASH-TABLE: odd number of keyword arguments");
    }

    let mut i = 0;
    while i < args.len() {
        let key_node = args[i];
        if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(key_node) {
            if let Some(name) = ctx.symbols.read().unwrap().symbol_name(SymbolId(*id)) {
                if name.eq_ignore_ascii_case("TEST") {
                    if i + 1 >= args.len() {
                        return err_helper("MAKE-HASH-TABLE: missing :TEST value");
                    }
                    test_mode = parse_hash_test_mode(proc, ctx, args[i + 1]);
                }
            }
        }
        i += 2;
    }

    let handle = proc.hashtables.alloc(HashTable::new(test_mode));
    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::HashHandle(handle.0))))
}

fn prim_gethash(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return err_helper("GETHASH: requires key and hash-table");
    }
    crate::hashtables::record_get();
    let key = args[0];
    let table_node = args[1];
    let default = args.get(2).copied().unwrap_or_else(|| proc.make_nil());

    let handle = node_to_hash_handle(proc, table_node)
        .ok_or_else(|| ControlSignal::Error("GETHASH: not a hash-table".to_string()))?;
    let table = proc
        .hashtables
        .get(handle)
        .ok_or_else(|| ControlSignal::Error("GETHASH: invalid hash-table".to_string()))?;

    if let Some(val) = table.get(key, &proc.arena.inner, table.test_mode.clone()) {
        Ok(set_multiple_values(proc, vec![val, proc.make_t(ctx)]))
    } else {
        Ok(set_multiple_values(proc, vec![default, proc.make_nil()]))
    }
}

fn prim_set_gethash(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 3 {
        return err_helper("SET-GETHASH: requires key, hash-table, value");
    }
    crate::hashtables::record_set();
    let key = args[0];
    let table_node = args[1];
    let value = args[2];

    let handle = node_to_hash_handle(proc, table_node)
        .ok_or_else(|| ControlSignal::Error("SET-GETHASH: not a hash-table".to_string()))?;
    let table = proc
        .hashtables
        .get_mut(handle)
        .ok_or_else(|| ControlSignal::Error("SET-GETHASH: invalid hash-table".to_string()))?;
    table.insert(key, value, &proc.arena.inner);
    Ok(value)
}

fn prim_remhash(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return err_helper("REMHASH: requires key and hash-table");
    }
    crate::hashtables::record_rem();
    let key = args[0];
    let table_node = args[1];

    let handle = node_to_hash_handle(proc, table_node)
        .ok_or_else(|| ControlSignal::Error("REMHASH: not a hash-table".to_string()))?;
    let table = proc
        .hashtables
        .get_mut(handle)
        .ok_or_else(|| ControlSignal::Error("REMHASH: invalid hash-table".to_string()))?;

    Ok(if table.remove(key, &proc.arena.inner) {
        proc.make_t(ctx)
    } else {
        proc.make_nil()
    })
}

fn prim_clrhash(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("CLRHASH: requires hash-table");
    }
    crate::hashtables::record_clr();
    let table_node = args[0];
    let handle = node_to_hash_handle(proc, table_node)
        .ok_or_else(|| ControlSignal::Error("CLRHASH: not a hash-table".to_string()))?;
    let table = proc
        .hashtables
        .get_mut(handle)
        .ok_or_else(|| ControlSignal::Error("CLRHASH: invalid hash-table".to_string()))?;
    table.clear();
    Ok(table_node)
}

fn prim_maphash(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return err_helper("MAPHASH: requires function and hash-table");
    }
    crate::hashtables::record_maphash();
    let func = args[0];
    let table_node = args[1];

    let handle = node_to_hash_handle(proc, table_node)
        .ok_or_else(|| ControlSignal::Error("MAPHASH: not a hash-table".to_string()))?;
    let entries = {
        let table = proc
            .hashtables
            .get(handle)
            .ok_or_else(|| ControlSignal::Error("MAPHASH: invalid hash-table".to_string()))?;
        table.entries()
    };

    let mut interpreter = Interpreter::new(proc, ctx);
    let env = crate::eval::Environment::new();
    for (k, v) in entries {
        let args_list = interpreter.list(&[k, v]);
        interpreter.apply_function(func, args_list, &env)?;
    }

    Ok(proc.make_nil())
}

fn prim_assert(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    // Arg 0 is the value (evaluated)
    if let Some(&val) = args.first() {
        if let Node::Leaf(OpaqueValue::Nil) = proc.arena.inner.get_unchecked(val) {
            return err_helper("ASSERT failed");
        }
    }
    Ok(proc.make_nil())
}

// ============================================================================
// Arithmetic Primitives
// ============================================================================

fn prim_add(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    let mut sum = NumVal::Int(0);

    for &arg in args {
        let val = extract_number(&proc.arena.inner, arg);
        sum = sum.add(val);
    }

    Ok(sum.to_node(&mut proc.arena.inner))
}

fn prim_sub(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(0))));
    }

    let first = extract_number(&proc.arena.inner, args[0]);

    if args.len() == 1 {
        // Unary minus
        match first {
            NumVal::Int(n) => match n.checked_neg() {
                Some(res) => Ok(proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Integer(res)))),
                None => Ok(proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Float(-(n as f64))))),
            },
            NumVal::Big(n) => Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::BigInt(-n)))),
            NumVal::Ratio(n, d) => Ok(ratio_from_bigints(-n, d).to_node(&mut proc.arena.inner)),
            NumVal::Float(f) => Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Float(-f)))),
            NumVal::None => return err_helper("Arithmetic error: non-numeric argument"),
            // GlobalContext holds nil_sym, but nil_node is in process arena?
            // Actually context.rs line 26: nil_sym.
            // But we need NodeId.
            // We can alloc NIL value.
        }
    } else {
        let mut result = first;
        for &arg in &args[1..] {
            let val = extract_number(&proc.arena.inner, arg);
            result = result.sub(val);
        }
        Ok(result.to_node(&mut proc.arena.inner))
    }
}

// Note: To support "ctx.nil_node", we either need to alloc NIL,
// or check if Process has cached NIL.
// For now, let's assume we alloc new NILs. Leaf(Nil) is small.
fn make_nil(proc: &mut crate::process::Process) -> NodeId {
    proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Nil))
}

fn prim_mul(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    let mut product = NumVal::Int(1);

    for &arg in args {
        let val = extract_number(&proc.arena.inner, arg);
        product = product.mul(val);
    }

    Ok(product.to_node(&mut proc.arena.inner))
}

fn prim_div(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(1))));
    }

    let first = extract_number(&proc.arena.inner, args[0]);

    if args.len() == 1 {
        // Reciprocal
        let result = NumVal::Int(1).div(first);
        Ok(result.to_node(&mut proc.arena.inner))
    } else {
        let mut result = first;
        for &arg in &args[1..] {
            let val = extract_number(&proc.arena.inner, arg);
            result = result.div(val);
        }
        Ok(result.to_node(&mut proc.arena.inner))
    }
}

fn prim_1plus(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        let val = extract_number(&proc.arena.inner, arg);
        Ok(val.add(NumVal::Int(1)).to_node(&mut proc.arena.inner))
    } else {
        Ok(make_nil(proc))
    }
}

fn prim_1minus(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        let val = extract_number(&proc.arena.inner, arg);
        Ok(val.sub(NumVal::Int(1)).to_node(&mut proc.arena.inner))
    } else {
        Ok(make_nil(proc))
    }
}

fn prim_mod(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() >= 2 {
        let a_val = extract_number(&proc.arena.inner, args[0]);
        let b_val = extract_number(&proc.arena.inner, args[1]);

        match (a_val, b_val) {
            (NumVal::Int(a), NumVal::Int(b)) if b != 0 => {
                return Ok(proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Integer(a % b))));
            }
            (NumVal::Big(a), NumVal::Big(b)) if b != BigInt::from(0) => {
                return Ok(NumVal::Big(a % b).to_node(&mut proc.arena.inner));
            }
            (NumVal::Big(a), NumVal::Int(b)) if b != 0 => {
                return Ok(NumVal::Big(a % BigInt::from(b)).to_node(&mut proc.arena.inner));
            }
            (NumVal::Int(a), NumVal::Big(b)) if b != BigInt::from(0) => {
                return Ok(NumVal::Big(BigInt::from(a) % b).to_node(&mut proc.arena.inner));
            }
            _ => {}
        }
    }
    Ok(make_nil(proc))
}

// ============================================================================
// Comparison Primitives
// ============================================================================

// ============================================================================
// Comparison Primitives
// ============================================================================

fn prim_num_eq(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return Ok(proc.make_t(ctx));
    }

    let first = extract_number(&proc.arena.inner, args[0]);
    for &arg in &args[1..] {
        let val = extract_number(&proc.arena.inner, arg);
        if !first.eq(&val) {
            return Ok(proc.make_nil());
        }
    }
    Ok(proc.make_t(ctx))
}

fn prim_lt(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    compare_chain(proc, ctx, args, |a, b| a < b)
}

fn prim_gt(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    compare_chain(proc, ctx, args, |a, b| a > b)
}

fn prim_le(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    compare_chain(proc, ctx, args, |a, b| a <= b)
}

fn prim_ge(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    compare_chain(proc, ctx, args, |a, b| a >= b)
}

fn compare_chain<F>(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
    cmp: F,
) -> EvalResult
where
    F: Fn(&NumVal, &NumVal) -> bool,
{
    if args.len() < 2 {
        return Ok(proc.make_t(ctx));
    }

    let mut prev = extract_number(&proc.arena.inner, args[0]);
    for &arg in &args[1..] {
        let curr = extract_number(&proc.arena.inner, arg);
        if !cmp(&prev, &curr) {
            return Ok(proc.make_nil());
        }
        prev = curr;
    }
    Ok(proc.make_t(ctx))
}

// ============================================================================
// List Primitives
// ============================================================================

fn prim_cons(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() >= 2 {
        Ok(proc.arena.inner.alloc(Node::Fork(args[0], args[1])))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_car(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        match proc.arena.inner.get_unchecked(arg) {
            Node::Fork(car, _) => Ok(*car),
            Node::Leaf(OpaqueValue::Nil) => Ok(proc.make_nil()),
            _ => Err(ControlSignal::Error(
                "CAR: Argument is not a list".to_string(),
            )),
        }
    } else {
        Err(ControlSignal::Error("CAR: Too few arguments".to_string()))
    }
}

fn prim_cdr(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        match proc.arena.inner.get_unchecked(arg) {
            Node::Fork(_, cdr) => Ok(*cdr),
            Node::Leaf(OpaqueValue::Nil) => Ok(proc.make_nil()),
            _ => Err(ControlSignal::Error(
                "CDR: Argument is not a list".to_string(),
            )),
        }
    } else {
        Err(ControlSignal::Error("CDR: Too few arguments".to_string()))
    }
}

fn prim_list(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    Ok(proc.make_list(args))
}

fn prim_length(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        match proc.arena.inner.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::String(s)) => {
                return Ok(proc.make_integer(s.chars().count() as i64))
            }
            Node::Leaf(OpaqueValue::VectorHandle(id)) => {
                if let Some(len) = proc.arrays.length(crate::arrays::VectorId(*id)) {
                    return Ok(proc.make_integer(len as i64));
                }
                return Err(ControlSignal::Error(
                    "LENGTH: argument is not a sequence".to_string(),
                ));
            }
            _ => {}
        }
        let mut len = 0;
        let mut current = arg;
        while let Node::Fork(_, cdr) = proc.arena.inner.get_unchecked(current).clone() {
            len += 1;
            current = cdr;
        }
        Ok(proc.make_integer(len))
    } else {
        Ok(proc.make_integer(0))
    }
}

fn prim_append(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return Ok(proc.make_nil());
    }

    // Collect all elements
    let mut all_elements = Vec::new();
    for (i, &arg) in args.iter().enumerate() {
        if i == args.len() - 1 {
            // Last arg is used as-is for tail
            if all_elements.is_empty() {
                return Ok(arg);
            }
            let mut result = arg;
            for elem in all_elements.into_iter().rev() {
                result = proc.arena.inner.alloc(Node::Fork(elem, result));
            }
            return Ok(result);
        }

        let mut current = arg;
        while let Node::Fork(car, cdr) = proc.arena.inner.get_unchecked(current).clone() {
            all_elements.push(car);
            current = cdr;
        }
    }

    Ok(proc.make_list(&all_elements))
}

fn prim_reverse(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        let mut elements = Vec::new();
        let mut current = arg;
        while let Node::Fork(car, cdr) = proc.arena.inner.get_unchecked(current).clone() {
            elements.push(car);
            current = cdr;
        }
        elements.reverse();
        Ok(proc.make_list(&elements))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_nth(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() >= 2 {
        if let NumVal::Int(n) = extract_number(&proc.arena.inner, args[0]) {
            let mut current = args[1];
            for _ in 0..n {
                if let Node::Fork(_, cdr) = proc.arena.inner.get_unchecked(current).clone() {
                    current = cdr;
                } else {
                    return Ok(proc.make_nil());
                }
            }
            if let Node::Fork(car, _) = proc.arena.inner.get_unchecked(current).clone() {
                return Ok(car);
            }
        }
    }
    Ok(proc.make_nil())
}

// ============================================================================
// Predicates
// ============================================================================

fn prim_null(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        // Need to check if arg is NIL node (which is distinct now) or Leaf(Nil)
        if let Node::Leaf(OpaqueValue::Nil) = proc.arena.inner.get_unchecked(arg) {
            Ok(proc.make_t(ctx))
        } else {
            Ok(proc.make_nil())
        }
    } else {
        Ok(proc.make_t(ctx))
    }
}

fn prim_atom(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        match proc.arena.inner.get_unchecked(arg) {
            Node::Fork(_, _) => Ok(proc.make_nil()),
            _ => Ok(proc.make_t(ctx)),
        }
    } else {
        Ok(proc.make_t(ctx))
    }
}

fn prim_consp(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        match proc.arena.inner.get_unchecked(arg) {
            Node::Fork(_, _) => Ok(proc.make_t(ctx)),
            _ => Ok(proc.make_nil()),
        }
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_listp(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        match proc.arena.inner.get_unchecked(arg) {
            Node::Fork(_, _) => Ok(proc.make_t(ctx)),
            Node::Leaf(OpaqueValue::Nil) => Ok(proc.make_t(ctx)),
            _ => Ok(proc.make_nil()),
        }
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_numberp(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        match proc.arena.inner.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::Integer(_))
            | Node::Leaf(OpaqueValue::Float(_))
            | Node::Leaf(OpaqueValue::BigInt(_))
            | Node::Leaf(OpaqueValue::Ratio(_, _))
            | Node::Leaf(OpaqueValue::Complex(_, _)) => {
                Ok(proc.make_t(ctx))
            }
            _ => Ok(proc.make_nil()),
        }
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_characterp(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        match proc.arena.inner.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::Char(_)) => Ok(proc.make_t(ctx)),
            _ => Ok(proc.make_nil()),
        }
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_stringp(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("STRINGP requires exactly 1 argument");
    }
    let node = args[0];
    let is_string = match proc.arena.inner.get_unchecked(node) {
        Node::Leaf(OpaqueValue::String(_)) => true,
        Node::Leaf(OpaqueValue::VectorHandle(id)) => proc
            .arrays
            .get(crate::arrays::VectorId(*id))
            .map(|arr| arr.element_type.is_character())
            .unwrap_or(false),
        _ => false,
    };
    Ok(if is_string {
        proc.make_t(ctx)
    } else {
        proc.make_nil()
    })
}

fn prim_character(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("CHARACTER requires exactly 1 argument");
    }
    if let Some(ch) = node_to_char(proc, ctx, args[0]) {
        return Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Char(ch))));
    }
    err_helper("CHARACTER: invalid character designator")
}

fn prim_char_code(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("CHAR-CODE requires exactly 1 argument");
    }
    match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::Char(c)) => Ok(proc.make_integer(*c as i64)),
        _ => err_helper("CHAR-CODE: argument must be a character"),
    }
}

fn prim_code_char(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("CODE-CHAR requires exactly 1 argument");
    }
    let n = match extract_number(&proc.arena.inner, args[0]) {
        NumVal::Int(i) if i >= 0 => i as u32,
        _ => return Ok(proc.make_nil()),
    };
    if let Some(ch) = std::char::from_u32(n) {
        Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Char(ch))))
    } else {
        Ok(proc.make_nil())
    }
}

fn char_name_str(ch: char) -> Option<&'static str> {
    match ch {
        ' ' => Some("SPACE"),
        '\n' => Some("NEWLINE"),
        '\t' => Some("TAB"),
        '\r' => Some("RETURN"),
        '\x0c' => Some("PAGE"),
        '\x7f' => Some("RUBOUT"),
        '\x08' => Some("BACKSPACE"),
        '\0' => Some("NULL"),
        _ => None,
    }
}

fn name_char_str(name: &str) -> Option<char> {
    match name {
        "SPACE" => Some(' '),
        "NEWLINE" => Some('\n'),
        "TAB" => Some('\t'),
        "RETURN" => Some('\r'),
        "LINEFEED" => Some('\n'),
        "PAGE" => Some('\x0c'),
        "RUBOUT" => Some('\x7f'),
        "BACKSPACE" => Some('\x08'),
        "NULL" => Some('\0'),
        _ if name.chars().count() == 1 => name.chars().next(),
        _ => None,
    }
}

fn prim_char_name(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("CHAR-NAME requires exactly 1 argument");
    }
    let ch = match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::Char(c)) => *c,
        _ => return err_helper("CHAR-NAME: argument must be a character"),
    };
    if let Some(name) = char_name_str(ch) {
        Ok(proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String(name.to_string()))))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_name_char(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("NAME-CHAR requires exactly 1 argument");
    }
    let s = match string_from_designator(proc, ctx, args[0]) {
        Some(s) => s,
        None => return err_helper("NAME-CHAR: argument must be a string designator"),
    };
    let upper = s.to_uppercase();
    if let Some(ch) = name_char_str(upper.as_str()) {
        Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Char(ch))))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_char_upcase(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("CHAR-UPCASE requires exactly 1 argument");
    }
    let ch = node_to_char(proc, ctx, args[0]).ok_or_else(|| {
        ControlSignal::Error("CHAR-UPCASE: argument must be a character".to_string())
    })?;
    let up = ch.to_uppercase().next().unwrap_or(ch);
    Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Char(up))))
}

fn prim_char_downcase(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("CHAR-DOWNCASE requires exactly 1 argument");
    }
    let ch = node_to_char(proc, ctx, args[0]).ok_or_else(|| {
        ControlSignal::Error("CHAR-DOWNCASE: argument must be a character".to_string())
    })?;
    let down = ch.to_lowercase().next().unwrap_or(ch);
    Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Char(down))))
}

fn prim_upper_case_p(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("UPPER-CASE-P requires exactly 1 argument");
    }
    let ch = node_to_char(proc, ctx, args[0]).ok_or_else(|| {
        ControlSignal::Error("UPPER-CASE-P: argument must be a character".to_string())
    })?;
    Ok(if ch.is_uppercase() {
        proc.make_t(ctx)
    } else {
        proc.make_nil()
    })
}

fn prim_lower_case_p(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("LOWER-CASE-P requires exactly 1 argument");
    }
    let ch = node_to_char(proc, ctx, args[0]).ok_or_else(|| {
        ControlSignal::Error("LOWER-CASE-P: argument must be a character".to_string())
    })?;
    Ok(if ch.is_lowercase() {
        proc.make_t(ctx)
    } else {
        proc.make_nil()
    })
}

fn prim_both_case_p(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("BOTH-CASE-P requires exactly 1 argument");
    }
    let ch = node_to_char(proc, ctx, args[0]).ok_or_else(|| {
        ControlSignal::Error("BOTH-CASE-P: argument must be a character".to_string())
    })?;
    Ok(if ch.is_uppercase() || ch.is_lowercase() {
        proc.make_t(ctx)
    } else {
        proc.make_nil()
    })
}

fn prim_alphanumericp(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("ALPHANUMERICP requires exactly 1 argument");
    }
    let ch = node_to_char(proc, ctx, args[0]).ok_or_else(|| {
        ControlSignal::Error("ALPHANUMERICP: argument must be a character".to_string())
    })?;
    Ok(if ch.is_alphanumeric() {
        proc.make_t(ctx)
    } else {
        proc.make_nil()
    })
}

fn digit_value(ch: char) -> Option<u32> {
    match ch {
        '0'..='9' => Some((ch as u8 - b'0') as u32),
        'A'..='Z' => Some((ch as u8 - b'A') as u32 + 10),
        'a'..='z' => Some((ch as u8 - b'a') as u32 + 10),
        _ => None,
    }
}

fn prim_digit_char(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 2 {
        return err_helper("DIGIT-CHAR requires 1 or 2 arguments");
    }
    let weight = match extract_number(&proc.arena.inner, args[0]) {
        NumVal::Int(n) if n >= 0 => n as u32,
        _ => return Ok(proc.make_nil()),
    };
    let radix = if args.len() > 1 {
        match extract_number(&proc.arena.inner, args[1]) {
            NumVal::Int(n) if n >= 2 && n <= 36 => n as u32,
            _ => return Ok(proc.make_nil()),
        }
    } else {
        10
    };
    if weight >= radix {
        return Ok(proc.make_nil());
    }
    let ch = if weight < 10 {
        (b'0' + weight as u8) as char
    } else {
        (b'A' + (weight - 10) as u8) as char
    };
    Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Char(ch))))
}

fn prim_digit_char_p(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 2 {
        return err_helper("DIGIT-CHAR-P requires 1 or 2 arguments");
    }
    let ch = node_to_char(proc, ctx, args[0]).ok_or_else(|| {
        ControlSignal::Error("DIGIT-CHAR-P: argument must be a character".to_string())
    })?;
    let radix = if args.len() > 1 {
        match extract_number(&proc.arena.inner, args[1]) {
            NumVal::Int(n) if n >= 2 && n <= 36 => n as u32,
            _ => return Ok(proc.make_nil()),
        }
    } else {
        10
    };
    if let Some(val) = digit_value(ch) {
        if val < radix {
            return Ok(proc.make_integer(val as i64));
        }
    }
    Ok(proc.make_nil())
}

fn prim_symbolp(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        match proc.arena.inner.get_unchecked(arg) {
            // Symbols are OpaqueValue::Symbol now
            Node::Leaf(OpaqueValue::Symbol(_)) => Ok(proc.make_t(ctx)),
            Node::Leaf(OpaqueValue::Nil) => Ok(proc.make_t(ctx)), // NIL is a symbol
            // T? T is OpaqueValue::Symbol.
            _ => Ok(proc.make_nil()),
        }
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_eq(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return Ok(proc.make_t(ctx));
    }

    if args[0] == args[1] {
        return Ok(proc.make_t(ctx));
    }

    // Check for same symbol with different NodeIds
    match (
        proc.arena.inner.get_unchecked(args[0]),
        proc.arena.inner.get_unchecked(args[1]),
    ) {
        (Node::Leaf(OpaqueValue::Symbol(id1)), Node::Leaf(OpaqueValue::Symbol(id2))) => {
            if id1 == id2 {
                return Ok(proc.make_t(ctx));
            }
        }
        (Node::Leaf(OpaqueValue::Class(id1)), Node::Leaf(OpaqueValue::Class(id2))) => {
            if id1 == id2 {
                return Ok(proc.make_t(ctx));
            }
        }
        (Node::Leaf(OpaqueValue::Instance(id1)), Node::Leaf(OpaqueValue::Instance(id2))) => {
            if id1 == id2 {
                return Ok(proc.make_t(ctx));
            }
        }
        (Node::Leaf(OpaqueValue::Generic(id1)), Node::Leaf(OpaqueValue::Generic(id2))) => {
            if id1 == id2 {
                return Ok(proc.make_t(ctx));
            }
        }
        (Node::Leaf(OpaqueValue::Method(id1)), Node::Leaf(OpaqueValue::Method(id2))) => {
            if id1 == id2 {
                return Ok(proc.make_t(ctx));
            }
        }
        (Node::Leaf(OpaqueValue::EqlSpecializer(id1)), Node::Leaf(OpaqueValue::EqlSpecializer(id2))) => {
            if id1 == id2 {
                return Ok(proc.make_t(ctx));
            }
        }
        (Node::Leaf(OpaqueValue::Readtable(id1)), Node::Leaf(OpaqueValue::Readtable(id2))) => {
            if id1 == id2 {
                return Ok(proc.make_t(ctx));
            }
        }
        (
            Node::Leaf(OpaqueValue::SlotDefinition(c1, s1, d1)),
            Node::Leaf(OpaqueValue::SlotDefinition(c2, s2, d2)),
        ) => {
            if c1 == c2 && s1 == s2 && d1 == d2 {
                return Ok(proc.make_t(ctx));
            }
        }
        (Node::Leaf(OpaqueValue::Nil), Node::Leaf(OpaqueValue::Nil)) => {
            return Ok(proc.make_t(ctx));
        }
        _ => {}
    }

    Ok(proc.make_nil())
}

fn prim_functionp(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("FUNCTIONP requires exactly 1 argument");
    }

    let is_func = match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::Closure(_))
        | Node::Leaf(OpaqueValue::Generic(_))
        | Node::Leaf(OpaqueValue::MethodWrapper(_, _))
        | Node::Leaf(OpaqueValue::NextMethod(_))
        | Node::Leaf(OpaqueValue::NextMethodP(_))
        | Node::Leaf(OpaqueValue::CallMethod(_)) => true,
        _ => false,
    };

    Ok(if is_func {
        proc.make_t(ctx)
    } else {
        proc.make_nil()
    })
}

fn prim_eql(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return Ok(proc.make_t(ctx));
    }

    if args[0] == args[1] {
        return Ok(proc.make_t(ctx));
    }

    // Check numeric equality
    let a = extract_number(&proc.arena.inner, args[0]);
    let b = extract_number(&proc.arena.inner, args[1]);
    if a.eq(&b) {
        return Ok(proc.make_t(ctx));
    }

    // Character equality
    if let (Node::Leaf(OpaqueValue::Char(a)), Node::Leaf(OpaqueValue::Char(b))) = (
        proc.arena.inner.get_unchecked(args[0]),
        proc.arena.inner.get_unchecked(args[1]),
    ) {
        if a == b {
            return Ok(proc.make_t(ctx));
        }
    }

    // Complex equality (compare parts numerically)
    if let (Node::Leaf(OpaqueValue::Complex(ar, ai)), Node::Leaf(OpaqueValue::Complex(br, bi))) = (
        proc.arena.inner.get_unchecked(args[0]),
        proc.arena.inner.get_unchecked(args[1]),
    ) {
        let ra = extract_number(&proc.arena.inner, *ar);
        let rb = extract_number(&proc.arena.inner, *br);
        let ia = extract_number(&proc.arena.inner, *ai);
        let ib = extract_number(&proc.arena.inner, *bi);
        if ra.eq(&rb) && ia.eq(&ib) {
            return Ok(proc.make_t(ctx));
        }
    }

    // Fallback to EQ semantics for non-numeric objects
    match (
        proc.arena.inner.get_unchecked(args[0]),
        proc.arena.inner.get_unchecked(args[1]),
    ) {
        (Node::Leaf(OpaqueValue::Symbol(id1)), Node::Leaf(OpaqueValue::Symbol(id2))) => {
            if id1 == id2 {
                return Ok(proc.make_t(ctx));
            }
        }
        (Node::Leaf(OpaqueValue::Class(id1)), Node::Leaf(OpaqueValue::Class(id2))) => {
            if id1 == id2 {
                return Ok(proc.make_t(ctx));
            }
        }
        (Node::Leaf(OpaqueValue::Instance(id1)), Node::Leaf(OpaqueValue::Instance(id2))) => {
            if id1 == id2 {
                return Ok(proc.make_t(ctx));
            }
        }
        (Node::Leaf(OpaqueValue::Generic(id1)), Node::Leaf(OpaqueValue::Generic(id2))) => {
            if id1 == id2 {
                return Ok(proc.make_t(ctx));
            }
        }
        (Node::Leaf(OpaqueValue::Method(id1)), Node::Leaf(OpaqueValue::Method(id2))) => {
            if id1 == id2 {
                return Ok(proc.make_t(ctx));
            }
        }
        (Node::Leaf(OpaqueValue::EqlSpecializer(id1)), Node::Leaf(OpaqueValue::EqlSpecializer(id2))) => {
            if id1 == id2 {
                return Ok(proc.make_t(ctx));
            }
        }
        (Node::Leaf(OpaqueValue::Readtable(id1)), Node::Leaf(OpaqueValue::Readtable(id2))) => {
            if id1 == id2 {
                return Ok(proc.make_t(ctx));
            }
        }
        (
            Node::Leaf(OpaqueValue::SlotDefinition(c1, s1, d1)),
            Node::Leaf(OpaqueValue::SlotDefinition(c2, s2, d2)),
        ) => {
            if c1 == c2 && s1 == s2 && d1 == d2 {
                return Ok(proc.make_t(ctx));
            }
        }
        _ => {}
    }

    Ok(proc.make_nil())
}

fn prim_equal(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return Ok(proc.make_t(ctx));
    }

    fn equal_rec(arena: &Arena, a: NodeId, b: NodeId) -> bool {
        if a == b {
            return true;
        }

        match (arena.get_unchecked(a), arena.get_unchecked(b)) {
            (Node::Leaf(va), Node::Leaf(vb)) => va == vb,
            (Node::Stem(ia), Node::Stem(ib)) => equal_rec(arena, *ia, *ib),
            (Node::Fork(ca, da), Node::Fork(cb, db)) => {
                equal_rec(arena, *ca, *cb) && equal_rec(arena, *da, *db)
            }
            _ => false,
        }
    }

    if equal_rec(&proc.arena.inner, args[0], args[1]) {
        Ok(proc.make_t(ctx))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_not(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Node::Leaf(OpaqueValue::Nil) = proc.arena.inner.get_unchecked(arg) {
            Ok(proc.make_t(ctx))
        } else {
            Ok(proc.make_nil())
        }
    } else {
        Ok(proc.make_t(ctx))
    }
}

// ============================================================================
// Symbol Primitives
// ============================================================================

fn prim_symbol_value(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(arg) {
            let sym_id = SymbolId(*id);
            // 1. Check Process Dictionary (Dynamic Scope)
            if let Some(val) = proc.get_value(sym_id) {
                return Ok(val);
            }

            // 2. Check Global Context (Global Scope)
            // Constants like T and NIL
            if sym_id == ctx.t_sym || sym_id == ctx.nil_sym {
                return Ok(arg);
            }
            if let Some(pkg) = ctx.symbols.read().unwrap().get_package(PackageId(0)) {
                if let Some(s) = ctx.symbols.read().unwrap().symbol_name(sym_id) {
                    if pkg.find_external(s).is_some() {
                        return Ok(arg);
                    }
                }
            }

            return Err(ControlSignal::Error(format!(
                "Variable '{:?}' is not bound",
                ctx.symbols
                    .read()
                    .unwrap()
                    .symbol_name(sym_id)
                    .unwrap_or("?")
            )));
        } else {
            Err(ControlSignal::Error(
                "Argument to SYMBOL-VALUE must be a symbol".to_string(),
            ))
        }
    } else {
        Err(ControlSignal::Error(
            "SYMBOL-VALUE requires 1 argument".to_string(),
        ))
    }
}

#[derive(Clone, Copy, Debug)]
struct AssocOptions {
    test: Option<NodeId>,
    test_not: Option<NodeId>,
    key: Option<NodeId>,
}

fn parse_assoc_kwargs(
    proc: &Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
    name: &str,
) -> Result<AssocOptions, ControlSignal> {
    let mut options = AssocOptions {
        test: None,
        test_not: None,
        key: None,
    };

    if args.is_empty() {
        return Ok(options);
    }

    if args.len() % 2 != 0 {
        return Err(ControlSignal::Error(format!(
            "{name}: odd number of keyword arguments"
        )));
    }

    let syms = ctx.symbols.read().unwrap();
    let keyword_pkg = syms.get_package(PackageId(0));
    let kw_test = keyword_pkg.and_then(|p| p.find_external("TEST"));
    let kw_test_not = keyword_pkg.and_then(|p| p.find_external("TEST-NOT"));
    let kw_key = keyword_pkg.and_then(|p| p.find_external("KEY"));
    let kw_allow_other_keys = keyword_pkg.and_then(|p| p.find_external("ALLOW-OTHER-KEYS"));

    let mut allow_other_keys = false;
    let mut unknown = false;

    for pair in args.chunks(2) {
        let key_node = pair[0];
        let val_node = pair[1];
        let key_sym = node_to_symbol(proc, key_node).ok_or_else(|| {
            ControlSignal::Error(format!("{name}: keyword must be a symbol"))
        })?;

        if Some(key_sym) == kw_test {
            if options.test.is_none() {
                options.test = Some(val_node);
            }
            continue;
        }
        if Some(key_sym) == kw_test_not {
            if options.test_not.is_none() {
                options.test_not = Some(val_node);
            }
            continue;
        }
        if Some(key_sym) == kw_key {
            if options.key.is_none() {
                options.key = Some(val_node);
            }
            continue;
        }
        if Some(key_sym) == kw_allow_other_keys {
            if !allow_other_keys {
                allow_other_keys = !node_is_nil(proc, val_node);
            }
            continue;
        }

        unknown = true;
    }

    if unknown && !allow_other_keys {
        return Err(ControlSignal::Error(format!(
            "{name}: invalid keyword argument"
        )));
    }

    if options.test.is_some() && options.test_not.is_some() {
        return Err(ControlSignal::Error(format!(
            "{name}: cannot supply both :test and :test-not"
        )));
    }

    Ok(options)
}

fn assoc_search(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    item: NodeId,
    list: NodeId,
    options: AssocOptions,
    use_cdr: bool,
    name: &str,
) -> EvalResult {
    let mut cur = list;

    loop {
        match proc.arena.inner.get_unchecked(cur) {
            Node::Leaf(OpaqueValue::Nil) => return Ok(proc.make_nil()),
            Node::Fork(car, cdr) => {
                let entry = *car;
                cur = *cdr;
                match proc.arena.inner.get_unchecked(entry) {
                    Node::Leaf(OpaqueValue::Nil) => continue,
                    Node::Fork(pair_car, pair_cdr) => {
                        let value = if use_cdr { *pair_cdr } else { *pair_car };
                        let key_val = match options.key {
                            Some(k) if !node_is_nil(proc, k) => {
                                call_function_node(proc, ctx, k, &[value])?
                            }
                            _ => value,
                        };

                        let matched = if let Some(test_fn) = options.test {
                            let res = call_function_node(proc, ctx, test_fn, &[item, key_val])?;
                            !node_is_nil(proc, res)
                        } else if let Some(test_not_fn) = options.test_not {
                            let res =
                                call_function_node(proc, ctx, test_not_fn, &[item, key_val])?;
                            node_is_nil(proc, res)
                        } else {
                            let res = prim_eql(proc, ctx, &[item, key_val])?;
                            !node_is_nil(proc, res)
                        };

                        if matched {
                            return Ok(entry);
                        }
                    }
                    _ => {
                        return Err(ControlSignal::Error(format!(
                            "{name}: list element is not a cons"
                        )))
                    }
                }
            }
            _ => {
                return Err(ControlSignal::Error(format!(
                    "{name}: requires a proper list"
                )))
            }
        }
    }
}

fn prim_assoc(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return err_helper("ASSOC: requires item and list");
    }
    let item = args[0];
    let list = args[1];
    let options = parse_assoc_kwargs(proc, ctx, &args[2..], "ASSOC")?;
    assoc_search(proc, ctx, item, list, options, false, "ASSOC")
}

fn prim_rassoc(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return err_helper("RASSOC: requires item and list");
    }
    let item = args[0];
    let list = args[1];
    let options = parse_assoc_kwargs(proc, ctx, &args[2..], "RASSOC")?;
    assoc_search(proc, ctx, item, list, options, true, "RASSOC")
}

fn bigint_to_node(proc: &mut crate::process::Process, val: &BigInt) -> NodeId {
    if let Some(i) = val.to_i64() {
        proc.make_integer(i)
    } else {
        proc.arena.inner.alloc(Node::Leaf(OpaqueValue::BigInt(val.clone())))
    }
}

fn read_counter(proc: &crate::process::Process, sym_id: SymbolId) -> BigInt {
    if let Some(val_node) = proc.get_value(sym_id) {
        match extract_number(&proc.arena.inner, val_node) {
            NumVal::Int(n) => BigInt::from(n),
            NumVal::Big(b) => b,
            _ => BigInt::from(0),
        }
    } else {
        BigInt::from(0)
    }
}

fn write_counter(proc: &mut crate::process::Process, sym_id: SymbolId, val: BigInt) {
    let node = bigint_to_node(proc, &val);
    proc.set_value(sym_id, node);
}

fn parse_unsigned_integer(
    proc: &crate::process::Process,
    node: NodeId,
) -> Result<BigInt, ControlSignal> {
    match extract_number(&proc.arena.inner, node) {
        NumVal::Int(n) if n >= 0 => Ok(BigInt::from(n)),
        NumVal::Big(b) if !b.is_negative() => Ok(b),
        _ => Err(ControlSignal::Error(
            "Expected non-negative integer".to_string(),
        )),
    }
}

fn prim_gensym(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() > 1 {
        return err_helper("GENSYM accepts at most one argument");
    }

    let counter_sym = ctx
        .symbols
        .write()
        .unwrap()
        .intern_in("*GENSYM-COUNTER*", crate::symbol::PackageId(1));

    let (prefix, use_counter, explicit_counter) = if let Some(&arg) = args.first() {
        match proc.arena.inner.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::String(s)) => (s.clone(), true, None),
            _ => {
                let n = parse_unsigned_integer(proc, arg)?;
                ("G".to_string(), false, Some(n))
            }
        }
    } else {
        ("G".to_string(), true, None)
    };

    let counter_val = if let Some(explicit) = explicit_counter {
        explicit
    } else {
        read_counter(proc, counter_sym)
    };

    let name = format!("{}{}", prefix, counter_val);
    let sym_id = ctx.symbols.write().unwrap().make_symbol(&name);

    if use_counter {
        let next = &counter_val + BigInt::from(1);
        write_counter(proc, counter_sym, next);
    }

    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0))))
}

fn prim_gentemp(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() > 2 {
        return err_helper("GENTEMP accepts at most two arguments");
    }

    let prefix = if let Some(&arg) = args.first() {
        string_from_designator(proc, ctx, arg)
            .ok_or_else(|| ControlSignal::Error("GENTEMP: invalid prefix".into()))?
    } else {
        "T".to_string()
    };

    let pkg_id = if args.len() == 2 {
        package_id_from_designator(proc, ctx, args[1])?
    } else {
        current_package_id(proc, ctx)
    };

    let counter_sym = ctx
        .symbols
        .write()
        .unwrap()
        .intern_in("*GENTEMP-COUNTER*", crate::symbol::PackageId(1));

    let mut counter = read_counter(proc, counter_sym);
    loop {
        let name = format!("{}{}", prefix, counter);
        let found = ctx
            .symbols
            .read()
            .unwrap()
            .find_symbol_in_package(pkg_id, &name)
            .is_some();
        if !found {
            let sym_id = ctx
                .symbols
                .write()
                .unwrap()
                .intern_in_with_status(&name, pkg_id)
                .0;
            let next = &counter + BigInt::from(1);
            write_counter(proc, counter_sym, next);
            return Ok(proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0))));
        }
        counter = &counter + BigInt::from(1);
    }
}

fn prim_make_symbol(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Node::Leaf(OpaqueValue::String(name)) = proc.arena.inner.get_unchecked(arg) {
            let sym_id = ctx.symbols.write().unwrap().make_symbol(name);
            Ok(proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0))))
        } else {
            err_helper("MAKE-SYMBOL: Argument must be a string")
        }
    } else {
        err_helper("MAKE-SYMBOL: Too few arguments")
    }
}

fn prim_intern(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 2 {
        return err_helper("INTERN requires a string and optional package");
    }
    let name = string_from_sequence(proc, ctx, args[0])
        .ok_or_else(|| ControlSignal::Error("INTERN: name must be a string designator".into()))?;
    let pkg_id = if args.len() == 2 {
        package_id_from_designator(proc, ctx, args[1])?
    } else {
        current_package_id(proc, ctx)
    };

    let (sym_id, status) = ctx.symbols.write().unwrap().intern_in_with_status(&name, pkg_id);
    let sym_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0)));
    let status_node = match status {
        None => proc.make_nil(),
        Some(crate::symbol::FindSymbolStatus::Internal) => {
            let id = ctx.symbols.write().unwrap().intern_in("INTERNAL", PackageId(0));
            proc.arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(id.0)))
        }
        Some(crate::symbol::FindSymbolStatus::External) => {
            let id = ctx.symbols.write().unwrap().intern_in("EXTERNAL", PackageId(0));
            proc.arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(id.0)))
        }
        Some(crate::symbol::FindSymbolStatus::Inherited) => {
            let id = ctx.symbols.write().unwrap().intern_in("INHERITED", PackageId(0));
            proc.arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(id.0)))
        }
    };
    let primary = set_multiple_values(proc, vec![sym_node, status_node]);
    Ok(primary)
}

fn prim_find_symbol(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 2 {
        return err_helper("FIND-SYMBOL requires a string and optional package");
    }
    let name = string_from_sequence(proc, ctx, args[0])
        .ok_or_else(|| ControlSignal::Error("FIND-SYMBOL: name must be a string designator".into()))?;
    let pkg_id = if args.len() == 2 {
        package_id_from_designator(proc, ctx, args[1])?
    } else {
        current_package_id(proc, ctx)
    };

    if let Some((sym_id, status)) = ctx.symbols.read().unwrap().find_symbol_in_package(pkg_id, &name) {
        let sym_node = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0)));
        let status_node = match status {
            crate::symbol::FindSymbolStatus::Internal => {
                let id = ctx.symbols.write().unwrap().intern_in("INTERNAL", PackageId(0));
                proc.arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Symbol(id.0)))
            }
            crate::symbol::FindSymbolStatus::External => {
                let id = ctx.symbols.write().unwrap().intern_in("EXTERNAL", PackageId(0));
                proc.arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Symbol(id.0)))
            }
            crate::symbol::FindSymbolStatus::Inherited => {
                let id = ctx.symbols.write().unwrap().intern_in("INHERITED", PackageId(0));
                proc.arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Symbol(id.0)))
            }
        };
        let primary = set_multiple_values(proc, vec![sym_node, status_node]);
        return Ok(primary);
    }

    let primary = set_multiple_values(proc, vec![proc.make_nil(), proc.make_nil()]);
    Ok(primary)
}

fn prim_find_all_symbols(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("FIND-ALL-SYMBOLS requires exactly 1 argument");
    }
    let name = string_from_sequence(proc, ctx, args[0])
        .ok_or_else(|| ControlSignal::Error("FIND-ALL-SYMBOLS: name must be a string designator".into()))?;

    let symbols = ctx.symbols.read().unwrap();
    let mut seen = crate::fastmap::HashSet::default();
    let mut out = Vec::new();
    for idx in 0..symbols.package_count() {
        let pkg_id = crate::symbol::PackageId(idx as u32);
        if let Some(pkg) = symbols.get_package(pkg_id) {
            if pkg.is_deleted() {
                continue;
            }
        }
        if let Some((sym_id, _)) = symbols.find_symbol_in_package(pkg_id, &name) {
            if seen.insert(sym_id.0) {
                out.push(proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0))));
            }
        }
    }
    Ok(proc.make_list(&out))
}

fn symbols_from_arg(
    proc: &crate::process::Process,
    arg: NodeId,
) -> Result<Vec<SymbolId>, ControlSignal> {
    match proc.arena.inner.get_unchecked(arg) {
        Node::Leaf(OpaqueValue::Nil) => Ok(Vec::new()),
        Node::Leaf(OpaqueValue::Symbol(id)) => Ok(vec![SymbolId(*id)]),
        Node::Fork(_, _) => {
            let items = list_to_vec_opt(proc, arg)
                .ok_or_else(|| ControlSignal::Error("Expected list of symbols".into()))?;
            let mut out = Vec::new();
            for item in items {
                if let Some(sym) = node_to_symbol(proc, item) {
                    out.push(sym);
                } else {
                    return Err(ControlSignal::Error(
                        "Expected symbol in list".to_string(),
                    ));
                }
            }
            Ok(out)
        }
        _ => Err(ControlSignal::Error("Expected symbol".into())),
    }
}

fn names_from_arg(
    proc: &crate::process::Process,
    ctx: &crate::context::GlobalContext,
    arg: NodeId,
) -> Result<Vec<String>, ControlSignal> {
    match proc.arena.inner.get_unchecked(arg) {
        Node::Leaf(OpaqueValue::Nil) => Ok(Vec::new()),
        Node::Fork(_, _) => {
            let items = list_to_vec_opt(proc, arg)
                .ok_or_else(|| ControlSignal::Error("Expected list of names".into()))?;
            let mut out = Vec::new();
            for item in items {
                let s = string_from_sequence(proc, ctx, item).ok_or_else(|| {
                    ControlSignal::Error("Expected string designator".to_string())
                })?;
                out.push(s);
            }
            Ok(out)
        }
        _ => {
            let s = string_from_sequence(proc, ctx, arg)
                .ok_or_else(|| ControlSignal::Error("Expected string designator".into()))?;
            Ok(vec![s])
        }
    }
}

fn packages_from_arg(
    proc: &crate::process::Process,
    ctx: &crate::context::GlobalContext,
    arg: NodeId,
) -> Result<Vec<PackageId>, ControlSignal> {
    match proc.arena.inner.get_unchecked(arg) {
        Node::Leaf(OpaqueValue::Nil) => Ok(Vec::new()),
        Node::Fork(_, _) => {
            let items = list_to_vec_opt(proc, arg)
                .ok_or_else(|| ControlSignal::Error("Expected list of packages".into()))?;
            let mut out = Vec::new();
            for item in items {
                out.push(package_id_from_designator(proc, ctx, item)?);
            }
            Ok(out)
        }
        _ => Ok(vec![package_id_from_designator(proc, ctx, arg)?]),
    }
}

fn prim_export(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 2 {
        return err_helper("EXPORT requires a symbol (or list) and optional package");
    }
    let symbols = symbols_from_arg(proc, args[0])?;
    let pkg_id = if args.len() == 2 {
        package_id_from_designator(proc, ctx, args[1])?
    } else {
        current_package_id(proc, ctx)
    };

    for sym in symbols {
        let name = ctx
            .symbols
            .read()
            .unwrap()
            .symbol_name(sym)
            .ok_or_else(|| ControlSignal::Error("Unknown symbol".into()))?
            .to_string();

        let (existing, _) = ctx
            .symbols
            .read()
            .unwrap()
            .find_symbol_in_package(pkg_id, &name)
            .ok_or_else(|| ControlSignal::Error("EXPORT: symbol not accessible in package".into()))?;
        if existing != sym {
            return Err(ControlSignal::Error(
                "EXPORT: name conflict in package".to_string(),
            ));
        }

        // Conflict check against used-by packages
        let used_by = ctx
            .symbols
            .read()
            .unwrap()
            .get_package(pkg_id)
            .map(|p| p.used_by_list().to_vec())
            .unwrap_or_default();
        for user_id in used_by {
            if let Some((other, _)) = ctx
                .symbols
                .read()
                .unwrap()
                .find_symbol_in_package(user_id, &name)
            {
                if other != sym {
                    return Err(ControlSignal::Error(
                        "EXPORT: name conflict in using package".to_string(),
                    ));
                }
            }
        }

        ctx.symbols
            .write()
            .unwrap()
            .export_in_package(pkg_id, sym)
            .map_err(ControlSignal::Error)?;
    }

    Ok(proc.make_t(ctx))
}

fn prim_unexport(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 2 {
        return err_helper("UNEXPORT requires a symbol (or list) and optional package");
    }
    let symbols = symbols_from_arg(proc, args[0])?;
    let pkg_id = if args.len() == 2 {
        package_id_from_designator(proc, ctx, args[1])?
    } else {
        current_package_id(proc, ctx)
    };

    for sym in symbols {
        ctx.symbols
            .write()
            .unwrap()
            .unexport_in_package(pkg_id, sym)
            .map_err(ControlSignal::Error)?;
    }

    Ok(proc.make_t(ctx))
}

fn prim_import(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 2 {
        return err_helper("IMPORT requires a symbol (or list) and optional package");
    }
    let symbols = symbols_from_arg(proc, args[0])?;
    let pkg_id = if args.len() == 2 {
        package_id_from_designator(proc, ctx, args[1])?
    } else {
        current_package_id(proc, ctx)
    };

    for sym in symbols {
        let name = ctx
            .symbols
            .read()
            .unwrap()
            .symbol_name(sym)
            .ok_or_else(|| ControlSignal::Error("Unknown symbol".into()))?
            .to_string();
        if let Some((existing, _)) = ctx
            .symbols
            .read()
            .unwrap()
            .find_symbol_in_package(pkg_id, &name)
        {
            if existing != sym {
                return Err(ControlSignal::Error("IMPORT: name conflict".into()));
            }
            continue;
        }
        ctx.symbols
            .write()
            .unwrap()
            .import_into_package(pkg_id, sym)
            .map_err(ControlSignal::Error)?;
    }

    Ok(proc.make_t(ctx))
}

fn prim_shadow(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 2 {
        return err_helper("SHADOW requires a name (or list) and optional package");
    }
    let names = names_from_arg(proc, ctx, args[0])?;
    let pkg_id = if args.len() == 2 {
        package_id_from_designator(proc, ctx, args[1])?
    } else {
        current_package_id(proc, ctx)
    };

    for name in names {
        let maybe = ctx
            .symbols
            .read()
            .unwrap()
            .find_symbol_in_package(pkg_id, &name);
        let sym_id = match maybe {
            Some((sym, crate::symbol::FindSymbolStatus::Internal))
            | Some((sym, crate::symbol::FindSymbolStatus::External)) => sym,
            _ => ctx
                .symbols
                .write()
                .unwrap()
                .create_symbol_in_package(&name, pkg_id),
        };
        ctx.symbols
            .write()
            .unwrap()
            .add_shadowing_symbol(pkg_id, sym_id)
            .map_err(ControlSignal::Error)?;
    }

    Ok(proc.make_t(ctx))
}

fn prim_shadowing_import(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 2 {
        return err_helper("SHADOWING-IMPORT requires a symbol (or list) and optional package");
    }
    let symbols = symbols_from_arg(proc, args[0])?;
    let pkg_id = if args.len() == 2 {
        package_id_from_designator(proc, ctx, args[1])?
    } else {
        current_package_id(proc, ctx)
    };

    for sym in symbols {
        let name = ctx
            .symbols
            .read()
            .unwrap()
            .symbol_name(sym)
            .ok_or_else(|| ControlSignal::Error("Unknown symbol".into()))?
            .to_string();

        if let Some((existing, _)) = ctx
            .symbols
            .read()
            .unwrap()
            .find_symbol_in_package(pkg_id, &name)
        {
            if existing != sym {
                ctx.symbols
                    .write()
                    .unwrap()
                    .unintern_from_package(pkg_id, existing)
                    .map_err(ControlSignal::Error)?;
            }
        }

        ctx.symbols
            .write()
            .unwrap()
            .import_into_package(pkg_id, sym)
            .map_err(ControlSignal::Error)?;
        ctx.symbols
            .write()
            .unwrap()
            .add_shadowing_symbol(pkg_id, sym)
            .map_err(ControlSignal::Error)?;
    }

    Ok(proc.make_t(ctx))
}

fn prim_unintern(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 2 {
        return err_helper("UNINTERN requires a symbol and optional package");
    }
    let symbols = symbols_from_arg(proc, args[0])?;
    let pkg_id = if args.len() == 2 {
        package_id_from_designator(proc, ctx, args[1])?
    } else {
        current_package_id(proc, ctx)
    };

    let mut removed_any = false;
    for sym in symbols {
        let removed = ctx
            .symbols
            .write()
            .unwrap()
            .unintern_from_package(pkg_id, sym)
            .map_err(ControlSignal::Error)?;
        if removed {
            removed_any = true;
        }
    }
    if removed_any {
        Ok(proc.make_t(ctx))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_use_package(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 2 {
        return err_helper("USE-PACKAGE requires a package (or list) and optional package");
    }
    let use_pkgs = packages_from_arg(proc, ctx, args[0])?;
    let pkg_id = if args.len() == 2 {
        package_id_from_designator(proc, ctx, args[1])?
    } else {
        current_package_id(proc, ctx)
    };

    for use_pkg in use_pkgs {
        ctx.symbols
            .write()
            .unwrap()
            .use_package(pkg_id, use_pkg)
            .map_err(ControlSignal::Error)?;
    }
    Ok(proc.make_t(ctx))
}

fn prim_unuse_package(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 2 {
        return err_helper("UNUSE-PACKAGE requires a package (or list) and optional package");
    }
    let use_pkgs = packages_from_arg(proc, ctx, args[0])?;
    let pkg_id = if args.len() == 2 {
        package_id_from_designator(proc, ctx, args[1])?
    } else {
        current_package_id(proc, ctx)
    };

    for use_pkg in use_pkgs {
        ctx.symbols
            .write()
            .unwrap()
            .unuse_package(pkg_id, use_pkg)
            .map_err(ControlSignal::Error)?;
    }
    Ok(proc.make_t(ctx))
}

fn prim_make_package(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return err_helper("MAKE-PACKAGE requires at least 1 argument");
    }
    let name = string_from_sequence(proc, ctx, args[0])
        .ok_or_else(|| ControlSignal::Error("MAKE-PACKAGE: invalid name".into()))?;

    let mut nicknames: Vec<String> = Vec::new();
    let mut use_list: Option<Vec<PackageId>> = None;
    let mut documentation: Option<String> = None;

    let mut i = 1;
    while i + 1 < args.len() {
        let key = args[i];
        let val = args[i + 1];
        if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(key) {
            let name_kw = ctx
                .symbols
                .read()
                .unwrap()
                .symbol_name(SymbolId(*id))
                .unwrap_or("")
                .to_uppercase();
            match name_kw.as_str() {
                "NICKNAMES" => {
                    nicknames = names_from_arg(proc, ctx, val)?;
                }
                "USE" => {
                    use_list = Some(packages_from_arg(proc, ctx, val)?);
                }
                "DOCUMENTATION" => {
                    if let Node::Leaf(OpaqueValue::String(s)) = proc.arena.inner.get_unchecked(val) {
                        documentation = Some(s.clone());
                    }
                }
                _ => {}
            }
        }
        i += 2;
    }

    let use_list = use_list.unwrap_or_default();
    let pkg_id = ctx
        .symbols
        .write()
        .unwrap()
        .make_package(&name, nicknames, use_list, documentation)
        .map_err(|e| ControlSignal::Error(format!("MAKE-PACKAGE: {}", e)))?;

    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Package(pkg_id.0))))
}

fn prim_delete_package(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("DELETE-PACKAGE requires exactly 1 argument");
    }
    let pkg_id = package_id_from_designator(proc, ctx, args[0])?;
    let deleted = ctx
        .symbols
        .write()
        .unwrap()
        .delete_package(pkg_id)
        .map_err(|e| ControlSignal::Error(format!("DELETE-PACKAGE: {}", e)))?;
    if deleted {
        Ok(proc.make_t(ctx))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_rename_package(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 || args.len() > 3 {
        return err_helper("RENAME-PACKAGE requires 2 or 3 arguments");
    }
    let pkg_id = package_id_from_designator(proc, ctx, args[0])?;
    let new_name = string_from_sequence(proc, ctx, args[1])
        .ok_or_else(|| ControlSignal::Error("RENAME-PACKAGE: invalid name".into()))?;
    let new_nicknames = if args.len() == 3 {
        Some(names_from_arg(proc, ctx, args[2])?)
    } else {
        None
    };
    ctx.symbols
        .write()
        .unwrap()
        .rename_package(pkg_id, &new_name, new_nicknames)
        .map_err(|e| ControlSignal::Error(format!("RENAME-PACKAGE: {}", e)))?;
    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Package(pkg_id.0))))
}

fn prim_packagep(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Node::Leaf(OpaqueValue::Package(id)) = proc.arena.inner.get_unchecked(arg) {
            let pkg_id = crate::symbol::PackageId(*id);
            if ctx.symbols.read().unwrap().get_package(pkg_id).is_some() {
                return Ok(proc.make_t(ctx));
            }
        }
    }
    Ok(proc.make_nil())
}

fn prim_package_nicknames(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Some(pkg_id) = package_id_from_designator_opt(proc, ctx, arg) {
            if let Some(pkg) = ctx.symbols.read().unwrap().get_package(pkg_id) {
                if pkg.is_deleted() {
                    return Ok(proc.make_nil());
                }
                let mut nodes = Vec::new();
                for nick in &pkg.nicknames {
                    nodes.push(
                        proc.arena
                            .inner
                            .alloc(Node::Leaf(OpaqueValue::String(nick.clone()))),
                    );
                }
                return Ok(proc.make_list(&nodes));
            }
        }
    }
    Ok(proc.make_nil())
}

fn prim_package_use_list(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Some(pkg_id) = package_id_from_designator_opt(proc, ctx, arg) {
            if let Some(pkg) = ctx.symbols.read().unwrap().get_package(pkg_id) {
                if pkg.is_deleted() {
                    return Ok(proc.make_nil());
                }
                let mut nodes = Vec::new();
                for used in pkg.use_list() {
                    nodes.push(proc
                        .arena
                        .inner
                        .alloc(Node::Leaf(OpaqueValue::Package(used.0))));
                }
                return Ok(proc.make_list(&nodes));
            }
        }
    }
    Ok(proc.make_nil())
}

fn prim_package_used_by_list(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Some(pkg_id) = package_id_from_designator_opt(proc, ctx, arg) {
            if let Some(pkg) = ctx.symbols.read().unwrap().get_package(pkg_id) {
                if pkg.is_deleted() {
                    return Ok(proc.make_nil());
                }
                let mut nodes = Vec::new();
                for used_by in pkg.used_by_list() {
                    nodes.push(proc
                        .arena
                        .inner
                        .alloc(Node::Leaf(OpaqueValue::Package(used_by.0))));
                }
                return Ok(proc.make_list(&nodes));
            }
        }
    }
    Ok(proc.make_nil())
}

fn prim_package_shadowing_symbols(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Some(pkg_id) = package_id_from_designator_opt(proc, ctx, arg) {
            if let Some(pkg) = ctx.symbols.read().unwrap().get_package(pkg_id) {
                if pkg.is_deleted() {
                    return Ok(proc.make_nil());
                }
                let mut nodes = Vec::new();
                for sym in pkg.shadowing_symbols() {
                    nodes.push(proc
                        .arena
                        .inner
                        .alloc(Node::Leaf(OpaqueValue::Symbol(sym.0))));
                }
                return Ok(proc.make_list(&nodes));
            }
        }
    }
    Ok(proc.make_nil())
}

fn prim_sys_defpackage(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return err_helper("SYS-DEFPACKAGE requires name and options list");
    }

    let name = string_from_sequence(proc, ctx, args[0])
        .ok_or_else(|| ControlSignal::Error("DEFPACKAGE: invalid name".into()))?;

    let debug = std::env::var("TREECL_DEBUG_DEFPACKAGE").is_ok();
    if debug {
        eprintln!("DEFPACKAGE start: {}", name);
    }

    let options = list_to_vec_opt(proc, args[1])
        .ok_or_else(|| ControlSignal::Error("DEFPACKAGE: invalid options".into()))?;

    let mut nicknames: Vec<String> = Vec::new();
    let mut use_specs: Option<Vec<PackageId>> = None;
    let mut shadow: Vec<String> = Vec::new();
    let mut shadowing_import_from: Vec<(PackageId, Vec<String>)> = Vec::new();
    let mut import_from: Vec<(PackageId, Vec<String>)> = Vec::new();
    let mut export: Vec<String> = Vec::new();
    let mut intern: Vec<String> = Vec::new();
    let mut documentation: Option<String> = None;

    for opt in options {
        let opt_list = list_to_vec_opt(proc, opt)
            .ok_or_else(|| ControlSignal::Error("DEFPACKAGE: option must be a list".into()))?;
        if opt_list.is_empty() {
            continue;
        }
        let key = opt_list[0];
        let key_name = if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(key) {
            ctx.symbols
                .read()
                .unwrap()
                .symbol_name(SymbolId(*id))
                .unwrap_or("")
                .to_uppercase()
        } else {
            return err_helper("DEFPACKAGE: invalid option keyword");
        };
        let args_list = &opt_list[1..];

        match key_name.as_str() {
            "NICKNAMES" => {
                for arg in args_list {
                    let n = string_from_sequence(proc, ctx, *arg)
                        .ok_or_else(|| ControlSignal::Error("DEFPACKAGE: invalid nickname".into()))?;
                    nicknames.push(n);
                }
            }
            "USE" => {
                let mut pkgs = Vec::new();
                for arg in args_list {
                    pkgs.push(package_id_from_designator(proc, ctx, *arg)?);
                }
                if let Some(existing) = &mut use_specs {
                    existing.extend(pkgs);
                } else {
                    use_specs = Some(pkgs);
                }
            }
            "SHADOW" => {
                for arg in args_list {
                    let n = string_from_sequence(proc, ctx, *arg)
                        .ok_or_else(|| ControlSignal::Error("DEFPACKAGE: invalid shadow name".into()))?;
                    shadow.push(n);
                }
            }
            "SHADOWING-IMPORT-FROM" => {
                if args_list.is_empty() {
                    continue;
                }
                let from_pkg = package_id_from_designator(proc, ctx, args_list[0])?;
                let mut names = Vec::new();
                for arg in &args_list[1..] {
                    let n = string_from_sequence(proc, ctx, *arg)
                        .ok_or_else(|| ControlSignal::Error("DEFPACKAGE: invalid shadowing import name".into()))?;
                    names.push(n);
                }
                shadowing_import_from.push((from_pkg, names));
            }
            "IMPORT-FROM" => {
                if args_list.is_empty() {
                    continue;
                }
                let from_pkg = package_id_from_designator(proc, ctx, args_list[0])?;
                let mut names = Vec::new();
                for arg in &args_list[1..] {
                    let n = string_from_sequence(proc, ctx, *arg)
                        .ok_or_else(|| ControlSignal::Error("DEFPACKAGE: invalid import name".into()))?;
                    names.push(n);
                }
                import_from.push((from_pkg, names));
            }
            "EXPORT" => {
                for arg in args_list {
                    let n = string_from_sequence(proc, ctx, *arg)
                        .ok_or_else(|| ControlSignal::Error("DEFPACKAGE: invalid export name".into()))?;
                    export.push(n);
                }
            }
            "INTERN" => {
                for arg in args_list {
                    let n = string_from_sequence(proc, ctx, *arg)
                        .ok_or_else(|| ControlSignal::Error("DEFPACKAGE: invalid intern name".into()))?;
                    intern.push(n);
                }
            }
            "DOCUMENTATION" => {
                if let Some(arg) = args_list.first() {
                    if let Node::Leaf(OpaqueValue::String(s)) = proc.arena.inner.get_unchecked(*arg)
                    {
                        documentation = Some(s.clone());
                    }
                }
            }
            _ => {}
        }
    }

    if debug {
        eprintln!("DEFPACKAGE find_package: {}", name);
    }
    let existing_pkg = {
        let syms = ctx.symbols.read().unwrap();
        syms.find_package(&name)
    };
    let pkg_id = if let Some(existing) = existing_pkg {
        if debug {
            eprintln!("DEFPACKAGE existing package: {}", name);
        }
        if !nicknames.is_empty() {
            ctx.symbols
                .write()
                .unwrap()
                .rename_package(existing, &name, Some(nicknames.clone()))
                .map_err(ControlSignal::Error)?;
        }
        existing
    } else {
        if debug {
            eprintln!("DEFPACKAGE make_package: {}", name);
        }
        ctx.symbols
            .write()
            .unwrap()
            .make_package(&name, nicknames.clone(), Vec::new(), documentation.clone())
            .map_err(|e| ControlSignal::Error(format!("DEFPACKAGE: {}", e)))?
    };
    if debug {
        eprintln!("DEFPACKAGE package ready: {}", name);
    }

    // Documentation update
    if let Some(pkg) = ctx.symbols.write().unwrap().get_package_mut(pkg_id) {
        pkg.set_documentation(documentation);
    }

    // Shadow
    if !shadow.is_empty() {
        for name in shadow {
            let maybe = ctx
                .symbols
                .read()
                .unwrap()
                .find_symbol_in_package(pkg_id, &name);
            let sym_id = match maybe {
                Some((sym, crate::symbol::FindSymbolStatus::Internal))
                | Some((sym, crate::symbol::FindSymbolStatus::External)) => sym,
                _ => ctx
                    .symbols
                    .write()
                    .unwrap()
                    .create_symbol_in_package(&name, pkg_id),
            };
            ctx.symbols
            .write()
            .unwrap()
            .add_shadowing_symbol(pkg_id, sym_id)
            .map_err(ControlSignal::Error)?;
        }
    }
    if debug {
        eprintln!("DEFPACKAGE shadow done: {}", name);
    }

    // Shadowing-import-from
    for (from_pkg, names) in shadowing_import_from {
        for name in names {
            let sym_id = ctx
                .symbols
                .read()
                .unwrap()
                .find_symbol_in_package(from_pkg, &name)
                .map(|(s, _)| s)
                .ok_or_else(|| ControlSignal::Error("DEFPACKAGE: symbol not found for shadowing-import".into()))?;
            // Remove conflicts and import
            let existing = {
                let syms = ctx.symbols.read().unwrap();
                syms.find_symbol_in_package(pkg_id, &name).map(|(s, _)| s)
            };
            if let Some(existing) = existing {
                if existing != sym_id {
                    ctx.symbols
                        .write()
                        .unwrap()
                        .unintern_from_package(pkg_id, existing)
                        .map_err(ControlSignal::Error)?;
                }
            }
            ctx.symbols
                .write()
                .unwrap()
                .import_into_package(pkg_id, sym_id)
                .map_err(ControlSignal::Error)?;
            ctx.symbols
                .write()
                .unwrap()
                .add_shadowing_symbol(pkg_id, sym_id)
                .map_err(ControlSignal::Error)?;
        }
    }
    if debug {
        eprintln!("DEFPACKAGE shadowing-import done: {}", name);
    }

    // Reset use-list if specified (after shadow/shadowing-import to avoid conflicts)
    if let Some(use_pkgs) = use_specs {
        let current_use = ctx
            .symbols
            .read()
            .unwrap()
            .get_package(pkg_id)
            .map(|p| p.use_list().to_vec())
            .unwrap_or_default();
        for used in current_use {
            let _ = ctx.symbols.write().unwrap().unuse_package(pkg_id, used);
        }
        for used in use_pkgs {
            ctx.symbols
                .write()
                .unwrap()
                .use_package(pkg_id, used)
                .map_err(ControlSignal::Error)?;
        }
    }
    if debug {
        eprintln!("DEFPACKAGE use list set: {}", name);
    }

    // Import-from
    for (from_pkg, names) in import_from {
        for name in names {
            let sym_id = ctx
                .symbols
                .read()
                .unwrap()
                .find_symbol_in_package(from_pkg, &name)
                .map(|(s, _)| s)
                .ok_or_else(|| ControlSignal::Error("DEFPACKAGE: symbol not found for import".into()))?;
            if let Some((existing, _)) = ctx
                .symbols
                .read()
                .unwrap()
                .find_symbol_in_package(pkg_id, &name)
            {
                if existing != sym_id {
                    return Err(ControlSignal::Error(
                        "DEFPACKAGE: import name conflict".into(),
                    ));
                }
                continue;
            }
            ctx.symbols
                .write()
                .unwrap()
                .import_into_package(pkg_id, sym_id)
                .map_err(ControlSignal::Error)?;
        }
    }
    if debug {
        eprintln!("DEFPACKAGE import done: {}", name);
    }

    // Intern
    for name in intern {
        ctx.symbols.write().unwrap().intern_in_with_status(&name, pkg_id);
    }
    if debug {
        eprintln!("DEFPACKAGE intern done: {}", name);
    }

    // Export
    for name in export {
        let sym_id = ctx
            .symbols
            .write()
            .unwrap()
            .intern_in_with_status(&name, pkg_id)
            .0;
        ctx.symbols
            .write()
            .unwrap()
            .export_in_package(pkg_id, sym_id)
            .map_err(ControlSignal::Error)?;
    }
    if debug {
        eprintln!("DEFPACKAGE export done: {}", name);
    }

    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Package(pkg_id.0))))
}

fn prim_sys_package_iterator_entries(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return err_helper("SYS-PACKAGE-ITERATOR-ENTRIES requires packages and types");
    }
    let pkgs = packages_from_arg(proc, ctx, args[0])?;
    let types = list_to_vec_opt(proc, args[1]).unwrap_or_default();

    let mut want_internal = false;
    let mut want_external = false;
    let mut want_inherited = false;
    for t in types {
        if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(t) {
            let name = ctx
                .symbols
                .read()
                .unwrap()
                .symbol_name(SymbolId(*id))
                .unwrap_or("")
                .to_uppercase();
            match name.as_str() {
                "INTERNAL" => want_internal = true,
                "EXTERNAL" => want_external = true,
                "INHERITED" => want_inherited = true,
                _ => {}
            }
        }
    }

    let (kw_internal, kw_external, kw_inherited) = {
        let mut syms = ctx.symbols.write().unwrap();
        (
            syms.intern_in("INTERNAL", PackageId(0)),
            syms.intern_in("EXTERNAL", PackageId(0)),
            syms.intern_in("INHERITED", PackageId(0)),
        )
    };
    let symbols = ctx.symbols.read().unwrap();
    let mut entries: Vec<NodeId> = Vec::new();
    for pkg_id in pkgs {
        let pkg = match symbols.get_package(pkg_id) {
            Some(p) if !p.is_deleted() => p,
            _ => continue,
        };

        if want_internal {
            for (_name, sym) in pkg.internal_symbols() {
                let sym_node = proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Symbol(sym.0)));
                let status_node = proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Symbol(kw_internal.0)));
                let pkg_node = proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Package(pkg_id.0)));
                let entry = proc.make_list(&[sym_node, status_node, pkg_node]);
                entries.push(entry);
            }
        }

        if want_external {
            for (_name, sym) in pkg.external_symbols() {
                let sym_node = proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Symbol(sym.0)));
                let status_node = proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Symbol(kw_external.0)));
                let pkg_node = proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Package(pkg_id.0)));
                let entry = proc.make_list(&[sym_node, status_node, pkg_node]);
                entries.push(entry);
            }
        }

        if want_inherited {
            let mut seen = crate::fastmap::HashSet::default();
            for used in pkg.use_list() {
                let used_pkg = match symbols.get_package(*used) {
                    Some(p) if !p.is_deleted() => p,
                    _ => continue,
                };
                for (name, sym) in used_pkg.external_symbols() {
                    if let Some((sym_id, crate::symbol::FindSymbolStatus::Inherited)) =
                        symbols.find_symbol_in_package(pkg_id, name)
                    {
                        if sym_id != sym {
                            continue;
                        }
                        if !seen.insert(sym_id.0) {
                            continue;
                        }
                        let sym_node = proc
                            .arena
                            .inner
                            .alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0)));
                        let status_node = proc
                            .arena
                            .inner
                            .alloc(Node::Leaf(OpaqueValue::Symbol(kw_inherited.0)));
                        let pkg_node = proc
                            .arena
                            .inner
                            .alloc(Node::Leaf(OpaqueValue::Package(pkg_id.0)));
                        let entry = proc.make_list(&[sym_node, status_node, pkg_node]);
                        entries.push(entry);
                    }
                }
            }
        }
    }

    Ok(proc.make_list(&entries))
}

// ============================================================================
// I/O Primitives
// ============================================================================

/// Get the current output stream from *STANDARD-OUTPUT*
fn get_current_output_stream(
    proc: &crate::process::Process,
    ctx: &crate::context::GlobalContext,
) -> crate::streams::StreamId {
    use crate::symbol::PackageId;

    // Look up *STANDARD-OUTPUT* symbol in COMMON-LISP package
    if let Some(pkg) = ctx.symbols.read().unwrap().get_package(PackageId(1)) {
        if let Some(sym) = pkg.find_symbol("*STANDARD-OUTPUT*") {
            // Check process dictionary for binding
            if let Some(bind) = proc.dictionary.get(&sym) {
                if let Some(val) = bind.value {
                    if let Node::Leaf(OpaqueValue::StreamHandle(id)) =
                        proc.arena.inner.get_unchecked(val)
                    {
                        return crate::streams::StreamId(*id);
                    }
                }
            }
        }
    }
    // Fallback to the fixed stdout (1)
    crate::streams::StreamId(1)
}

fn get_current_input_stream(
    proc: &crate::process::Process,
    ctx: &crate::context::GlobalContext,
) -> crate::streams::StreamId {
    use crate::symbol::PackageId;

    if let Some(pkg) = ctx.symbols.read().unwrap().get_package(PackageId(1)) {
        if let Some(sym) = pkg.find_symbol("*STANDARD-INPUT*") {
            if let Some(bind) = proc.dictionary.get(&sym) {
                if let Some(val) = bind.value {
                    if let Node::Leaf(OpaqueValue::StreamHandle(id)) =
                        proc.arena.inner.get_unchecked(val)
                    {
                        return crate::streams::StreamId(*id);
                    }
                }
            }
        }
    }
    crate::streams::StreamId(0)
}

fn get_terminal_io_stream(
    proc: &crate::process::Process,
    ctx: &crate::context::GlobalContext,
) -> Option<crate::streams::StreamId> {
    let sym = ctx
        .symbols
        .write()
        .unwrap()
        .intern_in("*TERMINAL-IO*", PackageId(1));
    if let Some(val) = proc.get_value(sym) {
        if let Node::Leaf(OpaqueValue::StreamHandle(id)) = proc.arena.inner.get_unchecked(val) {
            return Some(crate::streams::StreamId(*id));
        }
    }
    None
}

fn resolve_input_stream(
    proc: &crate::process::Process,
    ctx: &crate::context::GlobalContext,
    arg: Option<NodeId>,
) -> Result<crate::streams::StreamId, ControlSignal> {
    let stream_id = match arg {
        None => get_current_input_stream(proc, ctx),
        Some(node) => match proc.arena.inner.get_unchecked(node) {
            Node::Leaf(OpaqueValue::Nil) => get_current_input_stream(proc, ctx),
            Node::Leaf(OpaqueValue::Symbol(id))
                if crate::symbol::SymbolId(*id) == ctx.t_sym =>
            {
                get_terminal_io_stream(proc, ctx)
                    .ok_or_else(|| ControlSignal::Error("TERMINAL-IO not bound".into()))?
            }
            Node::Leaf(OpaqueValue::StreamHandle(id)) => crate::streams::StreamId(*id),
            _ => {
                return Err(ControlSignal::Error(
                    "Invalid input stream designator".into(),
                ))
            }
        },
    };

    Ok(stream_id)
}

fn resolve_input_stream_id(
    proc: &crate::process::Process,
    ctx: &crate::context::GlobalContext,
    stream_id: crate::streams::StreamId,
) -> Result<crate::streams::StreamId, ControlSignal> {
    use crate::streams::Stream;

    let mut current = stream_id;
    for _ in 0..8 {
        let next = match proc.streams.get(current) {
            Some(Stream::TwoWayStream { input, .. }) => Some(*input),
            Some(Stream::EchoStream { input, .. }) => Some(*input),
            Some(Stream::SynonymStream { symbol_id }) => {
                let sym = crate::symbol::SymbolId(*symbol_id);
                if let Some(val) = proc.get_value(sym) {
                    if let Node::Leaf(OpaqueValue::StreamHandle(id)) =
                        proc.arena.inner.get_unchecked(val)
                    {
                        Some(crate::streams::StreamId(*id))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        };

        if let Some(next_id) = next {
            current = next_id;
        } else {
            return Ok(current);
        }
    }

    Err(ControlSignal::Error(
        "Too many nested synonym/two-way streams".into(),
    ))
}

fn prim_print(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    use crate::printer::print_to_string;

    if let Some(&arg) = args.first() {
        let s = print_to_string(&proc.arena.inner, &*ctx.symbols.read().unwrap(), arg);
        let out_id = get_current_output_stream(proc, ctx);
        let _ = proc.streams.write_string(out_id, &s);
        let _ = proc.streams.write_newline(out_id);
        Ok(arg)
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_princ(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    use crate::printer::princ_to_string;

    if let Some(&arg) = args.first() {
        let s = princ_to_string(&proc.arena.inner, &*ctx.symbols.read().unwrap(), arg);
        let out_id = get_current_output_stream(proc, ctx);
        let _ = proc.streams.write_string(out_id, &s);
        Ok(arg)
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_terpri(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    _args: &[NodeId],
) -> EvalResult {
    let out_id = get_current_output_stream(proc, ctx);
    let _ = proc.streams.write_newline(out_id);
    Ok(proc.make_nil())
}

fn prim_values(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    Ok(set_multiple_values(proc, args.to_vec()))
}

fn prim_values_list(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("VALUES-LIST requires exactly 1 argument");
    }

    let mut values = Vec::new();
    let mut cur = args[0];
    loop {
        match proc.arena.inner.get_unchecked(cur) {
            Node::Leaf(OpaqueValue::Nil) => break,
            Node::Fork(car, cdr) => {
                values.push(*car);
                cur = *cdr;
            }
            _ => return err_helper("VALUES-LIST requires a proper list"),
        }
    }

    Ok(set_multiple_values(proc, values))
}

/// (format destination control-string &rest args)
/// Implements common CL format directives:
/// ~A - Aesthetic (princ-style, no escaping)
/// ~S - Standard (prin1-style, with escaping)
/// ~D - Decimal integer
/// ~B - Binary integer
/// ~O - Octal integer
/// ~X - Hexadecimal integer
/// ~F - Floating point
/// ~% - Newline
/// ~& - Fresh line (newline if not at column 0)
/// ~~ - Literal tilde
fn prim_format(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    use crate::printer::{princ_to_string, print_to_string};

    if args.len() < 2 {
        return err_helper("FORMAT requires at least 2 arguments (destination control-string)");
    }

    let dest = args[0];
    let control_string_node = args[1];
    let format_args = &args[2..];

    // Get the control string
    let control_string = match proc.arena.inner.get_unchecked(control_string_node) {
        Node::Leaf(OpaqueValue::String(s)) => s.clone(),
        _ => return err_helper("FORMAT: control-string must be a string"),
    };

    // Process the format string
    let mut result = String::new();
    let mut arg_index = 0;
    let chars: Vec<char> = control_string.chars().collect();
    let mut i = 0;

    while i < chars.len() {
        if chars[i] == '~' {
            i += 1;
            if i >= chars.len() {
                return err_helper("FORMAT: unexpected end of control string after ~");
            }

            // Parse optional parameters (mincol, colinc, minpad, padchar)
            // For simplicity, we skip complex parameter parsing and handle basic directives
            let mut colon = false;
            let mut at_sign = false;

            // Check for modifiers
            while i < chars.len() && (chars[i] == ':' || chars[i] == '@') {
                if chars[i] == ':' {
                    colon = true;
                }
                if chars[i] == '@' {
                    at_sign = true;
                }
                i += 1;
            }

            if i >= chars.len() {
                return err_helper("FORMAT: unexpected end of control string");
            }

            let directive = chars[i].to_ascii_uppercase();

            match directive {
                'A' => {
                    // Aesthetic output (princ)
                    if arg_index >= format_args.len() {
                        return err_helper("FORMAT: not enough arguments for ~A");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;

                    if colon
                        && matches!(
                            proc.arena.inner.get_unchecked(arg),
                            Node::Leaf(OpaqueValue::Nil)
                        )
                    {
                        result.push_str("()");
                    } else {
                        result.push_str(&princ_to_string(
                            &proc.arena.inner,
                            &*ctx.symbols.read().unwrap(),
                            arg,
                        ));
                    }
                }
                'S' => {
                    // Standard output (prin1)
                    if arg_index >= format_args.len() {
                        return err_helper("FORMAT: not enough arguments for ~S");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    result.push_str(&print_to_string(
                        &proc.arena.inner,
                        &*ctx.symbols.read().unwrap(),
                        arg,
                    ));
                }
                'D' => {
                    // Decimal integer
                    if arg_index >= format_args.len() {
                        return err_helper("FORMAT: not enough arguments for ~D");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    match proc.arena.inner.get_unchecked(arg) {
                        Node::Leaf(OpaqueValue::Integer(n)) => {
                            if at_sign && *n >= 0 {
                                result.push('+');
                            }
                            result.push_str(&n.to_string());
                        }
                        _ => result.push_str(&princ_to_string(
                            &proc.arena.inner,
                            &*ctx.symbols.read().unwrap(),
                            arg,
                        )),
                    }
                }
                'B' => {
                    // Binary integer
                    if arg_index >= format_args.len() {
                        return err_helper("FORMAT: not enough arguments for ~B");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    match proc.arena.inner.get_unchecked(arg) {
                        Node::Leaf(OpaqueValue::Integer(n)) => {
                            result.push_str(&format!("{:b}", n));
                        }
                        _ => result.push_str(&princ_to_string(
                            &proc.arena.inner,
                            &*ctx.symbols.read().unwrap(),
                            arg,
                        )),
                    }
                }
                'O' => {
                    // Octal integer
                    if arg_index >= format_args.len() {
                        return err_helper("FORMAT: not enough arguments for ~O");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    match proc.arena.inner.get_unchecked(arg) {
                        Node::Leaf(OpaqueValue::Integer(n)) => {
                            result.push_str(&format!("{:o}", n));
                        }
                        _ => result.push_str(&princ_to_string(
                            &proc.arena.inner,
                            &*ctx.symbols.read().unwrap(),
                            arg,
                        )),
                    }
                }
                'X' => {
                    // Hexadecimal integer
                    if arg_index >= format_args.len() {
                        return err_helper("FORMAT: not enough arguments for ~X");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    match proc.arena.inner.get_unchecked(arg) {
                        Node::Leaf(OpaqueValue::Integer(n)) => {
                            result.push_str(&format!("{:x}", n));
                        }
                        _ => result.push_str(&princ_to_string(
                            &proc.arena.inner,
                            &*ctx.symbols.read().unwrap(),
                            arg,
                        )),
                    }
                }
                'F' => {
                    // Floating point
                    if arg_index >= format_args.len() {
                        return err_helper("FORMAT: not enough arguments for ~F");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    match proc.arena.inner.get_unchecked(arg) {
                        Node::Leaf(OpaqueValue::Float(f)) => {
                            result.push_str(&format!("{}", f));
                        }
                        Node::Leaf(OpaqueValue::Integer(n)) => {
                            result.push_str(&format!("{}.0", n));
                        }
                        _ => result.push_str(&princ_to_string(
                            &proc.arena.inner,
                            &*ctx.symbols.read().unwrap(),
                            arg,
                        )),
                    }
                }
                'C' => {
                    // Character
                    if arg_index >= format_args.len() {
                        return err_helper("FORMAT: not enough arguments for ~C");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    match proc.arena.inner.get_unchecked(arg) {
                        Node::Leaf(OpaqueValue::Char(c)) => {
                            result.push(*c);
                        }
                        Node::Leaf(OpaqueValue::Integer(n)) => {
                            if let Some(c) = char::from_u32(*n as u32) {
                                result.push(c);
                            }
                        }
                        Node::Leaf(OpaqueValue::String(s)) => {
                            if let Some(c) = s.chars().next() {
                                result.push(c);
                            }
                        }
                        _ => result.push_str(&princ_to_string(
                            &proc.arena.inner,
                            &*ctx.symbols.read().unwrap(),
                            arg,
                        )),
                    }
                }
                '%' => {
                    // Newline
                    result.push('\n');
                }
                '&' => {
                    // Fresh line (for simplicity, just add newline if result doesn't end with one)
                    if !result.ends_with('\n') {
                        result.push('\n');
                    }
                }
                '~' => {
                    // Literal tilde
                    result.push('~');
                }
                'R' => {
                    // Radix (basic support: just decimal for now)
                    if arg_index >= format_args.len() {
                        return err_helper("FORMAT: not enough arguments for ~R");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    match proc.arena.inner.get_unchecked(arg) {
                        Node::Leaf(OpaqueValue::Integer(n)) => {
                            result.push_str(&n.to_string());
                        }
                        _ => result.push_str(&princ_to_string(
                            &proc.arena.inner,
                            &*ctx.symbols.read().unwrap(),
                            arg,
                        )),
                    }
                }
                '*' => {
                    // Goto (skip/backup args)
                    if colon {
                        // ~:* - backup one argument
                        if arg_index > 0 {
                            arg_index -= 1;
                        }
                    } else if at_sign {
                        // ~@* - goto absolute position (not fully implemented)
                        arg_index = 0;
                    } else {
                        // ~* - skip one argument
                        if arg_index < format_args.len() {
                            arg_index += 1;
                        }
                    }
                }
                '?' => {
                    // Recursive format (not fully implemented - treat as ~A)
                    if arg_index >= format_args.len() {
                        return err_helper("FORMAT: not enough arguments for ~?");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    result.push_str(&princ_to_string(
                        &proc.arena.inner,
                        &*ctx.symbols.read().unwrap(),
                        arg,
                    ));
                }
                _ => {
                    // Unknown directive - just output it
                    result.push('~');
                    result.push(directive);
                }
            }
        } else {
            result.push(chars[i]);
        }
        i += 1;
    }

    // Handle destination
    let is_nil = matches!(
        proc.arena.inner.get_unchecked(dest),
        Node::Leaf(OpaqueValue::Nil)
    );
    let is_t = if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(dest) {
        SymbolId(*id) == ctx.t_sym
    } else {
        false
    };
    let stream_id =
        if let Node::Leaf(OpaqueValue::StreamHandle(id)) = proc.arena.inner.get_unchecked(dest) {
            Some(crate::streams::StreamId(*id))
        } else {
            None
        };

    if is_nil {
        // Return the formatted string
        Ok(proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String(result))))
    } else if is_t {
        // Output to standard output
        let out_id = get_current_output_stream(proc, ctx);
        let _ = proc.streams.write_string(out_id, &result);
        Ok(proc.make_nil())
    } else if let Some(id) = stream_id {
        // Output to specified stream
        let _ = proc.streams.write_string(id, &result);
        Ok(proc.make_nil())
    } else {
        // For unknown destinations, output to stdout
        let out_id = get_current_output_stream(proc, ctx);
        let _ = proc.streams.write_string(out_id, &result);
        Ok(proc.make_nil())
    }
}

fn get_rusage_times() -> (f64, f64) {
    unsafe {
        let mut usage: libc::rusage = std::mem::zeroed();
        if libc::getrusage(libc::RUSAGE_SELF, &mut usage) != 0 {
            return (0.0, 0.0);
        }
        let user = usage.ru_utime.tv_sec as f64
            + (usage.ru_utime.tv_usec as f64 / 1_000_000.0);
        let sys = usage.ru_stime.tv_sec as f64
            + (usage.ru_stime.tv_usec as f64 / 1_000_000.0);
        (user, sys)
    }
}

fn prim_sys_time_eval(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("SYS-TIME-EVAL requires one argument (thunk)");
    }

    let thunk = args[0];
    let start_real = std::time::Instant::now();
    let (start_user, start_sys) = get_rusage_times();
    let start_gc_count = proc.gc_count;
    let start_gc_time = proc.gc_time_sec;
    let start_gc_freed = proc.gc_freed_total;
    let start_stats = proc.arena.inner.stats();
    let live_before = start_stats.total_slots.saturating_sub(start_stats.free_slots);

    let result = call_function_node(proc, ctx, thunk, &[])?;

    let real = start_real.elapsed().as_secs_f64();
    let (end_user, end_sys) = get_rusage_times();
    let user = (end_user - start_user).max(0.0);
    let sys = (end_sys - start_sys).max(0.0);
    let total = user + sys;
    let cpu = if real > 0.0 { (total / real) * 100.0 } else { 0.0 };
    let gc_count = proc.gc_count.saturating_sub(start_gc_count);
    let gc_time = (proc.gc_time_sec - start_gc_time).max(0.0);
    let gc_freed = proc.gc_freed_total.saturating_sub(start_gc_freed);
    let gc_pct = if total > 0.0 { (gc_time / total) * 100.0 } else { 0.0 };
    let end_stats = proc.arena.inner.stats();
    let heap_bytes = proc.arena.inner.total_bytes();
    let live_after = end_stats
        .total_slots
        .saturating_sub(end_stats.free_slots);

    let output = format!(
        "Evaluation time:\n  {:.3} seconds of real time\n  {:.6} seconds of total run time ({:.6} user, {:.6} system)\n  {:.2}% CPU\n  {:.6} seconds of GC time ({:.2}% of total), {} collections, {} nodes freed\n  Live nodes: {} -> {}, Heap size: {} slots ({} bytes), Allocs since GC: {}\n",
        real,
        total,
        user,
        sys,
        cpu,
        gc_time,
        gc_pct,
        gc_count,
        gc_freed,
        live_before,
        live_after,
        end_stats.total_slots,
        heap_bytes,
        end_stats.allocs_since_gc
    );
    let out_id = get_current_output_stream(proc, ctx);
    let _ = proc.streams.write_string(out_id, &output);

    Ok(result)
}

fn read_eval_marker_form(
    proc: &Process,
    ctx: &crate::context::GlobalContext,
    node: NodeId,
) -> Option<NodeId> {
    let (car, cdr) = match proc.arena.inner.get_unchecked(node) {
        Node::Fork(car, cdr) => (*car, *cdr),
        _ => return None,
    };
    let sym_id = match proc.arena.inner.get_unchecked(car) {
        Node::Leaf(OpaqueValue::Symbol(id)) => SymbolId(*id),
        _ => return None,
    };
    let symbols = ctx.symbols.read().unwrap();
    if symbols.symbol_package(sym_id).is_some() {
        return None;
    }
    if symbols.symbol_name(sym_id) != Some("%READ-EVAL%") {
        return None;
    }
    match proc.arena.inner.get_unchecked(cdr) {
        Node::Fork(form, rest) => match proc.arena.inner.get_unchecked(*rest) {
            Node::Leaf(OpaqueValue::Nil) => Some(*form),
            _ => Some(*form),
        },
        _ => None,
    }
}

fn resolve_read_eval(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    env: &Environment,
    node: NodeId,
) -> EvalResult {
    if let Some(form) = read_eval_marker_form(proc, ctx, node) {
        let resolved_form = resolve_read_eval(proc, ctx, env, form)?;
        let mut interp = Interpreter::new(proc, ctx);
        return interp.eval(resolved_form, env);
    }

    match proc.arena.inner.get_unchecked(node).clone() {
        Node::Fork(car, cdr) => {
            let new_car = resolve_read_eval(proc, ctx, env, car)?;
            let new_cdr = resolve_read_eval(proc, ctx, env, cdr)?;
            if new_car == car && new_cdr == cdr {
                Ok(node)
            } else {
                Ok(proc.arena.inner.alloc(Node::Fork(new_car, new_cdr)))
            }
        }
        _ => Ok(node),
    }
}

fn read_one_from_str(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    input: &str,
    preserve_whitespace: bool,
) -> Result<(Option<NodeId>, usize), ControlSignal> {
    let options = build_reader_options(proc, ctx, preserve_whitespace);
    let rt_id = current_readtable_id(proc, ctx);
    let readtable = proc
        .readtable_by_id(rt_id)
        .ok_or_else(|| ControlSignal::Error("READ: missing readtable".to_string()))?
        .clone();

    let env = Environment::new();
    let proc_ptr = proc as *mut Process;
    let globals_ptr = ctx as *const _;
    let (mut value_opt, consumed, needs_read_eval) = {
        let mut symbols_guard = ctx.symbols.write().unwrap();
        let mut reader = crate::reader::Reader::new_with_options(
            input,
            &mut proc.arena.inner,
            &mut *symbols_guard,
            &readtable,
            Some(&mut proc.arrays),
            options,
        );

        crate::reader::set_read_eval_context(Some(crate::reader::ReadEvalContext {
            proc_ptr,
            globals_ptr,
            env_ptr: &env as *const _,
        }));

        let result = if reader.eof_after_whitespace() {
            Ok((None, reader.position(), reader.read_eval_hit()))
        } else {
            let read_result = reader.read();
            let needs_read_eval = reader.read_eval_hit();
            read_result.map(|v| (Some(v), reader.position(), needs_read_eval))
        };

        crate::reader::set_read_eval_context(None);
        result.map_err(|e| ControlSignal::Error(format!("READ: read error: {}", e)))?
    };

    if needs_read_eval {
        if let Some(value) = value_opt {
            value_opt = Some(resolve_read_eval(proc, ctx, &env, value)?);
        }
    }

    Ok((value_opt, consumed))
}

fn prim_read(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() > 4 {
        return err_helper("READ accepts at most 4 arguments");
    }

    let stream_id = resolve_input_stream(proc, ctx, args.get(0).copied())?;
    let stream_id = resolve_input_stream_id(proc, ctx, stream_id)?;

    let eof_error_p = args
        .get(1)
        .map(|v| !matches!(proc.arena.inner.get_unchecked(*v), Node::Leaf(OpaqueValue::Nil)))
        .unwrap_or(true);
    let eof_value = args.get(2).copied().unwrap_or_else(|| proc.make_nil());

    let preserve_whitespace = false;
    let (buffer, start_pos) = match proc.streams.get(stream_id) {
        Some(crate::streams::Stream::StringInputStream { buffer, position }) => {
            (buffer.clone(), *position)
        }
        _ => {
            return Err(ControlSignal::Error(
                "READ currently supports only string input streams".into(),
            ))
        }
    };
    let remaining: String = buffer.chars().skip(start_pos).collect();
    let result = read_one_from_str(proc, ctx, &remaining, preserve_whitespace)?;
    let (value_opt, consumed) = (result.0, (start_pos, result.1));

    if let Some(crate::streams::Stream::StringInputStream { position, .. }) =
        proc.streams.get_mut(stream_id)
    {
        *position = consumed.0 + consumed.1;
    }

    match value_opt {
        Some(val) => Ok(val),
        None => {
            if eof_error_p {
                Err(ControlSignal::Error("READ: end of file".into()))
            } else {
                Ok(eof_value)
            }
        }
    }
}

fn prim_read_preserving_whitespace(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() > 4 {
        return err_helper("READ-PRESERVING-WHITESPACE accepts at most 4 arguments");
    }

    let stream_id = resolve_input_stream(proc, ctx, args.get(0).copied())?;
    let stream_id = resolve_input_stream_id(proc, ctx, stream_id)?;

    let eof_error_p = args
        .get(1)
        .map(|v| !matches!(proc.arena.inner.get_unchecked(*v), Node::Leaf(OpaqueValue::Nil)))
        .unwrap_or(true);
    let eof_value = args.get(2).copied().unwrap_or_else(|| proc.make_nil());

    let preserve_whitespace = true;
    let (buffer, start_pos) = match proc.streams.get(stream_id) {
        Some(crate::streams::Stream::StringInputStream { buffer, position }) => {
            (buffer.clone(), *position)
        }
        _ => {
            return Err(ControlSignal::Error(
                "READ-PRESERVING-WHITESPACE currently supports only string input streams".into(),
            ))
        }
    };
    let remaining: String = buffer.chars().skip(start_pos).collect();
    let result = read_one_from_str(proc, ctx, &remaining, preserve_whitespace)?;
    let (value_opt, consumed) = (result.0, (start_pos, result.1));

    if let Some(crate::streams::Stream::StringInputStream { position, .. }) =
        proc.streams.get_mut(stream_id)
    {
        *position = consumed.0 + consumed.1;
    }

    match value_opt {
        Some(val) => Ok(val),
        None => {
            if eof_error_p {
                Err(ControlSignal::Error(
                    "READ-PRESERVING-WHITESPACE: end of file".into(),
                ))
            } else {
                Ok(eof_value)
            }
        }
    }
}

fn prim_read_from_string(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return err_helper("READ-FROM-STRING requires a string argument");
    }

    let input_string = match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::String(s)) => s.clone(),
        _ => return err_helper("READ-FROM-STRING: first argument must be a string"),
    };

    let eof_error_p = args
        .get(1)
        .map(|v| !matches!(proc.arena.inner.get_unchecked(*v), Node::Leaf(OpaqueValue::Nil)))
        .unwrap_or(true);
    let eof_value = args.get(2).copied().unwrap_or_else(|| proc.make_nil());

    let mut start: Option<usize> = None;
    let mut end: Option<usize> = None;
    let mut preserve_whitespace = false;
    let mut allow_other_keys = false;

    // First pass: resolve ALLOW-OTHER-KEYS (last occurrence wins)
    let mut i = 3;
    while i < args.len() {
        if i + 1 >= args.len() {
            return err_helper("READ-FROM-STRING: odd number of keyword args");
        }
        let key = args[i];
        let val = args[i + 1];
        if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(key) {
            let key_name = ctx
                .symbols
                .read()
                .unwrap()
                .symbol_name(SymbolId(*id))
                .unwrap_or("")
                .to_uppercase();
            if key_name == "ALLOW-OTHER-KEYS" {
                if !matches!(
                    proc.arena.inner.get_unchecked(val),
                    Node::Leaf(OpaqueValue::Nil)
                ) {
                    allow_other_keys = true;
                }
            }
        }
        i += 2;
    }

    // Second pass: parse all keys
    i = 3;
    while i < args.len() {
        let key = args[i];
        let val = args[i + 1];
        let key_name = match proc.arena.inner.get_unchecked(key) {
            Node::Leaf(OpaqueValue::Symbol(id)) => ctx
                .symbols
                .read()
                .unwrap()
                .symbol_name(SymbolId(*id))
                .unwrap_or("")
                .to_uppercase(),
            _ => {
                return err_helper("READ-FROM-STRING: keyword must be a symbol");
            }
        };

        match key_name.as_str() {
            "START" => {
                let n = extract_number(&proc.arena.inner, val);
                if let NumVal::Int(v) = n {
                    if v < 0 {
                        return err_helper("READ-FROM-STRING: START must be >= 0");
                    }
                    start = Some(v as usize);
                } else {
                    return err_helper("READ-FROM-STRING: START must be an integer");
                }
            }
            "END" => {
                if matches!(
                    proc.arena.inner.get_unchecked(val),
                    Node::Leaf(OpaqueValue::Nil)
                ) {
                    end = None;
                } else if let NumVal::Int(v) = extract_number(&proc.arena.inner, val) {
                    if v < 0 {
                        return err_helper("READ-FROM-STRING: END must be >= 0");
                    }
                    end = Some(v as usize);
                } else {
                    return err_helper("READ-FROM-STRING: END must be an integer");
                }
            }
            "PRESERVE-WHITESPACE" => {
                preserve_whitespace = !matches!(
                    proc.arena.inner.get_unchecked(val),
                    Node::Leaf(OpaqueValue::Nil)
                );
            }
            "ALLOW-OTHER-KEYS" => {}
            _ => {
                if !allow_other_keys {
                    return err_helper("READ-FROM-STRING: unknown keyword");
                }
            }
        }
        i += 2;
    }

    let chars: Vec<char> = input_string.chars().collect();
    let len = chars.len();
    let start_idx = start.unwrap_or(0);
    let end_idx = end.unwrap_or(len);

    if start_idx > end_idx || start_idx > len || end_idx > len {
        return err_helper("READ-FROM-STRING: invalid start/end");
    }

    if start_idx == end_idx {
        let index_node = proc.make_integer(start_idx as i64);
        let primary = if eof_error_p {
            return err_helper("READ-FROM-STRING: end of file");
        } else {
            eof_value
        };
        let primary = set_multiple_values(proc, vec![primary, index_node]);
        return Ok(primary);
    }

    let slice: String = chars[start_idx..end_idx].iter().collect();
    let (value_opt, consumed) = read_one_from_str(proc, ctx, &slice, preserve_whitespace)?;
    let index = start_idx + consumed;
    let index_node = proc.make_integer(index as i64);

    match value_opt {
        Some(val) => {
            let primary = set_multiple_values(proc, vec![val, index_node]);
            Ok(primary)
        }
        None => {
            if eof_error_p {
                err_helper("READ-FROM-STRING: end of file")
            } else {
                let primary = set_multiple_values(proc, vec![eof_value, index_node]);
                Ok(primary)
            }
        }
    }
}

fn prim_read_delimited_list(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return err_helper("READ-DELIMITED-LIST requires a delimiter char");
    }
    if args.len() > 3 {
        return err_helper("READ-DELIMITED-LIST accepts at most 3 arguments");
    }

    let delim = node_to_char(proc, ctx, args[0])
        .ok_or_else(|| ControlSignal::Error("READ-DELIMITED-LIST: invalid delimiter".into()))?;

    let stream_id = resolve_input_stream(proc, ctx, args.get(1).copied())?;
    let stream_id = resolve_input_stream_id(proc, ctx, stream_id)?;

    let preserve_whitespace = false;
    let (buffer, start_pos) = match proc.streams.get(stream_id) {
        Some(crate::streams::Stream::StringInputStream { buffer, position }) => {
            (buffer.clone(), *position)
        }
        _ => {
            return Err(ControlSignal::Error(
                "READ-DELIMITED-LIST currently supports only string input streams".into(),
            ))
        }
    };
    let remaining: String = buffer.chars().skip(start_pos).collect();
    let options = build_reader_options(proc, ctx, preserve_whitespace);
    let rt_id = current_readtable_id(proc, ctx);
    let readtable = proc
        .readtable_by_id(rt_id)
        .ok_or_else(|| ControlSignal::Error("READ-DELIMITED-LIST: missing readtable".to_string()))?
        .clone();
    let env = Environment::new();
    let proc_ptr = proc as *mut Process;
    let globals_ptr = ctx as *const _;
    let mut symbols_guard = ctx.symbols.write().unwrap();
    let mut reader = crate::reader::Reader::new_with_options(
        &remaining,
        &mut proc.arena.inner,
        &mut *symbols_guard,
        &readtable,
        Some(&mut proc.arrays),
        options,
    );
    crate::reader::set_read_eval_context(Some(crate::reader::ReadEvalContext {
        proc_ptr,
        globals_ptr,
        env_ptr: &env as *const _,
    }));
    let result = reader.read_delimited_list(delim).map(|v| (Some(v), reader.position()));
    crate::reader::set_read_eval_context(None);
    let result = result.map_err(|e| {
        ControlSignal::Error(format!("READ-DELIMITED-LIST: read error: {}", e))
    })?;
    let (value_opt, consumed) = (result.0, (start_pos, result.1));

    if let Some(crate::streams::Stream::StringInputStream { position, .. }) =
        proc.streams.get_mut(stream_id)
    {
        *position = consumed.0 + consumed.1;
    }

    Ok(value_opt.unwrap_or_else(|| proc.make_nil()))
}

fn prim_read_char(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() > 4 {
        return err_helper("READ-CHAR accepts at most 4 arguments");
    }

    let stream_id = resolve_input_stream(proc, ctx, args.get(0).copied())?;
    let stream_id = resolve_input_stream_id(proc, ctx, stream_id)?;

    let eof_error_p = args
        .get(1)
        .map(|v| !matches!(proc.arena.inner.get_unchecked(*v), Node::Leaf(OpaqueValue::Nil)))
        .unwrap_or(true);
    let eof_value = args.get(2).copied().unwrap_or_else(|| proc.make_nil());

    match proc.streams.read_char(stream_id) {
        Ok(Some(c)) => Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Char(c)))),
        Ok(None) => {
            if eof_error_p {
                Err(ControlSignal::Error("READ-CHAR: end of file".into()))
            } else {
                Ok(eof_value)
            }
        }
        Err(e) => Err(ControlSignal::Error(format!("READ-CHAR: {}", e))),
    }
}

fn prim_unread_char(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 2 {
        return err_helper("UNREAD-CHAR requires 1 or 2 arguments");
    }

    let ch = match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::Char(c)) => *c,
        Node::Leaf(OpaqueValue::Integer(n)) => std::char::from_u32(*n as u32)
            .ok_or_else(|| ControlSignal::Error("UNREAD-CHAR: invalid char".into()))?,
        _ => return err_helper("UNREAD-CHAR: invalid character"),
    };

    let stream_id = resolve_input_stream(proc, ctx, args.get(1).copied())?;
    let stream_id = resolve_input_stream_id(proc, ctx, stream_id)?;

    proc.streams
        .unread_char(stream_id, ch)
        .map_err(|e| ControlSignal::Error(format!("UNREAD-CHAR: {}", e)))?;

    Ok(proc.make_nil())
}

fn prim_read_line(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() > 4 {
        return err_helper("READ-LINE accepts at most 4 arguments");
    }

    let stream_id = resolve_input_stream(proc, ctx, args.get(0).copied())?;
    let stream_id = resolve_input_stream_id(proc, ctx, stream_id)?;

    let eof_error_p = args
        .get(1)
        .map(|v| !matches!(proc.arena.inner.get_unchecked(*v), Node::Leaf(OpaqueValue::Nil)))
        .unwrap_or(true);
    let eof_value = args.get(2).copied().unwrap_or_else(|| proc.make_nil());

    match proc.streams.read_line(stream_id) {
        Ok(Some(mut line)) => {
            if line.ends_with('\n') {
                line.pop();
                if line.ends_with('\r') {
                    line.pop();
                }
            }
            let line_node = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(line)));
            let eof_flag = proc.make_nil();
            let primary = set_multiple_values(proc, vec![line_node, eof_flag]);
            Ok(primary)
        }
        Ok(None) => {
            if eof_error_p {
                Err(ControlSignal::Error("READ-LINE: end of file".into()))
            } else {
                let eof_flag = proc.make_t(ctx);
                let primary = set_multiple_values(proc, vec![eof_value, eof_flag]);
                Ok(primary)
            }
        }
        Err(e) => Err(ControlSignal::Error(format!("READ-LINE: {}", e))),
    }
}

// ============================================================================
// Stream Primitives
// ============================================================================

/// (make-string-output-stream) -> stream
fn prim_make_string_output_stream(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    _args: &[NodeId],
) -> EvalResult {
    use crate::streams::Stream;

    let stream = Stream::StringOutputStream {
        buffer: String::new(),
    };
    let id = proc.streams.alloc(stream);
    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::StreamHandle(id.0))))
}

/// (get-output-stream-string stream) -> string
fn prim_get_output_stream_string(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Node::Leaf(OpaqueValue::StreamHandle(id)) = proc.arena.inner.get_unchecked(arg) {
            let stream_id = crate::streams::StreamId(*id);
            if let Some(s) = proc.streams.get_output_stream_string(stream_id) {
                return Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(s))));
            } else {
                return err_helper("GET-OUTPUT-STREAM-STRING: not a string output stream");
            }
        }
    }
    err_helper("GET-OUTPUT-STREAM-STRING requires a stream argument")
}

/// (make-string-input-stream string) -> stream
fn prim_make_string_input_stream(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    use crate::streams::Stream;

    if let Some(&arg) = args.first() {
        if let Node::Leaf(OpaqueValue::String(s)) = proc.arena.inner.get_unchecked(arg) {
            let stream = Stream::StringInputStream {
                buffer: s.clone(),
                position: 0,
            };
            let id = proc.streams.alloc(stream);
            return Ok(proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::StreamHandle(id.0))));
        }
    }
    err_helper("MAKE-STRING-INPUT-STREAM requires a string argument")
}

/// (make-two-way-stream input output) -> stream
fn prim_make_two_way_stream(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    use crate::streams::Stream;

    if args.len() != 2 {
        return err_helper("MAKE-TWO-WAY-STREAM requires input and output streams");
    }

    let input_id = match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::StreamHandle(id)) => crate::streams::StreamId(*id),
        _ => return err_helper("MAKE-TWO-WAY-STREAM: input must be a stream"),
    };
    let output_id = match proc.arena.inner.get_unchecked(args[1]) {
        Node::Leaf(OpaqueValue::StreamHandle(id)) => crate::streams::StreamId(*id),
        _ => return err_helper("MAKE-TWO-WAY-STREAM: output must be a stream"),
    };

    let stream = Stream::TwoWayStream {
        input: input_id,
        output: output_id,
    };
    let id = proc.streams.alloc(stream);
    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::StreamHandle(id.0))))
}

/// (make-broadcast-stream &rest streams) -> stream
fn prim_make_broadcast_stream(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    use crate::streams::Stream;

    let mut targets = Vec::new();
    for &arg in args {
        match proc.arena.inner.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::StreamHandle(id)) => {
                targets.push(crate::streams::StreamId(*id))
            }
            _ => return err_helper("MAKE-BROADCAST-STREAM: args must be streams"),
        }
    }

    let stream = Stream::BroadcastStream { targets };
    let id = proc.streams.alloc(stream);
    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::StreamHandle(id.0))))
}

/// (close stream) -> t
fn prim_close(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Node::Leaf(OpaqueValue::StreamHandle(id)) = proc.arena.inner.get_unchecked(arg) {
            let stream_id = crate::streams::StreamId(*id);
            if proc.streams.close(stream_id) {
                return Ok(proc.make_t(ctx));
            }
        }
    }
    Ok(proc.make_nil())
}

/// (write-string string &optional stream) -> string
fn prim_write_string(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return err_helper("WRITE-STRING requires at least 1 argument");
    }

    let string_arg = args[0];
    let stream_id = if args.len() > 1 {
        if let Node::Leaf(OpaqueValue::StreamHandle(id)) = proc.arena.inner.get_unchecked(args[1]) {
            crate::streams::StreamId(*id)
        } else {
            proc.streams.stdout_id()
        }
    } else {
        proc.streams.stdout_id()
    };

    if let Node::Leaf(OpaqueValue::String(s)) = proc.arena.inner.get_unchecked(string_arg) {
        let s_clone = s.clone();
        let _ = proc.streams.write_string(stream_id, &s_clone);
        Ok(string_arg)
    } else {
        use crate::printer::princ_to_string;
        let s = princ_to_string(&proc.arena.inner, &*ctx.symbols.read().unwrap(), string_arg);
        let _ = proc.streams.write_string(stream_id, &s);
        Ok(string_arg)
    }
}

/// (write-char char &optional stream) -> char
fn prim_write_char(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return err_helper("WRITE-CHAR requires at least 1 argument");
    }

    let char_arg = args[0];
    let stream_id = if args.len() > 1 {
        if let Node::Leaf(OpaqueValue::StreamHandle(id)) = proc.arena.inner.get_unchecked(args[1]) {
            crate::streams::StreamId(*id)
        } else {
            proc.streams.stdout_id()
        }
    } else {
        proc.streams.stdout_id()
    };

    let c = match proc.arena.inner.get_unchecked(char_arg) {
        Node::Leaf(OpaqueValue::Char(c)) => *c,
        Node::Leaf(OpaqueValue::Integer(n)) => char::from_u32(*n as u32).unwrap_or('?'),
        Node::Leaf(OpaqueValue::String(s)) => s.chars().next().unwrap_or('?'),
        _ => '?',
    };

    let _ = proc.streams.write_char(stream_id, c);
    Ok(char_arg)
}

/// (fresh-line &optional stream) -> generalized-boolean
fn prim_fresh_line(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    let stream_id = if !args.is_empty() {
        if let Node::Leaf(OpaqueValue::StreamHandle(id)) = proc.arena.inner.get_unchecked(args[0]) {
            crate::streams::StreamId(*id)
        } else {
            proc.streams.stdout_id()
        }
    } else {
        proc.streams.stdout_id()
    };

    match proc.streams.fresh_line(stream_id) {
        Ok(true) => Ok(proc.make_t(ctx)),
        Ok(false) => Ok(proc.make_nil()),
        Err(_) => Ok(proc.make_nil()),
    }
}

// ============================================================================
// CLOS Primitives
// ============================================================================

fn prim_find_class(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Some(sym) = node_to_symbol(proc, arg) {
            if let Some(id) = proc.mop.find_class(sym) {
                return Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Class(id.0))));
            }
        }
    }
    Ok(proc.make_nil())
}

fn prim_allocate_instance(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    use crate::clos::ClassId;
    if let Some(&class_arg) = args.first() {
        let class_id = match proc.arena.inner.get_unchecked(class_arg) {
            Node::Leaf(OpaqueValue::Class(id)) => Some(ClassId(*id)),
            _ => {
                // Try symbol
                if let Some(sym) = node_to_symbol(proc, class_arg) {
                    proc.mop.find_class(sym)
                } else {
                    None
                }
            }
        };

        if let Some(id) = class_id {
            // Create instance (all slots nil)
            let unbound = proc.make_unbound();
            if let Some(inst_idx) = proc.mop.make_instance(id, unbound) {
                let inst_node = proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Instance(inst_idx as u32)));
                return Ok(inst_node);
            }
        }
    }
    Err(crate::eval::ControlSignal::Error(
        "allocate-instance: invalid class".into(),
    ))
}

pub(crate) fn prim_shared_initialize(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    // (shared-initialize instance slot-names &rest initargs)
    if args.len() < 2 {
        return Err(crate::eval::ControlSignal::Error(
            "shared-initialize: too few args".into(),
        ));
    }
    let instance = args[0];
    let slot_names = args[1];
    let initargs = &args[2..];

    // Extract instance index
    let inst_idx =
        if let Node::Leaf(OpaqueValue::Instance(idx)) = proc.arena.inner.get_unchecked(instance) {
            *idx as usize
        } else {
            return Err(crate::eval::ControlSignal::Error(
                "shared-initialize: first arg must be instance".into(),
            ));
        };

    let class_id = proc.mop.get_instance(inst_idx).map(|i| i.class).ok_or(
        crate::eval::ControlSignal::Error("Instance lost class?".into()),
    )?;

    if initargs.is_empty() {
        if let Some(class) = proc.mop.get_class(class_id) {
            if class.slots.is_empty() && class.default_initargs.is_empty() {
                return Ok(instance);
            }
        }
    }

    // Calculate slots info
    // We need to do this properly.
    // Initargs is a list of keys and values.

    // Parse initargs to map? No, repeated keys allowed?
    // "The first value ... is used."
    // So scan.
    let mut initargs_map = if initargs.is_empty() {
        HashMap::default()
    } else {
        parse_keywords_list(proc, initargs)
    };

    // Determine slot-names behavior
    let t_sym = ctx
        .symbols
        .write()
        .unwrap()
        .intern_in("T", PackageId(1));
    let slot_names_node = proc.arena.inner.get_unchecked(slot_names);
    let slot_names_all = matches!(
        slot_names_node,
        Node::Leaf(OpaqueValue::Symbol(id)) if *id == t_sym.0
    );
    let slot_names_none = matches!(slot_names_node, Node::Leaf(OpaqueValue::Nil));
    let slot_names_set = if slot_names_all || slot_names_none {
        None
    } else {
        let mut set = crate::fastmap::HashSet::default();
        for head in list_to_vec(proc, slot_names) {
            if let Some(sym) = node_to_symbol(proc, head) {
                set.insert(sym);
            }
        }
        Some(set)
    };

    // Get slots
    if let Some(class) = proc.mop.get_class(class_id) {
        // Merge class default initargs unless slot-names is NIL (reinitialize-instance style).
        if !slot_names_none {
            for (key, val) in &class.default_initargs {
                if !initargs_map.contains_key(key) {
                    initargs_map.insert(*key, *val);
                }
            }
        }
        let slots = class.slots.clone();
        for slot in slots {
            let mut initialized = false;
            if let Some(key) = slot.initarg {
                if let Some(&val) = initargs_map.get(&key) {
                    enforce_slot_type(proc, ctx, &slot, val)?;
                    match slot.allocation {
                        crate::clos::SlotAllocation::Instance => {
                            proc.mop.set_slot_value(inst_idx, slot.index, val);
                        }
                        crate::clos::SlotAllocation::Class => {
                            if let Some(class) = proc.mop.get_class_mut(class_id) {
                                if let Some(s) = class
                                    .slots
                                    .iter_mut()
                                    .find(|s| s.name == slot.name)
                                {
                                    s.class_value = Some(val);
                                }
                            }
                        }
                    }
                    initialized = true;
                }
            }

            let should_initform = if slot_names_all {
                true
            } else if slot_names_none {
                false
            } else {
                slot_names_set
                    .as_ref()
                    .map(|s| s.contains(&slot.name))
                    .unwrap_or(false)
            };

            if !initialized && should_initform {
                let skip_default = matches!(
                    slot.allocation,
                    crate::clos::SlotAllocation::Class if slot.class_value.is_some()
                );
                if skip_default {
                    continue;
                }
                let value = if let Some(initfn) = slot.initfunction {
                    Some(call_function_node(proc, ctx, initfn, &[])?)
                } else {
                    slot.initform
                };

                if let Some(val) = value {
                    enforce_slot_type(proc, ctx, &slot, val)?;
                    match slot.allocation {
                        crate::clos::SlotAllocation::Instance => {
                            // NOTE: We treat initform as a literal node for now.
                            proc.mop.set_slot_value(inst_idx, slot.index, val);
                        }
                        crate::clos::SlotAllocation::Class => {
                            if let Some(class) = proc.mop.get_class_mut(class_id) {
                                if let Some(s) = class
                                    .slots
                                    .iter_mut()
                                    .find(|s| s.name == slot.name)
                                {
                                    if s.class_value.is_none() {
                                        s.class_value = Some(val);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    Ok(instance)
}

fn prim_make_instance(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    // Call allocate-instance
    let instance = prim_allocate_instance(proc, ctx, &[args[0]])?;

    // Call initialize-instance
    // We construct a call?
    // (initialize-instance instance args...)
    // But primitives cannot return code to EVAL mode easily (unless we refactor step_application).
    // Temporary: Call shared-initialize directly here to maintain behavior until init.lisp defines make-instance.

    let mut shared_args = vec![instance, proc.make_t(ctx)]; // instance, slot-names=T
    shared_args.extend_from_slice(&args[1..]); // initargs

    prim_shared_initialize(proc, ctx, &shared_args)
}

fn prim_class_of(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        let class_id = match proc.arena.inner.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::Integer(_)) => proc.mop.integer_class,
            Node::Leaf(OpaqueValue::Instance(idx)) => proc
                .mop
                .get_instance(*idx as usize)
                .map(|i| i.class)
                .unwrap_or(proc.mop.t_class),
            Node::Leaf(OpaqueValue::Class(id)) => proc
                .mop
                .get_class(crate::clos::ClassId(*id))
                .map(|c| c.metaclass)
                .unwrap_or(proc.mop.standard_class),
            Node::Leaf(OpaqueValue::Generic(_)) => proc.mop.standard_generic_function,
            Node::Leaf(OpaqueValue::Method(_)) => proc.mop.standard_method,
            Node::Leaf(OpaqueValue::SlotDefinition(_, _, direct)) => {
                if *direct {
                    proc.mop.standard_direct_slot_definition
                } else {
                    proc.mop.standard_effective_slot_definition
                }
            }
            Node::Leaf(OpaqueValue::EqlSpecializer(_)) => proc.mop.eql_specializer_class,
            _ => proc.mop.t_class,
        };
        // Return class object
        Ok(proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Class(class_id.0))))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_slot_value(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() >= 2 {
        let instance = args[0];
        let slot_name = args[1];

        // Extract instance index (class objects map to class metaobjects)
        let inst_idx = instance_index_from_node(proc, ctx, instance).ok();

        // Extract slot name symbol
        let slot_sym = node_to_symbol(proc, slot_name);

        if let (Some(idx), Some(sym)) = (inst_idx, slot_sym) {
            // Find slot definition in class
            if let Some(inst) = proc.mop.get_instance(idx) {
                let class_obj = proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Class(inst.class.0)));
                if let Some(class) = proc.mop.get_class(inst.class) {
                    if let Some(slot) = class.slots.iter().find(|s| s.name == sym) {
                        match slot.allocation {
                            crate::clos::SlotAllocation::Instance => {
                                if let Some(val) = proc.mop.slot_value(idx, slot.index) {
                                    if matches!(
                                        proc.arena.inner.get_unchecked(val),
                                        Node::Leaf(OpaqueValue::Unbound)
                                    ) {
                                        return call_slot_unbound(
                                            proc,
                                            ctx,
                                            class_obj,
                                            instance,
                                            slot_name,
                                        );
                                    }
                                    return Ok(val);
                                }
                            }
                            crate::clos::SlotAllocation::Class => {
                                if let Some(val) = slot.class_value {
                                    if matches!(
                                        proc.arena.inner.get_unchecked(val),
                                        Node::Leaf(OpaqueValue::Unbound)
                                    ) {
                                        return call_slot_unbound(
                                            proc,
                                            ctx,
                                            class_obj,
                                            instance,
                                            slot_name,
                                        );
                                    }
                                    return Ok(val);
                                }
                                return call_slot_unbound(proc, ctx, class_obj, instance, slot_name);
                            }
                        }
                    } else {
                        return call_slot_missing(
                            proc,
                            ctx,
                            class_obj,
                            instance,
                            slot_name,
                            "SLOT-VALUE",
                            None,
                        );
                    }
                }
            }
        }
    }

    Err(crate::eval::ControlSignal::Error(
        "Invalid slot access".to_string(),
    ))
}

fn prim_set_slot_value(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() >= 3 {
        let instance = args[0];
        let slot_name = args[1];
        let new_val = args[2];

        // Extract instance index (class objects map to class metaobjects)
        let inst_idx = instance_index_from_node(proc, ctx, instance).ok();

        // Extract slot name symbol
        let slot_sym = node_to_symbol(proc, slot_name);

        if let (Some(idx), Some(sym)) = (inst_idx, slot_sym) {
            if let Some(inst) = proc.mop.get_instance(idx) {
                let class_obj = proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Class(inst.class.0)));
                if let Some(class) = proc.mop.get_class(inst.class) {
                    if let Some(slot) = class.slots.iter().find(|s| s.name == sym) {
                        enforce_slot_type(proc, ctx, slot, new_val)?;
                        match slot.allocation {
                            crate::clos::SlotAllocation::Instance => {
                                proc.mop.set_slot_value(idx, slot.index, new_val);
                                return Ok(new_val);
                            }
                            crate::clos::SlotAllocation::Class => {
                                if let Some(class_mut) = proc.mop.get_class_mut(inst.class) {
                                    if let Some(s) = class_mut
                                        .slots
                                        .iter_mut()
                                        .find(|s| s.name == sym)
                                    {
                                        s.class_value = Some(new_val);
                                        return Ok(new_val);
                                    }
                                }
                            }
                        }
                    } else {
                        return call_slot_missing(
                            proc,
                            ctx,
                            class_obj,
                            instance,
                            slot_name,
                            "SET-SLOT-VALUE",
                            Some(new_val),
                        );
                    }
                }
            }
        }
    }
    Err(crate::eval::ControlSignal::Error(
        "Invalid slot set".to_string(),
    ))
}

fn list_to_vec(proc: &Process, list: NodeId) -> Vec<NodeId> {
    let mut vec = Vec::new();
    let mut curr = list;
    while let Node::Fork(head, tail) = proc.arena.inner.get_unchecked(curr).clone() {
        vec.push(head);
        curr = tail;
    }
    vec
}

fn setf_function_name_from_node(proc: &Process, node: NodeId) -> Option<SymbolId> {
    if let Node::Fork(car, rest) = proc.arena.inner.get_unchecked(node).clone() {
        if let Some(sym) = node_to_symbol(proc, car) {
            if sym == proc.mop.setf_symbol {
                if let Node::Fork(target, _) = proc.arena.inner.get_unchecked(rest).clone() {
                    return node_to_symbol(proc, target);
                }
            }
        }
    }
    None
}

fn class_id_from_node(proc: &Process, node: NodeId) -> Option<crate::clos::ClassId> {
    match proc.arena.inner.get_unchecked(node) {
        Node::Leaf(OpaqueValue::Class(id)) => Some(crate::clos::ClassId(*id)),
        Node::Leaf(OpaqueValue::Symbol(id)) => proc.mop.find_class(SymbolId(*id)),
        Node::Leaf(OpaqueValue::Instance(id)) => proc
            .mop
            .get_instance(*id as usize)
            .map(|i| i.class),
        _ => None,
    }
}

fn eql_specializer_id_from_node(proc: &Process, node: NodeId) -> Option<u32> {
    match proc.arena.inner.get_unchecked(node) {
        Node::Leaf(OpaqueValue::EqlSpecializer(id)) => Some(*id),
        _ => None,
    }
}

fn parse_specializer_node(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    node: NodeId,
) -> crate::clos::Specializer {
    if let Some(idx) = eql_specializer_id_from_node(proc, node) {
        return crate::clos::Specializer::Eql(idx);
    }

    if let Some(cid) = class_id_from_node(proc, node) {
        return crate::clos::Specializer::Class(cid);
    }

    if let Node::Fork(car, rest) = proc.arena.inner.get_unchecked(node).clone() {
        if let Some(sym) = node_to_symbol(proc, car) {
            if let Some(name) = ctx.symbols.read().unwrap().symbol_name(sym) {
                if name.eq_ignore_ascii_case("EQL") {
                    if let Node::Fork(obj, _) = proc.arena.inner.get_unchecked(rest).clone() {
                        let idx =
                            proc.mop.intern_eql_specializer(&proc.arena.inner, obj);
                        return crate::clos::Specializer::Eql(idx);
                    }
                }
            }
        }
    }

    crate::clos::Specializer::Class(proc.mop.t_class)
}

fn specializer_from_node(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    node: NodeId,
) -> Result<crate::clos::Specializer, ControlSignal> {
    if let Some(idx) = eql_specializer_id_from_node(proc, node) {
        return Ok(crate::clos::Specializer::Eql(idx));
    }

    if let Some(cid) = class_id_from_node(proc, node) {
        return Ok(crate::clos::Specializer::Class(cid));
    }

    if let Node::Fork(car, rest) = proc.arena.inner.get_unchecked(node).clone() {
        if let Some(sym) = node_to_symbol(proc, car) {
            if let Some(name) = ctx.symbols.read().unwrap().symbol_name(sym) {
                if name.eq_ignore_ascii_case("EQL") {
                    if let Node::Fork(obj, _) = proc.arena.inner.get_unchecked(rest).clone() {
                        let idx = proc.mop.intern_eql_specializer(&proc.arena.inner, obj);
                        return Ok(crate::clos::Specializer::Eql(idx));
                    }
                }
            }
        }
    }

    Err(ControlSignal::Error(
        "Invalid specializer (expected class or eql specializer)".to_string(),
    ))
}

fn specializer_to_node(proc: &mut Process, spec: &crate::clos::Specializer) -> NodeId {
    match spec {
        crate::clos::Specializer::Class(cid) => proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Class(cid.0))),
        crate::clos::Specializer::Eql(idx) => proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::EqlSpecializer(*idx))),
    }
}

fn generic_id_from_node(proc: &Process, node: NodeId) -> Option<crate::clos::GenericId> {
    match proc.arena.inner.get_unchecked(node) {
        Node::Leaf(OpaqueValue::Generic(id)) => Some(crate::clos::GenericId(*id)),
        Node::Leaf(OpaqueValue::Symbol(id)) => proc.mop.find_generic(SymbolId(*id)),
        _ => setf_function_name_from_node(proc, node).and_then(|sym| proc.mop.find_setf_generic(sym)),
    }
}

fn method_id_from_node(proc: &Process, node: NodeId) -> Option<crate::clos::MethodId> {
    match proc.arena.inner.get_unchecked(node) {
        Node::Leaf(OpaqueValue::Method(id)) => Some(crate::clos::MethodId(*id)),
        _ => None,
    }
}

enum DependentKey {
    Class(crate::clos::ClassId),
    Generic(crate::clos::GenericId),
}

fn dependent_key_from_node(proc: &Process, node: NodeId) -> Option<DependentKey> {
    match proc.arena.inner.get_unchecked(node) {
        Node::Leaf(OpaqueValue::Class(id)) => Some(DependentKey::Class(crate::clos::ClassId(*id))),
        Node::Leaf(OpaqueValue::Generic(id)) => {
            Some(DependentKey::Generic(crate::clos::GenericId(*id)))
        }
        Node::Leaf(OpaqueValue::Symbol(id)) => {
            let sym = SymbolId(*id);
            if let Some(cid) = proc.mop.find_class(sym) {
                Some(DependentKey::Class(cid))
            } else if let Some(gid) = proc.mop.find_generic(sym) {
                Some(DependentKey::Generic(gid))
            } else {
                None
            }
        }
        Node::Leaf(OpaqueValue::Instance(idx)) => {
            let inst_idx = *idx as usize;
            if let Some(cid) = proc.mop.class_id_for_meta_instance(inst_idx) {
                Some(DependentKey::Class(cid))
            } else if let Some(gid) = proc.mop.generic_id_for_meta_instance(inst_idx) {
                Some(DependentKey::Generic(gid))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn arg_class_id(proc: &Process, node: NodeId) -> crate::clos::ClassId {
    match proc.arena.inner.get_unchecked(node) {
        Node::Leaf(OpaqueValue::Instance(id)) => proc
            .mop
            .get_instance(*id as usize)
            .map(|i| i.class)
            .unwrap_or(proc.mop.standard_object),
        Node::Leaf(OpaqueValue::Class(_)) => proc.mop.standard_class,
        Node::Leaf(OpaqueValue::Symbol(_)) => proc.mop.symbol_class,
        Node::Leaf(OpaqueValue::Integer(_)) => proc.mop.integer_class,
        Node::Leaf(OpaqueValue::Generic(_)) => proc.mop.standard_generic_function,
        Node::Leaf(OpaqueValue::Method(_)) => proc.mop.standard_method,
        Node::Leaf(OpaqueValue::SlotDefinition(_, _, direct)) => {
            if *direct {
                proc.mop.standard_direct_slot_definition
            } else {
                proc.mop.standard_effective_slot_definition
            }
        }
        Node::Leaf(OpaqueValue::EqlSpecializer(_)) => proc.mop.eql_specializer_class,
        _ => proc.mop.t_class,
    }
}

fn slot_def_from_node(
    proc: &Process,
    node: NodeId,
) -> Option<(crate::clos::ClassId, usize, bool)> {
    match proc.arena.inner.get_unchecked(node) {
        Node::Leaf(OpaqueValue::SlotDefinition(class_id, slot_idx, direct)) => {
            Some((crate::clos::ClassId(*class_id), *slot_idx as usize, *direct))
        }
        _ => None,
    }
}

fn make_class_list(proc: &mut Process, class_ids: &[crate::clos::ClassId]) -> NodeId {
    let mut nodes = Vec::with_capacity(class_ids.len());
    for cid in class_ids {
        nodes.push(
            proc.arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Class(cid.0))),
        );
    }
    proc.make_list(&nodes)
}

fn make_method_list(proc: &mut Process, method_ids: &[crate::clos::MethodId]) -> NodeId {
    let mut nodes = Vec::with_capacity(method_ids.len());
    for mid in method_ids {
        nodes.push(
            proc.arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Method(mid.0))),
        );
    }
    proc.make_list(&nodes)
}

fn generic_name_to_node(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    name: GenericName,
) -> NodeId {
    match name {
        GenericName::Symbol(sym) => proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(sym.0))),
        GenericName::Setf(sym) => {
            let setf_sym = cl_symbol_id(ctx, "SETF");
            let setf_node = proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(setf_sym.0)));
            let base_node = proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(sym.0)));
            proc.make_list(&[setf_node, base_node])
        }
    }
}

fn generic_name_to_string(
    ctx: &crate::context::GlobalContext,
    name: GenericName,
) -> String {
    match name {
        GenericName::Symbol(sym) => ctx
            .symbols
            .read()
            .unwrap()
            .symbol_name(sym)
            .map(|s| s.to_string())
            .unwrap_or_else(|| "?".to_string()),
        GenericName::Setf(sym) => {
            let base = ctx
                .symbols
                .read()
                .unwrap()
                .symbol_name(sym)
                .map(|s| s.to_string())
                .unwrap_or_else(|| "?".to_string());
            format!("(SETF {})", base)
        }
    }
}

fn make_initargs_plist(proc: &mut Process, pairs: &[(SymbolId, NodeId)]) -> NodeId {
    let mut nodes = Vec::with_capacity(pairs.len() * 2);
    for (sym, val) in pairs {
        nodes.push(
            proc.arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(sym.0))),
        );
        nodes.push(*val);
    }
    proc.make_list(&nodes)
}

fn make_symbol_list(proc: &mut Process, symbols: &[SymbolId]) -> NodeId {
    let mut nodes = Vec::with_capacity(symbols.len());
    for sym in symbols {
        nodes.push(
            proc.arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(sym.0))),
        );
    }
    proc.make_list(&nodes)
}

fn call_mop_function(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    name: &str,
    args: &[NodeId],
) -> EvalResult {
    let (sym_user, sym_cl) = {
        let mut syms = ctx.symbols.write().unwrap();
        let sym_user = syms.intern_in(name, PackageId(2));
        let sym_cl = syms.intern_in(name, PackageId(1));
        (sym_user, sym_cl)
    };
    let func_node = proc
        .get_function(sym_user)
        .or_else(|| proc.get_function(sym_cl));
    if let Some(func_node) = func_node {
        let args_list = proc.make_list(args);
        let env = Environment::new();
        let saved_program = proc.program;
        let saved_mode = proc.execution_mode.clone();
        let saved_env = proc.current_env.clone();
        let saved_stack = std::mem::take(&mut proc.continuation_stack);
        let saved_pending = proc.pending_redex;
        let saved_next_methods = std::mem::take(&mut proc.next_method_states);
        let result = {
            let mut interp = Interpreter::new(proc, ctx);
            interp.apply_values(func_node, args_list, &env)
        };
        proc.program = saved_program;
        proc.execution_mode = saved_mode;
        proc.current_env = saved_env;
        proc.continuation_stack = saved_stack;
        proc.pending_redex = saved_pending;
        proc.next_method_states = saved_next_methods;
        result
    } else {
        Err(ControlSignal::Error(format!("Undefined function: {}", name)))
    }
}

fn update_dependent_available(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
) -> bool {
    let (sym_user, sym_cl) = {
        let mut syms = ctx.symbols.write().unwrap();
        let sym_user = syms.intern_in("UPDATE-DEPENDENT", PackageId(2));
        let sym_cl = syms.intern_in("UPDATE-DEPENDENT", PackageId(1));
        (sym_user, sym_cl)
    };
    proc.get_function(sym_user).is_some() || proc.get_function(sym_cl).is_some()
}

fn notify_dependents(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    key: DependentKey,
    extra_args: &[NodeId],
) -> Result<(), ControlSignal> {
    if !update_dependent_available(proc, ctx) {
        return Ok(());
    }

    let deps = match key {
        DependentKey::Class(cid) => proc.mop.class_dependents(cid).map(|d| d.to_vec()),
        DependentKey::Generic(gid) => proc.mop.generic_dependents(gid).map(|d| d.to_vec()),
    };

    let deps = match deps {
        Some(deps) if !deps.is_empty() => deps,
        _ => return Ok(()),
    };

    let meta_node = match key {
        DependentKey::Class(cid) => proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Class(cid.0))),
        DependentKey::Generic(gid) => proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Generic(gid.0))),
    };

    for dep in deps {
        let mut args = Vec::with_capacity(2 + extra_args.len());
        args.push(meta_node);
        args.push(dep);
        args.extend_from_slice(extra_args);
        let _ = call_mop_function(proc, ctx, "UPDATE-DEPENDENT", &args)?;
    }

    Ok(())
}

fn call_slot_missing(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    class_node: NodeId,
    instance_node: NodeId,
    slot_name_node: NodeId,
    operation: &str,
    new_value: Option<NodeId>,
) -> EvalResult {
    let op_sym = ctx
        .symbols
        .write()
        .unwrap()
        .intern_in(operation, PackageId(1));
    let op_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(op_sym.0)));
    let mut args = vec![class_node, instance_node, slot_name_node, op_node];
    if let Some(val) = new_value {
        args.push(val);
    }
    call_mop_function(proc, ctx, "SLOT-MISSING", &args)
}

fn call_slot_unbound(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    class_node: NodeId,
    instance_node: NodeId,
    slot_name_node: NodeId,
) -> EvalResult {
    let args = [class_node, instance_node, slot_name_node];
    call_mop_function(proc, ctx, "SLOT-UNBOUND", &args)
}

fn resolve_function_designator(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    func: NodeId,
) -> Result<NodeId, ControlSignal> {
    match proc.arena.inner.get_unchecked(func) {
        Node::Leaf(OpaqueValue::Closure(_)) | Node::Leaf(OpaqueValue::Generic(_)) => Ok(func),
        Node::Leaf(OpaqueValue::Symbol(id)) => {
            let sym = SymbolId(*id);
            proc.get_function(sym).ok_or_else(|| {
                ControlSignal::Error("Initfunction symbol has no function".to_string())
            })
        }
        _ => {
            let env = Environment::new();
            let saved_env = proc.current_env.clone();
            let result = {
                let mut interp = Interpreter::new(proc, ctx);
                interp.eval(func, &env)
            };
            proc.current_env = saved_env;
            let func_node = result?;
            match proc.arena.inner.get_unchecked(func_node) {
                Node::Leaf(OpaqueValue::Closure(_)) | Node::Leaf(OpaqueValue::Generic(_)) => {
                    Ok(func_node)
                }
                Node::Leaf(OpaqueValue::Symbol(id)) => {
                    let sym = SymbolId(*id);
                    proc.get_function(sym).ok_or_else(|| {
                        ControlSignal::Error("Initfunction did not evaluate to function".to_string())
                    })
                }
                _ => Err(ControlSignal::Error(
                    "Initfunction did not evaluate to function".to_string(),
                )),
            }
        }
    }
}

fn resolve_funcallable_designator(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    func: NodeId,
) -> Result<NodeId, ControlSignal> {
    match proc.arena.inner.get_unchecked(func) {
        Node::Leaf(OpaqueValue::Symbol(id)) => {
            let sym = SymbolId(*id);
            if proc.get_function(sym).is_some() || ctx.primitives.contains_key(&sym) {
                Ok(func)
            } else {
                Err(ControlSignal::Error(
                    "Funcallable function symbol is not fbound".to_string(),
                ))
            }
        }
        Node::Leaf(OpaqueValue::Closure(_))
        | Node::Leaf(OpaqueValue::Generic(_))
        | Node::Leaf(OpaqueValue::Instance(_)) => Ok(func),
        _ => resolve_function_designator(proc, ctx, func),
    }
}

fn call_function_node(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    func: NodeId,
    args: &[NodeId],
) -> EvalResult {
    let func_node = resolve_function_designator(proc, ctx, func)?;
    let args_list = if args.is_empty() {
        proc.make_nil()
    } else {
        proc.make_list(args)
    };
    let env = Environment::new();
    let saved_program = proc.program;
    let saved_mode = proc.execution_mode.clone();
    let saved_env = proc.current_env.clone();
    let saved_stack = std::mem::take(&mut proc.continuation_stack);
    let saved_pending = proc.pending_redex;
    let saved_next_methods = std::mem::take(&mut proc.next_method_states);
    let result = {
        let mut interp = Interpreter::new(proc, ctx);
        interp.apply_values(func_node, args_list, &env)
    };
    proc.program = saved_program;
    proc.execution_mode = saved_mode;
    proc.current_env = saved_env;
    proc.continuation_stack = saved_stack;
    proc.pending_redex = saved_pending;
    proc.next_method_states = saved_next_methods;
    result
}

fn value_class_id(proc: &Process, node: NodeId) -> crate::clos::ClassId {
    match proc.arena.inner.get_unchecked(node) {
        Node::Leaf(OpaqueValue::Integer(_)) => proc.mop.integer_class,
        Node::Leaf(OpaqueValue::Symbol(_)) => proc.mop.symbol_class,
        Node::Leaf(OpaqueValue::Nil) => proc.mop.symbol_class,
        Node::Leaf(OpaqueValue::Instance(idx)) => proc
            .mop
            .get_instance(*idx as usize)
            .map(|i| i.class)
            .unwrap_or(proc.mop.t_class),
        Node::Leaf(OpaqueValue::Class(id)) => proc
            .mop
            .get_class(crate::clos::ClassId(*id))
            .map(|c| c.metaclass)
            .unwrap_or(proc.mop.standard_class),
        Node::Leaf(OpaqueValue::Generic(_)) => proc.mop.standard_generic_function,
        Node::Leaf(OpaqueValue::Method(_)) => proc.mop.standard_method,
        Node::Leaf(OpaqueValue::SlotDefinition(_, _, direct)) => {
            if *direct {
                proc.mop.standard_direct_slot_definition
            } else {
                proc.mop.standard_effective_slot_definition
            }
        }
        Node::Leaf(OpaqueValue::EqlSpecializer(_)) => proc.mop.eql_specializer_class,
        _ => proc.mop.t_class,
    }
}

fn is_subclass(proc: &Process, sub: crate::clos::ClassId, sup: crate::clos::ClassId) -> bool {
    if sub == sup {
        return true;
    }
    proc.mop
        .get_class(sub)
        .map(|c| c.cpl.contains(&sup))
        .unwrap_or(false)
}

fn enforce_slot_type(
    proc: &Process,
    ctx: &crate::context::GlobalContext,
    slot: &crate::clos::SlotDefinition,
    value: NodeId,
) -> Result<(), ControlSignal> {
    let Some(type_node) = slot.slot_type else {
        return Ok(());
    };

    let required_class = match proc.arena.inner.get_unchecked(type_node) {
        Node::Leaf(OpaqueValue::Symbol(id)) => {
            let sym = SymbolId(*id);
            let t_sym = cl_symbol_id(ctx, "T");
            if sym == t_sym {
                return Ok(());
            }
            proc.mop.find_class(sym)
        }
        Node::Leaf(OpaqueValue::Class(id)) => Some(crate::clos::ClassId(*id)),
        _ => None,
    };

    if let Some(req) = required_class {
        if req == proc.mop.t_class {
            return Ok(());
        }
        let val_class = value_class_id(proc, value);
        if val_class == proc.mop.t_class {
            return Ok(());
        }
        if !is_subclass(proc, val_class, req) {
            return Err(ControlSignal::Error("Slot type mismatch".to_string()));
        }
    }

    Ok(())
}

fn slot_map_for_class(
    proc: &Process,
    class_id: crate::clos::ClassId,
) -> Result<HashMap<SymbolId, usize>, ControlSignal> {
    let class = proc
        .mop
        .get_class(class_id)
        .ok_or_else(|| ControlSignal::Error("Class missing".into()))?;
    let mut slot_map = HashMap::default();
    for slot in &class.slots {
        slot_map.insert(slot.name, slot.index);
    }
    Ok(slot_map)
}

fn cl_symbol_id(ctx: &crate::context::GlobalContext, name: &str) -> SymbolId {
    ctx.symbols
        .write()
        .unwrap()
        .intern_in(name, PackageId(1))
}

fn resolve_slot_def(
    proc: &Process,
    class_id: crate::clos::ClassId,
    idx: usize,
    direct: bool,
) -> Option<crate::clos::SlotDefinition> {
    if class_id.0 == crate::clos::STANDALONE_SLOT_DEF_CLASS_ID {
        return proc
            .mop
            .get_standalone_slot_def(idx as u32)
            .cloned();
    }
    proc.mop.get_class(class_id).and_then(|class| {
        if direct {
            class.direct_slots.get(idx).cloned()
        } else {
            class.slots.get(idx).cloned()
        }
    })
}

fn ensure_class_metaobject(
    proc: &mut Process,
    _ctx: &crate::context::GlobalContext,
    class_id: crate::clos::ClassId,
) -> Result<usize, ControlSignal> {
    if let Some(idx) = proc.mop.get_class_meta_instance(class_id) {
        return Ok(idx);
    }
    let unbound = proc.make_unbound();
    let meta_id = proc
        .mop
        .get_class(class_id)
        .map(|c| c.metaclass)
        .unwrap_or(proc.mop.standard_class);
    let inst_idx = proc
        .mop
        .make_instance(meta_id, unbound)
        .ok_or_else(|| ControlSignal::Error("Failed to allocate class metaobject".into()))?;
    proc.mop.set_class_meta_instance(class_id, inst_idx);
    Ok(inst_idx)
}

fn ensure_generic_metaobject(
    proc: &mut Process,
    _ctx: &crate::context::GlobalContext,
    generic_id: crate::clos::GenericId,
) -> Result<usize, ControlSignal> {
    if let Some(idx) = proc.mop.get_generic_meta_instance(generic_id) {
        return Ok(idx);
    }
    let unbound = proc.make_unbound();
    let inst_idx = proc
        .mop
        .make_instance(proc.mop.standard_generic_function, unbound)
        .ok_or_else(|| ControlSignal::Error("Failed to allocate generic metaobject".into()))?;
    proc.mop.set_generic_meta_instance(generic_id, inst_idx);
    Ok(inst_idx)
}

fn ensure_method_metaobject(
    proc: &mut Process,
    _ctx: &crate::context::GlobalContext,
    method_id: crate::clos::MethodId,
) -> Result<usize, ControlSignal> {
    if let Some(idx) = proc.mop.get_method_meta_instance(method_id) {
        return Ok(idx);
    }
    let unbound = proc.make_unbound();
    let inst_idx = proc
        .mop
        .make_instance(proc.mop.standard_method, unbound)
        .ok_or_else(|| ControlSignal::Error("Failed to allocate method metaobject".into()))?;
    proc.mop.set_method_meta_instance(method_id, inst_idx);
    Ok(inst_idx)
}

fn ensure_slot_def_metaobject(
    proc: &mut Process,
    _ctx: &crate::context::GlobalContext,
    class_id: crate::clos::ClassId,
    slot_idx: u32,
    direct: bool,
) -> Result<usize, ControlSignal> {
    if let Some(idx) = proc
        .mop
        .get_slot_def_meta_instance(class_id, slot_idx, direct)
    {
        return Ok(idx);
    }
    let unbound = proc.make_unbound();
    let class = if direct {
        proc.mop.standard_direct_slot_definition
    } else {
        proc.mop.standard_effective_slot_definition
    };
    let inst_idx = proc
        .mop
        .make_instance(class, unbound)
        .ok_or_else(|| ControlSignal::Error("Failed to allocate slot-definition metaobject".into()))?;
    proc.mop
        .set_slot_def_meta_instance(class_id, slot_idx, direct, inst_idx);
    Ok(inst_idx)
}

fn sync_class_metaobject(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    class_id: crate::clos::ClassId,
) -> Result<(), ControlSignal> {
    let inst_idx = ensure_class_metaobject(proc, ctx, class_id)?;
    let (
        class_name,
        supers,
        subs,
        cpl,
        direct_len,
        slots_len,
        finalized_flag,
        inst_size,
        direct_default_initargs,
        default_initargs,
        metaclass_id,
    ) = {
        let class = proc
            .mop
            .get_class(class_id)
            .ok_or_else(|| ControlSignal::Error("Class missing".into()))?;
        (
            class.name,
            class.supers.clone(),
            class.direct_subclasses.clone(),
            class.cpl.clone(),
            class.direct_slots.len(),
            class.slots.len(),
            class.finalized,
            class.instance_size,
            class.direct_default_initargs.clone(),
            class.default_initargs.clone(),
            class.metaclass,
        )
    };

    // Map slot name -> index using metaclass effective slots.
    let sc_slots = {
        let sc = proc
            .mop
            .get_class(metaclass_id)
            .ok_or_else(|| ControlSignal::Error("Metaclass missing".into()))?;
        sc.slots.clone()
    };
    let mut slot_map: HashMap<SymbolId, usize> = HashMap::default();
    for slot in &sc_slots {
        slot_map.insert(slot.name, slot.index);
    }

    let name_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(class_name.0)));
    let direct_supers = make_class_list(proc, &supers);
    let direct_subs = make_class_list(proc, &subs);
    let cpl = make_class_list(proc, &cpl);

    let direct_slots = {
        let mut nodes = Vec::with_capacity(direct_len);
        for idx in 0..direct_len {
            nodes.push(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::SlotDefinition(
                class_id.0,
                idx as u32,
                true,
            ))));
        }
        proc.make_list(&nodes)
    };

    let slots = {
        let mut nodes = Vec::with_capacity(slots_len);
        for idx in 0..slots_len {
            nodes.push(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::SlotDefinition(
                class_id.0,
                idx as u32,
                false,
            ))));
        }
        proc.make_list(&nodes)
    };

    let finalized = if finalized_flag {
        proc.make_t(ctx)
    } else {
        proc.make_nil()
    };
    let instance_size = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Integer(inst_size as i64)));
    let direct_default_initargs = make_initargs_plist(proc, &direct_default_initargs);
    let default_initargs = make_initargs_plist(proc, &default_initargs);

    let mut set_slot = |sym: &str, value: NodeId| {
        let sym_id = ctx
            .symbols
            .read()
            .unwrap()
            .get_package(PackageId(1))
            .and_then(|p| p.find_symbol(sym))
            .unwrap_or(SymbolId(0));
        if let Some(&idx) = slot_map.get(&sym_id) {
            proc.mop.set_slot_value(inst_idx, idx, value);
        }
    };

    set_slot("NAME", name_node);
    set_slot("DIRECT-SUPERCLASSES", direct_supers);
    set_slot("DIRECT-SUBCLASSES", direct_subs);
    set_slot("DIRECT-SLOTS", direct_slots);
    set_slot("CLASS-PRECEDENCE-LIST", cpl);
    set_slot("SLOTS", slots);
    set_slot("FINALIZED-P", finalized);
    set_slot("INSTANCE-SIZE", instance_size);
    set_slot("DIRECT-DEFAULT-INITARGS", direct_default_initargs);
    set_slot("DEFAULT-INITARGS", default_initargs);

    Ok(())
}

fn sync_generic_metaobject(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    generic_id: crate::clos::GenericId,
) -> Result<(), ControlSignal> {
    let inst_idx = ensure_generic_metaobject(proc, ctx, generic_id)?;
    let (gf_name, gf_lambda_list, gf_methods, gf_method_combination, gf_arg_precedence) = {
        let gf = proc
            .mop
            .get_generic(generic_id)
            .ok_or_else(|| ControlSignal::Error("Generic function missing".into()))?;
        (
            gf.name,
            gf.lambda_list.clone(),
            gf.methods.clone(),
            gf.method_combination.clone(),
            gf.argument_precedence_order
                .as_ref()
                .cloned()
                .unwrap_or_else(|| gf.required_parameters.clone()),
        )
    };

    let slot_map = slot_map_for_class(proc, proc.mop.standard_generic_function)?;

    let name_node = generic_name_to_node(proc, ctx, gf_name);
    let lambda_list = make_symbol_list(proc, &gf_lambda_list);
    let methods = make_method_list(proc, &gf_methods);
    let method_combination = {
        let sym_id = match &gf_method_combination {
            crate::clos::MethodCombination::Standard => cl_symbol_id(ctx, "STANDARD"),
            crate::clos::MethodCombination::Operator { name, .. } => *name,
            crate::clos::MethodCombination::UserLong { name, .. } => *name,
        };
        proc.arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0)))
    };

    let arg_precedence = make_symbol_list(proc, &gf_arg_precedence);

    let mut set_slot = |name: &str, value: NodeId| {
        let sym_id = cl_symbol_id(ctx, name);
        if let Some(&idx) = slot_map.get(&sym_id) {
            proc.mop.set_slot_value(inst_idx, idx, value);
        }
    };

    set_slot("NAME", name_node);
    set_slot("LAMBDA-LIST", lambda_list);
    set_slot("METHODS", methods);
    set_slot("METHOD-COMBINATION", method_combination);
    set_slot("ARGUMENT-PRECEDENCE-ORDER", arg_precedence);

    Ok(())
}

fn sync_method_metaobject(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    method_id: crate::clos::MethodId,
) -> Result<(), ControlSignal> {
    let inst_idx = ensure_method_metaobject(proc, ctx, method_id)?;
    let (lambda_list_src, qualifiers_src, specializers_src, generic_src, body_src) = {
        let method = proc
            .mop
            .get_method(method_id)
            .ok_or_else(|| ControlSignal::Error("Method missing".into()))?;
        (
            method.lambda_list.clone(),
            method.qualifiers.clone(),
            method.specializers.clone(),
            method.generic,
            method.body,
        )
    };

    let slot_map = slot_map_for_class(proc, proc.mop.standard_method)?;

    let lambda_list = make_symbol_list(proc, &lambda_list_src);
    let qualifiers = make_symbol_list(proc, &qualifiers_src);
    let mut spec_nodes = Vec::with_capacity(specializers_src.len());
    for spec in &specializers_src {
        spec_nodes.push(specializer_to_node(proc, spec));
    }
    let specializers = proc.make_list(&spec_nodes);
    let generic_function = if let Some(gid) = generic_src {
        proc.arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Generic(gid.0)))
    } else {
        proc.make_nil()
    };
    let function = body_src;

    let mut set_slot = |name: &str, value: NodeId| {
        let sym_id = cl_symbol_id(ctx, name);
        if let Some(&idx) = slot_map.get(&sym_id) {
            proc.mop.set_slot_value(inst_idx, idx, value);
        }
    };

    set_slot("LAMBDA-LIST", lambda_list);
    set_slot("QUALIFIERS", qualifiers);
    set_slot("SPECIALIZERS", specializers);
    set_slot("GENERIC-FUNCTION", generic_function);
    set_slot("FUNCTION", function);

    Ok(())
}

fn sync_slot_def_metaobject(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    class_id: crate::clos::ClassId,
    slot_idx: u32,
    direct: bool,
) -> Result<(), ControlSignal> {
    let inst_idx = ensure_slot_def_metaobject(proc, ctx, class_id, slot_idx, direct)?;
    let slot = resolve_slot_def(proc, class_id, slot_idx as usize, direct)
        .ok_or_else(|| ControlSignal::Error("Slot definition missing".into()))?;
    let (
        slot_name,
        slot_initform,
        slot_initfunction,
        slot_initarg,
        slot_readers,
        slot_writers,
        slot_allocation,
        slot_type,
        slot_index,
    ) = (
        slot.name,
        slot.initform,
        slot.initfunction,
        slot.initarg,
        slot.readers.clone(),
        slot.writers.clone(),
        slot.allocation,
        slot.slot_type,
        slot.index,
    );

    let slot_class = if direct {
        proc.mop.standard_direct_slot_definition
    } else {
        proc.mop.standard_effective_slot_definition
    };
    let slot_map = slot_map_for_class(proc, slot_class)?;

    let name_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(slot_name.0)));
    let initform = slot_initform.unwrap_or(proc.make_nil());
    let initfunction = slot_initfunction.unwrap_or(proc.make_nil());
    let initargs = if let Some(initarg) = slot_initarg {
        let node = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(initarg.0)));
        proc.make_list(&[node])
    } else {
        proc.make_nil()
    };
    let readers = make_symbol_list(proc, &slot_readers);
    let writers = make_symbol_list(proc, &slot_writers);
    let allocation = {
        let name = match slot_allocation {
            crate::clos::SlotAllocation::Instance => "INSTANCE",
            crate::clos::SlotAllocation::Class => "CLASS",
        };
        let sym_id = ctx
            .symbols
            .write()
            .unwrap()
            .intern_in(name, PackageId(0));
        proc.arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0)))
    };
    let slot_type = slot_type.unwrap_or(proc.make_nil());
    let location = if slot_allocation == crate::clos::SlotAllocation::Instance
        && slot_index != usize::MAX
    {
        proc.arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Integer(slot_index as i64)))
    } else {
        proc.make_nil()
    };

    let mut set_slot = |name: &str, value: NodeId| {
        let sym_id = cl_symbol_id(ctx, name);
        if let Some(&idx) = slot_map.get(&sym_id) {
            proc.mop.set_slot_value(inst_idx, idx, value);
        }
    };

    set_slot("NAME", name_node);
    set_slot("INITFORM", initform);
    set_slot("INITFUNCTION", initfunction);
    set_slot("INITARGS", initargs);
    set_slot("READERS", readers);
    set_slot("WRITERS", writers);
    set_slot("ALLOCATION", allocation);
    set_slot("TYPE", slot_type);
    set_slot("LOCATION", location);

    Ok(())
}

fn instance_index_from_node(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    node: NodeId,
) -> Result<usize, ControlSignal> {
    match proc.arena.inner.get_unchecked(node).clone() {
        Node::Leaf(OpaqueValue::Instance(idx)) => Ok(idx as usize),
        Node::Leaf(OpaqueValue::Class(id)) => {
            let cid = crate::clos::ClassId(id);
            let idx = ensure_class_metaobject(proc, ctx, cid)?;
            let _ = sync_class_metaobject(proc, ctx, cid);
            Ok(idx)
        }
        Node::Leaf(OpaqueValue::Generic(id)) => {
            let gid = crate::clos::GenericId(id);
            let idx = ensure_generic_metaobject(proc, ctx, gid)?;
            let _ = sync_generic_metaobject(proc, ctx, gid);
            Ok(idx)
        }
        Node::Leaf(OpaqueValue::Method(id)) => {
            let mid = crate::clos::MethodId(id);
            let idx = ensure_method_metaobject(proc, ctx, mid)?;
            let _ = sync_method_metaobject(proc, ctx, mid);
            Ok(idx)
        }
        Node::Leaf(OpaqueValue::SlotDefinition(class_id, slot_idx, direct)) => {
            let cid = crate::clos::ClassId(class_id);
            let idx = ensure_slot_def_metaobject(proc, ctx, cid, slot_idx, direct)?;
            let _ = sync_slot_def_metaobject(proc, ctx, cid, slot_idx, direct);
            Ok(idx)
        }
        _ => Err(ControlSignal::Error(
            "Expected instance or class object".to_string(),
        )),
    }
}

fn parse_keywords_list(proc: &Process, args: &[NodeId]) -> HashMap<SymbolId, NodeId> {
    let mut keywords = HashMap::default();
    let mut i = 0;
    while i < args.len() {
        if i + 1 >= args.len() {
            break;
        }
        if let Some(key) = node_to_symbol(proc, args[i]) {
            // ANSI: the leftmost occurrence wins.
            if !keywords.contains_key(&key) {
                keywords.insert(key, args[i + 1]);
            }
        }
        i += 2;
    }
    keywords
}

fn parse_slot_def(
    proc: &mut Process,
    spec: NodeId,
    index: usize,
    ctx: &crate::context::GlobalContext,
) -> Result<crate::clos::SlotDefinition, crate::eval::ControlSignal> {
    use crate::clos::SlotDefinition;

    let (name_node, rest) = match proc.arena.inner.get_unchecked(spec) {
        Node::Leaf(OpaqueValue::Symbol(_)) => (spec, proc.make_nil()),
        Node::Fork(h, t) => (*h, *t),
        _ => {
            return Err(crate::eval::ControlSignal::Error(
                "Invalid slot spec".to_string(),
            ))
        }
    };

    let name = node_to_symbol(proc, name_node)
        .ok_or_else(|| crate::eval::ControlSignal::Error("Slot name must be symbol".to_string()))?;

    let rest_vec = list_to_vec(proc, rest);
    let props = parse_keywords_list(proc, &rest_vec);

    let syms = ctx.symbols.read().unwrap();
    let keyword_pkg = syms.get_package(crate::symbol::PackageId(0));

    let k_initform = keyword_pkg.and_then(|p| p.find_external("INITFORM"));
    let k_initfunction = keyword_pkg.and_then(|p| p.find_external("INITFUNCTION"));
    let k_initarg = keyword_pkg.and_then(|p| p.find_external("INITARG"));
    let k_reader = keyword_pkg.and_then(|p| p.find_external("READER"));
    let k_writer = keyword_pkg.and_then(|p| p.find_external("WRITER"));
    let k_accessor = keyword_pkg.and_then(|p| p.find_external("ACCESSOR"));
    let k_allocation = keyword_pkg.and_then(|p| p.find_external("ALLOCATION"));
    let k_type = keyword_pkg.and_then(|p| p.find_external("TYPE"));
    drop(syms);

    let initform = k_initform.and_then(|k| props.get(&k)).copied();
    let initfunction = k_initfunction.and_then(|k| props.get(&k)).copied();
    let initarg = k_initarg
        .and_then(|k| props.get(&k))
        .and_then(|&n| node_to_symbol(proc, n));

    let mut readers = Vec::new();
    let mut writers = Vec::new();

    if let Some(k) = k_reader {
        if let Some(&r) = props.get(&k) {
            if let Some(s) = node_to_symbol(proc, r) {
                readers.push(s);
            }
        }
    }
    if let Some(k) = k_writer {
        if let Some(&w) = props.get(&k) {
            if let Some(s) = node_to_symbol(proc, w) {
                writers.push(s);
            }
        }
    }
    if let Some(k) = k_accessor {
        if let Some(&a) = props.get(&k) {
            if let Some(s) = node_to_symbol(proc, a) {
                readers.push(s);
                writers.push(s);
            }
        }
    }

    let allocation = if let Some(k) = k_allocation {
        if let Some(&alloc_node) = props.get(&k) {
            if let Some(sym) = node_to_symbol(proc, alloc_node) {
                let name = ctx
                    .symbols
                    .read()
                    .unwrap()
                    .symbol_name(sym)
                    .unwrap_or("")
                    .to_string();
                if name == "CLASS" {
                    crate::clos::SlotAllocation::Class
                } else {
                    crate::clos::SlotAllocation::Instance
                }
            } else {
                crate::clos::SlotAllocation::Instance
            }
        } else {
            crate::clos::SlotAllocation::Instance
        }
    } else {
        crate::clos::SlotAllocation::Instance
    };

    let slot_type = k_type.and_then(|k| props.get(&k)).copied();

    Ok(SlotDefinition {
        name,
        initform,
        initfunction,
        initarg,
        readers,
        writers,
        allocation,
        slot_type,
        class_value: None,
        index,
    })
}

fn parse_symbol_list(proc: &Process, node: NodeId) -> Vec<SymbolId> {
    if let Some(sym) = node_to_symbol(proc, node) {
        return vec![sym];
    }
    let mut out = Vec::new();
    let mut curr = node;
    while let Node::Fork(head, tail) = proc.arena.inner.get_unchecked(curr).clone() {
        if let Some(sym) = node_to_symbol(proc, head) {
            out.push(sym);
        }
        curr = tail;
    }
    out
}

fn parse_slot_def_from_initargs(
    proc: &Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> Result<crate::clos::SlotDefinition, ControlSignal> {
    use crate::clos::SlotDefinition;

    let props = parse_keywords_list(proc, args);

    let syms = ctx.symbols.read().unwrap();
    let keyword_pkg = syms.get_package(crate::symbol::PackageId(0));

    let k_name = keyword_pkg.and_then(|p| p.find_external("NAME"));
    let k_initform = keyword_pkg.and_then(|p| p.find_external("INITFORM"));
    let k_initfunction = keyword_pkg.and_then(|p| p.find_external("INITFUNCTION"));
    let k_initargs = keyword_pkg.and_then(|p| p.find_external("INITARGS"));
    let k_readers = keyword_pkg.and_then(|p| p.find_external("READERS"));
    let k_writers = keyword_pkg.and_then(|p| p.find_external("WRITERS"));
    let k_allocation = keyword_pkg.and_then(|p| p.find_external("ALLOCATION"));
    let k_type = keyword_pkg.and_then(|p| p.find_external("TYPE"));
    let k_location = keyword_pkg.and_then(|p| p.find_external("LOCATION"));
    drop(syms);

    let name_node = k_name
        .and_then(|k| props.get(&k))
        .copied()
        .ok_or(ControlSignal::Error(
            "MAKE-DIRECT-SLOT-DEFINITION requires :NAME".to_string(),
        ))?;
    let name = node_to_symbol(proc, name_node)
        .ok_or(ControlSignal::Error("Slot name must be symbol".to_string()))?;

    let initform = k_initform.and_then(|k| props.get(&k)).copied();
    let initfunction = k_initfunction.and_then(|k| props.get(&k)).copied();

    let initarg = k_initargs.and_then(|k| props.get(&k)).and_then(|&n| {
        if let Some(sym) = node_to_symbol(proc, n) {
            Some(sym)
        } else {
            list_to_vec(proc, n)
                .into_iter()
                .find_map(|node| node_to_symbol(proc, node))
        }
    });

    let readers = k_readers
        .and_then(|k| props.get(&k))
        .map(|&n| parse_symbol_list(proc, n))
        .unwrap_or_default();
    let writers = k_writers
        .and_then(|k| props.get(&k))
        .map(|&n| parse_symbol_list(proc, n))
        .unwrap_or_default();

    let allocation = if let Some(k) = k_allocation {
        if let Some(&alloc_node) = props.get(&k) {
            if let Some(sym) = node_to_symbol(proc, alloc_node) {
                let name = ctx
                    .symbols
                    .read()
                    .unwrap()
                    .symbol_name(sym)
                    .unwrap_or("")
                    .to_string();
                if name == "CLASS" {
                    crate::clos::SlotAllocation::Class
                } else {
                    crate::clos::SlotAllocation::Instance
                }
            } else {
                crate::clos::SlotAllocation::Instance
            }
        } else {
            crate::clos::SlotAllocation::Instance
        }
    } else {
        crate::clos::SlotAllocation::Instance
    };

    let slot_type = k_type.and_then(|k| props.get(&k)).copied();

    let mut index = usize::MAX;
    if let Some(k) = k_location {
        if let Some(&loc_node) = props.get(&k) {
            if let Node::Leaf(OpaqueValue::Integer(n)) = proc.arena.inner.get_unchecked(loc_node) {
                if *n >= 0 {
                    index = *n as usize;
                }
            }
        }
    }

    Ok(SlotDefinition {
        name,
        initform,
        initfunction,
        initarg,
        readers,
        writers,
        allocation,
        slot_type,
        class_value: None,
        index,
    })
}

fn prim_make_direct_slot_definition(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return Err(ControlSignal::Error(
            "MAKE-DIRECT-SLOT-DEFINITION requires initargs".to_string(),
        ));
    }
    let start = if class_id_from_node(proc, args[0]).is_some() {
        1
    } else {
        0
    };
    if start >= args.len() {
        return Err(ControlSignal::Error(
            "MAKE-DIRECT-SLOT-DEFINITION requires initargs".to_string(),
        ));
    }
    let slot = parse_slot_def_from_initargs(proc, ctx, &args[start..])?;
    let idx = proc.mop.add_standalone_slot_def(slot);
    Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::SlotDefinition(
        crate::clos::STANDALONE_SLOT_DEF_CLASS_ID,
        idx,
        true,
    ))))
}

fn prim_make_effective_slot_definition(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return Err(ControlSignal::Error(
            "MAKE-EFFECTIVE-SLOT-DEFINITION requires initargs".to_string(),
        ));
    }
    let start = if class_id_from_node(proc, args[0]).is_some() {
        1
    } else {
        0
    };
    if start >= args.len() {
        return Err(ControlSignal::Error(
            "MAKE-EFFECTIVE-SLOT-DEFINITION requires initargs".to_string(),
        ));
    }
    let slot = parse_slot_def_from_initargs(proc, ctx, &args[start..])?;
    let idx = proc.mop.add_standalone_slot_def(slot);
    Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::SlotDefinition(
        crate::clos::STANDALONE_SLOT_DEF_CLASS_ID,
        idx,
        false,
    ))))
}

fn update_instances_for_redefined_class(
    proc: &mut Process,
    class_id: crate::clos::ClassId,
    old_slots: &[crate::clos::SlotDefinition],
) {
    let unbound = proc.make_unbound();
    let mut old_map: HashMap<SymbolId, usize> = HashMap::default();
    for slot in old_slots {
        if slot.allocation == crate::clos::SlotAllocation::Instance {
            old_map.insert(slot.name, slot.index);
        }
    }

    let new_slots = match proc.mop.get_class(class_id) {
        Some(class) => class.slots.clone(),
        None => return,
    };
    let new_size = proc
        .mop
        .get_class(class_id)
        .map(|c| c.instance_size)
        .unwrap_or(0);

    let inst_count = proc.mop.instance_count();
    for idx in 0..inst_count {
        let needs_update = proc
            .mop
            .get_instance(idx)
            .map(|inst| inst.class == class_id)
            .unwrap_or(false);
        if !needs_update {
            continue;
        }
        if let Some(inst) = proc.mop.get_instance_mut(idx) {
            let old_values = inst.slots.clone();
            let mut new_values = vec![unbound; new_size];
            for slot in &new_slots {
                if slot.allocation != crate::clos::SlotAllocation::Instance {
                    continue;
                }
                if let Some(old_idx) = old_map.get(&slot.name) {
                    if let Some(val) = old_values.get(*old_idx) {
                        new_values[slot.index] = *val;
                        continue;
                    }
                }
                if let Some(form) = slot.initform {
                    new_values[slot.index] = form;
                }
            }
            inst.slots = new_values;
        }
    }
}

fn define_slot_accessors(
    proc: &mut Process,
    ctx: &crate::context::GlobalContext,
    class_id: crate::clos::ClassId,
    slots: &[crate::clos::SlotDefinition],
) -> Result<(), ControlSignal> {
    let cl_pkg = crate::symbol::PackageId(1);
    let mut syms = ctx.symbols.write().unwrap();
    let slot_value_sym = syms.intern_in("SLOT-VALUE", cl_pkg);
    let set_slot_value_sym = syms.intern_in("SET-SLOT-VALUE", cl_pkg);
    let quote_sym = syms.intern_in("QUOTE", cl_pkg);
    let obj_sym = syms.intern_in("OBJ", cl_pkg);
    let val_sym = syms.intern_in("VALUE", cl_pkg);
    syms.export_symbol(slot_value_sym);
    syms.export_symbol(set_slot_value_sym);
    syms.export_symbol(quote_sym);
    syms.export_symbol(obj_sym);
    syms.export_symbol(val_sym);
    drop(syms);

    let slot_value_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(slot_value_sym.0)));
    let set_slot_value_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(set_slot_value_sym.0)));
    let quote_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(quote_sym.0)));
    let obj_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(obj_sym.0)));
    let val_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(val_sym.0)));

    let kw_add_method = ctx
        .symbols
        .write()
        .unwrap()
        .intern_in("ADD-METHOD", PackageId(0));
    let kw_add_method_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(kw_add_method.0)));

    for slot in slots {
        let slot_sym_node = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(slot.name.0)));
        let quoted_slot = proc.make_list(&[quote_node, slot_sym_node]);

        // Readers
        for &reader in &slot.readers {
            let gf_id = proc.mop.define_generic(reader, vec![obj_sym]);
            let gf_node = proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Generic(gf_id.0)));
            proc.set_function(reader, gf_node);

            let body = proc.make_list(&[slot_value_node, obj_node, quoted_slot]);
            let mut lambda_list = ParsedLambdaList::default();
            lambda_list.req = vec![obj_node];
            let closure = Closure {
                lambda_list,
                destructuring: None,
                body,
                env: Environment::new(),
            };
            let closure_idx = proc.closures.len();
            proc.closures.push(closure);
            let closure_node = proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Closure(closure_idx as u32)));

            let method_id = proc.mop.add_method(
                gf_id,
                vec![crate::clos::Specializer::Class(class_id)],
                Vec::new(),
                vec![obj_sym],
                closure_node,
            );
            let method_node = proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Method(method_id.0)));
            notify_dependents(
                proc,
                ctx,
                DependentKey::Generic(gf_id),
                &[kw_add_method_node, method_node],
            )?;
        }

        // Writers (if also reader, use setf generic for accessor)
        for &writer in &slot.writers {
            if slot.readers.contains(&writer) {
                let gf_id = proc.mop.define_setf_generic_with_options(
                    writer,
                    vec![val_sym, obj_sym],
                    Vec::new(),
                    None,
                );
                let gf_node = proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Generic(gf_id.0)));
                proc.set_setf_function(writer, gf_node);

                let body = proc.make_list(&[
                    set_slot_value_node,
                    obj_node,
                    quoted_slot,
                    val_node,
                ]);
                let mut lambda_list = ParsedLambdaList::default();
                lambda_list.req = vec![val_node, obj_node];
                let closure = Closure {
                    lambda_list,
                    destructuring: None,
                    body,
                    env: Environment::new(),
                };
                let closure_idx = proc.closures.len();
                proc.closures.push(closure);
                let closure_node = proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Closure(closure_idx as u32)));

                let method_id = proc.mop.add_method(
                    gf_id,
                    vec![
                        crate::clos::Specializer::Class(proc.mop.t_class),
                        crate::clos::Specializer::Class(class_id),
                    ],
                    Vec::new(),
                    vec![val_sym, obj_sym],
                    closure_node,
                );
                let method_node = proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Method(method_id.0)));
                notify_dependents(
                    proc,
                    ctx,
                    DependentKey::Generic(gf_id),
                    &[kw_add_method_node, method_node],
                )?;
                continue;
            }

            let gf_id = proc.mop.define_generic(writer, vec![val_sym, obj_sym]);
            let gf_node = proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Generic(gf_id.0)));
            proc.set_function(writer, gf_node);

            let body = proc.make_list(&[
                set_slot_value_node,
                obj_node,
                quoted_slot,
                val_node,
            ]);
            let mut lambda_list = ParsedLambdaList::default();
            lambda_list.req = vec![val_node, obj_node];
            let closure = Closure {
                lambda_list,
                destructuring: None,
                body,
                env: Environment::new(),
            };
            let closure_idx = proc.closures.len();
            proc.closures.push(closure);
            let closure_node = proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Closure(closure_idx as u32)));

            let method_id = proc.mop.add_method(
                gf_id,
                vec![
                    crate::clos::Specializer::Class(proc.mop.t_class),
                    crate::clos::Specializer::Class(class_id),
                ],
                Vec::new(),
                vec![val_sym, obj_sym],
                closure_node,
            );
            let method_node = proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Method(method_id.0)));
            notify_dependents(
                proc,
                ctx,
                DependentKey::Generic(gf_id),
                &[kw_add_method_node, method_node],
            )?;
        }
    }

    Ok(())
}

pub(crate) fn prim_ensure_class(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    use crate::clos::ClassId;

    if args.is_empty() {
        return Err(crate::eval::ControlSignal::Error(
            "ENSURE-CLASS requires at least a name".to_string(),
        ));
    }

    let name_node = args[0];
    let name = node_to_symbol(proc, name_node).ok_or_else(|| {
        crate::eval::ControlSignal::Error("Class name must be a symbol".to_string())
    })?;
    let kwargs = parse_keywords_list(proc, &args[1..]);

    let syms = ctx.symbols.read().unwrap();
    let keyword_pkg = syms.get_package(crate::symbol::PackageId(0));
    let kw_supers = keyword_pkg.and_then(|p| p.find_external("DIRECT-SUPERCLASSES"));
    let kw_slots = keyword_pkg.and_then(|p| p.find_external("DIRECT-SLOTS"));
    let kw_metaclass = keyword_pkg.and_then(|p| p.find_external("METACLASS"));
    let kw_default_initargs = keyword_pkg.and_then(|p| p.find_external("DEFAULT-INITARGS"));
    drop(syms);

    let mut supers = Vec::new();
    if let Some(k) = kw_supers {
        if let Some(&supers_node) = kwargs.get(&k) {
            for head in list_to_vec(proc, supers_node) {
                let class_id = match proc.arena.inner.get_unchecked(head) {
                    Node::Leaf(OpaqueValue::Class(id)) => Some(ClassId(*id)),
                    Node::Leaf(OpaqueValue::Symbol(id)) => {
                        let sym = SymbolId(*id);
                        if let Some(cid) = proc.mop.find_class(sym) {
                            Some(cid)
                        } else {
                            // Allow forward-referenced superclasses by creating a stub.
                            Some(proc.mop.define_class(sym, Vec::new(), Vec::new()))
                        }
                    }
                    _ => None,
                };

                if let Some(cid) = class_id {
                    supers.push(cid);
                } else {
                    return Err(crate::eval::ControlSignal::Error(format!(
                        "Unknown superclass: {:?}",
                        head
                    )));
                }
            }
        }
    }

    let mut slots = Vec::new();
    if let Some(k) = kw_slots {
        if let Some(&slots_node) = kwargs.get(&k) {
            let mut index = 0;
            for head in list_to_vec(proc, slots_node) {
                let slot_def = parse_slot_def(proc, head, index, ctx)?;
                slots.push(slot_def);
                index += 1;
            }
        }
    }

    let mut metaclass = None;
    if let Some(k) = kw_metaclass {
        if let Some(&meta_node) = kwargs.get(&k) {
            metaclass = class_id_from_node(proc, meta_node);
        }
    }

    if let Some(meta_id) = metaclass {
        if meta_id == proc.mop.funcallable_standard_class
            && (supers.is_empty()
                || (supers.len() == 1 && supers[0] == proc.mop.standard_object))
        {
            supers = vec![proc.mop.funcallable_standard_object];
        }
    }

    let mut direct_default_initargs: Vec<(SymbolId, NodeId)> = Vec::new();
    if let Some(k) = kw_default_initargs {
        if let Some(&defaults_node) = kwargs.get(&k) {
            let mut seen = HashMap::default();
            let elems = list_to_vec(proc, defaults_node);
            let mut i = 0;
            while i + 1 < elems.len() {
                if let Some(key) = node_to_symbol(proc, elems[i]) {
                    if !seen.contains_key(&key) {
                        seen.insert(key, true);
                        direct_default_initargs.push((key, elems[i + 1]));
                    }
                }
                i += 2;
            }
        }
    }

    let old_slots = proc
        .mop
        .find_class(name)
        .and_then(|cid| proc.mop.get_class(cid).map(|c| c.slots.clone()));
    let class_existed = old_slots.is_some();

    let class_id = proc.mop.define_class_with_meta(
        name,
        supers,
        slots.clone(),
        metaclass,
        direct_default_initargs,
    );

    if let Some(old_slots) = old_slots {
        update_instances_for_redefined_class(proc, class_id, &old_slots);
    }

    // Define slot accessors for direct slots.
    let _ = define_slot_accessors(proc, ctx, class_id, &slots);

    // Sync class metaobjects for all classes (keeps direct-subclasses up to date).
    let class_ids = proc.mop.class_ids();
    for cid in class_ids {
        let _ = sync_class_metaobject(proc, ctx, cid);
    }
    if class_existed {
        notify_dependents(proc, ctx, DependentKey::Class(class_id), &args[1..])?;
    }
    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Class(class_id.0))))
}

fn prim_ensure_generic_function(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return Err(crate::eval::ControlSignal::Error(
            "ENSURE-GENERIC requires name".to_string(),
        ));
    }
    let name_node = args[0];
    let (name, is_setf) = if let Some(sym) = node_to_symbol(proc, name_node) {
        (sym, false)
    } else if let Some(sym) = setf_function_name_from_node(proc, name_node) {
        (sym, true)
    } else {
        return Err(crate::eval::ControlSignal::Error(
            "Generic name must be a symbol or (setf <symbol>)".to_string(),
        ));
    };
    let generic_existed = if is_setf {
        proc.mop.find_setf_generic(name).is_some()
    } else {
        proc.mop.find_generic(name).is_some()
    };

    let kwargs = parse_keywords_list(proc, &args[1..]);

    let syms = ctx.symbols.read().unwrap();
    let keyword_pkg = syms.get_package(crate::symbol::PackageId(0));
    let kw_lambda_list = keyword_pkg.and_then(|p| p.find_external("LAMBDA-LIST"));
    let kw_method_combination = keyword_pkg.and_then(|p| p.find_external("METHOD-COMBINATION"));
    let kw_arg_precedence =
        keyword_pkg.and_then(|p| p.find_external("ARGUMENT-PRECEDENCE-ORDER"));
    drop(syms);

    let mut lambda_list = Vec::new();
    if let Some(k) = kw_lambda_list {
        if let Some(&ll_node) = kwargs.get(&k) {
            for head in list_to_vec(proc, ll_node) {
                if let Some(s) = node_to_symbol(proc, head) {
                    lambda_list.push(s);
                } else {
                    return Err(crate::eval::ControlSignal::Error(format!(
                        "Invalid parameter in lambda list: {:?}",
                        head
                    )));
                }
            }
        }
    }

    let mut argument_precedence_order: Option<Vec<SymbolId>> = None;
    if let Some(k) = kw_arg_precedence {
        if let Some(&apo_node) = kwargs.get(&k) {
            let mut order = Vec::new();
            for head in list_to_vec(proc, apo_node) {
                if let Some(sym) = node_to_symbol(proc, head) {
                    order.push(sym);
                }
            }
            if !order.is_empty() {
                argument_precedence_order = Some(order);
            }
        }
    }

    // Parse argument-precedence-order option (list form: (:argument-precedence-order ...))
    if argument_precedence_order.is_none() {
        for &opt in &args[1..] {
            if let Node::Fork(head, tail) = proc.arena.inner.get_unchecked(opt) {
                if let Some(sym) = node_to_symbol(proc, *head) {
                    if let Some(k) = kw_arg_precedence {
                        if sym == k {
                            if let Node::Fork(order_node, _rest) =
                                proc.arena.inner.get_unchecked(*tail)
                            {
                                let mut order = Vec::new();
                                for head in list_to_vec(proc, *order_node) {
                                    if let Some(sym) = node_to_symbol(proc, head) {
                                        order.push(sym);
                                    }
                                }
                                if !order.is_empty() {
                                    argument_precedence_order = Some(order);
                                }
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    let required_parameters = {
        let syms = ctx.symbols.read().unwrap();
        let mut required = Vec::new();
        for sym in &lambda_list {
            let name = syms.symbol_name(*sym).unwrap_or("");
            if matches!(
                name,
                "&OPTIONAL" | "&REST" | "&KEY" | "&AUX" | "&ALLOW-OTHER-KEYS"
            ) {
                break;
            }
            required.push(*sym);
        }
        required
    };

    if let Some(order) = argument_precedence_order.as_mut() {
        order.retain(|sym| required_parameters.contains(sym));
        if order.is_empty() {
            argument_precedence_order = None;
        }
    }

    // Parse method-combination option (short form / keyword style).
    let mut method_combination_node = None;
    if let Some(k) = kw_method_combination {
        if let Some(&mc_node) = kwargs.get(&k) {
            method_combination_node = Some(mc_node);
        }
    }

    // Parse method-combination option (list form: (:method-combination comb ...))
    if method_combination_node.is_none() {
        for &opt in &args[1..] {
            if let Node::Fork(head, tail) = proc.arena.inner.get_unchecked(opt) {
                if let Some(sym) = node_to_symbol(proc, *head) {
                    if let Some(k) = kw_method_combination {
                        if sym == k {
                            if let Node::Fork(comb_node, _rest) =
                                proc.arena.inner.get_unchecked(*tail)
                            {
                                method_combination_node = Some(*comb_node);
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    let gid = if is_setf {
        proc.mop.define_setf_generic_with_options(
            name,
            lambda_list,
            required_parameters,
            argument_precedence_order,
        )
    } else {
        proc.mop.define_generic_with_options(
            name,
            lambda_list,
            required_parameters,
            argument_precedence_order,
        )
    };
    if let Some(mc_node) = method_combination_node {
        let mut comb_args = proc.make_nil();
        let comb_sym = if let Some(sym) = node_to_symbol(proc, mc_node) {
            Some(sym)
        } else if let Node::Fork(head, tail) = proc.arena.inner.get_unchecked(mc_node) {
            comb_args = *tail;
            node_to_symbol(proc, *head)
        } else {
            None
        };

        if let Some(comb_sym) = comb_sym {
            let comb_name = ctx
                .symbols
                .read()
                .unwrap()
                .symbol_name(comb_sym)
                .unwrap_or("")
                .to_string();

            use crate::clos::{MethodCombination, MethodCombinationDef};
            let comb = if let Some(def) = proc.mop.get_method_combination(comb_sym) {
                match def {
                    MethodCombinationDef::Operator {
                        operator,
                        identity_with_one_arg,
                    } => MethodCombination::Operator {
                        name: comb_sym,
                        operator: *operator,
                        identity_with_one_arg: *identity_with_one_arg,
                    },
                    MethodCombinationDef::Long { expander } => MethodCombination::UserLong {
                        name: comb_sym,
                        expander: *expander,
                        options: comb_args,
                    },
                }
            } else {
                match comb_name.as_str() {
                    "STANDARD" | "STANDARD-METHOD-COMBINATION" => MethodCombination::Standard,
                    "+" | "*" | "APPEND" | "LIST" | "MAX" | "MIN" | "NCONC" | "PROGN" | "AND"
                    | "OR" => MethodCombination::Operator {
                        name: comb_sym,
                        operator: comb_sym,
                        identity_with_one_arg: matches!(comb_name.as_str(), "AND" | "OR" | "PROGN"),
                    },
                    _ => {
                        return Err(crate::eval::ControlSignal::Error(format!(
                            "Unsupported method-combination: {}",
                            comb_name
                        )));
                    }
                }
            };

            proc.mop.set_generic_method_combination(gid, comb);
        }
    }
    let gf_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Generic(gid.0)));

    // Bind to function name in process
    if is_setf {
        proc.set_setf_function(name, gf_node);
    } else {
        proc.set_function(name, gf_node);
    }

    if generic_existed {
        notify_dependents(proc, ctx, DependentKey::Generic(gid), &args[1..])?;
    }

    Ok(gf_node)
}

fn prim_sys_allocate_instance(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return Err(crate::eval::ControlSignal::Error(
            "sys-allocate-instance requires class".to_string(),
        ));
    }

    let class_node = proc.arena.inner.get_unchecked(args[0]);
    let class_id = if let Node::Leaf(OpaqueValue::Class(id)) = class_node {
        crate::clos::ClassId(*id)
    } else if let Some(sym) = node_to_symbol(proc, args[0]) {
        if let Some(id) = proc.mop.find_class(sym) {
            id
        } else {
            return Err(crate::eval::ControlSignal::Error(format!(
                "sys-allocate-instance: Unknown class symbol: {:?}",
                class_node
            )));
        }
    } else {
        return Err(crate::eval::ControlSignal::Error(format!(
            "sys-allocate-instance: Invalid argument (Expected Class or Symbol): {:?}",
            class_node
        )));
    };

    let unbound = proc.make_unbound();
    if let Some(inst_idx) = proc.mop.make_instance(class_id, unbound) {
        Ok(proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Instance(inst_idx as u32))))
    } else {
        Err(crate::eval::ControlSignal::Error(
            "Failed to allocate instance".to_string(),
        ))
    }
}

fn prim_ensure_method(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    use crate::clos::GenericId;

    if args.is_empty() {
        return Err(crate::eval::ControlSignal::Error(
            "ENSURE-METHOD requires GF".to_string(),
        ));
    }

    let gf_node = args[0];
    let mut gf_name: Option<SymbolId> = None;
    let mut gf_setf_name: Option<SymbolId> = None;
    let gf_id = match proc.arena.inner.get_unchecked(gf_node) {
        Node::Leaf(OpaqueValue::Generic(id)) => GenericId(*id),
        Node::Leaf(OpaqueValue::Symbol(id)) => {
            let name = SymbolId(*id);
            gf_name = Some(name);
            if let Some(gid) = proc.mop.find_generic(name) {
                gid
            } else {
                proc.mop.define_generic(name, Vec::new())
            }
        }
        _ => {
            if let Some(sym) = setf_function_name_from_node(proc, gf_node) {
                gf_setf_name = Some(sym);
                if let Some(gid) = proc.mop.find_setf_generic(sym) {
                    gid
                } else {
                    proc.mop.define_setf_generic_with_options(sym, Vec::new(), Vec::new(), None)
                }
            } else {
                return Err(crate::eval::ControlSignal::Error(
                    "Invalid GF spec".to_string(),
                ));
            }
        }
    };

    let kwargs = parse_keywords_list(proc, &args[1..]);

    let syms = ctx.symbols.read().unwrap();
    let keyword_pkg = syms.get_package(crate::symbol::PackageId(0));
    let kw_specializers = keyword_pkg.and_then(|p| p.find_external("SPECIALIZERS"));
    let kw_qualifiers = keyword_pkg.and_then(|p| p.find_external("QUALIFIERS"));
    let kw_body = keyword_pkg.and_then(|p| p.find_external("BODY"));
    let kw_lambda_list = keyword_pkg.and_then(|p| p.find_external("LAMBDA-LIST"));
    drop(syms);

    let mut specializers = Vec::new();
    if let Some(k) = kw_specializers {
        if let Some(&specs_node) = kwargs.get(&k) {
            for head in list_to_vec(proc, specs_node) {
                specializers.push(parse_specializer_node(proc, ctx, head));
            }
        }
    }

    let mut qualifiers = Vec::new();
    if let Some(k) = kw_qualifiers {
        if let Some(&quals_node) = kwargs.get(&k) {
            for head in list_to_vec(proc, quals_node) {
                if let Some(s) = node_to_symbol(proc, head) {
                    qualifiers.push(s);
                }
            }
        }
    }

    let mut body = proc.make_nil();
    if let Some(k) = kw_body {
        if let Some(&b) = kwargs.get(&k) {
            body = b;
        }
    }

    let mut lambda_list = Vec::new();
    if let Some(k) = kw_lambda_list {
        if let Some(&ll_node) = kwargs.get(&k) {
            for head in list_to_vec(proc, ll_node) {
                if let Some(sym) = node_to_symbol(proc, head) {
                    lambda_list.push(sym);
                }
            }
        }
    }

    let method_id = proc
        .mop
        .add_method(gf_id, specializers, qualifiers, lambda_list, body);

    proc.fast_make_instance_ok = None;

    if let Some(name) = gf_name {
        let gf_node = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Generic(gf_id.0)));
        proc.set_function(name, gf_node);
    }
    if let Some(name) = gf_setf_name {
        let gf_node = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Generic(gf_id.0)));
        proc.set_setf_function(name, gf_node);
    }

    let method_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Method(method_id.0)));

    let kw_add_method = ctx
        .symbols
        .write()
        .unwrap()
        .intern_in("ADD-METHOD", PackageId(0));
    let kw_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(kw_add_method.0)));
    notify_dependents(
        proc,
        ctx,
        DependentKey::Generic(gf_id),
        &[kw_node, method_node],
    )?;

    Ok(method_node)
}

fn prim_register_method_combination(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return Err(ControlSignal::Error(
            "REGISTER-METHOD-COMBINATION requires name".to_string(),
        ));
    }

    let name = node_to_symbol(proc, args[0]).ok_or(ControlSignal::Error(
        "REGISTER-METHOD-COMBINATION name must be symbol".to_string(),
    ))?;

    let kwargs = parse_keywords_list(proc, &args[1..]);

    let syms = ctx.symbols.read().unwrap();
    let keyword_pkg = syms.get_package(crate::symbol::PackageId(0));
    let kw_type = keyword_pkg.and_then(|p| p.find_external("TYPE"));
    let kw_operator = keyword_pkg.and_then(|p| p.find_external("OPERATOR"));
    let kw_identity = keyword_pkg.and_then(|p| p.find_external("IDENTITY-WITH-ONE-ARGUMENT"));
    let kw_expander = keyword_pkg.and_then(|p| p.find_external("EXPANDER"));
    drop(syms);

    let type_name = kw_type
        .and_then(|k| kwargs.get(&k))
        .and_then(|node| node_to_symbol(proc, *node))
        .and_then(|sym| {
            ctx.symbols
                .read()
                .unwrap()
                .symbol_name(sym)
                .map(|s| s.to_string())
        })
        .unwrap_or_else(|| "OPERATOR".to_string());

    let has_expander = kw_expander.and_then(|k| kwargs.get(&k)).is_some();
    let is_long = has_expander || matches!(type_name.as_str(), "LONG" | "LONG-FORM");

    if is_long {
        let expander_node = kw_expander
            .and_then(|k| kwargs.get(&k))
            .copied()
            .ok_or(ControlSignal::Error(
                "REGISTER-METHOD-COMBINATION long form requires :EXPANDER".to_string(),
            ))?;

        if let Node::Leaf(OpaqueValue::Closure(_)) = proc.arena.inner.get_unchecked(expander_node)
        {
            proc.mop.register_method_combination(
                name,
                crate::clos::MethodCombinationDef::Long {
                    expander: expander_node,
                },
            );
            return Ok(proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(name.0))));
        }

        return Err(ControlSignal::Error(
            "REGISTER-METHOD-COMBINATION :EXPANDER must be a function".to_string(),
        ));
    }

    let operator_sym = if let Some(k) = kw_operator {
        if let Some(node) = kwargs.get(&k) {
            node_to_symbol(proc, *node).ok_or(ControlSignal::Error(
                "REGISTER-METHOD-COMBINATION :OPERATOR must be a symbol".to_string(),
            ))?
        } else {
            name
        }
    } else {
        name
    };

    let identity_with_one_arg = kw_identity
        .and_then(|k| kwargs.get(&k))
        .map(|node| !matches!(proc.arena.inner.get_unchecked(*node), Node::Leaf(OpaqueValue::Nil)))
        .unwrap_or(false);

    proc.mop.register_method_combination(
        name,
        crate::clos::MethodCombinationDef::Operator {
            operator: operator_sym,
            identity_with_one_arg,
        },
    );

    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(name.0))))
}

fn prim_method_qualifiers(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "METHOD-QUALIFIERS requires one argument".to_string(),
        ));
    }

    let method_id = match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::Method(id)) => crate::clos::MethodId(*id),
        _ => {
            return Err(ControlSignal::Error(
                "METHOD-QUALIFIERS expects a method object".to_string(),
            ))
        }
    };

    let qualifiers = proc
        .mop
        .get_method_qualifiers(method_id)
        .ok_or_else(|| ControlSignal::Error("Invalid method object".to_string()))?;

    let mut nodes = Vec::with_capacity(qualifiers.len());
    for &q in qualifiers {
        nodes.push(
            proc.arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(q.0))),
        );
    }

    Ok(proc.make_list(&nodes))
}

fn prim_class_name(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "CLASS-NAME requires one argument".to_string(),
        ));
    }
    if let Some(class_id) = class_id_from_node(proc, args[0]) {
        if let Some(class) = proc.mop.get_class(class_id) {
            return Ok(proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(class.name.0))));
        }
    }
    Ok(proc.make_nil())
}

fn prim_class_direct_superclasses(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "CLASS-DIRECT-SUPERCLASSES requires one argument".to_string(),
        ));
    }
    if let Some(class_id) = class_id_from_node(proc, args[0]) {
        if let Some(class) = proc.mop.get_class(class_id) {
            let supers = class.supers.clone();
            return Ok(make_class_list(proc, &supers));
        }
    }
    Ok(proc.make_nil())
}

fn prim_class_direct_subclasses(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "CLASS-DIRECT-SUBCLASSES requires one argument".to_string(),
        ));
    }
    if let Some(class_id) = class_id_from_node(proc, args[0]) {
        if let Some(subs) = proc.mop.get_class_direct_subclasses(class_id) {
            let subs = subs.to_vec();
            return Ok(make_class_list(proc, &subs));
        }
    }
    Ok(proc.make_nil())
}

fn prim_class_direct_slots(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "CLASS-DIRECT-SLOTS requires one argument".to_string(),
        ));
    }
    if let Some(class_id) = class_id_from_node(proc, args[0]) {
        if let Some(slots) = proc.mop.get_class_direct_slots(class_id) {
            let mut nodes = Vec::with_capacity(slots.len());
            for (idx, _slot) in slots.iter().enumerate() {
                nodes.push(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::SlotDefinition(
                    class_id.0,
                    idx as u32,
                    true,
                ))));
            }
            return Ok(proc.make_list(&nodes));
        }
    }
    Ok(proc.make_nil())
}

fn prim_class_slots(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "CLASS-SLOTS requires one argument".to_string(),
        ));
    }
    if let Some(class_id) = class_id_from_node(proc, args[0]) {
        if let Some(slots) = proc.mop.get_class(class_id) {
            let mut nodes = Vec::with_capacity(slots.slots.len());
            for (idx, _slot) in slots.slots.iter().enumerate() {
                nodes.push(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::SlotDefinition(
                    class_id.0,
                    idx as u32,
                    false,
                ))));
            }
            return Ok(proc.make_list(&nodes));
        }
    }
    Ok(proc.make_nil())
}

fn prim_sys_class_direct_methods(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "SYS-CLASS-DIRECT-METHODS requires one argument".to_string(),
        ));
    }
    let class_id = class_id_from_node(proc, args[0]).ok_or_else(|| {
        ControlSignal::Error("SYS-CLASS-DIRECT-METHODS expects a class".to_string())
    })?;
    let methods = proc.mop.class_direct_methods(class_id);
    Ok(make_method_list(proc, &methods))
}

fn prim_sys_class_direct_generic_functions(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "SYS-CLASS-DIRECT-GENERIC-FUNCTIONS requires one argument".to_string(),
        ));
    }
    let class_id = class_id_from_node(proc, args[0]).ok_or_else(|| {
        ControlSignal::Error(
            "SYS-CLASS-DIRECT-GENERIC-FUNCTIONS expects a class".to_string(),
        )
    })?;
    let generics = proc.mop.class_direct_generic_functions(class_id);
    let mut nodes = Vec::with_capacity(generics.len());
    for gid in generics {
        nodes.push(
            proc.arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Generic(gid.0))),
        );
    }
    Ok(proc.make_list(&nodes))
}

fn prim_sys_specializer_direct_methods(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "SYS-SPECIALIZER-DIRECT-METHODS requires one argument".to_string(),
        ));
    }
    let spec = specializer_from_node(proc, ctx, args[0])?;
    let methods = proc.mop.specializer_direct_methods(&spec);
    Ok(make_method_list(proc, &methods))
}

fn prim_sys_specializer_direct_generic_functions(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "SYS-SPECIALIZER-DIRECT-GENERIC-FUNCTIONS requires one argument".to_string(),
        ));
    }
    let spec = specializer_from_node(proc, ctx, args[0])?;
    let generics = proc.mop.specializer_direct_generic_functions(&spec);
    let mut nodes = Vec::with_capacity(generics.len());
    for gid in generics {
        nodes.push(
            proc.arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Generic(gid.0))),
        );
    }
    Ok(proc.make_list(&nodes))
}

fn prim_class_precedence_list(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "CLASS-PRECEDENCE-LIST requires one argument".to_string(),
        ));
    }
    if let Some(class_id) = class_id_from_node(proc, args[0]) {
        if let Some(class) = proc.mop.get_class(class_id) {
            let cpl = class.cpl.clone();
            return Ok(make_class_list(proc, &cpl));
        }
    }
    Ok(proc.make_nil())
}

fn prim_class_finalized_p(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "CLASS-FINALIZED-P requires one argument".to_string(),
        ));
    }
    if let Some(class_id) = class_id_from_node(proc, args[0]) {
        if let Some(class) = proc.mop.get_class(class_id) {
            return Ok(if class.finalized {
                proc.make_t(ctx)
            } else {
                proc.make_nil()
            });
        }
    }
    Ok(proc.make_nil())
}

fn prim_class_prototype(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "CLASS-PROTOTYPE requires one argument".to_string(),
        ));
    }
    if let Some(class_id) = class_id_from_node(proc, args[0]) {
        let unbound = proc.make_unbound();
        if let Some(inst_idx) = proc.mop.make_instance(class_id, unbound) {
            return Ok(proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Instance(inst_idx as u32))));
        }
    }
    Ok(proc.make_nil())
}

fn prim_class_direct_default_initargs(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "CLASS-DIRECT-DEFAULT-INITARGS requires one argument".to_string(),
        ));
    }
    if let Some(class_id) = class_id_from_node(proc, args[0]) {
        if let Some(class) = proc.mop.get_class(class_id) {
            let pairs = class.direct_default_initargs.clone();
            return Ok(make_initargs_plist(proc, &pairs));
        }
    }
    Ok(proc.make_nil())
}

fn prim_class_default_initargs(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "CLASS-DEFAULT-INITARGS requires one argument".to_string(),
        ));
    }
    if let Some(class_id) = class_id_from_node(proc, args[0]) {
        if let Some(class) = proc.mop.get_class(class_id) {
            let pairs = class.default_initargs.clone();
            return Ok(make_initargs_plist(proc, &pairs));
        }
    }
    Ok(proc.make_nil())
}

fn prim_generic_function_name(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "GENERIC-FUNCTION-NAME requires one argument".to_string(),
        ));
    }
    if let Some(gid) = generic_id_from_node(proc, args[0]) {
        if let Some(gf) = proc.mop.get_generic(gid) {
            return Ok(generic_name_to_node(proc, _ctx, gf.name));
        }
    }
    Ok(proc.make_nil())
}

fn prim_generic_function_lambda_list(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "GENERIC-FUNCTION-LAMBDA-LIST requires one argument".to_string(),
        ));
    }
    if let Some(gid) = generic_id_from_node(proc, args[0]) {
        if let Some(gf) = proc.mop.get_generic(gid) {
            let ll = gf.lambda_list.clone();
            return Ok(make_symbol_list(proc, &ll));
        }
    }
    Ok(proc.make_nil())
}

fn prim_generic_function_methods(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "GENERIC-FUNCTION-METHODS requires one argument".to_string(),
        ));
    }
    if let Some(gid) = generic_id_from_node(proc, args[0]) {
        if let Some(methods) = proc.mop.get_generic_methods(gid.0) {
            let mut nodes = Vec::with_capacity(methods.len());
            for mid in methods {
                nodes.push(
                    proc.arena
                        .inner
                        .alloc(Node::Leaf(OpaqueValue::Method(mid.0))),
                );
            }
            return Ok(proc.make_list(&nodes));
        }
    }
    Ok(proc.make_nil())
}

fn prim_generic_function_method_combination(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "GENERIC-FUNCTION-METHOD-COMBINATION requires one argument".to_string(),
        ));
    }
    if let Some(gid) = generic_id_from_node(proc, args[0]) {
        if let Some(gf) = proc.mop.get_generic(gid) {
            let sym_id = match &gf.method_combination {
                crate::clos::MethodCombination::Standard => {
                    ctx.symbols
                        .write()
                        .unwrap()
                        .intern_in("STANDARD", PackageId(1))
                }
                crate::clos::MethodCombination::Operator { name, .. } => *name,
                crate::clos::MethodCombination::UserLong { name, .. } => *name,
            };
            return Ok(proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0))));
        }
    }
    Ok(proc.make_nil())
}

fn prim_sys_generic_function_argument_precedence_order(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "SYS-GENERIC-FUNCTION-ARGUMENT-PRECEDENCE-ORDER requires one argument".to_string(),
        ));
    }
    if let Some(gid) = generic_id_from_node(proc, args[0]) {
        if let Some(order) = proc.mop.get_generic_argument_precedence_order(gid) {
            let order = order.to_vec();
            return Ok(make_symbol_list(proc, &order));
        }
    }
    Ok(proc.make_nil())
}

fn prim_sys_dispatch_generic(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return Err(ControlSignal::Error(
            "SYS-DISPATCH-GENERIC requires generic function and args list".to_string(),
        ));
    }

    let gid = generic_id_from_node(proc, args[0]).ok_or_else(|| {
        ControlSignal::Error("SYS-DISPATCH-GENERIC requires a generic function".to_string())
    })?;
    let args_list = args[1];
    let arg_vals = list_to_vec(proc, args_list);

    let uses_eql = proc.mop.generic_uses_eql_specializers(gid);
    let arg_classes: Vec<_> = if uses_eql {
        Vec::new()
    } else {
        arg_vals.iter().map(|&v| arg_class_id(proc, v)).collect()
    };

    if !uses_eql {
        if let Some(effective_fn) = proc.mop.get_cached_effective_method(gid, &arg_classes) {
            return call_function_node(proc, ctx, effective_fn, &arg_vals);
        }
    }

    let methods = proc
        .mop
        .compute_applicable_methods(gid, &arg_vals, &proc.arena.inner);

    if methods.is_empty() {
        let gf_name = proc
            .mop
            .get_generic(gid)
            .map(|g| generic_name_to_string(ctx, g.name))
            .unwrap_or_else(|| "?".to_string());
        return Err(ControlSignal::Error(format!(
            "No applicable method for generic function {} {:?} with args {:?}",
            gf_name, gid, arg_vals
        )));
    }

    let method_nodes: Vec<NodeId> = methods
        .iter()
        .map(|mid| {
            proc.arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Method(mid.0)))
        })
        .collect();
    let methods_list = proc.make_list(&method_nodes);

    let mc_sym = {
        let gf = proc
            .mop
            .get_generic(gid)
            .ok_or_else(|| ControlSignal::Error("Generic function missing".into()))?;
        match &gf.method_combination {
            crate::clos::MethodCombination::Standard => ctx
                .symbols
                .write()
                .unwrap()
                .intern_in("STANDARD", PackageId(1)),
            crate::clos::MethodCombination::Operator { name, .. } => *name,
            crate::clos::MethodCombination::UserLong { name, .. } => *name,
        }
    };
    let mc_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(mc_sym.0)));

    let gf_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Generic(gid.0)));

    let saved_program = proc.program;
    let saved_mode = proc.execution_mode.clone();
    let saved_env = proc.current_env.clone();
    let saved_stack = std::mem::take(&mut proc.continuation_stack);
    let saved_pending = proc.pending_redex;
    let saved_next_methods = std::mem::take(&mut proc.next_method_states);

    let mut interp = Interpreter::new(proc, ctx);
    interp.apply_methods_with_combination(gid, methods.clone(), arg_vals)?;

    let result = loop {
        match interp.step() {
            Ok(true) => continue,
            Ok(false) => break interp.process.program,
            Err(e) => return Err(e),
        }
    };

    proc.program = saved_program;
    proc.execution_mode = saved_mode;
    proc.current_env = saved_env;
    proc.continuation_stack = saved_stack;
    proc.pending_redex = saved_pending;
    proc.next_method_states = saved_next_methods;

    if !uses_eql {
        let effective_method = call_mop_function(
            proc,
            ctx,
            "COMPUTE-EFFECTIVE-METHOD",
            &[gf_node, mc_node, methods_list],
        )?;
        let effective_fn = call_mop_function(
            proc,
            ctx,
            "COMPUTE-EFFECTIVE-METHOD-FUNCTION",
            &[gf_node, effective_method],
        )?;
        proc.mop
            .set_cached_effective_method(gid, arg_classes.clone(), effective_fn);
    }

    Ok(result)
}

fn prim_sys_apply_effective_method(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 3 {
        return Err(ControlSignal::Error(
            "SYS-APPLY-EFFECTIVE-METHOD requires generic, methods list, args list".to_string(),
        ));
    }

    let gid = generic_id_from_node(proc, args[0]).ok_or_else(|| {
        ControlSignal::Error("SYS-APPLY-EFFECTIVE-METHOD requires a generic function".to_string())
    })?;
    let methods_list = args[1];
    let args_list = args[2];

    let mut methods = Vec::new();
    for node in list_to_vec(proc, methods_list) {
        let mid = method_id_from_node(proc, node).ok_or_else(|| {
            ControlSignal::Error("SYS-APPLY-EFFECTIVE-METHOD expects method objects".to_string())
        })?;
        methods.push(mid);
    }

    let arg_vals = list_to_vec(proc, args_list);

    let saved_program = proc.program;
    let saved_mode = proc.execution_mode.clone();
    let saved_env = proc.current_env.clone();
    let saved_stack = std::mem::take(&mut proc.continuation_stack);
    let saved_pending = proc.pending_redex;
    let saved_next_methods = std::mem::take(&mut proc.next_method_states);

    let mut interp = Interpreter::new(proc, ctx);
    interp.apply_methods_with_combination(gid, methods, arg_vals)?;

    let result = loop {
        match interp.step() {
            Ok(true) => continue,
            Ok(false) => break Ok(interp.process.program),
            Err(e) => break Err(e),
        }
    };

    proc.program = saved_program;
    proc.execution_mode = saved_mode;
    proc.current_env = saved_env;
    proc.continuation_stack = saved_stack;
    proc.pending_redex = saved_pending;
    proc.next_method_states = saved_next_methods;

    result
}

fn prim_method_specializers(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "METHOD-SPECIALIZERS requires one argument".to_string(),
        ));
    }
    if let Some(mid) = method_id_from_node(proc, args[0]) {
        if let Some(specs) = proc.mop.get_method_specializers(mid) {
            let specs = specs.to_vec();
            let mut nodes = Vec::with_capacity(specs.len());
            for spec in &specs {
                nodes.push(specializer_to_node(proc, spec));
            }
            return Ok(proc.make_list(&nodes));
        }
    }
    Ok(proc.make_nil())
}

fn prim_method_lambda_list(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "METHOD-LAMBDA-LIST requires one argument".to_string(),
        ));
    }
    if let Some(mid) = method_id_from_node(proc, args[0]) {
        if let Some(ll) = proc.mop.get_method_lambda_list(mid) {
            let ll = ll.to_vec();
            return Ok(make_symbol_list(proc, &ll));
        }
    }
    Ok(proc.make_nil())
}

fn prim_method_generic_function(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "METHOD-GENERIC-FUNCTION requires one argument".to_string(),
        ));
    }
    if let Some(mid) = method_id_from_node(proc, args[0]) {
        if let Some(gid) = proc.mop.get_method_generic(mid) {
            return Ok(proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Generic(gid.0))));
        }
    }
    Ok(proc.make_nil())
}

fn prim_method_body(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "METHOD-BODY requires one argument".to_string(),
        ));
    }
    if let Some(mid) = method_id_from_node(proc, args[0]) {
        if let Some(m) = proc.mop.get_method(mid) {
            return Ok(m.body);
        }
    }
    Ok(proc.make_nil())
}

fn prim_intern_eql_specializer(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "INTERN-EQL-SPECIALIZER requires one argument".to_string(),
        ));
    }
    let obj = args[0];
    let idx = proc.mop.intern_eql_specializer(&proc.arena.inner, obj);
    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::EqlSpecializer(idx))))
}

fn prim_sys_eql_specializer_object(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "SYS-EQL-SPECIALIZER-OBJECT requires one argument".to_string(),
        ));
    }
    if let Some(idx) = eql_specializer_id_from_node(proc, args[0]) {
        if let Some(obj) = proc.mop.get_eql_specializer_object(idx) {
            return Ok(obj);
        }
    }
    Err(ControlSignal::Error(
        "SYS-EQL-SPECIALIZER-OBJECT requires an eql-specializer".to_string(),
    ))
}

fn prim_slot_definition_name(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "SLOT-DEFINITION-NAME requires one argument".to_string(),
        ));
    }
    if let Some((class_id, idx, direct)) = slot_def_from_node(proc, args[0]) {
        if let Some(s) = resolve_slot_def(proc, class_id, idx, direct) {
            return Ok(proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(s.name.0))));
        }
    }
    Ok(proc.make_nil())
}

fn prim_slot_definition_initform(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "SLOT-DEFINITION-INITFORM requires one argument".to_string(),
        ));
    }
    if let Some((class_id, idx, direct)) = slot_def_from_node(proc, args[0]) {
        if let Some(s) = resolve_slot_def(proc, class_id, idx, direct) {
            return Ok(s.initform.unwrap_or(proc.make_nil()));
        }
    }
    Ok(proc.make_nil())
}

fn prim_slot_definition_initfunction(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "SLOT-DEFINITION-INITFUNCTION requires one argument".to_string(),
        ));
    }
    if let Some((class_id, idx, direct)) = slot_def_from_node(proc, args[0]) {
        if let Some(s) = resolve_slot_def(proc, class_id, idx, direct) {
            return Ok(s.initfunction.unwrap_or(proc.make_nil()));
        }
    }
    Ok(proc.make_nil())
}

fn prim_slot_definition_initargs(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "SLOT-DEFINITION-INITARGS requires one argument".to_string(),
        ));
    }
    if let Some((class_id, idx, direct)) = slot_def_from_node(proc, args[0]) {
        if let Some(s) = resolve_slot_def(proc, class_id, idx, direct) {
            if let Some(initarg) = s.initarg {
                let node = proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Symbol(initarg.0)));
                return Ok(proc.make_list(&[node]));
            }
            return Ok(proc.make_nil());
        }
    }
    Ok(proc.make_nil())
}

fn prim_slot_definition_readers(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "SLOT-DEFINITION-READERS requires one argument".to_string(),
        ));
    }
    if let Some((class_id, idx, direct)) = slot_def_from_node(proc, args[0]) {
        if let Some(s) = resolve_slot_def(proc, class_id, idx, direct) {
            let readers = s.readers.clone();
            return Ok(make_symbol_list(proc, &readers));
        }
    }
    Ok(proc.make_nil())
}

fn prim_slot_definition_writers(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "SLOT-DEFINITION-WRITERS requires one argument".to_string(),
        ));
    }
    if let Some((class_id, idx, direct)) = slot_def_from_node(proc, args[0]) {
        if let Some(s) = resolve_slot_def(proc, class_id, idx, direct) {
            let writers = s.writers.clone();
            return Ok(make_symbol_list(proc, &writers));
        }
    }
    Ok(proc.make_nil())
}

fn prim_slot_definition_allocation(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "SLOT-DEFINITION-ALLOCATION requires one argument".to_string(),
        ));
    }
    if let Some((class_id, idx, direct)) = slot_def_from_node(proc, args[0]) {
        if let Some(s) = resolve_slot_def(proc, class_id, idx, direct) {
            let name = match s.allocation {
                crate::clos::SlotAllocation::Instance => "INSTANCE",
                crate::clos::SlotAllocation::Class => "CLASS",
            };
            let sym = ctx
                .symbols
                .write()
                .unwrap()
                .intern_in(name, PackageId(0));
            return Ok(proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(sym.0))));
        }
    }
    Ok(proc.make_nil())
}

fn prim_slot_definition_type(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "SLOT-DEFINITION-TYPE requires one argument".to_string(),
        ));
    }
    if let Some((class_id, idx, direct)) = slot_def_from_node(proc, args[0]) {
        if let Some(s) = resolve_slot_def(proc, class_id, idx, direct) {
            return Ok(s.slot_type.unwrap_or(proc.make_nil()));
        }
    }
    Ok(proc.make_nil())
}

fn prim_slot_definition_location(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "SLOT-DEFINITION-LOCATION requires one argument".to_string(),
        ));
    }
    if let Some((class_id, idx, direct)) = slot_def_from_node(proc, args[0]) {
        if let Some(s) = resolve_slot_def(proc, class_id, idx, direct) {
            if s.allocation == crate::clos::SlotAllocation::Instance && s.index != usize::MAX {
                return Ok(proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Integer(s.index as i64))));
            }
            return Ok(proc.make_nil());
        }
    }
    Ok(proc.make_nil())
}

fn prim_slot_boundp(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return Err(ControlSignal::Error(
            "SLOT-BOUNDP requires instance and slot-name".to_string(),
        ));
    }
    let instance = args[0];
    let slot_name = args[1];

    let inst_idx = instance_index_from_node(proc, ctx, instance)?;

    let slot_sym = node_to_symbol(proc, slot_name)
        .ok_or(ControlSignal::Error("SLOT-BOUNDP slot-name must be symbol".to_string()))?;

    if let Some(inst) = proc.mop.get_instance(inst_idx) {
        let class_obj = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Class(inst.class.0)));
        if let Some(class) = proc.mop.get_class(inst.class) {
            if let Some(slot) = class.slots.iter().find(|s| s.name == slot_sym) {
                let bound = match slot.allocation {
                    crate::clos::SlotAllocation::Instance => {
                        if let Some(val) = proc.mop.slot_value(inst_idx, slot.index) {
                            !matches!(
                                proc.arena.inner.get_unchecked(val),
                                Node::Leaf(OpaqueValue::Unbound)
                            )
                        } else {
                            false
                        }
                    }
                    crate::clos::SlotAllocation::Class => slot.class_value.is_some(),
                };
                return Ok(if bound { proc.make_t(ctx) } else { proc.make_nil() });
            } else {
                return call_slot_missing(
                    proc,
                    ctx,
                    class_obj,
                    instance,
                    slot_name,
                    "SLOT-BOUNDP",
                    None,
                );
            }
        }
    }

    Ok(proc.make_nil())
}

fn prim_slot_exists_p(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return Err(ControlSignal::Error(
            "SLOT-EXISTS-P requires instance and slot-name".to_string(),
        ));
    }
    let instance = args[0];
    let slot_name = args[1];

    let inst_idx = instance_index_from_node(proc, ctx, instance)?;

    let slot_sym = node_to_symbol(proc, slot_name)
        .ok_or(ControlSignal::Error("SLOT-EXISTS-P slot-name must be symbol".to_string()))?;

    if let Some(inst) = proc.mop.get_instance(inst_idx) {
        if let Some(class) = proc.mop.get_class(inst.class) {
            if class.slots.iter().any(|s| s.name == slot_sym) {
                return Ok(proc.make_t(ctx));
            }
        }
    }
    Ok(proc.make_nil())
}

fn prim_slot_makunbound(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return Err(ControlSignal::Error(
            "SLOT-MAKUNBOUND requires instance and slot-name".to_string(),
        ));
    }
    let instance = args[0];
    let slot_name = args[1];

    let inst_idx = instance_index_from_node(proc, ctx, instance)?;

    let slot_sym = node_to_symbol(proc, slot_name)
        .ok_or(ControlSignal::Error("SLOT-MAKUNBOUND slot-name must be symbol".to_string()))?;

    if let Some(inst) = proc.mop.get_instance(inst_idx) {
        let class_obj = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Class(inst.class.0)));
        if let Some(class) = proc.mop.get_class(inst.class) {
            if let Some(slot) = class.slots.iter().find(|s| s.name == slot_sym) {
                match slot.allocation {
                    crate::clos::SlotAllocation::Instance => {
                        let unbound = proc.make_unbound();
                        proc.mop.set_slot_value(inst_idx, slot.index, unbound);
                    }
                    crate::clos::SlotAllocation::Class => {
                        if let Some(class_mut) = proc.mop.get_class_mut(inst.class) {
                            if let Some(s) = class_mut
                                .slots
                                .iter_mut()
                                .find(|s| s.name == slot_sym)
                            {
                                s.class_value = None;
                            }
                        }
                    }
                }
                return Ok(instance);
            } else {
                return call_slot_missing(
                    proc,
                    ctx,
                    class_obj,
                    instance,
                    slot_name,
                    "SLOT-MAKUNBOUND",
                    None,
                );
            }
        }
    }

    Err(ControlSignal::Error("Invalid slot".to_string()))
}

fn prim_slot_value_using_class(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 3 {
        return Err(ControlSignal::Error(
            "SLOT-VALUE-USING-CLASS requires class, instance, slot".to_string(),
        ));
    }
    let class_id = class_id_from_node(proc, args[0]).ok_or(ControlSignal::Error(
        "SLOT-VALUE-USING-CLASS requires a class".to_string(),
    ))?;

    let inst_idx = if let Node::Leaf(OpaqueValue::Instance(idx)) =
        proc.arena.inner.get_unchecked(args[1])
    {
        *idx as usize
    } else {
        return Err(ControlSignal::Error(
            "SLOT-VALUE-USING-CLASS requires an instance".to_string(),
        ));
    };

    let class_obj = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Class(class_id.0)));

    let slot_def = if let Some((slot_class_id, slot_idx, direct)) =
        slot_def_from_node(proc, args[2])
    {
        resolve_slot_def(proc, slot_class_id, slot_idx, direct)
    } else if let Some(sym) = node_to_symbol(proc, args[2]) {
        proc.mop
            .get_class(class_id)
            .and_then(|class| class.slots.iter().find(|s| s.name == sym).cloned())
    } else {
        None
    };

    if let Some(slot) = slot_def {
        let slot_name_node = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(slot.name.0)));
        match slot.allocation {
            crate::clos::SlotAllocation::Instance => {
                if let Some(val) = proc.mop.slot_value(inst_idx, slot.index) {
                    if matches!(
                        proc.arena.inner.get_unchecked(val),
                        Node::Leaf(OpaqueValue::Unbound)
                    ) {
                        return call_slot_unbound(proc, ctx, class_obj, args[1], slot_name_node);
                    }
                    return Ok(val);
                }
            }
            crate::clos::SlotAllocation::Class => {
                if let Some(val) = slot.class_value {
                    if matches!(
                        proc.arena.inner.get_unchecked(val),
                        Node::Leaf(OpaqueValue::Unbound)
                    ) {
                        return call_slot_unbound(proc, ctx, class_obj, args[1], slot_name_node);
                    }
                    return Ok(val);
                }
                return call_slot_unbound(proc, ctx, class_obj, args[1], slot_name_node);
            }
        }
    }

    call_slot_missing(
        proc,
        ctx,
        class_obj,
        args[1],
        args[2],
        "SLOT-VALUE",
        None,
    )
}

fn prim_set_slot_value_using_class(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 4 {
        return Err(ControlSignal::Error(
            "SET-SLOT-VALUE-USING-CLASS requires class, instance, slot, value".to_string(),
        ));
    }
    let class_id = class_id_from_node(proc, args[0]).ok_or(ControlSignal::Error(
        "SET-SLOT-VALUE-USING-CLASS requires a class".to_string(),
    ))?;

    let inst_idx = if let Node::Leaf(OpaqueValue::Instance(idx)) =
        proc.arena.inner.get_unchecked(args[1])
    {
        *idx as usize
    } else {
        return Err(ControlSignal::Error(
            "SET-SLOT-VALUE-USING-CLASS requires an instance".to_string(),
        ));
    };

    let value = args[3];

    let class_obj = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Class(class_id.0)));

    let slot_def = if let Some((slot_class_id, slot_idx, direct)) =
        slot_def_from_node(proc, args[2])
    {
        resolve_slot_def(proc, slot_class_id, slot_idx, direct)
    } else if let Some(sym) = node_to_symbol(proc, args[2]) {
        proc.mop
            .get_class(class_id)
            .and_then(|class| class.slots.iter().find(|s| s.name == sym).cloned())
    } else {
        None
    };

    if let Some(slot) = slot_def {
        enforce_slot_type(proc, ctx, &slot, value)?;
        let slot_name = slot.name;
        match slot.allocation {
            crate::clos::SlotAllocation::Instance => {
                proc.mop.set_slot_value(inst_idx, slot.index, value);
                return Ok(value);
            }
            crate::clos::SlotAllocation::Class => {
                if let Some(class_mut) = proc.mop.get_class_mut(class_id) {
                    if let Some(s) = class_mut
                        .slots
                        .iter_mut()
                        .find(|s| s.name == slot_name)
                    {
                        s.class_value = Some(value);
                        return Ok(value);
                    }
                }
            }
        }
    }

    call_slot_missing(
        proc,
        ctx,
        class_obj,
        args[1],
        args[2],
        "SET-SLOT-VALUE",
        Some(value),
    )
}

fn prim_slot_boundp_using_class(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 3 {
        return Err(ControlSignal::Error(
            "SLOT-BOUNDP-USING-CLASS requires class, instance, slot".to_string(),
        ));
    }
    let class_id = class_id_from_node(proc, args[0]).ok_or(ControlSignal::Error(
        "SLOT-BOUNDP-USING-CLASS requires a class".to_string(),
    ))?;

    let inst_idx = if let Node::Leaf(OpaqueValue::Instance(idx)) =
        proc.arena.inner.get_unchecked(args[1])
    {
        *idx as usize
    } else {
        return Err(ControlSignal::Error(
            "SLOT-BOUNDP-USING-CLASS requires an instance".to_string(),
        ));
    };

    let class_obj = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Class(class_id.0)));

    let slot_def = if let Some((slot_class_id, slot_idx, direct)) =
        slot_def_from_node(proc, args[2])
    {
        resolve_slot_def(proc, slot_class_id, slot_idx, direct)
    } else if let Some(sym) = node_to_symbol(proc, args[2]) {
        proc.mop
            .get_class(class_id)
            .and_then(|class| class.slots.iter().find(|s| s.name == sym).cloned())
    } else {
        None
    };

    if let Some(slot) = slot_def {
        let bound = match slot.allocation {
            crate::clos::SlotAllocation::Instance => {
                if let Some(val) = proc.mop.slot_value(inst_idx, slot.index) {
                    !matches!(
                        proc.arena.inner.get_unchecked(val),
                        Node::Leaf(OpaqueValue::Unbound)
                    )
                } else {
                    false
                }
            }
            crate::clos::SlotAllocation::Class => slot.class_value.is_some(),
        };
        return Ok(if bound { proc.make_t(ctx) } else { proc.make_nil() });
    }

    call_slot_missing(
        proc,
        ctx,
        class_obj,
        args[1],
        args[2],
        "SLOT-BOUNDP",
        None,
    )
}

fn prim_slot_makunbound_using_class(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 3 {
        return Err(ControlSignal::Error(
            "SLOT-MAKUNBOUND-USING-CLASS requires class, instance, slot".to_string(),
        ));
    }
    let class_id = class_id_from_node(proc, args[0]).ok_or(ControlSignal::Error(
        "SLOT-MAKUNBOUND-USING-CLASS requires a class".to_string(),
    ))?;

    let inst_idx = if let Node::Leaf(OpaqueValue::Instance(idx)) =
        proc.arena.inner.get_unchecked(args[1])
    {
        *idx as usize
    } else {
        return Err(ControlSignal::Error(
            "SLOT-MAKUNBOUND-USING-CLASS requires an instance".to_string(),
        ));
    };

    let class_obj = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Class(class_id.0)));

    let slot_def = if let Some((slot_class_id, slot_idx, direct)) =
        slot_def_from_node(proc, args[2])
    {
        resolve_slot_def(proc, slot_class_id, slot_idx, direct)
    } else if let Some(sym) = node_to_symbol(proc, args[2]) {
        proc.mop
            .get_class(class_id)
            .and_then(|class| class.slots.iter().find(|s| s.name == sym).cloned())
    } else {
        None
    };

    if let Some(slot) = slot_def {
        match slot.allocation {
            crate::clos::SlotAllocation::Instance => {
                let unbound = proc.make_unbound();
                proc.mop.set_slot_value(inst_idx, slot.index, unbound);
            }
            crate::clos::SlotAllocation::Class => {
                if let Some(class_mut) = proc.mop.get_class_mut(class_id) {
                    if let Some(s) = class_mut.slots.iter_mut().find(|s| s.name == slot.name) {
                        s.class_value = None;
                    }
                }
            }
        }
        return Ok(args[1]);
    }

    call_slot_missing(
        proc,
        ctx,
        class_obj,
        args[1],
        args[2],
        "SLOT-MAKUNBOUND",
        None,
    )
}

fn prim_slot_exists_p_using_class(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 3 {
        return Err(ControlSignal::Error(
            "SLOT-EXISTS-P-USING-CLASS requires class, instance, slot".to_string(),
        ));
    }
    let class_id = class_id_from_node(proc, args[0]).ok_or(ControlSignal::Error(
        "SLOT-EXISTS-P-USING-CLASS requires a class".to_string(),
    ))?;

    let slot_sym = if let Some(sym) = node_to_symbol(proc, args[2]) {
        sym
    } else if let Some((slot_class_id, slot_idx, direct)) = slot_def_from_node(proc, args[2]) {
        if let Some(class) = proc.mop.get_class(slot_class_id) {
            let slot = if direct {
                class.direct_slots.get(slot_idx)
            } else {
                class.slots.get(slot_idx)
            };
            if let Some(s) = slot {
                s.name
            } else {
                return Ok(proc.make_nil());
            }
        } else {
            return Ok(proc.make_nil());
        }
    } else {
        return Ok(proc.make_nil());
    };

    if let Some(class) = proc.mop.get_class(class_id) {
        if class.slots.iter().any(|s| s.name == slot_sym) {
            return Ok(proc.make_t(ctx));
        }
    }
    Ok(proc.make_nil())
}

fn prim_compute_applicable_methods(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return Err(ControlSignal::Error(
            "COMPUTE-APPLICABLE-METHODS requires generic function and args list".to_string(),
        ));
    }
    let gf = args[0];
    let gid = generic_id_from_node(proc, gf).ok_or(ControlSignal::Error(
        "COMPUTE-APPLICABLE-METHODS requires a generic function".to_string(),
    ))?;
    let arg_nodes = if args.len() == 2 {
        let list_node = args[1];
        match proc.arena.inner.get_unchecked(list_node) {
            Node::Fork(_, _) | Node::Leaf(OpaqueValue::Nil) => list_to_vec(proc, list_node),
            _ => vec![list_node],
        }
    } else {
        args[1..].to_vec()
    };

    let methods = proc
        .mop
        .compute_applicable_methods(gid, &arg_nodes, &proc.arena.inner);
    let mut nodes = Vec::with_capacity(methods.len());
    for mid in methods {
        nodes.push(
            proc.arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Method(mid.0))),
        );
    }
    Ok(proc.make_list(&nodes))
}

fn prim_compute_applicable_methods_using_classes(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return Err(ControlSignal::Error(
            "COMPUTE-APPLICABLE-METHODS-USING-CLASSES requires generic function and class list"
                .to_string(),
        ));
    }
    let gid = generic_id_from_node(proc, args[0]).ok_or(ControlSignal::Error(
        "COMPUTE-APPLICABLE-METHODS-USING-CLASSES requires a generic function".to_string(),
    ))?;
    let mut class_ids = Vec::new();
    for head in list_to_vec(proc, args[1]) {
        if let Some(cid) = class_id_from_node(proc, head) {
            class_ids.push(cid);
        }
    }
    let methods = proc
        .mop
        .compute_applicable_methods_using_classes(gid, &class_ids);
    let mut nodes = Vec::with_capacity(methods.len());
    for mid in methods {
        nodes.push(
            proc.arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Method(mid.0))),
        );
    }
    Ok(proc.make_list(&nodes))
}

fn prim_find_method(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 3 {
        return Err(ControlSignal::Error(
            "FIND-METHOD requires generic function, qualifiers, specializers".to_string(),
        ));
    }
    let gid = generic_id_from_node(proc, args[0]).ok_or(ControlSignal::Error(
        "FIND-METHOD requires a generic function".to_string(),
    ))?;

    let qualifiers: Vec<SymbolId> = list_to_vec(proc, args[1])
        .iter()
        .filter_map(|&n| node_to_symbol(proc, n))
        .collect();

    let specializers: Vec<crate::clos::Specializer> = list_to_vec(proc, args[2])
        .iter()
        .map(|&n| parse_specializer_node(proc, ctx, n))
        .collect();

    if let Some(gf) = proc.mop.get_generic(gid) {
        for mid in &gf.methods {
            if let Some(method) = proc.mop.get_method(*mid) {
                if method.qualifiers == qualifiers && method.specializers == specializers {
                    return Ok(proc
                        .arena
                        .inner
                        .alloc(Node::Leaf(OpaqueValue::Method(mid.0))));
                }
            }
        }
    }
    Ok(proc.make_nil())
}

fn prim_ensure_class_using_class(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return Err(ControlSignal::Error(
            "ENSURE-CLASS-USING-CLASS requires class and name".to_string(),
        ));
    }
    // Ignore first arg (class metaobject) and delegate.
    prim_ensure_class(proc, ctx, &args[1..])
}

fn prim_ensure_generic_function_using_class(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return Err(ControlSignal::Error(
            "ENSURE-GENERIC-FUNCTION-USING-CLASS requires class and name".to_string(),
        ));
    }
    prim_ensure_generic_function(proc, ctx, &args[1..])
}

fn prim_finalize_inheritance(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "FINALIZE-INHERITANCE requires one argument".to_string(),
        ));
    }
    if let Some(class_id) = class_id_from_node(proc, args[0]) {
        if let Some(class) = proc.mop.get_class(class_id) {
            let name = class.name;
            let supers = class.supers.clone();
            let direct_slots = class.direct_slots.clone();
            let metaclass = class.metaclass;
            let direct_default_initargs = class.direct_default_initargs.clone();
            proc.mop.define_class_with_meta(
                name,
                supers,
                direct_slots,
                Some(metaclass),
                direct_default_initargs,
            );
        }
        return Ok(proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Class(class_id.0))));
    }
    Ok(proc.make_nil())
}

fn prim_validate_superclass(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return Err(ControlSignal::Error(
            "VALIDATE-SUPERCLASS requires two arguments".to_string(),
        ));
    }
    let class_ok = class_id_from_node(proc, args[0]).is_some();
    let super_ok = class_id_from_node(proc, args[1]).is_some();
    if class_ok && super_ok {
        Ok(proc.make_t(ctx))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_reinitialize_instance(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return Err(ControlSignal::Error(
            "REINITIALIZE-INSTANCE requires an instance".to_string(),
        ));
    }
    let instance = args[0];
    let mut shared_args = vec![instance, proc.make_nil()];
    if args.len() > 1 {
        shared_args.extend_from_slice(&args[1..]);
    }
    prim_shared_initialize(proc, ctx, &shared_args)
}

fn prim_set_funcallable_instance_function(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return Err(ControlSignal::Error(
            "SET-FUNCALLABLE-INSTANCE-FUNCTION requires instance and function".to_string(),
        ));
    }

    let func_node = resolve_funcallable_designator(proc, ctx, args[1])?;

    match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::Generic(id)) => {
            let gid = crate::clos::GenericId(*id);
            proc.mop.set_generic_discriminating_function(gid, func_node);
            Ok(func_node)
        }
        Node::Leaf(OpaqueValue::Symbol(id)) => {
            let sym = SymbolId(*id);
            if let Some(gid) = proc.mop.find_generic(sym) {
                proc.mop.set_generic_discriminating_function(gid, func_node);
                return Ok(func_node);
            }
            Err(ControlSignal::Error(
                "SET-FUNCALLABLE-INSTANCE-FUNCTION requires a funcallable instance or generic".to_string(),
            ))
        }
        Node::Leaf(OpaqueValue::Instance(idx)) => {
            let inst_idx = *idx as usize;
            let class_id = proc
                .mop
                .get_instance(inst_idx)
                .map(|i| i.class)
                .unwrap_or(proc.mop.standard_object);
            if !proc.mop.class_is_funcallable(class_id) {
                return Err(ControlSignal::Error(
                    "SET-FUNCALLABLE-INSTANCE-FUNCTION on non-funcallable instance".to_string(),
                ));
            }
            proc.mop.set_instance_function(inst_idx, func_node);
            Ok(func_node)
        }
        _ => Err(ControlSignal::Error(
            "SET-FUNCALLABLE-INSTANCE-FUNCTION requires a funcallable instance or generic".to_string(),
        )),
    }
}

fn prim_funcallable_standard_instance_access(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 || args.len() > 3 {
        return Err(ControlSignal::Error(
            "FUNCALLABLE-STANDARD-INSTANCE-ACCESS requires instance, index, and optional value"
                .to_string(),
        ));
    }

    let inst_idx = match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::Instance(idx)) => *idx as usize,
        _ => {
            return Err(ControlSignal::Error(
                "FUNCALLABLE-STANDARD-INSTANCE-ACCESS requires an instance".to_string(),
            ))
        }
    };

    let class_id = proc
        .mop
        .get_instance(inst_idx)
        .map(|i| i.class)
        .unwrap_or(proc.mop.standard_object);
    if !proc.mop.class_is_funcallable(class_id) {
        return Err(ControlSignal::Error(
            "FUNCALLABLE-STANDARD-INSTANCE-ACCESS on non-funcallable instance".to_string(),
        ));
    }

    let idx_val = extract_number(&proc.arena.inner, args[1]);
    let idx = match idx_val {
        NumVal::Int(n) if n >= 0 => n as usize,
        NumVal::Big(n) => n.to_usize().ok_or_else(|| {
            ControlSignal::Error("FUNCALLABLE-STANDARD-INSTANCE-ACCESS index out of range".into())
        })?,
        _ => {
            return Err(ControlSignal::Error(
                "FUNCALLABLE-STANDARD-INSTANCE-ACCESS index must be integer".to_string(),
            ))
        }
    };

    if args.len() == 2 {
        proc.mop
            .slot_value(inst_idx, idx)
            .ok_or_else(|| ControlSignal::Error("Slot index out of bounds".into()))
    } else {
        let value = args[2];
        proc.mop.set_slot_value(inst_idx, idx, value);
        Ok(value)
    }
}

fn prim_set_funcallable_standard_instance_access(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 3 {
        return Err(ControlSignal::Error(
            "SET-FUNCALLABLE-STANDARD-INSTANCE-ACCESS requires instance, index, value".to_string(),
        ));
    }
    prim_funcallable_standard_instance_access(proc, ctx, args)
}

fn prim_sys_add_dependent(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return Err(ControlSignal::Error(
            "SYS-ADD-DEPENDENT requires metaobject and dependent".to_string(),
        ));
    }
    let key = dependent_key_from_node(proc, args[0]).ok_or_else(|| {
        ControlSignal::Error("SYS-ADD-DEPENDENT requires class or generic".to_string())
    })?;
    let dependent = args[1];

    match key {
        DependentKey::Class(cid) => {
            proc.mop
                .add_class_dependent(cid, dependent, &proc.arena.inner);
        }
        DependentKey::Generic(gid) => {
            proc.mop
                .add_generic_dependent(gid, dependent, &proc.arena.inner);
        }
    }

    Ok(dependent)
}

fn prim_sys_remove_dependent(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return Err(ControlSignal::Error(
            "SYS-REMOVE-DEPENDENT requires metaobject and dependent".to_string(),
        ));
    }
    let key = dependent_key_from_node(proc, args[0]).ok_or_else(|| {
        ControlSignal::Error("SYS-REMOVE-DEPENDENT requires class or generic".to_string())
    })?;
    let dependent = args[1];

    let removed = match key {
        DependentKey::Class(cid) => proc
            .mop
            .remove_class_dependent(cid, dependent, &proc.arena.inner),
        DependentKey::Generic(gid) => proc
            .mop
            .remove_generic_dependent(gid, dependent, &proc.arena.inner),
    };

    if removed {
        Ok(proc.make_t(ctx))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_sys_map_dependents(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return Err(ControlSignal::Error(
            "SYS-MAP-DEPENDENTS requires metaobject and function".to_string(),
        ));
    }
    let key = dependent_key_from_node(proc, args[0]).ok_or_else(|| {
        ControlSignal::Error("SYS-MAP-DEPENDENTS requires class or generic".to_string())
    })?;
    let func = args[1];

    let deps = match key {
        DependentKey::Class(cid) => proc.mop.class_dependents(cid).map(|d| d.to_vec()),
        DependentKey::Generic(gid) => proc.mop.generic_dependents(gid).map(|d| d.to_vec()),
    }
    .unwrap_or_default();

    for dep in deps {
        let _ = call_function_node(proc, ctx, func, &[dep])?;
    }

    Ok(proc.make_nil())
}

fn prim_change_class(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return Err(ControlSignal::Error(
            "CHANGE-CLASS requires instance and class".to_string(),
        ));
    }
    let instance_node = args[0];
    let new_class_node = args[1];
    let initargs = &args[2..];

    let inst_idx =
        if let Node::Leaf(OpaqueValue::Instance(idx)) = proc.arena.inner.get_unchecked(instance_node)
        {
            *idx as usize
        } else {
            return Err(ControlSignal::Error(
                "CHANGE-CLASS: first arg must be instance".to_string(),
            ));
        };

    let new_class_id = class_id_from_node(proc, new_class_node).ok_or(ControlSignal::Error(
        "CHANGE-CLASS: second arg must be class".to_string(),
    ))?;

    let old_class_id = proc
        .mop
        .get_instance(inst_idx)
        .map(|i| i.class)
        .ok_or(ControlSignal::Error(
            "CHANGE-CLASS: instance missing class".to_string(),
        ))?;

    let old_class_slots = proc
        .mop
        .get_class(old_class_id)
        .ok_or(ControlSignal::Error(
            "CHANGE-CLASS: old class missing".to_string(),
        ))?
        .slots
        .clone();
    let (new_class_slots, new_instance_size) = {
        let new_class = proc
            .mop
            .get_class(new_class_id)
            .ok_or(ControlSignal::Error(
                "CHANGE-CLASS: new class missing".to_string(),
            ))?;
        (new_class.slots.clone(), new_class.instance_size)
    };

    let old_values = proc
        .mop
        .get_instance(inst_idx)
        .map(|i| i.slots.clone())
        .unwrap_or_default();

    let mut old_map: HashMap<SymbolId, NodeId> = HashMap::default();
    for slot in &old_class_slots {
        if slot.allocation == crate::clos::SlotAllocation::Instance {
            if let Some(val) = old_values.get(slot.index) {
                old_map.insert(slot.name, *val);
            }
        }
    }

    let initargs_map = parse_keywords_list(proc, initargs);
    let unbound = proc.make_unbound();
    let mut new_values = vec![unbound; new_instance_size];

    for slot in &new_class_slots {
        match slot.allocation {
            crate::clos::SlotAllocation::Instance => {
                if let Some(key) = slot.initarg {
                    if let Some(&val) = initargs_map.get(&key) {
                        if slot.index < new_values.len() {
                            new_values[slot.index] = val;
                        }
                        continue;
                    }
                }
                if let Some(val) = old_map.get(&slot.name) {
                    if slot.index < new_values.len() {
                        new_values[slot.index] = *val;
                    }
                    continue;
                }
                if let Some(form) = slot.initform {
                    if slot.index < new_values.len() {
                        new_values[slot.index] = form;
                    }
                }
            }
            crate::clos::SlotAllocation::Class => {
                if let Some(key) = slot.initarg {
                    if let Some(&val) = initargs_map.get(&key) {
                        if let Some(class_mut) = proc.mop.get_class_mut(new_class_id) {
                            if let Some(s) = class_mut
                                .slots
                                .iter_mut()
                                .find(|s| s.name == slot.name)
                            {
                                s.class_value = Some(val);
                            }
                        }
                    }
                }
            }
        }
    }

    if let Some(inst) = proc.mop.get_instance_mut(inst_idx) {
        inst.class = new_class_id;
        inst.slots = new_values;
    }

    Ok(instance_node)
}

fn prim_update_instance_for_redefined_class(
    _proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return Err(ControlSignal::Error(
            "UPDATE-INSTANCE-FOR-REDEFINED-CLASS requires an instance".to_string(),
        ));
    }
    // Default no-op (instances are updated during class redefinition).
    Ok(args[0])
}

fn prim_compute_class_precedence_list(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "COMPUTE-CLASS-PRECEDENCE-LIST requires one argument".to_string(),
        ));
    }
    if let Some(class_id) = class_id_from_node(proc, args[0]) {
        if let Some(class) = proc.mop.get_class(class_id) {
            let cpl = class.cpl.clone();
            return Ok(make_class_list(proc, &cpl));
        }
    }
    Ok(proc.make_nil())
}

fn prim_compute_slots(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "COMPUTE-SLOTS requires one argument".to_string(),
        ));
    }
    if let Some(class_id) = class_id_from_node(proc, args[0]) {
        if let Some(class) = proc.mop.get_class(class_id) {
            let mut nodes = Vec::with_capacity(class.slots.len());
            for (idx, _slot) in class.slots.iter().enumerate() {
                nodes.push(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::SlotDefinition(
                    class_id.0,
                    idx as u32,
                    false,
                ))));
            }
            return Ok(proc.make_list(&nodes));
        }
    }
    Ok(proc.make_nil())
}

fn prim_compute_effective_slot_definition(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return Err(ControlSignal::Error(
            "COMPUTE-EFFECTIVE-SLOT-DEFINITION requires class and slot-name".to_string(),
        ));
    }
    let class_id = class_id_from_node(proc, args[0]).ok_or(ControlSignal::Error(
        "COMPUTE-EFFECTIVE-SLOT-DEFINITION requires a class".to_string(),
    ))?;
    let slot_sym = node_to_symbol(proc, args[1]).ok_or(ControlSignal::Error(
        "COMPUTE-EFFECTIVE-SLOT-DEFINITION requires a slot name".to_string(),
    ))?;

    if let Some(class) = proc.mop.get_class(class_id) {
        if let Some((idx, _slot)) = class
            .slots
            .iter()
            .enumerate()
            .find(|(_, s)| s.name == slot_sym)
        {
            return Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::SlotDefinition(
                class_id.0,
                idx as u32,
                false,
            ))));
        }
    }
    Ok(proc.make_nil())
}

fn prim_sys_make_method(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(
            "SYS-MAKE-METHOD requires one argument".to_string(),
        ));
    }

    let body = args[0];
    if let Node::Leaf(OpaqueValue::Closure(_)) = proc.arena.inner.get_unchecked(body) {
        let method_id = proc.mop.add_method_raw(Vec::new(), Vec::new(), body);
        return Ok(proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Method(method_id.0))));
    }

    Err(ControlSignal::Error(
        "SYS-MAKE-METHOD requires a function".to_string(),
    ))
}

fn prim_error(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return Err(crate::eval::ControlSignal::Error(
            "Error called with no arguments".to_string(),
        ));
    }

    // (error "format" args...)
    // For now, simpler: (error "message")
    let fmt_node = args[0];
    let fmt = if let Node::Leaf(OpaqueValue::String(h)) = proc.arena.inner.get_unchecked(fmt_node) {
        h.clone()
    } else {
        // Coerce to string
        crate::printer::princ_to_string(&proc.arena.inner, &*ctx.symbols.read().unwrap(), fmt_node)
    };

    // Call signal_error
    err_helper(&fmt)
}

fn prim_gc(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    _args: &[NodeId],
) -> EvalResult {
    let freed = proc.collect_garbage();
    // Return freed count as integer
    let val = OpaqueValue::Integer(freed as i64);
    Ok(proc.arena.inner.alloc(Node::Leaf(val)))
}

fn prim_room(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    _args: &[NodeId],
) -> EvalResult {
    let stats = proc.arena.inner.stats();
    let array_count = proc.arrays.active_count();
    let array_elements = proc.arrays.total_elements();
    let closure_count = proc.closures.len();
    let symbol_count = ctx.symbols.read().unwrap().symbol_count();

    println!("=== ROOM ===");
    println!("Arena:");
    println!("  Total slots:     {}", stats.total_slots);
    println!("  Free slots:      {}", stats.free_slots);
    println!(
        "  Live nodes:      {}",
        stats.total_slots - stats.free_slots
    );
    println!(
        "Vectors:           {} ({} elements)",
        array_count, array_elements
    );
    println!("Closures:          {}", closure_count);
    println!("Symbols:           {}", symbol_count);
    println!("GC:");
    println!("  Threshold:       {}", proc.arena.gc_threshold);
    println!("  Allocs since GC: {}", stats.allocs_since_gc);

    Ok(proc.make_nil())
}

fn prim_make_array(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return Err(crate::eval::ControlSignal::Error(
            "MAKE-ARRAY requires at least 1 argument".to_string(),
        ));
    }

    let parse_dims = |proc: &Process, node: NodeId| -> Result<Vec<usize>, ControlSignal> {
        match proc.arena.inner.get_unchecked(node) {
            Node::Leaf(OpaqueValue::Nil) => Ok(Vec::new()),
            Node::Leaf(OpaqueValue::Integer(n)) if *n >= 0 => Ok(vec![*n as usize]),
            Node::Fork(_, _) => {
                let items = list_to_vec_opt(proc, node)
                    .ok_or_else(|| ControlSignal::Error("MAKE-ARRAY: invalid dimensions".into()))?;
                let mut dims = Vec::new();
                for item in items {
                    match extract_number(&proc.arena.inner, item) {
                        NumVal::Int(n) if n >= 0 => dims.push(n as usize),
                        _ => {
                            return Err(ControlSignal::Error(
                                "MAKE-ARRAY: invalid dimension".to_string(),
                            ))
                        }
                    }
                }
                Ok(dims)
            }
            _ => Err(ControlSignal::Error("MAKE-ARRAY: invalid dimensions".into())),
        }
    };

    let dims = parse_dims(proc, args[0])?;

    let mut element_type = crate::arrays::ArrayElementType::T;
    let mut initial_element = proc.make_nil();
    let mut initial_contents: Option<NodeId> = None;
    let mut fill_pointer: Option<usize> = None;
    let mut displaced_to: Option<NodeId> = None;
    let mut displaced_offset: usize = 0;

    // Backward-compatible positional initial-element
    if args.len() == 2 {
        if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(args[1]) {
            let is_kw = _ctx
                .symbols
                .read()
                .unwrap()
                .get_symbol(SymbolId(*id))
                .map(|s| s.is_keyword())
                .unwrap_or(false);
            if !is_kw {
                initial_element = args[1];
            }
        } else {
            initial_element = args[1];
        }
    }

    let mut i = 1;
    while i + 1 < args.len() {
        let key = args[i];
        let val = args[i + 1];
        if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(key) {
            let name = _ctx
                .symbols
                .read()
                .unwrap()
                .symbol_name(SymbolId(*id))
                .unwrap_or("")
                .to_uppercase();
            match name.as_str() {
                "ELEMENT-TYPE" => {
                    if let Node::Leaf(OpaqueValue::Symbol(tid)) = proc.arena.inner.get_unchecked(val)
                    {
                        let tname = _ctx
                            .symbols
                            .read()
                            .unwrap()
                            .symbol_name(SymbolId(*tid))
                            .unwrap_or("")
                            .to_uppercase();
                        element_type = match tname.as_str() {
                            "BIT" => crate::arrays::ArrayElementType::Bit,
                            "CHARACTER" | "BASE-CHAR" => crate::arrays::ArrayElementType::Character,
                            _ => crate::arrays::ArrayElementType::T,
                        };
                    }
                }
                "INITIAL-ELEMENT" => {
                    initial_element = val;
                }
                "INITIAL-CONTENTS" => {
                    initial_contents = Some(val);
                }
                "FILL-POINTER" => {
                    match extract_number(&proc.arena.inner, val) {
                        NumVal::Int(n) if n >= 0 => fill_pointer = Some(n as usize),
                        _ => {
                            if !matches!(proc.arena.inner.get_unchecked(val), Node::Leaf(OpaqueValue::Nil))
                            {
                                // Non-nil => full length if rank 1
                                if dims.len() == 1 {
                                    fill_pointer = Some(dims[0]);
                                }
                            }
                        }
                    }
                }
                "DISPLACED-TO" => {
                    displaced_to = Some(val);
                }
                "DISPLACED-INDEX-OFFSET" => {
                    if let NumVal::Int(n) = extract_number(&proc.arena.inner, val) {
                        if n >= 0 {
                            displaced_offset = n as usize;
                        }
                    }
                }
                _ => {}
            }
        }
        i += 2;
    }

    let total_size = if dims.is_empty() {
        1
    } else {
        dims.iter().product::<usize>()
    };

    fn build_sequence(proc: &mut Process, node: NodeId) -> Result<Vec<NodeId>, ControlSignal> {
        let node_val = proc.arena.inner.get_unchecked(node).clone();
        match node_val {
            Node::Leaf(OpaqueValue::String(s)) => Ok(s
                .chars()
                .map(|c| proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Char(c))))
                .collect()),
            Node::Leaf(OpaqueValue::VectorHandle(id)) => {
                let arr = proc
                    .arrays
                    .get(crate::arrays::VectorId(id))
                    .ok_or_else(|| ControlSignal::Error("MAKE-ARRAY: invalid array".into()))?;
                Ok(arr.elements_for_sequence())
            }
            Node::Fork(_, _) => Ok(list_to_vec_opt(proc, node).ok_or_else(|| {
                ControlSignal::Error("MAKE-ARRAY: invalid initial contents".into())
            })?),
            _ => Err(ControlSignal::Error(
                "MAKE-ARRAY: invalid initial contents".to_string(),
            )),
        }
    }

    fn fill_from_contents(
        proc: &mut Process,
        dims: &[usize],
        node: NodeId,
    ) -> Result<Vec<NodeId>, ControlSignal> {
        if dims.is_empty() {
            return Ok(vec![node]);
        }
        let seq = build_sequence(proc, node)?;
        if dims.len() == 1 {
            return Ok(seq);
        }
        if seq.len() != dims[0] {
            return Err(ControlSignal::Error(
                "MAKE-ARRAY: initial contents shape mismatch".to_string(),
            ));
        }
        let mut out = Vec::new();
        for item in seq {
            out.extend(fill_from_contents(proc, &dims[1..], item)?);
        }
        Ok(out)
    }

    let mut elements: Vec<NodeId> = Vec::new();
    if let Some(base) = displaced_to {
        let base_seq = build_sequence(proc, base)?;
        let slice = base_seq
            .into_iter()
            .skip(displaced_offset)
            .take(total_size);
        elements.extend(slice);
    } else if let Some(contents) = initial_contents {
        elements = fill_from_contents(proc, &dims, contents)?;
    } else {
        elements = vec![initial_element; total_size];
    }

    if element_type == crate::arrays::ArrayElementType::Character
        && dims.len() == 1
        && fill_pointer.is_none()
        && displaced_to.is_none()
    {
        let mut s = String::new();
        for node in &elements {
            let ch = node_to_char(proc, _ctx, *node).ok_or_else(|| {
                ControlSignal::Error("MAKE-ARRAY: invalid character element".into())
            })?;
            s.push(ch);
        }
        return Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(s))));
    }

    let vec_id = proc
        .arrays
        .alloc_array(dims, elements, element_type, fill_pointer);

    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::VectorHandle(vec_id.0))))
}

fn prim_aref(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return Err(crate::eval::ControlSignal::Error(
            "AREF requires at least 1 argument".to_string(),
        ));
    }

    let array = args[0];
    let indices = &args[1..];

    match proc.arena.inner.get_unchecked(array) {
        Node::Leaf(OpaqueValue::String(s)) => {
            if indices.len() != 1 {
                return Err(crate::eval::ControlSignal::Error(
                    "AREF: string requires exactly 1 index".to_string(),
                ));
            }
            let idx = match extract_number(&proc.arena.inner, indices[0]) {
                NumVal::Int(i) if i >= 0 => i as usize,
                _ => {
                    return Err(crate::eval::ControlSignal::Error(
                        "AREF: invalid index".to_string(),
                    ))
                }
            };
            let ch = s.chars().nth(idx).ok_or_else(|| {
                crate::eval::ControlSignal::Error("AREF: index out of bounds".to_string())
            })?;
            return Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Char(ch))));
        }
        Node::Leaf(OpaqueValue::VectorHandle(idx)) => {
            let vec_id = crate::arrays::VectorId(*idx);
            let arr = proc.arrays.get(vec_id).ok_or_else(|| {
                crate::eval::ControlSignal::Error("AREF: invalid array".to_string())
            })?;
            if indices.len() != arr.rank() {
                return Err(crate::eval::ControlSignal::Error(
                    "AREF: wrong number of indices".to_string(),
                ));
            }
            let mut idxs = Vec::with_capacity(indices.len());
            for &idx_node in indices {
                let i = match extract_number(&proc.arena.inner, idx_node) {
                    NumVal::Int(n) if n >= 0 => n as usize,
                    _ => {
                        return Err(crate::eval::ControlSignal::Error(
                            "AREF: invalid index".to_string(),
                        ))
                    }
                };
                idxs.push(i);
            }
            let mut linear = 0usize;
            let mut stride = 1usize;
            for (dim, idx) in arr
                .dimensions
                .iter()
                .rev()
                .zip(idxs.iter().rev())
            {
                if *idx >= *dim {
                    return Err(crate::eval::ControlSignal::Error(
                        "AREF: index out of bounds".to_string(),
                    ));
                }
                linear += idx * stride;
                stride *= *dim;
            }
            if let Some(val) = proc.arrays.aref(vec_id, linear) {
                return Ok(val);
            }
            return Err(crate::eval::ControlSignal::Error(
                "AREF: index out of bounds".to_string(),
            ));
        }
        _ => {}
    }

    Err(crate::eval::ControlSignal::Error(
        "AREF: not an array".to_string(),
    ))
}

fn prim_set_aref(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 3 {
        return Err(crate::eval::ControlSignal::Error(
            "SET-AREF requires at least 3 arguments".to_string(),
        ));
    }

    let array = args[0];
    let value = *args.last().unwrap();
    let indices = &args[1..args.len() - 1];

    if let Node::Leaf(OpaqueValue::VectorHandle(idx)) = proc.arena.inner.get_unchecked(array) {
        let vec_id = crate::arrays::VectorId(*idx);
        let arr = proc.arrays.get(vec_id).ok_or_else(|| {
            crate::eval::ControlSignal::Error("SET-AREF: invalid array".to_string())
        })?;
        if indices.len() != arr.rank() {
            return Err(crate::eval::ControlSignal::Error(
                "SET-AREF: wrong number of indices".to_string(),
            ));
        }
        let mut idxs = Vec::with_capacity(indices.len());
        for &idx_node in indices {
            let i = match extract_number(&proc.arena.inner, idx_node) {
                NumVal::Int(n) if n >= 0 => n as usize,
                _ => {
                    return Err(crate::eval::ControlSignal::Error(
                        "SET-AREF: invalid index".to_string(),
                    ))
                }
            };
            idxs.push(i);
        }
        let mut linear = 0usize;
        let mut stride = 1usize;
        for (dim, idx) in arr
            .dimensions
            .iter()
            .rev()
            .zip(idxs.iter().rev())
        {
            if *idx >= *dim {
                return Err(crate::eval::ControlSignal::Error(
                    "SET-AREF: index out of bounds".to_string(),
                ));
            }
            linear += idx * stride;
            stride *= *dim;
        }
        if proc.arrays.set_aref(vec_id, linear, value) {
            return Ok(value);
        }
        return Err(crate::eval::ControlSignal::Error(
            "SET-AREF: index out of bounds".to_string(),
        ));
    }

    Err(crate::eval::ControlSignal::Error(
        "SET-AREF: not an array".to_string(),
    ))
}

fn prim_set_macro_character(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    // (set-macro-character char function [non-terminating-p])
    if args.len() < 2 || args.len() > 4 {
        return Err(crate::eval::ControlSignal::Error(
            "SET-MACRO-CHARACTER requires 2 to 4 arguments".to_string(),
        ));
    }

    // 1. Character
    let ch = node_to_char(proc, ctx, args[0]).ok_or_else(|| {
        crate::eval::ControlSignal::Error("SET-MACRO-CHARACTER: invalid character".to_string())
    })?;

    // 2. Function designator (symbol or function)
    if matches!(proc.arena.inner.get_unchecked(args[1]), Node::Leaf(OpaqueValue::Nil)) {
        return Err(crate::eval::ControlSignal::Error(
            "SET-MACRO-CHARACTER: function designator required".to_string(),
        ));
    }
    let macro_fn = if let Some(sym_id) = node_to_symbol(proc, args[1]) {
        let func_name = ctx
            .symbols
            .read()
            .unwrap()
            .get_symbol(sym_id)
            .map(|s| s.name.clone())
            .unwrap_or_default();
        get_reader_macro(&func_name)
    } else {
        None
    };

    // 3. Non-terminating?
    let non_terminating = if args.len() > 2 {
        args[2] != proc.make_nil()
    } else {
        false
    };

    // 4. Optional readtable
    let rt_id = if args.len() > 3 {
        readtable_from_node(proc, args[3])?
    } else {
        current_readtable_id(proc, ctx)
    };
    let rt = proc
        .readtable_by_id_mut(rt_id)
        .ok_or_else(|| ControlSignal::Error("SET-MACRO-CHARACTER: invalid readtable".to_string()))?;

    // Update readtable
    use crate::readtable::SyntaxType;
    let syntax = if non_terminating {
        SyntaxType::NonTerminatingMacro
    } else {
        SyntaxType::TerminatingMacro
    };

    rt.set_syntax_type(ch, syntax);
    if let Some(f) = macro_fn {
        rt.set_macro_character(ch, Some(f));
    } else {
        rt.set_macro_character(ch, None);
    }
    rt.set_lisp_macro(ch, Some(args[1]));

    Ok(proc.make_t(ctx))
}

fn prim_readtablep(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("READTABLEP requires exactly 1 argument");
    }
    match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::Readtable(_)) => Ok(proc.make_t(ctx)),
        _ => Ok(proc.make_nil()),
    }
}

fn prim_copy_readtable(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() > 2 {
        return err_helper("COPY-READTABLE accepts at most 2 arguments");
    }

    let from_id = if args.is_empty() {
        current_readtable_id(proc, ctx)
    } else {
        readtable_from_node(proc, args[0])?
    };

    let from = proc
        .readtable_by_id(from_id)
        .ok_or_else(|| ControlSignal::Error("COPY-READTABLE: missing source".to_string()))?
        .clone();

    let dest_id = if args.len() == 2 {
        match proc.arena.inner.get_unchecked(args[1]) {
            Node::Leaf(OpaqueValue::Nil) => proc.readtables.alloc(from),
            Node::Leaf(OpaqueValue::Readtable(id)) => {
                let rid = ReadtableId(*id);
                if let Some(dest) = proc.readtable_by_id_mut(rid) {
                    *dest = from;
                    rid
                } else {
                    return err_helper("COPY-READTABLE: invalid destination");
                }
            }
            _ => return err_helper("COPY-READTABLE: invalid destination"),
        }
    } else {
        proc.readtables.alloc(from)
    };

    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Readtable(dest_id.0))))
}

fn prim_readtable_case(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() > 1 {
        return err_helper("READTABLE-CASE accepts at most 1 argument");
    }
    let rt_id = if args.is_empty() {
        current_readtable_id(proc, ctx)
    } else {
        readtable_from_node(proc, args[0])?
    };
    let rt = proc
        .readtable_by_id(rt_id)
        .ok_or_else(|| ControlSignal::Error("READTABLE-CASE: invalid readtable".to_string()))?;

    let case_sym = match rt.readtable_case() {
        ReadtableCase::Upcase => "UPCASE",
        ReadtableCase::Downcase => "DOWNCASE",
        ReadtableCase::Preserve => "PRESERVE",
        ReadtableCase::Invert => "INVERT",
    };
    let sym_id = ctx.symbols.write().unwrap().intern_keyword(case_sym);
    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0))))
}

fn prim_set_readtable_case(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return err_helper("SET-READTABLE-CASE requires readtable and case");
    }
    let rt_id = readtable_from_node(proc, args[0])?;
    let case_sym = match proc.arena.inner.get_unchecked(args[1]) {
        Node::Leaf(OpaqueValue::Symbol(id)) => ctx
            .symbols
            .read()
            .unwrap()
            .symbol_name(SymbolId(*id))
            .unwrap_or("")
            .to_uppercase(),
        _ => {
            return err_helper("SET-READTABLE-CASE: case must be a symbol");
        }
    };

    let mode = match case_sym.as_str() {
        "UPCASE" => ReadtableCase::Upcase,
        "DOWNCASE" => ReadtableCase::Downcase,
        "PRESERVE" => ReadtableCase::Preserve,
        "INVERT" => ReadtableCase::Invert,
        _ => return err_helper("SET-READTABLE-CASE: invalid case symbol"),
    };

    if let Some(rt) = proc.readtable_by_id_mut(rt_id) {
        rt.set_readtable_case(mode);
    }

    let sym_id = ctx.symbols.write().unwrap().intern_keyword(&case_sym);
    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0))))
}

fn prim_get_macro_character(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 2 {
        return err_helper("GET-MACRO-CHARACTER requires 1 or 2 arguments");
    }

    let ch = node_to_char(proc, ctx, args[0])
        .ok_or_else(|| ControlSignal::Error("GET-MACRO-CHARACTER: invalid character".to_string()))?;

    let rt_id = if args.len() > 1 {
        readtable_from_node(proc, args[1])?
    } else {
        current_readtable_id(proc, ctx)
    };
    let rt = proc
        .readtable_by_id(rt_id)
        .ok_or_else(|| ControlSignal::Error("GET-MACRO-CHARACTER: invalid readtable".to_string()))?;

    let lisp_macro = rt.get_lisp_macro(ch);
    let has_macro = rt.get_macro_character(ch).is_some();
    let syntax = rt.get_syntax_type(ch);

    let mut func_node = lisp_macro;
    if func_node.is_none() && has_macro {
        let name = match ch {
            '(' => Some("READ-LEFT-PAREN"),
            ')' => Some("READ-RIGHT-PAREN"),
            '\'' => Some("READ-QUOTE"),
            '"' => Some("READ-STRING"),
            ';' => Some("READ-COMMENT"),
            '`' => Some("READ-BACKQUOTE"),
            ',' => Some("READ-COMMA"),
            '#' => Some("READ-DISPATCH"),
            _ => None,
        };
        if let Some(n) = name {
            let sym_id = ctx.symbols.write().unwrap().intern_in(n, PackageId(2));
            func_node = Some(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0))));
        }
    }

    let non_term = if func_node.is_some() {
        matches!(syntax, crate::readtable::SyntaxType::NonTerminatingMacro)
    } else {
        false
    };
    let func_node = func_node.unwrap_or_else(|| proc.make_nil());
    let non_term_node = if non_term {
        proc.make_t(ctx)
    } else {
        proc.make_nil()
    };
    let primary = set_multiple_values(proc, vec![func_node, non_term_node]);
    Ok(primary)
}

fn prim_set_syntax_from_char(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 || args.len() > 4 {
        return err_helper("SET-SYNTAX-FROM-CHAR requires 2 to 4 arguments");
    }

    let to_ch = node_to_char(proc, ctx, args[0])
        .ok_or_else(|| ControlSignal::Error("SET-SYNTAX-FROM-CHAR: invalid to-char".into()))?;
    let from_ch = node_to_char(proc, ctx, args[1])
        .ok_or_else(|| ControlSignal::Error("SET-SYNTAX-FROM-CHAR: invalid from-char".into()))?;

    let to_rt_id = if args.len() > 2 {
        readtable_from_node(proc, args[2])?
    } else {
        current_readtable_id(proc, ctx)
    };
    let from_rt_id = if args.len() > 3 {
        readtable_from_node(proc, args[3])?
    } else {
        current_readtable_id(proc, ctx)
    };

    let from_rt = proc
        .readtable_by_id(from_rt_id)
        .ok_or_else(|| ControlSignal::Error("SET-SYNTAX-FROM-CHAR: invalid from readtable".to_string()))?;
    let syntax = from_rt.get_syntax_type(from_ch);
    let macro_fn = from_rt.get_macro_character(from_ch);
    let lisp_macro = from_rt.get_lisp_macro(from_ch);
    let dispatch_table = from_rt.get_dispatch_table(from_ch).cloned();

    let to_rt = proc
        .readtable_by_id_mut(to_rt_id)
        .ok_or_else(|| ControlSignal::Error("SET-SYNTAX-FROM-CHAR: invalid to readtable".to_string()))?;
    to_rt.set_syntax_type(to_ch, syntax);
    if let Some(f) = macro_fn {
        to_rt.set_macro_character(to_ch, Some(f));
    } else {
        to_rt.set_macro_character(to_ch, None);
    }
    to_rt.set_lisp_macro(to_ch, lisp_macro);
    to_rt.set_dispatch_table(to_ch, dispatch_table);

    Ok(proc.make_t(ctx))
}

fn prim_make_dispatch_macro_character(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() || args.len() > 3 {
        return err_helper("MAKE-DISPATCH-MACRO-CHARACTER requires 1 to 3 arguments");
    }

    let ch = node_to_char(proc, ctx, args[0]).ok_or_else(|| {
        ControlSignal::Error("MAKE-DISPATCH-MACRO-CHARACTER: invalid character".to_string())
    })?;

    let non_terminating = if args.len() > 1 {
        args[1] != proc.make_nil()
    } else {
        false
    };

    let rt_id = if args.len() > 2 {
        readtable_from_node(proc, args[2])?
    } else {
        current_readtable_id(proc, ctx)
    };
    let rt = proc
        .readtable_by_id_mut(rt_id)
        .ok_or_else(|| ControlSignal::Error("MAKE-DISPATCH-MACRO-CHARACTER: invalid readtable".to_string()))?;

    use crate::readtable::SyntaxType;
    let syntax = if non_terminating {
        SyntaxType::NonTerminatingMacro
    } else {
        SyntaxType::TerminatingMacro
    };
    rt.set_syntax_type(ch, syntax);
    rt.make_dispatch_macro_character(ch);

    Ok(proc.make_t(ctx))
}

fn prim_set_dispatch_macro_character(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 3 || args.len() > 4 {
        return err_helper("SET-DISPATCH-MACRO-CHARACTER requires 3 or 4 arguments");
    }

    let disp = node_to_char(proc, ctx, args[0]).ok_or_else(|| {
        ControlSignal::Error("SET-DISPATCH-MACRO-CHARACTER: invalid dispatch char".to_string())
    })?;
    let sub = node_to_char(proc, ctx, args[1]).ok_or_else(|| {
        ControlSignal::Error("SET-DISPATCH-MACRO-CHARACTER: invalid sub char".to_string())
    })?;

    let func = if matches!(proc.arena.inner.get_unchecked(args[2]), Node::Leaf(OpaqueValue::Nil))
    {
        None
    } else {
        Some(args[2])
    };
    let rt_id = if args.len() > 3 {
        readtable_from_node(proc, args[3])?
    } else {
        current_readtable_id(proc, ctx)
    };
    let rt = proc
        .readtable_by_id_mut(rt_id)
        .ok_or_else(|| {
            ControlSignal::Error("SET-DISPATCH-MACRO-CHARACTER: invalid readtable".to_string())
        })?;
    if !rt.is_dispatch_macro_character(disp) {
        return Err(ControlSignal::Error(
            "SET-DISPATCH-MACRO-CHARACTER: not a dispatch macro character".into(),
        ));
    }
    rt.set_dispatch_macro_character(disp, sub, func);

    Ok(proc.make_t(ctx))
}

fn prim_get_dispatch_macro_character(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 || args.len() > 3 {
        return err_helper("GET-DISPATCH-MACRO-CHARACTER requires 2 or 3 arguments");
    }

    let disp = node_to_char(proc, ctx, args[0]).ok_or_else(|| {
        ControlSignal::Error("GET-DISPATCH-MACRO-CHARACTER: invalid dispatch char".to_string())
    })?;
    let sub = node_to_char(proc, ctx, args[1]).ok_or_else(|| {
        ControlSignal::Error("GET-DISPATCH-MACRO-CHARACTER: invalid sub char".to_string())
    })?;

    let rt_id = if args.len() > 2 {
        readtable_from_node(proc, args[2])?
    } else {
        current_readtable_id(proc, ctx)
    };
    let rt = proc
        .readtable_by_id(rt_id)
        .ok_or_else(|| ControlSignal::Error("GET-DISPATCH-MACRO-CHARACTER: invalid readtable".to_string()))?;

    if !rt.is_dispatch_macro_character(disp) {
        return Err(ControlSignal::Error(
            "GET-DISPATCH-MACRO-CHARACTER: not a dispatch macro character".into(),
        ));
    }

    if let Some(func) = rt.get_dispatch_macro_character(disp, sub) {
        Ok(func)
    } else {
        Ok(proc.make_nil())
    }
}

fn get_reader_macro(name: &str) -> Option<crate::readtable::ReaderMacroFn> {
    match name {
        "READ-LEFT-BRACKET" => Some(wrap_read_left_bracket),
        "READ-RIGHT-BRACKET" => Some(wrap_read_right_bracket),
        _ => None,
    }
}

fn current_readtable_id(
    proc: &crate::process::Process,
    ctx: &crate::context::GlobalContext,
) -> ReadtableId {
    let readtable_sym = ctx
        .symbols
        .write()
        .unwrap()
        .intern_in("*READTABLE*", PackageId(1));
    if let Some(val) = proc.get_value(readtable_sym) {
        if let Node::Leaf(OpaqueValue::Readtable(id)) = proc.arena.inner.get_unchecked(val) {
            let rid = ReadtableId(*id);
            if proc.readtable_by_id(rid).is_some() {
                return rid;
            }
        }
    }
    proc.current_readtable
}

fn readtable_from_node(
    proc: &crate::process::Process,
    node: NodeId,
) -> Result<ReadtableId, ControlSignal> {
    match proc.arena.inner.get_unchecked(node) {
        Node::Leaf(OpaqueValue::Readtable(id)) => {
            let rid = ReadtableId(*id);
            if proc.readtable_by_id(rid).is_some() {
                Ok(rid)
            } else {
                Err(ControlSignal::Error("Invalid readtable id".to_string()))
            }
        }
        Node::Leaf(OpaqueValue::Nil) => Ok(proc.standard_readtable),
        _ => Err(ControlSignal::Error("Invalid readtable designator".to_string())),
    }
}

fn wrap_read_left_bracket(
    reader: &mut crate::reader::Reader,
    c: char,
) -> crate::reader::ReaderResult {
    reader.read_left_bracket(c)
}

fn wrap_read_right_bracket(
    reader: &mut crate::reader::Reader,
    c: char,
) -> crate::reader::ReaderResult {
    reader.read_right_bracket(c)
}

// ============================================================================
// Helper Types
// ============================================================================

#[derive(Debug, Clone)]
enum NumVal {
    Int(i64),
    Big(BigInt),
    Ratio(BigInt, BigInt),
    Float(f64),
    None,
}

fn normalize_ratio(mut num: BigInt, mut den: BigInt) -> Option<(BigInt, BigInt)> {
    if den == BigInt::from(0) {
        return None;
    }
    if den.is_negative() {
        num = -num;
        den = -den;
    }
    let mut a = num.abs();
    let mut b = den.abs();
    while b != BigInt::from(0) {
        let r = &a % &b;
        a = b;
        b = r;
    }
    if a != BigInt::from(0) {
        num /= &a;
        den /= &a;
    }
    Some((num, den))
}

fn ratio_from_bigints(num: BigInt, den: BigInt) -> NumVal {
    match normalize_ratio(num, den) {
        None => NumVal::None,
        Some((n, d)) => {
            if d == BigInt::from(1) {
                if let Some(v) = n.to_i64() {
                    NumVal::Int(v)
                } else {
                    NumVal::Big(n)
                }
            } else {
                NumVal::Ratio(n, d)
            }
        }
    }
}

fn ratio_to_f64(num: &BigInt, den: &BigInt) -> Option<f64> {
    let n = num.to_f64()?;
    let d = den.to_f64()?;
    Some(n / d)
}

impl NumVal {
    fn add(self, other: NumVal) -> NumVal {
        match (self, other) {
            (NumVal::Int(a), NumVal::Int(b)) => match a.checked_add(b) {
                Some(res) => NumVal::Int(res),
                None => NumVal::Big(BigInt::from(a) + BigInt::from(b)),
            },
            (NumVal::Big(a), NumVal::Big(b)) => NumVal::Big(a + b),
            (NumVal::Int(a), NumVal::Big(b)) => NumVal::Big(BigInt::from(a) + b),
            (NumVal::Big(a), NumVal::Int(b)) => NumVal::Big(a + BigInt::from(b)),
            (NumVal::Ratio(a, b), NumVal::Ratio(c, d)) => {
                ratio_from_bigints(a * d.clone() + c * b.clone(), b * d)
            }
            (NumVal::Ratio(a, b), NumVal::Int(n)) => {
                ratio_from_bigints(a + BigInt::from(n) * b.clone(), b)
            }
            (NumVal::Int(n), NumVal::Ratio(a, b)) => {
                ratio_from_bigints(BigInt::from(n) * b.clone() + a, b)
            }
            (NumVal::Ratio(a, b), NumVal::Big(c)) => {
                ratio_from_bigints(a + c * b.clone(), b)
            }
            (NumVal::Big(c), NumVal::Ratio(a, b)) => {
                ratio_from_bigints(c * b.clone() + a, b)
            }
            (NumVal::Ratio(a, b), NumVal::Float(f)) => ratio_to_f64(&a, &b)
                .map(|v| NumVal::Float(v + f))
                .unwrap_or(NumVal::None),
            (NumVal::Float(f), NumVal::Ratio(a, b)) => ratio_to_f64(&a, &b)
                .map(|v| NumVal::Float(f + v))
                .unwrap_or(NumVal::None),

            (NumVal::Float(a), NumVal::Float(b)) => NumVal::Float(a + b),
            (NumVal::Int(a), NumVal::Float(b)) => NumVal::Float(a as f64 + b),
            (NumVal::Float(a), NumVal::Int(b)) => NumVal::Float(a + b as f64),
            (NumVal::Big(a), NumVal::Float(b)) => {
                NumVal::Float(a.to_f64().unwrap_or(f64::INFINITY) + b)
            }
            (NumVal::Float(a), NumVal::Big(b)) => {
                NumVal::Float(a + b.to_f64().unwrap_or(f64::INFINITY))
            }
            _ => NumVal::None,
        }
    }

    fn sub(self, other: NumVal) -> NumVal {
        match (self, other) {
            (NumVal::Int(a), NumVal::Int(b)) => match a.checked_sub(b) {
                Some(res) => NumVal::Int(res),
                None => NumVal::Big(BigInt::from(a) - BigInt::from(b)),
            },
            (NumVal::Big(a), NumVal::Big(b)) => NumVal::Big(a - b),
            (NumVal::Int(a), NumVal::Big(b)) => NumVal::Big(BigInt::from(a) - b),
            (NumVal::Big(a), NumVal::Int(b)) => NumVal::Big(a - BigInt::from(b)),
            (NumVal::Ratio(a, b), NumVal::Ratio(c, d)) => {
                ratio_from_bigints(a * d.clone() - c * b.clone(), b * d)
            }
            (NumVal::Ratio(a, b), NumVal::Int(n)) => {
                ratio_from_bigints(a - BigInt::from(n) * b.clone(), b)
            }
            (NumVal::Int(n), NumVal::Ratio(a, b)) => {
                ratio_from_bigints(BigInt::from(n) * b.clone() - a, b)
            }
            (NumVal::Ratio(a, b), NumVal::Big(c)) => {
                ratio_from_bigints(a - c * b.clone(), b)
            }
            (NumVal::Big(c), NumVal::Ratio(a, b)) => {
                ratio_from_bigints(c * b.clone() - a, b)
            }
            (NumVal::Ratio(a, b), NumVal::Float(f)) => ratio_to_f64(&a, &b)
                .map(|v| NumVal::Float(v - f))
                .unwrap_or(NumVal::None),
            (NumVal::Float(f), NumVal::Ratio(a, b)) => ratio_to_f64(&a, &b)
                .map(|v| NumVal::Float(f - v))
                .unwrap_or(NumVal::None),

            (NumVal::Float(a), NumVal::Float(b)) => NumVal::Float(a - b),
            (NumVal::Int(a), NumVal::Float(b)) => NumVal::Float(a as f64 - b),
            (NumVal::Float(a), NumVal::Int(b)) => NumVal::Float(a - b as f64),
            (NumVal::Big(a), NumVal::Float(b)) => {
                NumVal::Float(a.to_f64().unwrap_or(f64::INFINITY) - b)
            }
            (NumVal::Float(a), NumVal::Big(b)) => {
                NumVal::Float(a - b.to_f64().unwrap_or(f64::INFINITY))
            }
            _ => NumVal::None,
        }
    }

    fn mul(self, other: NumVal) -> NumVal {
        match (self, other) {
            (NumVal::Int(a), NumVal::Int(b)) => match a.checked_mul(b) {
                Some(res) => NumVal::Int(res),
                None => NumVal::Big(BigInt::from(a) * BigInt::from(b)),
            },
            (NumVal::Big(a), NumVal::Big(b)) => NumVal::Big(a * b),
            (NumVal::Int(a), NumVal::Big(b)) => NumVal::Big(BigInt::from(a) * b),
            (NumVal::Big(a), NumVal::Int(b)) => NumVal::Big(a * BigInt::from(b)),
            (NumVal::Ratio(a, b), NumVal::Ratio(c, d)) => {
                ratio_from_bigints(a * c, b * d)
            }
            (NumVal::Ratio(a, b), NumVal::Int(n)) => {
                ratio_from_bigints(a * BigInt::from(n), b)
            }
            (NumVal::Int(n), NumVal::Ratio(a, b)) => {
                ratio_from_bigints(BigInt::from(n) * a, b)
            }
            (NumVal::Ratio(a, b), NumVal::Big(c)) => ratio_from_bigints(a * c, b),
            (NumVal::Big(c), NumVal::Ratio(a, b)) => ratio_from_bigints(c * a, b),
            (NumVal::Ratio(a, b), NumVal::Float(f)) => ratio_to_f64(&a, &b)
                .map(|v| NumVal::Float(v * f))
                .unwrap_or(NumVal::None),
            (NumVal::Float(f), NumVal::Ratio(a, b)) => ratio_to_f64(&a, &b)
                .map(|v| NumVal::Float(f * v))
                .unwrap_or(NumVal::None),

            (NumVal::Float(a), NumVal::Float(b)) => NumVal::Float(a * b),
            (NumVal::Int(a), NumVal::Float(b)) => NumVal::Float(a as f64 * b),
            (NumVal::Float(a), NumVal::Int(b)) => NumVal::Float(a * b as f64),
            (NumVal::Big(a), NumVal::Float(b)) => {
                NumVal::Float(a.to_f64().unwrap_or(f64::INFINITY) * b)
            }
            (NumVal::Float(a), NumVal::Big(b)) => {
                NumVal::Float(a * b.to_f64().unwrap_or(f64::INFINITY))
            }
            _ => NumVal::None,
        }
    }

    fn div(self, other: NumVal) -> NumVal {
        match (self, other) {
            (NumVal::Int(a), NumVal::Int(b)) => {
                ratio_from_bigints(BigInt::from(a), BigInt::from(b))
            }
            (NumVal::Big(a), NumVal::Big(b)) => ratio_from_bigints(a, b),
            (NumVal::Big(a), NumVal::Int(b)) => ratio_from_bigints(a, BigInt::from(b)),
            (NumVal::Int(a), NumVal::Big(b)) => ratio_from_bigints(BigInt::from(a), b),
            (NumVal::Ratio(a, b), NumVal::Ratio(c, d)) => {
                ratio_from_bigints(a * d, b * c)
            }
            (NumVal::Ratio(a, b), NumVal::Int(n)) => {
                ratio_from_bigints(a, b * BigInt::from(n))
            }
            (NumVal::Int(n), NumVal::Ratio(a, b)) => {
                ratio_from_bigints(BigInt::from(n) * b, a)
            }
            (NumVal::Ratio(a, b), NumVal::Big(c)) => ratio_from_bigints(a, b * c),
            (NumVal::Big(c), NumVal::Ratio(a, b)) => ratio_from_bigints(c * b, a),
            (NumVal::Ratio(a, b), NumVal::Float(f)) => ratio_to_f64(&a, &b)
                .map(|v| NumVal::Float(v / f))
                .unwrap_or(NumVal::None),
            (NumVal::Float(f), NumVal::Ratio(a, b)) => ratio_to_f64(&a, &b)
                .map(|v| NumVal::Float(f / v))
                .unwrap_or(NumVal::None),
            (NumVal::Int(a), NumVal::Float(b)) => NumVal::Float(a as f64 / b),
            (NumVal::Big(a), NumVal::Float(b)) => {
                NumVal::Float(a.to_f64().unwrap_or(f64::INFINITY) / b)
            }
            (NumVal::Float(a), NumVal::Int(b)) => NumVal::Float(a / b as f64),
            (NumVal::Float(a), NumVal::Big(b)) => {
                NumVal::Float(a / b.to_f64().unwrap_or(f64::INFINITY))
            }
            (NumVal::Float(a), NumVal::Float(b)) => NumVal::Float(a / b),
            _ => NumVal::None,
        }
    }
}

impl PartialEq for NumVal {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (NumVal::Int(a), NumVal::Int(b)) => a == b,
            (NumVal::Big(a), NumVal::Big(b)) => a == b,
            (NumVal::Int(a), NumVal::Big(b)) => &BigInt::from(*a) == b,
            (NumVal::Big(a), NumVal::Int(b)) => a == &BigInt::from(*b),
            (NumVal::Ratio(a, b), NumVal::Ratio(c, d)) => a * d == c * b,
            (NumVal::Ratio(a, b), NumVal::Int(n)) => a == &(BigInt::from(*n) * b),
            (NumVal::Int(n), NumVal::Ratio(a, b)) => BigInt::from(*n) * b == *a,
            (NumVal::Ratio(a, b), NumVal::Big(c)) => a == &(c * b),
            (NumVal::Big(c), NumVal::Ratio(a, b)) => c * b == *a,
            (NumVal::Ratio(a, b), NumVal::Float(f)) => ratio_to_f64(a, b)
                .map(|v| v == *f)
                .unwrap_or(false),
            (NumVal::Float(f), NumVal::Ratio(a, b)) => ratio_to_f64(a, b)
                .map(|v| *f == v)
                .unwrap_or(false),
            (NumVal::Float(a), NumVal::Float(b)) => a == b,
            (NumVal::Int(a), NumVal::Float(b)) => (*a as f64) == *b,
            (NumVal::Float(a), NumVal::Int(b)) => *a == (*b as f64),
            (NumVal::Big(a), NumVal::Float(b)) => a.to_f64().unwrap_or(f64::INFINITY) == *b,
            (NumVal::Float(a), NumVal::Big(b)) => *a == b.to_f64().unwrap_or(f64::INFINITY),
            _ => false,
        }
    }
}

impl PartialOrd for NumVal {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (NumVal::Int(a), NumVal::Int(b)) => a.partial_cmp(b),
            (NumVal::Big(a), NumVal::Big(b)) => a.partial_cmp(b),
            (NumVal::Int(a), NumVal::Big(b)) => BigInt::from(*a).partial_cmp(b),
            (NumVal::Big(a), NumVal::Int(b)) => a.partial_cmp(&BigInt::from(*b)),
            (NumVal::Ratio(a, b), NumVal::Ratio(c, d)) => Some((a * d).cmp(&(c * b))),
            (NumVal::Ratio(a, b), NumVal::Int(n)) => {
                Some(a.cmp(&(BigInt::from(*n) * b)))
            }
            (NumVal::Int(n), NumVal::Ratio(a, b)) => {
                Some((BigInt::from(*n) * b).cmp(a))
            }
            (NumVal::Ratio(a, b), NumVal::Big(c)) => Some(a.cmp(&(c * b))),
            (NumVal::Big(c), NumVal::Ratio(a, b)) => Some((c * b).cmp(a)),
            (NumVal::Ratio(a, b), NumVal::Float(f)) => ratio_to_f64(a, b)
                .and_then(|v| v.partial_cmp(f)),
            (NumVal::Float(f), NumVal::Ratio(a, b)) => ratio_to_f64(a, b)
                .and_then(|v| f.partial_cmp(&v)),
            (NumVal::Float(a), NumVal::Float(b)) => a.partial_cmp(b),
            (NumVal::Int(a), NumVal::Float(b)) => (*a as f64).partial_cmp(b),
            (NumVal::Float(a), NumVal::Int(b)) => a.partial_cmp(&(*b as f64)),
            (NumVal::Big(a), NumVal::Float(b)) => {
                a.to_f64().unwrap_or(f64::INFINITY).partial_cmp(b)
            }
            (NumVal::Float(a), NumVal::Big(b)) => {
                a.partial_cmp(&b.to_f64().unwrap_or(f64::INFINITY))
            }
            _ => None,
        }
    }
}

impl NumVal {
    fn to_node(self, arena: &mut Arena) -> NodeId {
        match self {
            NumVal::Int(n) => arena.alloc(Node::Leaf(OpaqueValue::Integer(n))),
            NumVal::Big(n) => arena.alloc(Node::Leaf(OpaqueValue::BigInt(n))),
            NumVal::Ratio(n, d) => arena.alloc(Node::Leaf(OpaqueValue::Ratio(n, d))),
            NumVal::Float(f) => arena.alloc(Node::Leaf(OpaqueValue::Float(f))),
            NumVal::None => arena.alloc(Node::Leaf(OpaqueValue::Nil)),
        }
    }
}

fn extract_number(arena: &Arena, node: NodeId) -> NumVal {
    match arena.get_unchecked(node) {
        Node::Leaf(OpaqueValue::Integer(n)) => NumVal::Int(*n),
        Node::Leaf(OpaqueValue::BigInt(n)) => NumVal::Big(n.clone()),
        Node::Leaf(OpaqueValue::Ratio(n, d)) => NumVal::Ratio(n.clone(), d.clone()),
        Node::Leaf(OpaqueValue::Float(f)) => NumVal::Float(*f),
        _ => NumVal::None,
    }
}

fn prim_compile(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        let node = proc.arena.inner.get_unchecked(arg).clone();

        let target_closure = match node {
            Node::Leaf(OpaqueValue::Symbol(id)) => {
                let sym = SymbolId(id);
                if let Some(func_node) = proc.get_function(sym) {
                    if let Node::Leaf(OpaqueValue::Closure(idx)) =
                        proc.arena.inner.get_unchecked(func_node)
                    {
                        Some(*idx)
                    } else {
                        return err_helper("COMPILE: Symbol function is not a closure (maybe already compiled or primitive?)");
                    }
                } else {
                    return err_helper("COMPILE: Symbol has no function definition");
                }
            }
            Node::Leaf(OpaqueValue::Closure(idx)) => Some(idx),
            _ => {
                return err_helper("COMPILE: Argument must be a symbol or closure");
            }
        };

        if let Some(idx) = target_closure {
            let (params, body) = {
                let closure = &proc.closures[idx as usize];
                let mut params = Vec::new();
                for &p in &closure.lambda_list.req {
                    if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(p) {
                        params.push(SymbolId(*id));
                    } else {
                        // If we can't compile destructuring, just pass empty or error later?
                        // For now we assume symbols. If not, the compiler will mismatch count or logic.
                        // But compile_func expects SymbolId.
                    }
                }
                (params, closure.body)
            };

            match crate::compiler::compile_func(proc, ctx, &params, body) {
                Ok(compiled_node) => return Ok(compiled_node),
                Err(e) => return err_helper(&format!("Compilation failed: {}", e)),
            }
        }
    }

    err_helper("COMPILE: Invalid argument")
}

fn prim_compile_lisp(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        let node = proc.arena.inner.get_unchecked(arg).clone();

        let target_closure = match node {
            Node::Leaf(OpaqueValue::Symbol(id)) => {
                let sym = SymbolId(id);
                if let Some(func_node) = proc.get_function(sym) {
                    if let Node::Leaf(OpaqueValue::Closure(idx)) =
                        proc.arena.inner.get_unchecked(func_node)
                    {
                        Some(*idx)
                    } else {
                        return err_helper("COMPILE-LISP: Symbol function is not a closure (maybe already compiled or primitive?)");
                    }
                } else {
                    return err_helper("COMPILE-LISP: Symbol has no function definition");
                }
            }
            Node::Leaf(OpaqueValue::Closure(idx)) => Some(idx),
            _ => {
                return err_helper("COMPILE-LISP: Argument must be a symbol or closure");
            }
        };

        if let Some(idx) = target_closure {
            let (params, body) = {
                let closure = &proc.closures[idx as usize];
                let mut params = Vec::new();
                for &p in &closure.lambda_list.req {
                    if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(p) {
                        params.push(SymbolId(*id));
                    }
                }
                (params, closure.body)
            };

            match crate::compiler::compile_func_extended(proc, ctx, &params, body) {
                Ok(compiled_node) => return Ok(compiled_node),
                Err(e) => return err_helper(&format!("Compilation failed: {}", e)),
            }
        }
    }

    err_helper("COMPILE-LISP: Invalid argument")
}

fn prim_tree_string(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        let s = crate::printer::tree_format(&proc.arena.inner, arg);
        Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(s))))
    } else {
        Err(ControlSignal::Error(
            "TREE-STRING requires 1 argument".to_string(),
        ))
    }
}

fn prim_tc_encode_nat(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("TC-ENCODE-NAT requires 1 argument");
    }
    let node = proc.arena.inner.get_unchecked(args[0]);
    let n = match node {
        Node::Leaf(OpaqueValue::Integer(i)) if *i >= 0 => *i as u64,
        Node::Leaf(OpaqueValue::BigInt(b)) if b.sign() != num_bigint::Sign::Minus => {
            b.to_u64().ok_or_else(|| ControlSignal::Error("TC-ENCODE-NAT: too large".to_string()))?
        }
        _ => return err_helper("TC-ENCODE-NAT expects a non-negative integer"),
    };
    let encoded = tree_calculus::encode_nat(&mut proc.arena.inner, n);
    Ok(encoded)
}

fn prim_tc_decode_nat(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("TC-DECODE-NAT requires 1 argument");
    }
    let n = tree_calculus::decode_nat(&proc.arena.inner, args[0])
        .ok_or_else(|| ControlSignal::Error("TC-DECODE-NAT: not a tree-calculus nat".to_string()))?;
    if n <= i64::MAX as u64 {
        Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(n as i64))))
    } else {
        Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::BigInt(
            num_bigint::BigInt::from(n),
        ))))
    }
}

fn prim_tc_encode_string(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("TC-ENCODE-STRING requires 1 argument");
    }
    let node = proc.arena.inner.get_unchecked(args[0]);
    let s = match node {
        Node::Leaf(OpaqueValue::String(val)) => val.clone(),
        _ => return err_helper("TC-ENCODE-STRING expects a string"),
    };
    let encoded = tree_calculus::encode_string(&mut proc.arena.inner, &s);
    Ok(encoded)
}

fn prim_tc_decode_string(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("TC-DECODE-STRING requires 1 argument");
    }
    let s = tree_calculus::decode_string(&proc.arena.inner, args[0])
        .ok_or_else(|| ControlSignal::Error("TC-DECODE-STRING: not a TC string".to_string()))?;
    Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(s))))
}

fn prim_tc_succ(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return err_helper("TC-SUCC requires 1 argument");
    }
    let n = tree_calculus::decode_nat(&proc.arena.inner, args[0])
        .ok_or_else(|| ControlSignal::Error("TC-SUCC: not a tree-calculus nat".to_string()))?;
    let encoded = tree_calculus::encode_nat(&mut proc.arena.inner, n + 1);
    Ok(encoded)
}

fn prim_tc_add(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return err_helper("TC-ADD requires 2 arguments");
    }
    let a = tree_calculus::decode_nat(&proc.arena.inner, args[0])
        .ok_or_else(|| ControlSignal::Error("TC-ADD: first arg not a tree-calculus nat".to_string()))?;
    let b = tree_calculus::decode_nat(&proc.arena.inner, args[1])
        .ok_or_else(|| ControlSignal::Error("TC-ADD: second arg not a tree-calculus nat".to_string()))?;
    let sum = a
        .checked_add(b)
        .ok_or_else(|| ControlSignal::Error("TC-ADD: overflow".to_string()))?;
    let encoded = tree_calculus::encode_nat(&mut proc.arena.inner, sum);
    Ok(encoded)
}

fn prim_tc_equal(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 2 {
        return err_helper("TC-EQUAL requires 2 arguments");
    }
    let a = tree_calculus::decode_nat(&proc.arena.inner, args[0])
        .ok_or_else(|| ControlSignal::Error("TC-EQUAL: first arg not a tree-calculus nat".to_string()))?;
    let b = tree_calculus::decode_nat(&proc.arena.inner, args[1])
        .ok_or_else(|| ControlSignal::Error("TC-EQUAL: second arg not a tree-calculus nat".to_string()))?;
    if a == b {
        Ok(tree_calculus::k(&mut proc.arena.inner))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_tc_triage(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 4 {
        return err_helper("TC-TRIAGE requires 4 arguments: f0 f1 f2 z");
    }
    let f0 = args[0];
    let f1 = args[1];
    let f2 = args[2];
    let z = args[3];

    let arena = &mut proc.arena.inner;
    match arena.get_unchecked(z) {
        Node::Leaf(OpaqueValue::Nil) => Ok(f0),
        Node::Leaf(_) => err_helper("TC-TRIAGE: non-NIL leaf is not a pure tree"),
        _ => {
            if let Some(x) = tc_split_stem(arena, z) {
                Ok(arena.alloc(Node::Fork(f1, x)))
            } else if let Some((x, y)) = tc_split_fork(arena, z) {
                let fx = arena.alloc(Node::Fork(f2, x));
                Ok(arena.alloc(Node::Fork(fx, y)))
            } else {
                err_helper("TC-TRIAGE: not a leaf, stem, or fork")
            }
        }
    }
}

fn tc_split_stem(arena: &Arena, node: NodeId) -> Option<NodeId> {
    match arena.get_unchecked(node) {
        Node::Stem(x) => Some(*x),
        Node::Fork(op, x) if tree_calculus::is_delta(arena, *op) => Some(*x),
        _ => None,
    }
}

fn tc_split_fork(arena: &Arena, node: NodeId) -> Option<(NodeId, NodeId)> {
    match arena.get_unchecked(node) {
        Node::Fork(left, right) => tc_split_stem(arena, *left).map(|x| (x, *right)),
        _ => None,
    }
}

/// (funcall function arg1 arg2 ...)
fn prim_funcall(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return Err(ControlSignal::Error(
            "FUNCALL requires at least 1 argument".to_string(),
        ));
    }

    let func = args[0];
    let func_args = if args.len() > 1 {
        proc.make_list(&args[1..])
    } else {
        proc.make_nil()
    };

    let env = crate::eval::Environment::new();
    let saved_program = proc.program;
    let saved_mode = proc.execution_mode.clone();
    let saved_env = proc.current_env.clone();
    let saved_stack = std::mem::take(&mut proc.continuation_stack);
    let saved_pending = proc.pending_redex;
    let saved_next_methods = std::mem::take(&mut proc.next_method_states);
    let result = {
        let mut interp = Interpreter::new(proc, ctx);
        interp.apply_values(func, func_args, &env)
    };
    proc.program = saved_program;
    proc.execution_mode = saved_mode;
    proc.current_env = saved_env;
    proc.continuation_stack = saved_stack;
    proc.pending_redex = saved_pending;
    proc.next_method_states = saved_next_methods;
    result
}

/// (eval form)
fn prim_eval(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() != 1 {
        return Err(ControlSignal::Error(format!(
            "EVAL expects 1 argument, got {}",
            args.len()
        )));
    }

    let expr = args[0];
    let mut interp = Interpreter::new(proc, ctx);
    // Use an empty lexical environment for EVAL
    let env = crate::eval::Environment::new();
    interp.eval(expr, &env)
}

/// (apply function arg1 ... argn-1 list)
fn prim_apply(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return Err(ControlSignal::Error(
            "APPLY requires at least 2 arguments".to_string(),
        ));
    }

    let func = args[0];
    let last_arg = args[args.len() - 1]; // The list argument

    // Construct argument list.
    let mut final_args = last_arg;
    for &arg in args[1..args.len() - 1].iter().rev() {
        final_args = proc.arena.inner.alloc(Node::Fork(arg, final_args));
    }

    let env = crate::eval::Environment::new();
    // Preserve caller state so APPLY doesn't clobber it.
    let saved_program = proc.program;
    let saved_mode = proc.execution_mode.clone();
    let saved_env = proc.current_env.clone();
    let saved_stack = std::mem::take(&mut proc.continuation_stack);
    let saved_pending = proc.pending_redex;
    let saved_next_methods = std::mem::take(&mut proc.next_method_states);

    let result = {
        let mut interp = Interpreter::new(proc, ctx);
        interp.apply_values(func, final_args, &env)
    };

    proc.program = saved_program;
    proc.execution_mode = saved_mode;
    proc.current_env = saved_env;
    proc.continuation_stack = saved_stack;
    proc.pending_redex = saved_pending;
    proc.next_method_states = saved_next_methods;

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reader::read_from_string;

    #[test]
    fn test_add() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        let a = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(1)));
        let b = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(2)));
        let c = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(3)));

        let result = prim_add(&mut proc, &globals, &[a, b, c]).unwrap();
        match proc.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(6)) => {}
            _ => panic!("Expected 6"),
        }
    }

    #[test]
    fn test_cons_car_cdr() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        let a = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(1)));
        let b = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(2)));

        let cell = prim_cons(&mut proc, &globals, &[a, b]).unwrap();
        let car = prim_car(&mut proc, &globals, &[cell]).unwrap();
        let cdr = prim_cdr(&mut proc, &globals, &[cell]).unwrap();

        assert_eq!(car, a);
        assert_eq!(cdr, b);
    }

    #[test]
    fn test_length() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        let a = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(1)));
        let b = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(2)));
        let c = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(3)));
        let list = proc.make_list(&[a, b, c]);

        let len = prim_length(&mut proc, &globals, &[list]).unwrap();
        match proc.arena.inner.get_unchecked(len) {
            Node::Leaf(OpaqueValue::Integer(3)) => {}
            _ => panic!("Expected length 3"),
        }
    }

    #[test]
    fn test_defpackage_shadowing_import_before_use() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let name1 = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String("DS1-ORDER-TEST".to_string())));
        let opts1 = read_from_string(
            "((:use) (:export \"A\"))",
            &mut proc.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        prim_sys_defpackage(&mut proc, &globals, &[name1, opts1]).unwrap();

        let name2 = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String("DS2-ORDER-TEST".to_string())));
        let opts2 = read_from_string(
            "((:use) (:export \"A\"))",
            &mut proc.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        prim_sys_defpackage(&mut proc, &globals, &[name2, opts2]).unwrap();

        let name3 = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String("DS3-ORDER-TEST".to_string())));
        let opts3 = read_from_string(
            "((:shadowing-import-from \"DS1-ORDER-TEST\" \"A\") (:use \"DS1-ORDER-TEST\" \"DS2-ORDER-TEST\"))",
            &mut proc.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        prim_sys_defpackage(&mut proc, &globals, &[name3, opts3]).unwrap();
    }

    #[test]
    fn test_read_eval_resolves_nested_forms() {
        let mut globals = crate::context::GlobalContext::new();
        register_primitives(&mut globals);
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let (value_opt, _) =
            read_one_from_str(&mut proc, &globals, "#.(list 1 #.(+ 1 1))", false).unwrap();
        let value = value_opt.expect("expected a value");
        let items = list_to_vec(&proc, value);

        assert_eq!(items.len(), 2);
        match proc.arena.inner.get_unchecked(items[0]) {
            Node::Leaf(OpaqueValue::Integer(1)) => {}
            _ => panic!("Expected integer 1"),
        }
        match proc.arena.inner.get_unchecked(items[1]) {
            Node::Leaf(OpaqueValue::Integer(2)) => {}
            _ => panic!("Expected integer 2"),
        }
    }

    // === Extensive Arithmetic Tests ===

    #[test]
    fn test_add_empty() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        let result = prim_add(&mut proc, &globals, &[]).unwrap();
        match proc.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(0)) => {}
            _ => panic!("Expected 0"),
        }
    }

    #[test]
    fn test_add_single() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        let a = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(42)));
        let result = prim_add(&mut proc, &globals, &[a]).unwrap();
        match proc.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(42)) => {}
            _ => panic!("Expected 42"),
        }
    }

    #[test]
    fn test_add_many() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        let nums: Vec<_> = (1..=10)
            .map(|i| {
                proc.arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Integer(i as i64)))
            })
            .collect();
        let result = prim_add(&mut proc, &globals, &nums).unwrap();
        match proc.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(55)) => {} // 1+2+...+10 = 55
            _ => panic!("Expected 55"),
        }
    }

    #[test]
    fn test_sub_unary() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        let a = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(5)));
        let result = prim_sub(&mut proc, &globals, &[a]).unwrap();
        match proc.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(-5)) => {}
            _ => panic!("Expected -5"),
        }
    }

    #[test]
    fn test_sub_chain() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        let a = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Integer(100)));
        let b = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(30)));
        let c = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(20)));
        let result = prim_sub(&mut proc, &globals, &[a, b, c]).unwrap();
        match proc.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(50)) => {} // 100-30-20 = 50
            _ => panic!("Expected 50"),
        }
    }

    #[test]
    fn test_mul_empty() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        let result = prim_mul(&mut proc, &globals, &[]).unwrap();
        match proc.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(1)) => {}
            _ => panic!("Expected 1"),
        }
    }

    #[test]
    fn test_mul_chain() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        let a = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(2)));
        let b = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(3)));
        let c = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(4)));
        let d = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(5)));
        let result = prim_mul(&mut proc, &globals, &[a, b, c, d]).unwrap();
        match proc.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(120)) => {} // 2*3*4*5 = 120
            _ => panic!("Expected 120"),
        }
    }

    #[test]
    fn test_div_exact() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        let a = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(20)));
        let b = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(4)));
        let result = prim_div(&mut proc, &globals, &[a, b]).unwrap();
        match proc.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(5)) => {}
            Node::Leaf(OpaqueValue::BigInt(n)) if n == &num_bigint::BigInt::from(5) => {}
            _ => panic!("Expected integer 5"),
        }
    }

    #[test]
    fn test_div_fractional() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        let a = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(5)));
        let b = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(19)));
        let result = prim_div(&mut proc, &globals, &[a, b]).unwrap();
        match proc.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Ratio(n, d))
                if n == &num_bigint::BigInt::from(5)
                    && d == &num_bigint::BigInt::from(19) => {}
            other => panic!("Expected 5/19, got {:?}", other),
        }
    }

    #[test]
    fn test_mixed_float_int() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        let a = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(10)));
        let b = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Float(2.5)));
        let result = prim_add(&mut proc, &globals, &[a, b]).unwrap();
        match proc.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Float(f)) if (*f - 12.5).abs() < 0.001 => {}
            _ => panic!("Expected 12.5"),
        }
    }

    #[test]
    fn test_comparison_lt() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        let a = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(1)));
        let b = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(2)));
        let c = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(3)));
        let result = prim_lt(&mut proc, &globals, &[a, b, c]).unwrap();

        // Check if result is T
        match proc.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Symbol(id)) if *id == globals.t_sym.0 => {}
            _ => panic!("Expected T"),
        }
    }

    #[test]
    fn test_comparison_lt_false() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        let a = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(1)));
        let b = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(3)));
        let c = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(2)));
        let result = prim_lt(&mut proc, &globals, &[a, b, c]).unwrap();

        // Check if result is NIL
        match proc.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Nil) => {}
            _ => panic!("Expected NIL"),
        }
    }

    #[test]
    fn test_num_eq() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        let a = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(42)));
        let b = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(42)));
        let result = prim_num_eq(&mut proc, &globals, &[a, b]).unwrap();

        // Check if result is T
        match proc.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Symbol(id)) if *id == globals.t_sym.0 => {}
            _ => panic!("Expected T"),
        }
    }

    #[test]
    fn test_mod() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        let a = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(17)));
        let b = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(5)));
        let result = prim_mod(&mut proc, &globals, &[a, b]).unwrap();
        match proc.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(2)) => {} // 17 mod 5 = 2
            _ => panic!("Expected 2"),
        }
    }

    #[test]
    fn test_overflow() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );
        // i64::MAX is 9,223,372,036,854,775,807
        let large = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Integer(i64::MAX)));
        let two = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(2)));

        let result = prim_add(&mut proc, &globals, &[large, two]).unwrap();
        match proc.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::BigInt(_)) => {
                // Success: it promoted to BigInt
            }
            _ => panic!(
                "Expected overflow to BigInt, got {:?}",
                proc.arena.inner.get_unchecked(result)
            ),
        }
    }

    #[test]
    fn test_make_pathname_directory_name_type() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let kw_dir = globals.symbols.write().unwrap().intern_keyword("DIRECTORY");
        let kw_name = globals.symbols.write().unwrap().intern_keyword("NAME");
        let kw_type = globals.symbols.write().unwrap().intern_keyword("TYPE");

        let dir_kw = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(kw_dir.0)));
        let name_kw = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(kw_name.0)));
        let type_kw = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(kw_type.0)));

        let dir = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String("/tmp/treecl-path".to_string())));
        let name = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String("sample".to_string())));
        let ty = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String("lisp".to_string())));

        let result = prim_make_pathname(&mut proc, &globals, &[dir_kw, dir, name_kw, name, type_kw, ty])
            .unwrap();
        let out = string_from_designator(&proc, &globals, result).unwrap();
        assert!(out.ends_with("/tmp/treecl-path/sample.lisp"));
    }

    #[test]
    fn test_pathname_name_type_and_namestrings() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let path = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String("/tmp/treecl/sample.lisp".to_string())));
        let name = prim_pathname_name(&mut proc, &globals, &[path]).unwrap();
        let typ = prim_pathname_type(&mut proc, &globals, &[path]).unwrap();
        let file_ns = prim_file_namestring(&mut proc, &globals, &[path]).unwrap();
        let dir_ns = prim_directory_namestring(&mut proc, &globals, &[path]).unwrap();

        assert_eq!(
            string_from_designator(&proc, &globals, name).unwrap(),
            "sample"
        );
        assert_eq!(
            string_from_designator(&proc, &globals, typ).unwrap(),
            "lisp"
        );
        assert_eq!(
            string_from_designator(&proc, &globals, file_ns).unwrap(),
            "sample.lisp"
        );
        let dir_out = string_from_designator(&proc, &globals, dir_ns).unwrap();
        assert!(dir_out.ends_with("/tmp/treecl/"));
    }

    #[test]
    fn test_merge_pathnames_with_defaults() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let defaults_sym = globals
            .symbols
            .write()
            .unwrap()
            .intern_in("*DEFAULT-PATHNAME-DEFAULTS*", PackageId(1));
        let defaults = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(
            "/tmp/treecl-defaults/base.lisp".to_string(),
        )));
        proc.set_value(defaults_sym, defaults);

        let specified = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String("child.lisp".to_string())));
        let merged = prim_merge_pathnames(&mut proc, &globals, &[specified]).unwrap();
        let out = string_from_designator(&proc, &globals, merged).unwrap();
        assert!(out.ends_with("/tmp/treecl-defaults/child.lisp"));
    }

    #[test]
    fn test_parse_namestring_basic_and_bounds() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let raw = "dir/file.lisp";
        let path = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String(raw.to_string())));
        let pn = prim_parse_namestring(&mut proc, &globals, &[path]).unwrap();
        let out = string_from_designator(&proc, &globals, pn).unwrap();
        assert_eq!(out, raw);
        assert!(proc.values.len() >= 2);
        match proc.arena.inner.get_unchecked(proc.values[1]) {
            Node::Leaf(OpaqueValue::Integer(n)) => {
                assert_eq!(*n as usize, raw.chars().count());
            }
            other => panic!("Expected integer index, got {:?}", other),
        }

        let nil = proc.make_nil();
        let kw_start = globals.symbols.write().unwrap().intern_keyword("START");
        let kw_end = globals.symbols.write().unwrap().intern_keyword("END");
        let start_kw = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(kw_start.0)));
        let end_kw = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(kw_end.0)));
        let start = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(4)));
        let end = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Integer(raw.chars().count() as i64)));
        let pn2 = prim_parse_namestring(
            &mut proc,
            &globals,
            &[path, nil, nil, start_kw, start, end_kw, end],
        )
        .unwrap();
        let out2 = string_from_designator(&proc, &globals, pn2).unwrap();
        assert_eq!(out2, "file.lisp");
    }

    #[test]
    fn test_parse_namestring_junk_allowed() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let raw = "foo.lisp junk";
        let path = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String(raw.to_string())));
        let nil = proc.make_nil();
        let kw_junk = globals.symbols.write().unwrap().intern_keyword("JUNK-ALLOWED");
        let junk_kw = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(kw_junk.0)));
        let t_node = proc.make_t(&globals);

        let pn = prim_parse_namestring(&mut proc, &globals, &[path, nil, nil, junk_kw, t_node])
            .unwrap();
        let out = string_from_designator(&proc, &globals, pn).unwrap();
        assert_eq!(out, "foo.lisp");
        assert!(proc.values.len() >= 2);
        match proc.arena.inner.get_unchecked(proc.values[1]) {
            Node::Leaf(OpaqueValue::Integer(n)) => {
                assert_eq!(*n as usize, "foo.lisp".chars().count());
            }
            other => panic!("Expected integer index, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_namestring_logical() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let raw = "SYS:FOO;BAR.LISP";
        let path = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String(raw.to_string())));
        let pn = prim_parse_namestring(&mut proc, &globals, &[path]).unwrap();

        let host = prim_pathname_host(&mut proc, &globals, &[pn]).unwrap();
        assert_eq!(
            string_from_designator(&proc, &globals, host).unwrap(),
            "SYS"
        );

        let dir = prim_pathname_directory(&mut proc, &globals, &[pn]).unwrap();
        let items = list_to_vec_opt(&proc, dir).unwrap();
        assert!(items.len() >= 2);
        let first = items[0];
        let first_sym = node_to_symbol(&proc, first).unwrap();
        let sym_table = globals.symbols.read().unwrap();
        let first_name = sym_table.symbol_name(first_sym).unwrap();
        assert_eq!(first_name, "RELATIVE");
        let second = string_from_designator(&proc, &globals, items[1]).unwrap();
        assert_eq!(second, "FOO");

        let name = prim_pathname_name(&mut proc, &globals, &[pn]).unwrap();
        assert_eq!(
            string_from_designator(&proc, &globals, name).unwrap(),
            "BAR"
        );
        let ty = prim_pathname_type(&mut proc, &globals, &[pn]).unwrap();
        assert_eq!(
            string_from_designator(&proc, &globals, ty).unwrap(),
            "LISP"
        );
    }

    #[test]
    fn test_logical_pathname_and_translate_logical_pathname() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let logical = alloc_string(&mut proc, "ANSI-TESTS:AUX;foo.lsp".to_string());
        let lp = prim_logical_pathname(&mut proc, &globals, &[logical]).unwrap();
        let host = prim_pathname_host(&mut proc, &globals, &[lp]).unwrap();
        assert_eq!(
            string_from_designator(&proc, &globals, host).unwrap(),
            "ANSI-TESTS"
        );

        let translated = prim_translate_logical_pathname(&mut proc, &globals, &[lp]).unwrap();
        let out = string_from_designator(&proc, &globals, translated).unwrap();
        assert!(out.ends_with("tests/ansi-test/auxiliary/foo.lsp"));
    }

    #[test]
    fn test_logical_pathname_requires_host() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let not_logical = alloc_string(&mut proc, "foo.txt".to_string());
        let err = prim_logical_pathname(&mut proc, &globals, &[not_logical]).unwrap_err();
        match err {
            ControlSignal::Error(msg) => {
                assert!(msg.contains("LOGICAL-PATHNAME"));
            }
            other => panic!("Expected LOGICAL-PATHNAME error, got {:?}", other),
        }
    }

    #[test]
    fn test_translate_logical_pathname_physical_identity() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let physical = alloc_pathname(&mut proc, Pathname::from_namestring("/tmp/a.lsp"));
        let translated = prim_translate_logical_pathname(&mut proc, &globals, &[physical]).unwrap();
        assert_eq!(translated, physical);
    }

    #[test]
    fn test_load_logical_pathname_translations_minimal_hosts() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let host = alloc_string(&mut proc, "CLTESTROOT".to_string());
        let res = prim_load_logical_pathname_translations(&mut proc, &globals, &[host]).unwrap();
        assert!(matches!(proc.arena.inner.get_unchecked(res), Node::Leaf(OpaqueValue::Nil)));

        let unknown = alloc_string(&mut proc, "NO-SUCH-HOST".to_string());
        assert!(prim_load_logical_pathname_translations(&mut proc, &globals, &[unknown]).is_err());
    }

    #[test]
    fn test_logical_pathname_translations_set_get_and_translate() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let host = alloc_string(&mut proc, "MYHOST".to_string());
        let from = alloc_string(&mut proc, "**;*.*.*".to_string());
        let to = alloc_string(&mut proc, "tmp/myhost/**/*.*".to_string());
        let pair = proc.make_list(&[from, to]);
        let table = proc.make_list(&[pair]);

        prim_set_logical_pathname_translations(&mut proc, &globals, &[host, table]).unwrap();
        let got = prim_logical_pathname_translations(&mut proc, &globals, &[host]).unwrap();
        let got_rows = list_to_vec_opt(&proc, got).unwrap();
        assert_eq!(got_rows.len(), 1);

        let logical = alloc_string(&mut proc, "MYHOST:foo;bar.txt".to_string());
        let translated = prim_translate_logical_pathname(&mut proc, &globals, &[logical]).unwrap();
        let out = string_from_designator(&proc, &globals, translated)
            .unwrap()
            .replace('\\', "/");
        assert!(out.contains("tmp/myhost"));
        assert!(out.ends_with("foo/bar.txt"));
    }

    #[test]
    fn test_translate_logical_pathname_recursive_host_rules() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let host_a = alloc_string(&mut proc, "AHOST".to_string());
        let a_from = alloc_string(&mut proc, "**;*.*.*".to_string());
        let a_to = alloc_string(&mut proc, "BHOST:**;*.*.*".to_string());
        let a_pair = proc.make_list(&[a_from, a_to]);
        let a_table = proc.make_list(&[a_pair]);
        prim_set_logical_pathname_translations(&mut proc, &globals, &[host_a, a_table]).unwrap();

        let host_b = alloc_string(&mut proc, "BHOST".to_string());
        let b_from = alloc_string(&mut proc, "**;*.*.*".to_string());
        let b_to = alloc_string(&mut proc, "tmp/recursive/**/*.*".to_string());
        let b_pair = proc.make_list(&[b_from, b_to]);
        let b_table = proc.make_list(&[b_pair]);
        prim_set_logical_pathname_translations(&mut proc, &globals, &[host_b, b_table]).unwrap();

        let logical = alloc_string(&mut proc, "AHOST:foo;baz.txt".to_string());
        let translated = prim_translate_logical_pathname(&mut proc, &globals, &[logical]).unwrap();
        let out = string_from_designator(&proc, &globals, translated)
            .unwrap()
            .replace('\\', "/");
        assert!(out.contains("tmp/recursive"));
        assert!(out.ends_with("foo/baz.txt"));
    }

    #[test]
    fn test_translate_pathname_wildcards() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let source = alloc_string(&mut proc, "SYS:src;unit;a.lsp.newest".to_string());
        let from = alloc_string(&mut proc, "SYS:**;*.*.*".to_string());
        let to = alloc_string(&mut proc, "tmp/out/**/*.*".to_string());
        let translated = prim_translate_pathname(&mut proc, &globals, &[source, from, to]).unwrap();
        let out = string_from_designator(&proc, &globals, translated)
            .unwrap()
            .replace('\\', "/");
        assert!(out.contains("tmp/out"));
        assert!(out.ends_with("src/unit/a.lsp"));
    }

    #[test]
    fn test_typep_pathname_and_logical_pathname() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let pn = alloc_pathname(&mut proc, Pathname::from_namestring("/tmp/a.lsp"));
        let lpn = alloc_pathname(&mut proc, Pathname::from_namestring("CLTEST:FOO.BAR"));

        let pathname_sym = globals.symbols.write().unwrap().intern_in("PATHNAME", PackageId(1));
        let logical_pathname_sym = globals
            .symbols
            .write()
            .unwrap()
            .intern_in("LOGICAL-PATHNAME", PackageId(1));
        let pathname_type = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(pathname_sym.0)));
        let logical_type = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(logical_pathname_sym.0)));

        let pn_is_pathname = prim_typep(&mut proc, &globals, &[pn, pathname_type]).unwrap();
        assert!(matches!(
            proc.arena.inner.get_unchecked(pn_is_pathname),
            Node::Leaf(OpaqueValue::Symbol(id)) if *id == globals.t_sym.0
        ));

        let pn_is_logical = prim_typep(&mut proc, &globals, &[pn, logical_type]).unwrap();
        assert!(matches!(proc.arena.inner.get_unchecked(pn_is_logical), Node::Leaf(OpaqueValue::Nil)));

        let lpn_is_logical = prim_typep(&mut proc, &globals, &[lpn, logical_type]).unwrap();
        assert!(matches!(
            proc.arena.inner.get_unchecked(lpn_is_logical),
            Node::Leaf(OpaqueValue::Symbol(id)) if *id == globals.t_sym.0
        ));
    }

    #[test]
    fn test_wild_pathname_p_and_match() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let kw_name = globals.symbols.write().unwrap().intern_keyword("NAME");
        let kw_type = globals.symbols.write().unwrap().intern_keyword("TYPE");
        let kw_wild = globals.symbols.write().unwrap().intern_keyword("WILD");
        let name_kw_node = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(kw_name.0)));
        let type_kw_node = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(kw_type.0)));
        let wild_node = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(kw_wild.0)));

        let pn = prim_make_pathname(&mut proc, &globals, &[name_kw_node, wild_node]).unwrap();
        let res = prim_wild_pathname_p(&mut proc, &globals, &[pn]).unwrap();
        assert!(matches!(proc.arena.inner.get_unchecked(res), Node::Leaf(OpaqueValue::Symbol(id)) if *id == globals.t_sym.0));

        let res_name = prim_wild_pathname_p(&mut proc, &globals, &[pn, name_kw_node]).unwrap();
        assert!(matches!(proc.arena.inner.get_unchecked(res_name), Node::Leaf(OpaqueValue::Symbol(id)) if *id == globals.t_sym.0));

        let res_type = prim_wild_pathname_p(&mut proc, &globals, &[pn, type_kw_node]).unwrap();
        assert!(matches!(proc.arena.inner.get_unchecked(res_type), Node::Leaf(OpaqueValue::Nil)));

        let pattern_str = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String("CLTEST:*.LSP".to_string())));
        let actual_str = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String("CLTEST:FOO.LSP".to_string())));
        let pattern = prim_parse_namestring(&mut proc, &globals, &[pattern_str]).unwrap();
        let actual = prim_parse_namestring(&mut proc, &globals, &[actual_str]).unwrap();
        let matched = prim_pathname_match_p(&mut proc, &globals, &[actual, pattern]).unwrap();
        assert!(matches!(proc.arena.inner.get_unchecked(matched), Node::Leaf(OpaqueValue::Symbol(id)) if *id == globals.t_sym.0));

        let foo_node = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String("foo".to_string())));
        let pn2 = prim_make_pathname(&mut proc, &globals, &[name_kw_node, foo_node]).unwrap();
        let mismatch = prim_pathname_match_p(&mut proc, &globals, &[pn, pn2]).unwrap();
        assert!(matches!(proc.arena.inner.get_unchecked(mismatch), Node::Leaf(OpaqueValue::Nil)));
    }

    #[test]
    fn test_probe_file_and_directory_glob() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let base = std::env::temp_dir().join(format!("treecl-probe-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        std::fs::create_dir_all(&base).unwrap();

        let file_a = base.join("a.lsp");
        let file_b = base.join("b.lsp");
        let file_c = base.join("c.txt");
        std::fs::write(&file_a, "a").unwrap();
        std::fs::write(&file_b, "b").unwrap();
        std::fs::write(&file_c, "c").unwrap();

        let probe_node = alloc_string(&mut proc, file_a.to_string_lossy().to_string());
        let probe = prim_probe_file(&mut proc, &globals, &[probe_node]).unwrap();
        let probe_str = string_from_designator(&proc, &globals, probe).unwrap();
        assert!(probe_str.ends_with("a.lsp"));

        let pattern = base.join("*.lsp").to_string_lossy().to_string();
        let pattern_node = alloc_string(&mut proc, pattern);
        let list = prim_directory(&mut proc, &globals, &[pattern_node]).unwrap();
        let items = list_to_vec_opt(&proc, list).unwrap();
        let mut names: Vec<String> = items
            .iter()
            .filter_map(|node| string_from_designator(&proc, &globals, *node))
            .collect();
        names.sort();
        assert_eq!(names.len(), 2);
        assert!(names.iter().any(|n| n.ends_with("a.lsp")));
        assert!(names.iter().any(|n| n.ends_with("b.lsp")));

        let _ = std::fs::remove_file(&file_a);
        let _ = std::fs::remove_file(&file_b);
        let _ = std::fs::remove_file(&file_c);
        let _ = std::fs::remove_dir_all(&base);
    }

    #[test]
    fn test_ensure_directories_exist_creates() {
        let mut globals = crate::context::GlobalContext::new();
        let mut proc = crate::process::Process::new(
            crate::process::Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            crate::types::NodeId(0),
            &mut globals,
        );

        let base = std::env::temp_dir().join(format!("treecl-ensure-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        let target = base.join("nested/dir/file.txt");
        let node = alloc_string(&mut proc, target.to_string_lossy().to_string());
        let _ = prim_ensure_directories_exist(&mut proc, &globals, &[node]).unwrap();

        assert!(proc.values.len() >= 2);
        let created = proc.values[1];
        match proc.arena.inner.get_unchecked(created) {
            Node::Leaf(OpaqueValue::Symbol(id)) if *id == globals.t_sym.0 => {}
            Node::Leaf(OpaqueValue::Nil) => {}
            other => panic!("Unexpected created flag {:?}", other),
        }

        assert!(base.join("nested/dir").exists());
        let _ = std::fs::remove_dir_all(&base);
    }
}

// ============================================================================
// Concurrency Primitives
// ============================================================================

pub fn prim_spawn(
    _proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> Result<NodeId, ControlSignal> {
    // (spawn lambda-node)
    // Check arg count
    if args.len() != 1 {
        return Err(ControlSignal::Error(format!(
            "spawn: expected 1 argument, got {}",
            args.len()
        )));
    }

    let func = args[0];

    // Return SysCall ControlSignal
    // The evaluator will catch this and suspend the process
    Err(ControlSignal::SysCall(SysCall::Spawn(func)))
}

pub fn prim_send(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> Result<NodeId, ControlSignal> {
    // (send pid msg)
    if args.len() != 2 {
        return Err(ControlSignal::Error(format!(
            "send: expected 2 arguments, got {}",
            args.len()
        )));
    }

    // Extract Pid from args[0]
    let target_id = args[0];
    let target_node = proc.arena.inner.get_unchecked(target_id);

    let target_pid = if let Node::Leaf(OpaqueValue::Pid(p)) = target_node {
        *p
    } else {
        return Err(ControlSignal::Error("send: target must be a PID".into()));
    };

    let msg = args[1];

    Err(ControlSignal::SysCall(SysCall::Send {
        target: target_pid,
        message: msg,
    }))
}

pub fn prim_receive(
    _proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> Result<NodeId, ControlSignal> {
    // (receive [pattern]) -> msg
    let pattern = if let Some(&arg) = args.first() {
        Some(arg)
    } else {
        None
    };

    Err(ControlSignal::SysCall(SysCall::Receive { pattern }))
}

pub fn prim_sleep(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> Result<NodeId, ControlSignal> {
    // (sleep ms)
    if args.len() != 1 {
        return Err(ControlSignal::Error("sleep: expected 1 argument".into()));
    }

    let node_id = args[0];
    let node = proc.arena.inner.get_unchecked(node_id);

    let ms = if let Node::Leaf(OpaqueValue::Integer(m)) = node {
        *m as u64
    } else {
        return Err(ControlSignal::Error(
            "sleep: argument must be integer ms".into(),
        ));
    };

    Err(ControlSignal::SysCall(SysCall::Sleep(ms)))
}

pub fn prim_self(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    _args: &[NodeId],
) -> Result<NodeId, ControlSignal> {
    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Pid(proc.pid))))
}

fn prim_apropos(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return err_helper("APROPOS: missing argument");
    }

    // 1. Parse search string
    let search_str =
        if let Node::Leaf(OpaqueValue::String(s)) = proc.arena.inner.get_unchecked(args[0]) {
            s.clone()
        } else if let Some(sym_id) = node_to_symbol(proc, args[0]) {
            ctx.symbols
                .read()
                .unwrap()
                .symbol_name(sym_id)
                .unwrap_or("")
                .to_string()
        } else {
            return err_helper("APROPOS: argument must be string or symbol");
        };

    let search_upper = search_str.to_uppercase();

    // 2. Optional package filter? (Taking Simplified approach first: scan all)
    // Common Lisp: (apropos string &optional package)

    // 3. Scan symbols
    let symbols_guard = ctx.symbols.read().unwrap();
    let count = symbols_guard.symbol_count();

    // We can't hold lock while printing if printing involves evaluation or re-locking?
    // Printing to stream using `proc.streams` might be fine if it doesn't touch symbols?
    // `princ_to_string` DOES touch symbols.

    // So we collect matches first.
    let mut matches = Vec::new();

    // SymbolId is just an index (u32)
    for i in 0..count {
        let id = SymbolId(i as u32);
        if let Some(name) = symbols_guard.symbol_name(id) {
            if name.contains(&search_upper) {
                matches.push(id);
            }
        }
    }

    // Drop lock
    drop(symbols_guard);

    // 4. Print matches
    for sym_id in matches {
        let name = ctx
            .symbols
            .read()
            .unwrap()
            .symbol_name(sym_id)
            .unwrap_or("???")
            .to_string();
        let _ = proc
            .streams
            .write_string(crate::streams::StreamId(1), &format!("{}\n", name)); // 1 = Standard Output
    }

    Ok(proc.make_nil())
}

fn prim_rplaca(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return err_helper("RPLACA: too few arguments");
    }
    let cons = args[0];
    let new_car = args[1];

    // Read current value to check if it's a Fork and get cdr
    let current_node = proc.arena.inner.get_unchecked(cons).clone();

    if let Node::Fork(_, cdr) = current_node {
        let new_node = Node::Fork(new_car, cdr);
        proc.arena.inner.overwrite(cons, new_node);
        Ok(cons)
    } else {
        err_helper("RPLACA: argument is not a cons")
    }
}

fn prim_rplacd(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return err_helper("RPLACD: too few arguments");
    }
    let cons = args[0];
    let new_cdr = args[1];

    // Read current value to check if it's a Fork and get car
    let current_node = proc.arena.inner.get_unchecked(cons).clone();

    if let Node::Fork(car, _) = current_node {
        let new_node = Node::Fork(car, new_cdr);
        proc.arena.inner.overwrite(cons, new_node);
        Ok(cons)
    } else {
        err_helper("RPLACD: argument is not a cons")
    }
}

fn prim_set_symbol_function(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return err_helper("SET-SYMBOL-FUNCTION: too few arguments");
    }
    let sym_node = args[0];
    let func_node = args[1];

    if let Some(sym_id) = node_to_symbol(proc, sym_node) {
        proc.set_function(sym_id, func_node);
        Ok(func_node)
    } else if let Some(sym_id) = setf_function_name_from_node(proc, sym_node) {
        proc.set_setf_function(sym_id, func_node);
        Ok(func_node)
    } else {
        err_helper("SET-SYMBOL-FUNCTION: first argument must be a symbol")
    }
}

fn prim_tree_to_dot(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        let symbols = _ctx.symbols.read().unwrap();
        let s = crate::printer::tree_to_dot(&proc.arena.inner, &symbols, arg);
        Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::String(s))))
    } else {
        Err(ControlSignal::Error(
            "TREE-TO-DOT requires 1 argument".to_string(),
        ))
    }
}

fn prim_save_tree_pdf(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return Err(ControlSignal::Error(
            "SAVE-TREE-PDF requires 2 arguments: (node filename)".to_string(),
        ));
    }
    let node = args[0];
    let filename_node = args[1];

    let filename = match proc.arena.inner.get_unchecked(filename_node) {
        Node::Leaf(OpaqueValue::String(s)) => s.clone(),
        _ => {
            return Err(ControlSignal::Error(
                "SAVE-TREE-PDF: second argument must be a string".to_string(),
            ))
        }
    };

    let symbols = _ctx.symbols.read().unwrap();
    let dot_content = crate::printer::tree_to_dot(&proc.arena.inner, &symbols, node);

    use std::io::Write;
    let mut child = std::process::Command::new("dot")
        .arg("-Tpdf")
        .arg("-o")
        .arg(&filename)
        .stdin(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| ControlSignal::Error(format!("Failed to spawn dot: {}", e)))?;

    if let Some(mut stdin) = child.stdin.take() {
        stdin
            .write_all(dot_content.as_bytes())
            .map_err(|e| ControlSignal::Error(format!("Failed to write to dot stdin: {}", e)))?;
    }

    let status = child
        .wait()
        .map_err(|e| ControlSignal::Error(format!("Failed to wait for dot: {}", e)))?;

    if status.success() {
        // Return T (SymbolId 0 is usually NIL, we need a true value.
        // For now let's just return the filename string as a truthy value)
        Ok(proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String(filename))))
    } else {
        Err(ControlSignal::Error(format!(
            "dot exited with status: {}",
            status
        )))
    }
}

fn prim_tree_to_pdf(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return Err(ControlSignal::Error(
            "TREE-TO-PDF requires 2 arguments: (dot-filename pdf-filename)".to_string(),
        ));
    }
    let dot_filename_node = args[0];
    let pdf_filename_node = args[1];

    let dot_filename = match proc.arena.inner.get_unchecked(dot_filename_node) {
        Node::Leaf(OpaqueValue::String(s)) => s.clone(),
        _ => {
            return Err(ControlSignal::Error(
                "TREE-TO-PDF: first argument must be a string".to_string(),
            ))
        }
    };
    let pdf_filename = match proc.arena.inner.get_unchecked(pdf_filename_node) {
        Node::Leaf(OpaqueValue::String(s)) => s.clone(),
        _ => {
            return Err(ControlSignal::Error(
                "TREE-TO-PDF: second argument must be a string".to_string(),
            ))
        }
    };

    let dot_content = std::fs::read_to_string(&dot_filename).map_err(|e| {
        ControlSignal::Error(format!(
            "TREE-TO-PDF: failed to read {}: {}",
            dot_filename, e
        ))
    })?;

    use std::io::Write;
    let mut child = std::process::Command::new("dot")
        .arg("-Tpdf")
        .arg("-o")
        .arg(&pdf_filename)
        .stdin(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| ControlSignal::Error(format!("Failed to spawn dot: {}", e)))?;

    if let Some(mut stdin) = child.stdin.take() {
        stdin
            .write_all(dot_content.as_bytes())
            .map_err(|e| ControlSignal::Error(format!("Failed to write to dot stdin: {}", e)))?;
    }

    let status = child
        .wait()
        .map_err(|e| ControlSignal::Error(format!("Failed to wait for dot: {}", e)))?;

    if status.success() {
        Ok(proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String(pdf_filename))))
    } else {
        Err(ControlSignal::Error(format!(
            "dot exited with status: {}",
            status
        )))
    }
}
