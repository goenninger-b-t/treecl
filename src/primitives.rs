// TreeCL Primitives - Built-in Functions
//
// Implements core CL primitives in Rust.

use crate::arena::{Arena, Node};
use crate::context::PrimitiveFn;
use crate::eval::{ControlSignal, EvalResult, Interpreter};
use crate::process::Process;
use crate::symbol::{PackageId, SymbolId};
use crate::syscall::SysCall;
use crate::types::{NodeId, OpaqueValue};
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use std::collections::HashMap;

fn err_helper(msg: &str) -> EvalResult {
    Err(ControlSignal::Error(msg.to_string()))
}

fn node_to_symbol(proc: &Process, node: NodeId) -> Option<SymbolId> {
    if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(node) {
        Some(SymbolId(*id))
    } else {
        None
    }
}

/// Registry of primitive functions
pub struct Primitives {
    functions: HashMap<SymbolId, PrimitiveFn>,
}

impl Primitives {
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
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

    // Predicates
    globals.register_primitive("NULL", cl, prim_null);
    globals.register_primitive("ATOM", cl, prim_atom);
    globals.register_primitive("CONSP", cl, prim_consp);
    globals.register_primitive("LISTP", cl, prim_listp);
    globals.register_primitive("NUMBERP", cl, prim_numberp);
    globals.register_primitive("SYMBOLP", cl, prim_symbolp);
    globals.register_primitive("EQ", cl, prim_eq);
    globals.register_primitive("EQL", cl, prim_eql);
    globals.register_primitive("EQUAL", cl, prim_equal);
    globals.register_primitive("SYMBOL-VALUE", cl, prim_symbol_value);
    globals.register_primitive("GENSYM", cl, prim_gensym);
    globals.register_primitive("MAKE-SYMBOL", cl, prim_make_symbol);

    // Logic
    globals.register_primitive("NOT", cl, prim_not);

    // I/O
    globals.register_primitive("PRINT", cl, prim_print);
    globals.register_primitive("PRINC", cl, prim_princ);
    globals.register_primitive("TERPRI", cl, prim_terpri);
    globals.register_primitive("FORMAT", cl, prim_format);

    // CLOS
    globals.register_primitive("FIND-CLASS", cl, prim_find_class);
    globals.register_primitive("MAKE-INSTANCE", cl, prim_make_instance);
    globals.register_primitive("CLASS-OF", cl, prim_class_of);
    globals.register_primitive("SLOT-VALUE", cl, prim_slot_value);
    globals.register_primitive("SET-SLOT-VALUE", cl, prim_set_slot_value);
    globals.register_primitive("ENSURE-CLASS", cl, prim_ensure_class);
    globals.register_primitive("ENSURE-GENERIC-FUNCTION", cl, prim_ensure_generic_function);
    globals.register_primitive("ENSURE-METHOD", cl, prim_ensure_method);

    // Error handling
    globals.register_primitive("ERROR", cl, prim_error);

    // System
    globals.register_primitive("GC", cl, prim_gc);
    globals.register_primitive("ROOM", cl, prim_room);

    // Arrays
    globals.register_primitive("MAKE-ARRAY", cl, prim_make_array);
    globals.register_primitive("AREF", cl, prim_aref);
    globals.register_primitive("SET-AREF", cl, prim_set_aref);

    // Readtable
    globals.register_primitive("SET-MACRO-CHARACTER", cl, prim_set_macro_character);
    globals.register_primitive("GET-MACRO-CHARACTER", cl, prim_get_macro_character);
    globals.register_primitive("SET-SYNTAX-FROM-CHAR", cl, prim_set_syntax_from_char);

    // Tools
    globals.register_primitive("COMPILE", cl, prim_compile);
    globals.register_primitive("TREE-STRING", cl, prim_tree_string);
    globals.register_primitive("TREE-TO-DOT", cl, prim_tree_to_dot);
    globals.register_primitive("SAVE-TREE-PDF", cl, prim_save_tree_pdf);
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
    globals.register_primitive("CLOSE", cl, prim_close);
    globals.register_primitive("WRITE-STRING", cl, prim_write_string);
    globals.register_primitive("WRITE-CHAR", cl, prim_write_char);
    globals.register_primitive("FRESH-LINE", cl, prim_fresh_line);

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
    globals.register_primitive("PATHNAME-TYPE", cl, prim_pathname_type);
    globals.register_primitive("DIRECTORY", cl, prim_directory);
    globals.register_primitive("DELETE-FILE", cl, prim_delete_file);
    globals.register_primitive("TRUENAME", cl, prim_truename);
    globals.register_primitive("COMPILE-FILE-PATHNAME", cl, prim_compile_file_pathname);
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
                return Ok(proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Package(id.0))));
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
    ctx: &crate::context::GlobalContext,
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
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return err_helper("SET: too few arguments");
    }
    let sym_node = args[0];
    let val_node = args[1];

    if let Some(sym_id) = node_to_symbol(proc, sym_node) {
        proc.set_value(sym_id, val_node);
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
        let name = match proc.arena.inner.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::String(s)) => Some(s.clone()),
            Node::Leaf(OpaqueValue::Symbol(id)) => ctx
                .symbols
                .read()
                .unwrap()
                .symbol_name(SymbolId(*id))
                .map(|s| s.to_string()),
            Node::Leaf(OpaqueValue::Package(id)) => {
                return Ok(arg);
            }
            _ => None,
        };

        if let Some(n) = name {
            if let Some(pkg_id) = ctx.symbols.read().unwrap().find_package(&n) {
                return Ok(proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Package(pkg_id.0))));
            }
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
    if let Some(&arg) = args.first() {
        if let Some(sym_id) = node_to_symbol(proc, arg) {
            let name = _ctx
                .symbols
                .read()
                .unwrap()
                .symbol_name(sym_id)
                .unwrap_or("G")
                .to_string();
            let new_sym_id = _ctx.symbols.write().unwrap().make_symbol(&name);
            return Ok(proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(new_sym_id.0))));
        }
    }
    Ok(proc.make_nil())
}

fn prim_package_name(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        let pkg_id_opt = match proc.arena.inner.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::Package(id)) => Some(crate::symbol::PackageId(*id)),
            Node::Leaf(OpaqueValue::Symbol(id)) => {
                // Return home package name? Or if arg represents package name?
                // Standard says: package designator.
                // If symbol, use its name to find package? No, symbols name packages.
                // Actually PACKAGE-NAME takes a package designator.
                // A string or symbol designates the package named by it.
                let name = ctx
                    .symbols
                    .read()
                    .unwrap()
                    .symbol_name(SymbolId(*id))
                    .unwrap_or("")
                    .to_string();
                ctx.symbols.read().unwrap().find_package(&name)
            }
            Node::Leaf(OpaqueValue::String(s)) => ctx.symbols.read().unwrap().find_package(s),
            _ => None,
        };

        if let Some(pkg_id) = pkg_id_opt {
            if let Some(pkg) = ctx.symbols.read().unwrap().get_package(pkg_id) {
                return Ok(proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::String(pkg.name.clone()))));
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

                        // Return (values expansion t) -> For now just list (expansion t)
                        // Or just expansion if we don't have multiple values.
                        // The user asked for VALUES support. If not present, we return list for now?
                        // Or we assume single value return for MVP if acceptable.
                        // Standard macroexpand-1 returns 2 values.
                        // Let's return list (expansion t) to be safe for now or single value?
                        // Actually, if I can't return values, (macroexpand-1) is hard to use correctly.
                        // Let's return list (expansion t) and let Lisp wrapper handle it?
                        // Or just return expansion.
                        // Issue: If it's not a macro, we return the form.
                        // If it IS a macro, we return expansion.
                        // How to distinguish? "Expanded-p".
                        // Let's implement values support later?
                        // I'll return a LIST of two elements: (expansion expanded-p)
                        // This is non-standard but functional for my lisp code.
                        // Wait, I can fix `macroexpand` in lisp to handle this.

                        let t_val = interpreter.process.make_t(ctx);
                        let result_list = interpreter.process.make_list(&[expanded, t_val]);
                        return Ok(result_list);
                    }
                }
            }
        }
        // Not a macro form or not a cons
        let nil_val = proc.make_nil();
        let result_list = proc.make_list(&[form, nil_val]);
        Ok(result_list)
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
        // Extract filename string
        // Arg should be evaluated (string or symbol)
        let filename = match proc.arena.inner.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::String(s)) => s.clone(),
            // If it's a symbol, use name?
            Node::Leaf(OpaqueValue::Symbol(id)) => ctx
                .symbols
                .read()
                .unwrap()
                .symbol_name(SymbolId(*id))
                .unwrap_or("")
                .to_string(),
            _ => return err_helper("LOAD: filename must be string or symbol"),
        };

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
        let load_pn_sym = ctx
            .symbols
            .write()
            .unwrap()
            .intern_in("*LOAD-PATHNAME*", crate::symbol::PackageId(1));
        let load_tn_sym = ctx
            .symbols
            .write()
            .unwrap()
            .intern_in("*LOAD-TRUENAME*", crate::symbol::PackageId(1));

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

        let content = std::fs::read_to_string(path)
            .map_err(|e| ControlSignal::Error(format!("LOAD: io error: {}", e)))?;

        // Parse and Eval loop
        // We need to use Reader and Interpreter
        let mut interpreter = Interpreter::new(proc, ctx);
        let env = crate::eval::Environment::new();

        let mut exprs = Vec::new();
        // Scope for reader
        {
            let mut symbols_guard = ctx.symbols.write().unwrap();
            let mut reader = crate::reader::Reader::new(
                &content,
                &mut interpreter.process.arena.inner,
                &mut *symbols_guard,
                &interpreter.process.readtable,
                Some(&mut interpreter.process.arrays),
            );

            loop {
                match reader.read() {
                    Ok(expr) => exprs.push(expr),
                    Err(crate::reader::ReaderError::UnexpectedEof) => break,
                    Err(e) => return Err(ControlSignal::Error(format!("LOAD: read error: {}", e))),
                }
            }
        }

        for expr in exprs {
            interpreter.eval(expr, &env)?;
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
    // Basic parser for :name "foo" :type "lisp"
    let mut name = String::new();
    let mut type_ext = String::new();

    let mut i = 0;
    while i < args.len() {
        if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(args[i]) {
            if let Some(s) = ctx.symbols.read().unwrap().symbol_name(SymbolId(*id)) {
                if s == "NAME" && i + 1 < args.len() {
                    if let Node::Leaf(OpaqueValue::String(val)) =
                        proc.arena.inner.get_unchecked(args[i + 1])
                    {
                        name = val.clone();
                    }
                    i += 2;
                    continue;
                }
                if s == "TYPE" && i + 1 < args.len() {
                    if let Node::Leaf(OpaqueValue::String(val)) =
                        proc.arena.inner.get_unchecked(args[i + 1])
                    {
                        type_ext = val.clone();
                    }
                    i += 2;
                    continue;
                }
            }
        }
        i += 1;
    }

    let res = if !type_ext.is_empty() {
        format!("{}.{}", name, type_ext)
    } else {
        name
    };

    // Fallback to "dummy" if empty?
    let final_res = if res.is_empty() {
        "dummy".to_string()
    } else {
        res
    };

    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::String(final_res))))
}

fn prim_merge_pathnames(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    // Return first arg if present
    if let Some(&arg) = args.first() {
        Ok(arg)
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_pathname(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        Ok(arg)
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_namestring(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if let Some(&arg) = args.first() {
        Ok(arg)
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_pathname_type(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    _args: &[NodeId],
) -> EvalResult {
    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::String("lsp".to_string()))))
}

fn prim_directory(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    _args: &[NodeId],
) -> EvalResult {
    Ok(proc.make_nil())
}

fn prim_delete_file(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    _args: &[NodeId],
) -> EvalResult {
    Ok(proc.make_t(ctx))
}

fn prim_truename(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    _args: &[NodeId],
) -> EvalResult {
    Ok(proc.make_t(ctx))
}

fn prim_compile_file_pathname(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    _args: &[NodeId],
) -> EvalResult {
    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::String("out.fasl".to_string()))))
}

fn prim_string_equal(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    _args: &[NodeId],
) -> EvalResult {
    // Basic stub
    Ok(proc.make_t(ctx))
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
        match first {
            NumVal::Int(n) if n != 0 => Ok(proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Float(1.0 / n as f64)))),
            NumVal::Float(f) => Ok(proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Float(1.0 / f)))),
            _ => Ok(make_nil(proc)),
        }
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
            Node::Leaf(OpaqueValue::Integer(_)) | Node::Leaf(OpaqueValue::Float(_)) => {
                Ok(proc.make_t(ctx))
            }
            _ => Ok(proc.make_nil()),
        }
    } else {
        Ok(proc.make_nil())
    }
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
        (Node::Leaf(OpaqueValue::Nil), Node::Leaf(OpaqueValue::Nil)) => {
            return Ok(proc.make_t(ctx));
        }
        _ => {}
    }

    Ok(proc.make_nil())
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

fn ensure_gensym_counter(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
) -> i64 {
    let counter_sym = ctx
        .symbols
        .write()
        .unwrap()
        .intern_in("*GENSYM-COUNTER*", crate::symbol::PackageId(1));

    if let Some(val_node) = proc.get_value(counter_sym) {
        if let NumVal::Int(n) = extract_number(&proc.arena.inner, val_node) {
            return n;
        }
    }

    // Initialize to 1
    let one = proc.make_integer(1);
    proc.set_value(counter_sym, one);
    1
}

fn inc_gensym_counter(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    current: i64,
) {
    let counter_sym = ctx
        .symbols
        .write()
        .unwrap()
        .intern_in("*GENSYM-COUNTER*", crate::symbol::PackageId(1));
    let next = proc.make_integer(current + 1);
    proc.set_value(counter_sym, next);
}

fn prim_gensym(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    let mut prefix = "G".to_string();

    if let Some(&arg) = args.first() {
        match proc.arena.inner.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::String(s)) => {
                prefix = s.clone();
            }
            _ => {}
        }
    }

    let counter = ensure_gensym_counter(proc, ctx);
    inc_gensym_counter(proc, ctx, counter);

    let name = format!("{}{}", prefix, counter);
    let sym_id = ctx.symbols.write().unwrap().make_symbol(&name);

    Ok(proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0))))
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
            let nil_val = proc.make_nil();
            if let Some(inst_idx) = proc.mop.make_instance(id, nil_val) {
                let inst_node = proc
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Instance(inst_idx as u32)));
                eprintln!(
                    "DEBUG: prim_allocate_instance returning Instance idx={}",
                    inst_idx
                );
                return Ok(inst_node);
            }
        }
    }
    Err(crate::eval::ControlSignal::Error(
        "allocate-instance: invalid class".into(),
    ))
}

fn prim_shared_initialize(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    // (shared-initialize instance slot-names &rest initargs)
    eprintln!(
        "DEBUG: prim_shared_initialize called with {} args",
        args.len()
    );
    if args.len() < 2 {
        return Err(crate::eval::ControlSignal::Error(
            "shared-initialize: too few args".into(),
        ));
    }
    let instance = args[0];
    // let slot_names = args[1]; // Ignored for now (assume T or nil logic implicit)
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

    // Calculate slots info
    // We need to do this properly.
    // Initargs is a list of keys and values.

    // Parse initargs to map? No, repeated keys allowed?
    // "The first value ... is used."
    // So scan.
    let initargs_map = parse_keywords_list(proc, initargs);

    // DEBUG: Print initargs map contents
    eprintln!("DEBUG: prim_shared_initialize initargs map keys:");
    for (k, v) in &initargs_map {
        let name = ctx
            .symbols
            .read()
            .unwrap()
            .symbol_name(*k)
            .unwrap_or("?")
            .to_string();
        eprintln!("  KEY: {:?} ({}) VAL: {:?}", k, name, v);
    }

    let class_id = proc.mop.get_instance(inst_idx).map(|i| i.class).ok_or(
        crate::eval::ControlSignal::Error("Instance lost class?".into()),
    )?;

    // Get slots
    let slots_info: Vec<(usize, Option<crate::symbol::SymbolId>, Option<NodeId>)> =
        if let Some(slots) = proc.mop.get_class_slots(class_id.0) {
            slots
                .iter()
                .map(|s| (s.index, s.initarg, s.initform))
                .collect()
        } else {
            Vec::new()
        };

    for (idx, initarg, initform) in slots_info {
        let mut initialized = false;
        if let Some(key) = initarg {
            if let Some(&val) = initargs_map.get(&key) {
                eprintln!(
                    "DEBUG: setting slot index {} with VAL {:?} (Matched Key {:?})",
                    idx, val, key
                );
                proc.mop.set_slot_value(inst_idx, idx, val);
                initialized = true;
            } else {
                eprintln!(
                    "DEBUG: initarg Key {:?} not found in initargs map for slot index {}",
                    key, idx
                );
            }
        } else {
            eprintln!("DEBUG: slot index {} has no initarg", idx);
        }

        if !initialized {
            if let Some(form) = initform {
                // NOTE: We treat initform as a literal node for now.
                proc.mop.set_slot_value(inst_idx, idx, form);
                eprintln!(
                    "DEBUG: setting slot index {} from initform {:?}",
                    idx, form
                );
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
    use crate::clos::ClassId;
    if let Some(&arg) = args.first() {
        let class_id = match proc.arena.inner.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::Integer(_)) => proc.mop.integer_class,
            Node::Leaf(OpaqueValue::Instance(idx)) => proc
                .mop
                .get_instance(*idx as usize)
                .map(|i| i.class)
                .unwrap_or(proc.mop.t_class),
            Node::Leaf(OpaqueValue::Class(_)) => proc.mop.standard_class,
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
    eprintln!("DEBUG: prim_slot_value called with {} args", args.len());
    if args.len() > 0 {
        let node = proc.arena.inner.get_unchecked(args[0]);
        eprintln!("DEBUG: prim_slot_value args[0] node={:?}", node);
        match node {
            Node::Fork(head, tail) => {
                eprintln!(
                    "DEBUG: prim_slot_value args[0] is List/Form. Head: {:?} Tail: {:?}",
                    proc.arena.inner.get_unchecked(*head),
                    proc.arena.inner.get_unchecked(*tail)
                );
                if let Node::Leaf(OpaqueValue::Symbol(id)) = proc.arena.inner.get_unchecked(*head) {
                    let sym_name = ctx
                        .symbols
                        .read()
                        .unwrap()
                        .symbol_name(crate::symbol::SymbolId(*id))
                        .unwrap_or("?")
                        .to_string();
                    eprintln!("DEBUG: Head is Symbol: {}", sym_name);
                }
            }
            _ => {}
        }
    }
    let mut inst_idx = None;
    let mut slot_sym = None;

    if args.len() >= 2 {
        let instance = args[0];
        let slot_name = args[1];

        // Extract instance index
        inst_idx = if let Node::Leaf(OpaqueValue::Instance(idx)) =
            proc.arena.inner.get_unchecked(instance)
        {
            Some(*idx as usize)
        } else {
            None
        };

        // Extract slot name symbol
        slot_sym = node_to_symbol(proc, slot_name);

        if let (Some(idx), Some(sym)) = (inst_idx, slot_sym) {
            // Find slot index in class
            if let Some(inst) = proc.mop.get_instance(idx) {
                if let Some(class) = proc.mop.get_class(inst.class) {
                    // Find slot definition
                    if let Some(pos) = class.slots.iter().position(|s| s.name == sym) {
                        return Ok(proc.mop.slot_value(idx, pos).unwrap_or(proc.make_nil()));
                    }
                }
            }
        }
    }

    // Report debug info about failure
    if let Some(idx) = inst_idx {
        if let Some(inst) = proc.mop.get_instance(idx) {
            if let Some(class) = proc.mop.get_class(inst.class) {
                let s_name = slot_sym
                    .and_then(|s| {
                        ctx.symbols
                            .read()
                            .unwrap()
                            .symbol_name(s)
                            .map(|x| x.to_string())
                    })
                    .unwrap_or("?".to_string());
                let c_name = ctx
                    .symbols
                    .read()
                    .unwrap()
                    .symbol_name(class.name)
                    .unwrap_or("?")
                    .to_string();

                eprintln!("DEBUG: prim_slot_value failed. Slot '{:?}' not found in class '{}'. Available slots:", s_name, c_name);
                for s in &class.slots {
                    let sn = ctx
                        .symbols
                        .read()
                        .unwrap()
                        .symbol_name(s.name)
                        .unwrap_or("?")
                        .to_string();
                    eprintln!("  - {}", sn);
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
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    eprintln!("DEBUG: prim_set_slot_value args len={}", args.len());
    if args.len() >= 3 {
        let instance = args[0];
        let slot_name = args[1];
        let new_val = args[2];

        // Extract instance index
        let inst_idx = if let Node::Leaf(OpaqueValue::Instance(idx)) =
            proc.arena.inner.get_unchecked(instance)
        {
            Some(*idx as usize)
        } else {
            eprintln!(
                "DEBUG: arg[0] is not an instance: {:?}",
                proc.arena.inner.get_unchecked(instance)
            );
            None
        };

        // Extract slot name symbol
        let slot_sym = node_to_symbol(proc, slot_name);
        if slot_sym.is_none() {
            eprintln!("DEBUG: arg[1] is not a symbol");
        }

        if let (Some(idx), Some(sym)) = (inst_idx, slot_sym) {
            // Find slot index in class
            if let Some(inst) = proc.mop.get_instance(idx) {
                if let Some(class) = proc.mop.get_class(inst.class) {
                    // Find slot definition
                    if let Some(pos) = class.slots.iter().position(|s| s.name == sym) {
                        proc.mop.set_slot_value(idx, pos, new_val);
                        return Ok(new_val);
                    } else {
                        eprintln!("DEBUG: Slot {:?} not found in class {:?}", sym, class.name);
                        eprintln!(
                            "DEBUG: Available slots: {:?}",
                            class.slots.iter().map(|s| s.name).collect::<Vec<_>>()
                        );
                    }
                } else {
                    eprintln!("DEBUG: Class not found for instance");
                }
            } else {
                eprintln!("DEBUG: Instance idx {} not found", idx);
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

fn parse_keywords_list(proc: &Process, args: &[NodeId]) -> HashMap<SymbolId, NodeId> {
    let mut keywords = HashMap::new();
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
    let k_initarg = keyword_pkg.and_then(|p| p.find_external("INITARG"));
    let k_reader = keyword_pkg.and_then(|p| p.find_external("READER"));
    let k_writer = keyword_pkg.and_then(|p| p.find_external("WRITER"));
    let k_accessor = keyword_pkg.and_then(|p| p.find_external("ACCESSOR"));
    drop(syms);

    let initform = k_initform.and_then(|k| props.get(&k)).copied();
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

    Ok(SlotDefinition {
        name,
        initform,
        initarg,
        readers,
        writers,
        index,
    })
}

fn prim_ensure_class(
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
    drop(syms);

    let mut supers = Vec::new();
    if let Some(k) = kw_supers {
        if let Some(&supers_node) = kwargs.get(&k) {
            for head in list_to_vec(proc, supers_node) {
                let class_id = match proc.arena.inner.get_unchecked(head) {
                    Node::Leaf(OpaqueValue::Class(id)) => Some(ClassId(*id)),
                    Node::Leaf(OpaqueValue::Symbol(id)) => proc.mop.find_class(SymbolId(*id)),
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

    let class_id = proc.mop.define_class(name, supers, slots);
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
    let name = node_to_symbol(proc, name_node).ok_or(crate::eval::ControlSignal::Error(
        "Generic name != symbol".to_string(),
    ))?;

    let kwargs = parse_keywords_list(proc, &args[1..]);

    let syms = ctx.symbols.read().unwrap();
    let keyword_pkg = syms.get_package(crate::symbol::PackageId(0));
    let kw_lambda_list = keyword_pkg.and_then(|p| p.find_external("LAMBDA-LIST"));
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

    let gid = proc.mop.define_generic(name, lambda_list);
    let gf_node = proc
        .arena
        .inner
        .alloc(Node::Leaf(OpaqueValue::Generic(gid.0)));

    // Bind to function name in process
    proc.set_function(name, gf_node);

    Ok(gf_node)
}

fn prim_sys_allocate_instance(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    eprintln!("DEBUG: prim_sys_allocate_instance called. Args: {:?}", args);
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

    let nil = proc.make_nil();
    if let Some(inst_idx) = proc.mop.make_instance(class_id, nil) {
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
    use crate::clos::{ClassId, GenericId};

    if args.is_empty() {
        return Err(crate::eval::ControlSignal::Error(
            "ENSURE-METHOD requires GF".to_string(),
        ));
    }

    let gf_node = args[0];
    let gf_id = match proc.arena.inner.get_unchecked(gf_node) {
        Node::Leaf(OpaqueValue::Generic(id)) => GenericId(*id),
        Node::Leaf(OpaqueValue::Symbol(id)) => {
            let name = SymbolId(*id);
            if let Some(gid) = proc.mop.find_generic(name) {
                gid
            } else {
                proc.mop.define_generic(name, Vec::new())
            }
        }
        _ => {
            return Err(crate::eval::ControlSignal::Error(
                "Invalid GF spec".to_string(),
            ))
        }
    };

    let kwargs = parse_keywords_list(proc, &args[1..]);

    let syms = ctx.symbols.read().unwrap();
    let keyword_pkg = syms.get_package(crate::symbol::PackageId(0));
    let kw_specializers = keyword_pkg.and_then(|p| p.find_external("SPECIALIZERS"));
    let kw_qualifiers = keyword_pkg.and_then(|p| p.find_external("QUALIFIERS"));
    let kw_body = keyword_pkg.and_then(|p| p.find_external("BODY"));
    drop(syms);

    let mut specializers = Vec::new();
    if let Some(k) = kw_specializers {
        if let Some(&specs_node) = kwargs.get(&k) {
            for head in list_to_vec(proc, specs_node) {
                let class_id = match proc.arena.inner.get_unchecked(head) {
                    Node::Leaf(OpaqueValue::Class(id)) => Some(ClassId(*id)),
                    Node::Leaf(OpaqueValue::Symbol(id)) => proc.mop.find_class(SymbolId(*id)),
                    _ => None,
                };

                if let Some(cid) = class_id {
                    specializers.push(cid);
                } else {
                    specializers.push(proc.mop.t_class); // Default to T
                }
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

    let mid = proc.mop.add_method(gf_id, specializers, qualifiers, body);

    // Return method object? For now, NIL.
    Ok(proc.make_nil())
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
    // (make-array size [initial-element])
    if args.is_empty() {
        return Err(crate::eval::ControlSignal::Error(
            "make-array requires at least 1 argument".to_string(),
        ));
    }

    let size_val = extract_number(&proc.arena.inner, args[0]);
    let size = match size_val {
        NumVal::Int(n) if n >= 0 => n as usize,
        _ => {
            return Err(crate::eval::ControlSignal::Error(
                "Invalid array size".to_string(),
            ))
        }
    };

    let initial = if args.len() > 1 {
        args[1]
    } else {
        proc.make_nil()
    };

    let vec_id = proc.arrays.alloc(size, initial);

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
    // (aref array index)
    if args.len() != 2 {
        return Err(crate::eval::ControlSignal::Error(
            "aref requires 2 arguments".to_string(),
        ));
    }

    // Check if array
    if let Node::Leaf(OpaqueValue::VectorHandle(idx)) = proc.arena.inner.get_unchecked(args[0]) {
        let vec_id = crate::arrays::VectorId(*idx);

        // Parse index
        let idx_val = extract_number(&proc.arena.inner, args[1]);
        if let NumVal::Int(i) = idx_val {
            if i >= 0 {
                if let Some(val) = proc.arrays.aref(vec_id, i as usize) {
                    return Ok(val);
                }
                return Err(crate::eval::ControlSignal::Error(format!(
                    "Array index out of bounds: {}",
                    i
                )));
            }
        }
        return Err(crate::eval::ControlSignal::Error(
            "Invalid array index".to_string(),
        ));
    }

    Err(crate::eval::ControlSignal::Error(
        "Not an array".to_string(),
    ))
}

fn prim_set_aref(
    proc: &mut crate::process::Process,
    _ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    // (set-aref array index value)
    if args.len() != 3 {
        return Err(crate::eval::ControlSignal::Error(
            "set-aref requires 3 arguments".to_string(),
        ));
    }

    if let Node::Leaf(OpaqueValue::VectorHandle(idx)) = proc.arena.inner.get_unchecked(args[0]) {
        let vec_id = crate::arrays::VectorId(*idx);

        let idx_val = extract_number(&proc.arena.inner, args[1]);
        if let NumVal::Int(i) = idx_val {
            if i >= 0 {
                let val = args[2];
                if proc.arrays.set_aref(vec_id, i as usize, val) {
                    return Ok(val);
                }
                return Err(crate::eval::ControlSignal::Error(format!(
                    "Array index out of bounds: {}",
                    i
                )));
            }
        }
        return Err(crate::eval::ControlSignal::Error(
            "Invalid array index".to_string(),
        ));
    }

    Err(crate::eval::ControlSignal::Error(
        "Not an array".to_string(),
    ))
}

fn prim_set_macro_character(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    // (set-macro-character char function [non-terminating-p])
    // function: currently only accepts a SYMBOL naming a built-in macro.
    if args.len() < 2 || args.len() > 3 {
        return Err(crate::eval::ControlSignal::Error(
            "set-macro-character requires 2 or 3 arguments".to_string(),
        ));
    }

    // 1. Character
    let char_val = extract_number(&proc.arena.inner, args[0]);
    let ch = match char_val {
        NumVal::Int(n) => std::char::from_u32(n as u32).ok_or(
            crate::eval::ControlSignal::Error("Invalid character code".to_string()),
        )?,
        _ => {
            return Err(crate::eval::ControlSignal::Error(
                "Character argument must be an integer (code point)".to_string(),
            ))
        }
    };

    // 2. Function (Symbol)
    // We expect a symbol.
    let func_name = if let Some(sym_id) = node_to_symbol(proc, args[1]) {
        ctx.symbols
            .read()
            .unwrap()
            .get_symbol(sym_id)
            .unwrap()
            .name
            .clone()
    } else {
        return Err(crate::eval::ControlSignal::Error(
            "Function argument must be a symbol naming a built-in macro".to_string(),
        ));
    };

    // Look up built-in
    let macro_fn = get_reader_macro(&func_name).ok_or_else(|| {
        crate::eval::ControlSignal::Error(format!("Unknown built-in reader macro: {}", func_name))
    })?;

    // 3. Non-terminating?
    let non_terminating = if args.len() > 2 {
        args[2] != proc.make_nil()
    } else {
        false
    };

    // Update readtable
    use crate::readtable::SyntaxType;
    let syntax = if non_terminating {
        SyntaxType::NonTerminatingMacro
    } else {
        SyntaxType::TerminatingMacro
    };

    proc.readtable.set_syntax_type(ch, syntax);
    proc.readtable.set_macro_character(ch, Some(macro_fn));

    Ok(proc.make_t(ctx))
}

fn prim_get_macro_character(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.is_empty() {
        return err_helper("get-macro-character: too few arguments");
    }

    let ch_code = if let Node::Leaf(OpaqueValue::Integer(n)) =
        proc.arena.inner.get_unchecked(args[0]).clone()
    {
        n as u32
    } else {
        return err_helper("get-macro-character: char code must be an integer");
    };

    let ch = std::char::from_u32(ch_code)
        .ok_or_else(|| ControlSignal::Error(format!("Invalid char code: {}", ch_code)))?;

    if let Some(_func) = proc.readtable.get_macro_character(ch) {
        // We can't return the Rust function pointer directly as a Lisp object yet
        // For Phase 10, let's just return T if a macro is set, or NIL.
        // In next phases, we would return a special OpaqueValue for read-macros.
        Ok(proc.make_t(ctx))
    } else {
        Ok(proc.make_nil())
    }
}

fn prim_set_syntax_from_char(
    proc: &mut crate::process::Process,
    ctx: &crate::context::GlobalContext,
    args: &[NodeId],
) -> EvalResult {
    if args.len() < 2 {
        return err_helper("set-syntax-from-char: too few arguments");
    }

    let to_code = if let Node::Leaf(OpaqueValue::Integer(n)) =
        proc.arena.inner.get_unchecked(args[0]).clone()
    {
        n as u32
    } else {
        return err_helper("set-syntax-from-char: to-char code must be an integer");
    };

    let from_code = if let Node::Leaf(OpaqueValue::Integer(n)) =
        proc.arena.inner.get_unchecked(args[1]).clone()
    {
        n as u32
    } else {
        return err_helper("set-syntax-from-char: from-char code must be an integer");
    };

    let to_ch = std::char::from_u32(to_code)
        .ok_or_else(|| ControlSignal::Error(format!("Invalid to-char code: {}", to_code)))?;
    let from_ch = std::char::from_u32(from_code)
        .ok_or_else(|| ControlSignal::Error(format!("Invalid from-char code: {}", from_code)))?;

    let syntax = proc.readtable.get_syntax_type(from_ch);
    let macro_fn = proc.readtable.get_macro_character(from_ch);

    proc.readtable.set_syntax_type(to_ch, syntax);
    if let Some(f) = macro_fn {
        proc.readtable.set_macro_character(to_ch, Some(f));
    } else {
        proc.readtable.set_macro_character(to_ch, None);
    }

    Ok(proc.make_t(ctx))
}

fn get_reader_macro(name: &str) -> Option<crate::readtable::ReaderMacroFn> {
    match name {
        "READ-LEFT-BRACKET" => Some(wrap_read_left_bracket),
        "READ-RIGHT-BRACKET" => Some(wrap_read_right_bracket),
        _ => None,
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
    Float(f64),
    None,
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
            (NumVal::Int(a), NumVal::Int(b)) if b != 0 => {
                // Use float division to match CL semantics
                NumVal::Float(a as f64 / b as f64)
            }
            (NumVal::Big(a), NumVal::Big(b)) if b != BigInt::from(0) => NumVal::Float(
                a.to_f64().unwrap_or(f64::INFINITY) / b.to_f64().unwrap_or(f64::INFINITY),
            ),
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
            NumVal::Float(f) => arena.alloc(Node::Leaf(OpaqueValue::Float(f))),
            NumVal::None => arena.alloc(Node::Leaf(OpaqueValue::Nil)),
        }
    }
}

fn extract_number(arena: &Arena, node: NodeId) -> NumVal {
    match arena.get_unchecked(node) {
        Node::Leaf(OpaqueValue::Integer(n)) => NumVal::Int(*n),
        Node::Leaf(OpaqueValue::BigInt(n)) => NumVal::Big(n.clone()),
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

    let mut interp = Interpreter::new(proc, ctx);

    let func = args[0];
    let func_args = if args.len() > 1 {
        interp.list(&args[1..])
    } else {
        interp.process.make_nil()
    };

    let env = crate::eval::Environment::new();
    interp.apply_function(func, func_args, &env)
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

    let mut interp = Interpreter::new(proc, ctx);

    let func = args[0];
    let last_arg = args[args.len() - 1]; // The list argument

    // Construct argument list.
    let mut final_args = last_arg;
    for &arg in args[1..args.len() - 1].iter().rev() {
        final_args = interp.cons(arg, final_args);
    }

    let env = crate::eval::Environment::new();
    interp.apply_values(func, final_args, &env)
}

#[cfg(test)]
mod tests {
    use super::*;

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
            Node::Leaf(OpaqueValue::Float(f)) if (*f - 5.0).abs() < 0.001 => {}
            _ => panic!("Expected 5.0"),
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
            Node::Leaf(OpaqueValue::Float(f)) if (*f - 0.2631578947368421).abs() < 0.0001 => {}
            other => panic!("Expected ~0.263, got {:?}", other),
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
