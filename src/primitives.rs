// TreeCL Primitives - Built-in Functions
//
// Implements core CL primitives in Rust.

use crate::arena::{Arena, Node};
use crate::types::{NodeId, OpaqueValue};
use crate::symbol::{SymbolId, PackageId};
use crate::eval::{Interpreter, EvalResult, PrimitiveFn, ControlSignal};
use std::collections::HashMap;
use num_bigint::BigInt;
use num_traits::ToPrimitive;

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
pub fn register_primitives(interp: &mut Interpreter) {
    let cl = PackageId(1);
    
    // Arithmetic
    interp.register_primitive("+", cl, prim_add);
    interp.register_primitive("-", cl, prim_sub);
    interp.register_primitive("*", cl, prim_mul);
    interp.register_primitive("/", cl, prim_div);
    interp.register_primitive("1+", cl, prim_1plus);
    interp.register_primitive("1-", cl, prim_1minus);
    interp.register_primitive("MOD", cl, prim_mod);
    
    // Comparison
    interp.register_primitive("=", cl, prim_num_eq);
    interp.register_primitive("<", cl, prim_lt);
    interp.register_primitive(">", cl, prim_gt);
    interp.register_primitive("<=", cl, prim_le);
    interp.register_primitive(">=", cl, prim_ge);
    
    // List operations
    interp.register_primitive("CONS", cl, prim_cons);
    interp.register_primitive("CAR", cl, prim_car);
    interp.register_primitive("CDR", cl, prim_cdr);
    interp.register_primitive("LIST", cl, prim_list);
    interp.register_primitive("LENGTH", cl, prim_length);
    interp.register_primitive("APPEND", cl, prim_append);
    interp.register_primitive("REVERSE", cl, prim_reverse);
    interp.register_primitive("NTH", cl, prim_nth);
    
    // Predicates
    interp.register_primitive("NULL", cl, prim_null);
    interp.register_primitive("ATOM", cl, prim_atom);
    interp.register_primitive("CONSP", cl, prim_consp);
    interp.register_primitive("LISTP", cl, prim_listp);
    interp.register_primitive("NUMBERP", cl, prim_numberp);
    interp.register_primitive("SYMBOLP", cl, prim_symbolp);
    interp.register_primitive("EQ", cl, prim_eq);
    interp.register_primitive("EQL", cl, prim_eql);
    interp.register_primitive("EQUAL", cl, prim_equal);
    
    // Logic
    interp.register_primitive("NOT", cl, prim_not);
    
    // I/O
    interp.register_primitive("PRINT", cl, prim_print);
    interp.register_primitive("PRINC", cl, prim_princ);
    interp.register_primitive("TERPRI", cl, prim_terpri);
    interp.register_primitive("FORMAT", cl, prim_format);
    
    // CLOS
    interp.register_primitive("FIND-CLASS", cl, prim_find_class);
    interp.register_primitive("MAKE-INSTANCE", cl, prim_make_instance);
    interp.register_primitive("CLASS-OF", cl, prim_class_of);
    interp.register_primitive("SLOT-VALUE", cl, prim_slot_value);
    interp.register_primitive("SET-SLOT-VALUE", cl, prim_set_slot_value);
    
    // Error handling
    interp.register_primitive("ERROR", cl, prim_error);

    // System
    interp.register_primitive("GC", cl, prim_gc);
    interp.register_primitive("ROOM", cl, prim_room);
    
    // Arrays
    interp.register_primitive("MAKE-ARRAY", cl, prim_make_array);
    interp.register_primitive("AREF", cl, prim_aref);
    interp.register_primitive("SET-AREF", cl, prim_set_aref);
    
    // Readtable
    interp.register_primitive("SET-MACRO-CHARACTER", cl, prim_set_macro_character);
    interp.register_primitive("GET-MACRO-CHARACTER", cl, prim_get_macro_character);
    interp.register_primitive("SET-SYNTAX-FROM-CHAR", cl, prim_set_syntax_from_char);
    
    // Tools
    interp.register_primitive("COMPILE", cl, prim_compile);
    interp.register_primitive("TREE-STRING", cl, prim_tree_string);
    interp.register_primitive("FUNCALL", cl, prim_funcall);
    interp.register_primitive("APPLY", cl, prim_apply);
    
    // Streams
    interp.register_primitive("MAKE-STRING-OUTPUT-STREAM", cl, prim_make_string_output_stream);
    interp.register_primitive("GET-OUTPUT-STREAM-STRING", cl, prim_get_output_stream_string);
    interp.register_primitive("MAKE-STRING-INPUT-STREAM", cl, prim_make_string_input_stream);
    interp.register_primitive("CLOSE", cl, prim_close);
    interp.register_primitive("WRITE-STRING", cl, prim_write_string);
    interp.register_primitive("WRITE-CHAR", cl, prim_write_char);
    interp.register_primitive("FRESH-LINE", cl, prim_fresh_line);
}

// ============================================================================
// Arithmetic Primitives
// ============================================================================

fn prim_add(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    let mut sum = NumVal::Int(0);
    
    for &arg in args {
        let val = extract_number(&interp.arena, arg);
        sum = sum.add(val);
    }
    
    Ok(sum.to_node(&mut interp.arena))
}

fn prim_sub(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.is_empty() {
        return Ok(interp.make_integer(0));
    }
    
    let first = extract_number(&interp.arena, args[0]);
    
    if args.len() == 1 {
        // Unary minus
        match first {
            NumVal::Int(n) => {
                match n.checked_neg() {
                    Some(res) => Ok(interp.arena.alloc(Node::Leaf(OpaqueValue::Integer(res)))),
                    None => Ok(interp.arena.alloc(Node::Leaf(OpaqueValue::Float(-(n as f64))))),
                }
            }
            NumVal::Big(n) => Ok(interp.arena.alloc(Node::Leaf(OpaqueValue::BigInt(-n)))),
            NumVal::Float(f) => Ok(interp.arena.alloc(Node::Leaf(OpaqueValue::Float(-f)))),
            NumVal::None => Ok(interp.nil_node),
        }
    } else {
        let mut result = first;
        for &arg in &args[1..] {
            let val = extract_number(&interp.arena, arg);
            result = result.sub(val);
        }
        Ok(result.to_node(&mut interp.arena))
    }
}

fn prim_mul(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    let mut product = NumVal::Int(1);
    
    for &arg in args {
        let val = extract_number(&interp.arena, arg);
        product = product.mul(val);
    }
    
    Ok(product.to_node(&mut interp.arena))
}

fn prim_div(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.is_empty() {
        return Ok(interp.make_integer(1));
    }
    
    let first = extract_number(&interp.arena, args[0]);
    
    if args.len() == 1 {
        // Reciprocal
        match first {
            NumVal::Int(n) if n != 0 => Ok(interp.arena.alloc(Node::Leaf(OpaqueValue::Float(1.0 / n as f64)))),
            NumVal::Float(f) => Ok(interp.arena.alloc(Node::Leaf(OpaqueValue::Float(1.0 / f)))),
            _ => Ok(interp.nil_node),
        }
    } else {
        let mut result = first;
        for &arg in &args[1..] {
            let val = extract_number(&interp.arena, arg);
            result = result.div(val);
        }
        Ok(result.to_node(&mut interp.arena))
    }
}

fn prim_1plus(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        let val = extract_number(&interp.arena, arg);
        Ok(val.add(NumVal::Int(1)).to_node(&mut interp.arena))
    } else {
        Ok(interp.nil_node)
    }
}

fn prim_1minus(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        let val = extract_number(&interp.arena, arg);
        Ok(val.sub(NumVal::Int(1)).to_node(&mut interp.arena))
    } else {
        Ok(interp.nil_node)
    }
}

fn prim_mod(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.len() >= 2 {
        let a_val = extract_number(&interp.arena, args[0]);
        let b_val = extract_number(&interp.arena, args[1]);
        
        match (a_val, b_val) {
            (NumVal::Int(a), NumVal::Int(b)) if b != 0 => {
                return Ok(interp.make_integer(a % b));
            }
            (NumVal::Big(a), NumVal::Big(b)) if b != BigInt::from(0) => {
                return Ok(NumVal::Big(a % b).to_node(&mut interp.arena));
            }
            (NumVal::Big(a), NumVal::Int(b)) if b != 0 => {
                return Ok(NumVal::Big(a % BigInt::from(b)).to_node(&mut interp.arena));
            }
            (NumVal::Int(a), NumVal::Big(b)) if b != BigInt::from(0) => {
                return Ok(NumVal::Big(BigInt::from(a) % b).to_node(&mut interp.arena));
            }
            _ => {}
        }
    }
    Ok(interp.nil_node)
}

// ============================================================================
// Comparison Primitives
// ============================================================================

fn prim_num_eq(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.len() < 2 {
        return Ok(interp.t_node);
    }
    
    let first = extract_number(&interp.arena, args[0]);
    for &arg in &args[1..] {
        let val = extract_number(&interp.arena, arg);
        if !first.eq(&val) {
            return Ok(interp.nil_node);
        }
    }
    Ok(interp.t_node)
}

fn prim_lt(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    compare_chain(interp, args, |a, b| a < b)
}

fn prim_gt(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    compare_chain(interp, args, |a, b| a > b)
}

fn prim_le(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    compare_chain(interp, args, |a, b| a <= b)
}

fn prim_ge(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    compare_chain(interp, args, |a, b| a >= b)
}

fn compare_chain<F>(interp: &mut Interpreter, args: &[NodeId], cmp: F) -> EvalResult
where
    F: Fn(&NumVal, &NumVal) -> bool,
{
    if args.len() < 2 {
        return Ok(interp.t_node);
    }
    
    let mut prev = extract_number(&interp.arena, args[0]);
    for &arg in &args[1..] {
        let curr = extract_number(&interp.arena, arg);
        if !cmp(&prev, &curr) {
            return Ok(interp.nil_node);
        }
        prev = curr;
    }
    Ok(interp.t_node)
}

// ============================================================================
// List Primitives
// ============================================================================

fn prim_cons(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.len() >= 2 {
        Ok(interp.arena.alloc(Node::Fork(args[0], args[1])))
    } else {
        Ok(interp.nil_node)
    }
}

fn prim_car(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        match interp.arena.get_unchecked(arg) {
            Node::Fork(car, _) => Ok(*car),
            Node::Leaf(OpaqueValue::Nil) => Ok(interp.nil_node),
            _ => interp.signal_error("CAR: Argument is not a list"),
        }
    } else {
        interp.signal_error("CAR: Too few arguments")
    }
}

fn prim_cdr(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        match interp.arena.get_unchecked(arg) {
            Node::Fork(_, cdr) => Ok(*cdr),
            Node::Leaf(OpaqueValue::Nil) => Ok(interp.nil_node),
            _ => interp.signal_error("CDR: Argument is not a list"),
        }
    } else {
        interp.signal_error("CDR: Too few arguments")
    }
}

fn prim_list(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    Ok(interp.list(args))
}

fn prim_length(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        let mut len = 0;
        let mut current = arg;
        while let Node::Fork(_, cdr) = interp.arena.get_unchecked(current).clone() {
            len += 1;
            current = cdr;
        }
        Ok(interp.make_integer(len))
    } else {
        Ok(interp.make_integer(0))
    }
}

fn prim_append(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.is_empty() {
        return Ok(interp.nil_node);
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
                result = interp.arena.alloc(Node::Fork(elem, result));
            }
            return Ok(result);
        }
        
        let mut current = arg;
        while let Node::Fork(car, cdr) = interp.arena.get_unchecked(current).clone() {
            all_elements.push(car);
            current = cdr;
        }
    }
    
    Ok(interp.list(&all_elements))
}

fn prim_reverse(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        let mut elements = Vec::new();
        let mut current = arg;
        while let Node::Fork(car, cdr) = interp.arena.get_unchecked(current).clone() {
            elements.push(car);
            current = cdr;
        }
        elements.reverse();
        Ok(interp.list(&elements))
    } else {
        Ok(interp.nil_node)
    }
}

fn prim_nth(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.len() >= 2 {
        if let NumVal::Int(n) = extract_number(&interp.arena, args[0]) {
            let mut current = args[1];
            for _ in 0..n {
                if let Node::Fork(_, cdr) = interp.arena.get_unchecked(current).clone() {
                    current = cdr;
                } else {
                    return Ok(interp.nil_node);
                }
            }
            if let Node::Fork(car, _) = interp.arena.get_unchecked(current).clone() {
                return Ok(car);
            }
        }
    }
    Ok(interp.nil_node)
}

// ============================================================================
// Predicates
// ============================================================================

fn prim_null(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        if arg == interp.nil_node {
            Ok(interp.t_node)
        } else if let Node::Leaf(OpaqueValue::Nil) = interp.arena.get_unchecked(arg) {
            Ok(interp.t_node)
        } else {
            Ok(interp.nil_node)
        }
    } else {
        Ok(interp.t_node)
    }
}

fn prim_atom(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        match interp.arena.get_unchecked(arg) {
            Node::Fork(_, _) => Ok(interp.nil_node),
            _ => Ok(interp.t_node),
        }
    } else {
        Ok(interp.t_node)
    }
}

fn prim_consp(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        match interp.arena.get_unchecked(arg) {
            Node::Fork(_, _) => Ok(interp.t_node),
            _ => Ok(interp.nil_node),
        }
    } else {
        Ok(interp.nil_node)
    }
}

fn prim_listp(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        match interp.arena.get_unchecked(arg) {
            Node::Fork(_, _) => Ok(interp.t_node),
            Node::Leaf(OpaqueValue::Nil) => Ok(interp.t_node),
            _ => Ok(interp.nil_node),
        }
    } else {
        Ok(interp.nil_node)
    }
}

fn prim_numberp(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        match interp.arena.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::Integer(_)) |
            Node::Leaf(OpaqueValue::Float(_)) => Ok(interp.t_node),
            _ => Ok(interp.nil_node),
        }
    } else {
        Ok(interp.nil_node)
    }
}

fn prim_symbolp(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        match interp.arena.get_unchecked(arg) {
            Node::Stem(_) => Ok(interp.t_node),
            _ => Ok(interp.nil_node),
        }
    } else {
        Ok(interp.nil_node)
    }
}

fn prim_eq(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.len() >= 2 && args[0] == args[1] {
        Ok(interp.t_node)
    } else {
        Ok(interp.nil_node)
    }
}

fn prim_eql(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.len() < 2 {
        return Ok(interp.t_node);
    }
    
    if args[0] == args[1] {
        return Ok(interp.t_node);
    }
    
    // Check numeric equality
    let a = extract_number(&interp.arena, args[0]);
    let b = extract_number(&interp.arena, args[1]);
    if a.eq(&b) {
        return Ok(interp.t_node);
    }
    
    Ok(interp.nil_node)
}

fn prim_equal(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.len() < 2 {
        return Ok(interp.t_node);
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
    
    if equal_rec(&interp.arena, args[0], args[1]) {
        Ok(interp.t_node)
    } else {
        Ok(interp.nil_node)
    }
}

fn prim_not(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        if arg == interp.nil_node {
            Ok(interp.t_node)
        } else if let Node::Leaf(OpaqueValue::Nil) = interp.arena.get_unchecked(arg) {
            Ok(interp.t_node)
        } else {
            Ok(interp.nil_node)
        }
    } else {
        Ok(interp.t_node)
    }
}

// ============================================================================
// I/O Primitives
// ============================================================================

/// Get the current output stream from *STANDARD-OUTPUT*
fn get_current_output_stream(interp: &Interpreter) -> crate::streams::StreamId {
    use crate::symbol::PackageId;
    
    // Look up *STANDARD-OUTPUT* symbol in COMMON-LISP package
    if let Some(pkg) = interp.symbols.get_package(PackageId(1)) {
        if let Some(sym) = pkg.find_symbol("*STANDARD-OUTPUT*") {
            if let Some(node) = interp.symbols.symbol_value(sym) {
                if let Node::Leaf(OpaqueValue::StreamHandle(id)) = interp.arena.get_unchecked(node) {
                    return crate::streams::StreamId(*id);
                }
            }
        }
    }
    // Fallback to the fixed stdout
    interp.standard_output
}

fn prim_print(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    use crate::printer::print_to_string;
    
    if let Some(&arg) = args.first() {
        let s = print_to_string(&interp.arena, &interp.symbols, arg);
        let out_id = get_current_output_stream(interp);
        let _ = interp.streams.write_string(out_id, &s);
        let _ = interp.streams.write_newline(out_id);
        Ok(arg)
    } else {
        Ok(interp.nil_node)
    }
}

fn prim_princ(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    use crate::printer::princ_to_string;
    
    if let Some(&arg) = args.first() {
        let s = princ_to_string(&interp.arena, &interp.symbols, arg);
        let out_id = get_current_output_stream(interp);
        let _ = interp.streams.write_string(out_id, &s);
        Ok(arg)
    } else {
        Ok(interp.nil_node)
    }
}

fn prim_terpri(interp: &mut Interpreter, _args: &[NodeId]) -> EvalResult {
    let out_id = get_current_output_stream(interp);
    let _ = interp.streams.write_newline(out_id);
    Ok(interp.nil_node)
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
fn prim_format(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    use crate::printer::{print_to_string, princ_to_string};
    
    if args.len() < 2 {
        return interp.signal_error("FORMAT requires at least 2 arguments (destination control-string)");
    }
    
    let dest = args[0];
    let control_string_node = args[1];
    let format_args = &args[2..];
    
    // Get the control string
    let control_string = match interp.arena.get_unchecked(control_string_node) {
        Node::Leaf(OpaqueValue::String(s)) => s.clone(),
        _ => return interp.signal_error("FORMAT: control-string must be a string"),
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
                return interp.signal_error("FORMAT: unexpected end of control string after ~");
            }
            
            // Parse optional parameters (mincol, colinc, minpad, padchar)
            // For simplicity, we skip complex parameter parsing and handle basic directives
            let mut colon = false;
            let mut at_sign = false;
            
            // Check for modifiers
            while i < chars.len() && (chars[i] == ':' || chars[i] == '@') {
                if chars[i] == ':' { colon = true; }
                if chars[i] == '@' { at_sign = true; }
                i += 1;
            }
            
            if i >= chars.len() {
                return interp.signal_error("FORMAT: unexpected end of control string");
            }
            
            let directive = chars[i].to_ascii_uppercase();
            
            match directive {
                'A' => {
                    // Aesthetic output (princ)
                    if arg_index >= format_args.len() {
                        return interp.signal_error("FORMAT: not enough arguments for ~A");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    
                    if colon && matches!(interp.arena.get_unchecked(arg), Node::Leaf(OpaqueValue::Nil)) {
                        result.push_str("()");
                    } else {
                        result.push_str(&princ_to_string(&interp.arena, &interp.symbols, arg));
                    }
                }
                'S' => {
                    // Standard output (prin1)
                    if arg_index >= format_args.len() {
                        return interp.signal_error("FORMAT: not enough arguments for ~S");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    result.push_str(&print_to_string(&interp.arena, &interp.symbols, arg));
                }
                'D' => {
                    // Decimal integer
                    if arg_index >= format_args.len() {
                        return interp.signal_error("FORMAT: not enough arguments for ~D");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    match interp.arena.get_unchecked(arg) {
                        Node::Leaf(OpaqueValue::Integer(n)) => {
                            if at_sign && *n >= 0 {
                                result.push('+');
                            }
                            result.push_str(&n.to_string());
                        }
                        _ => result.push_str(&princ_to_string(&interp.arena, &interp.symbols, arg)),
                    }
                }
                'B' => {
                    // Binary integer
                    if arg_index >= format_args.len() {
                        return interp.signal_error("FORMAT: not enough arguments for ~B");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    match interp.arena.get_unchecked(arg) {
                        Node::Leaf(OpaqueValue::Integer(n)) => {
                            result.push_str(&format!("{:b}", n));
                        }
                        _ => result.push_str(&princ_to_string(&interp.arena, &interp.symbols, arg)),
                    }
                }
                'O' => {
                    // Octal integer
                    if arg_index >= format_args.len() {
                        return interp.signal_error("FORMAT: not enough arguments for ~O");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    match interp.arena.get_unchecked(arg) {
                        Node::Leaf(OpaqueValue::Integer(n)) => {
                            result.push_str(&format!("{:o}", n));
                        }
                        _ => result.push_str(&princ_to_string(&interp.arena, &interp.symbols, arg)),
                    }
                }
                'X' => {
                    // Hexadecimal integer
                    if arg_index >= format_args.len() {
                        return interp.signal_error("FORMAT: not enough arguments for ~X");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    match interp.arena.get_unchecked(arg) {
                        Node::Leaf(OpaqueValue::Integer(n)) => {
                            result.push_str(&format!("{:x}", n));
                        }
                        _ => result.push_str(&princ_to_string(&interp.arena, &interp.symbols, arg)),
                    }
                }
                'F' => {
                    // Floating point
                    if arg_index >= format_args.len() {
                        return interp.signal_error("FORMAT: not enough arguments for ~F");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    match interp.arena.get_unchecked(arg) {
                        Node::Leaf(OpaqueValue::Float(f)) => {
                            result.push_str(&format!("{}", f));
                        }
                        Node::Leaf(OpaqueValue::Integer(n)) => {
                            result.push_str(&format!("{}.0", n));
                        }
                        _ => result.push_str(&princ_to_string(&interp.arena, &interp.symbols, arg)),
                    }
                }
                'C' => {
                    // Character
                    if arg_index >= format_args.len() {
                        return interp.signal_error("FORMAT: not enough arguments for ~C");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    match interp.arena.get_unchecked(arg) {
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
                        _ => result.push_str(&princ_to_string(&interp.arena, &interp.symbols, arg)),
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
                        return interp.signal_error("FORMAT: not enough arguments for ~R");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    match interp.arena.get_unchecked(arg) {
                        Node::Leaf(OpaqueValue::Integer(n)) => {
                            result.push_str(&n.to_string());
                        }
                        _ => result.push_str(&princ_to_string(&interp.arena, &interp.symbols, arg)),
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
                        return interp.signal_error("FORMAT: not enough arguments for ~?");
                    }
                    let arg = format_args[arg_index];
                    arg_index += 1;
                    result.push_str(&princ_to_string(&interp.arena, &interp.symbols, arg));
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
    let is_nil = matches!(interp.arena.get_unchecked(dest), Node::Leaf(OpaqueValue::Nil));
    let is_t = if let Node::Leaf(OpaqueValue::Symbol(id)) = interp.arena.get_unchecked(dest) {
        SymbolId(*id) == interp.t_sym
    } else {
        false
    };
    let stream_id = if let Node::Leaf(OpaqueValue::StreamHandle(id)) = interp.arena.get_unchecked(dest) {
        Some(crate::streams::StreamId(*id))
    } else {
        None
    };
    
    if is_nil {
        // Return the formatted string
        Ok(interp.arena.alloc(Node::Leaf(OpaqueValue::String(result))))
    } else if is_t {
        // Output to standard output
        let out_id = interp.standard_output;
        let _ = interp.streams.write_string(out_id, &result);
        Ok(interp.nil_node)
    } else if let Some(id) = stream_id {
        // Output to specified stream
        let _ = interp.streams.write_string(id, &result);
        Ok(interp.nil_node)
    } else {
        // For unknown destinations, output to stdout
        let out_id = interp.standard_output;
        let _ = interp.streams.write_string(out_id, &result);
        Ok(interp.nil_node)
    }
}

// ============================================================================
// Stream Primitives
// ============================================================================

/// (make-string-output-stream) -> stream
fn prim_make_string_output_stream(interp: &mut Interpreter, _args: &[NodeId]) -> EvalResult {
    use crate::streams::Stream;
    
    let stream = Stream::StringOutputStream { buffer: String::new() };
    let id = interp.streams.alloc(stream);
    Ok(interp.arena.alloc(Node::Leaf(OpaqueValue::StreamHandle(id.0))))
}

/// (get-output-stream-string stream) -> string
fn prim_get_output_stream_string(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Node::Leaf(OpaqueValue::StreamHandle(id)) = interp.arena.get_unchecked(arg) {
            let stream_id = crate::streams::StreamId(*id);
            if let Some(s) = interp.streams.get_output_stream_string(stream_id) {
                return Ok(interp.arena.alloc(Node::Leaf(OpaqueValue::String(s))));
            } else {
                return interp.signal_error("GET-OUTPUT-STREAM-STRING: not a string output stream");
            }
        }
    }
    interp.signal_error("GET-OUTPUT-STREAM-STRING requires a stream argument")
}

/// (make-string-input-stream string) -> stream
fn prim_make_string_input_stream(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    use crate::streams::Stream;
    
    if let Some(&arg) = args.first() {
        if let Node::Leaf(OpaqueValue::String(s)) = interp.arena.get_unchecked(arg) {
            let stream = Stream::StringInputStream { 
                buffer: s.clone(), 
                position: 0 
            };
            let id = interp.streams.alloc(stream);
            return Ok(interp.arena.alloc(Node::Leaf(OpaqueValue::StreamHandle(id.0))));
        }
    }
    interp.signal_error("MAKE-STRING-INPUT-STREAM requires a string argument")
}

/// (close stream) -> t
fn prim_close(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Node::Leaf(OpaqueValue::StreamHandle(id)) = interp.arena.get_unchecked(arg) {
            let stream_id = crate::streams::StreamId(*id);
            if interp.streams.close(stream_id) {
                return Ok(interp.t_node);
            }
        }
    }
    Ok(interp.nil_node)
}

/// (write-string string &optional stream) -> string
fn prim_write_string(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.is_empty() {
        return interp.signal_error("WRITE-STRING requires at least 1 argument");
    }
    
    let string_arg = args[0];
    let stream_id = if args.len() > 1 {
        if let Node::Leaf(OpaqueValue::StreamHandle(id)) = interp.arena.get_unchecked(args[1]) {
            crate::streams::StreamId(*id)
        } else {
            interp.standard_output
        }
    } else {
        interp.standard_output
    };
    
    if let Node::Leaf(OpaqueValue::String(s)) = interp.arena.get_unchecked(string_arg) {
        let s_clone = s.clone();
        let _ = interp.streams.write_string(stream_id, &s_clone);
        Ok(string_arg)
    } else {
        use crate::printer::princ_to_string;
        let s = princ_to_string(&interp.arena, &interp.symbols, string_arg);
        let _ = interp.streams.write_string(stream_id, &s);
        Ok(string_arg)
    }
}

/// (write-char char &optional stream) -> char
fn prim_write_char(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.is_empty() {
        return interp.signal_error("WRITE-CHAR requires at least 1 argument");
    }
    
    let char_arg = args[0];
    let stream_id = if args.len() > 1 {
        if let Node::Leaf(OpaqueValue::StreamHandle(id)) = interp.arena.get_unchecked(args[1]) {
            crate::streams::StreamId(*id)
        } else {
            interp.standard_output
        }
    } else {
        interp.standard_output
    };
    
    let c = match interp.arena.get_unchecked(char_arg) {
        Node::Leaf(OpaqueValue::Integer(n)) => char::from_u32(*n as u32).unwrap_or('?'),
        Node::Leaf(OpaqueValue::String(s)) => s.chars().next().unwrap_or('?'),
        _ => '?',
    };
    
    let _ = interp.streams.write_char(stream_id, c);
    Ok(char_arg)
}

/// (fresh-line &optional stream) -> generalized-boolean
fn prim_fresh_line(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    let stream_id = if !args.is_empty() {
        if let Node::Leaf(OpaqueValue::StreamHandle(id)) = interp.arena.get_unchecked(args[0]) {
            crate::streams::StreamId(*id)
        } else {
            interp.standard_output
        }
    } else {
        interp.standard_output
    };
    
    match interp.streams.fresh_line(stream_id) {
        Ok(true) => Ok(interp.t_node),
        Ok(false) => Ok(interp.nil_node),
        Err(_) => Ok(interp.nil_node),
    }
}

// ============================================================================
// CLOS Primitives
// ============================================================================

fn prim_find_class(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        if let Some(sym) = interp.node_to_symbol(arg) {
            if let Some(id) = interp.mop.find_class(sym) {
                return Ok(interp.arena.alloc(Node::Leaf(OpaqueValue::Class(id.0))));
            }
        }
    }
    Ok(interp.nil_node)
}

fn prim_make_instance(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    use crate::clos::ClassId;
    if let Some(&class_arg) = args.first() {
        let class_id = match interp.arena.get_unchecked(class_arg) {
            Node::Leaf(OpaqueValue::Class(id)) => Some(ClassId(*id)),
            _ => {
                // Try symbol
                if let Some(sym) = interp.node_to_symbol(class_arg) {
                    interp.mop.find_class(sym)
                } else { None }
            }
        };
        
        if let Some(id) = class_id {
            // Create instance
            if let Some(inst_idx) = interp.mop.make_instance(id, interp.nil_node) {
                // Handle Initargs? (TODO: process rest of args)
                // For now, simple creation
                return Ok(interp.arena.alloc(Node::Leaf(OpaqueValue::Instance(inst_idx as u32))));
            }
        }
    }
    Ok(interp.nil_node)
}

fn prim_class_of(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    use crate::clos::ClassId;
    if let Some(&arg) = args.first() {
        let class_id = match interp.arena.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::Integer(_)) => ClassId(0), // T/Integer map not full yet
            Node::Leaf(OpaqueValue::Instance(idx)) => {
                interp.mop.get_instance(*idx as usize).map(|i| i.class).unwrap_or(interp.mop.t_class)
            }
            Node::Leaf(OpaqueValue::Class(_)) => interp.mop.standard_class,
            _ => interp.mop.t_class,
        };
        // Return class object
        Ok(interp.arena.alloc(Node::Leaf(OpaqueValue::Class(class_id.0))))
    } else {
        Ok(interp.nil_node)
    }
}

fn prim_slot_value(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.len() >= 2 {
        let instance = args[0];
        let slot_name = args[1];
        
        // Extract instance index
        let inst_idx = if let Node::Leaf(OpaqueValue::Instance(idx)) = interp.arena.get_unchecked(instance) {
            Some(*idx as usize)
        } else { None };
        
        // Extract slot name symbol
        let slot_sym = interp.node_to_symbol(slot_name);
        
        if let (Some(idx), Some(sym)) = (inst_idx, slot_sym) {
            // Find slot index in class
            if let Some(inst) = interp.mop.get_instance(idx) {
                if let Some(class) = interp.mop.get_class(inst.class) {
                    // Find slot definition
                    if let Some(pos) = class.slots.iter().position(|s| s.name == sym) {
                         return Ok(interp.mop.slot_value(idx, pos).unwrap_or(interp.nil_node));
                    }
                }
            }
        }
    }
    Err(crate::eval::ControlSignal::Error("Invalid slot access".to_string()))
}

fn prim_set_slot_value(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.len() >= 3 {
        let instance = args[0];
        let slot_name = args[1];
        let new_val = args[2];
        
        // Extract instance index
        let inst_idx = if let Node::Leaf(OpaqueValue::Instance(idx)) = interp.arena.get_unchecked(instance) {
            Some(*idx as usize)
        } else { None };
        
        // Extract slot name symbol
        let slot_sym = interp.node_to_symbol(slot_name);
        
        if let (Some(idx), Some(sym)) = (inst_idx, slot_sym) {
            // Find slot index in class
            if let Some(inst) = interp.mop.get_instance(idx) {
                if let Some(class) = interp.mop.get_class(inst.class) {
                    // Find slot definition
                    if let Some(pos) = class.slots.iter().position(|s| s.name == sym) {
                         interp.mop.set_slot_value(idx, pos, new_val);
                         return Ok(new_val);
                    }
                }
            }
        }
    }
    Err(crate::eval::ControlSignal::Error("Invalid slot set".to_string()))
}

fn prim_error(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.is_empty() {
        return Err(crate::eval::ControlSignal::Error("Error called with no arguments".to_string()));
    }
    
    // (error "format" args...)
    // For now, simpler: (error "message")
    let fmt_node = args[0];
    let fmt = if let Node::Leaf(OpaqueValue::String(h)) = interp.arena.get_unchecked(fmt_node) {
        h.clone()
    } else {
        // Coerce to string
        crate::printer::princ_to_string(&interp.arena, &interp.symbols, fmt_node)
    };
    
    // Call signal_error
    interp.signal_error(&fmt)
}

fn prim_gc(interp: &mut Interpreter, _args: &[NodeId]) -> EvalResult {
    let freed = interp.collect_garbage();
    // Return freed count as integer
    let val = OpaqueValue::Integer(freed as i64);
    Ok(interp.arena.alloc(Node::Leaf(val)))
}

fn prim_room(interp: &mut Interpreter, _args: &[NodeId]) -> EvalResult {
    let stats = interp.arena.stats();
    let array_count = interp.arrays.active_count();
    let array_elements = interp.arrays.total_elements();
    let closure_count = interp.closures.len();
    let symbol_count = interp.symbols.symbol_count();
    
    println!("=== ROOM ===");
    println!("Arena:");
    println!("  Total slots:     {}", stats.total_slots);
    println!("  Free slots:      {}", stats.free_slots);
    println!("  Live nodes:      {}", stats.total_slots - stats.free_slots);
    println!("Vectors:           {} ({} elements)", array_count, array_elements);
    println!("Closures:          {}", closure_count);
    println!("Symbols:           {}", symbol_count);
    println!("GC:");
    println!("  Threshold:       {}", interp.gc_threshold);
    println!("  Allocs since GC: {}", stats.allocs_since_gc);
    
    Ok(interp.nil_node)
}

fn prim_make_array(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    // (make-array size [initial-element])
    if args.is_empty() {
        return Err(crate::eval::ControlSignal::Error("make-array requires at least 1 argument".to_string()));
    }
    
    let size_val = extract_number(&interp.arena, args[0]);
    let size = match size_val {
        NumVal::Int(n) if n >= 0 => n as usize,
        _ => return Err(crate::eval::ControlSignal::Error("Invalid array size".to_string())),
    };
    
    let initial = if args.len() > 1 { args[1] } else { interp.nil_node };
    
    let vec_id = interp.arrays.alloc(size, initial);
    
    Ok(interp.arena.alloc(Node::Leaf(OpaqueValue::VectorHandle(vec_id.0))))
}

fn prim_aref(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    // (aref array index)
    if args.len() != 2 {
        return Err(crate::eval::ControlSignal::Error("aref requires 2 arguments".to_string()));
    }
    
    // Check if array
    if let Node::Leaf(OpaqueValue::VectorHandle(idx)) = interp.arena.get_unchecked(args[0]) {
        let vec_id = crate::arrays::VectorId(*idx);
        
        // Parse index
        let idx_val = extract_number(&interp.arena, args[1]);
        if let NumVal::Int(i) = idx_val {
            if i >= 0 {
                if let Some(val) = interp.arrays.aref(vec_id, i as usize) {
                    return Ok(val);
                }
                return Err(crate::eval::ControlSignal::Error(format!("Array index out of bounds: {}", i)));
            }
        }
        return Err(crate::eval::ControlSignal::Error("Invalid array index".to_string()));
    }
    
    Err(crate::eval::ControlSignal::Error("Not an array".to_string()))
}

fn prim_set_aref(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    // (set-aref array index value)
    if args.len() != 3 {
        return Err(crate::eval::ControlSignal::Error("set-aref requires 3 arguments".to_string()));
    }
    
    if let Node::Leaf(OpaqueValue::VectorHandle(idx)) = interp.arena.get_unchecked(args[0]) {
         let vec_id = crate::arrays::VectorId(*idx);
         
         let idx_val = extract_number(&interp.arena, args[1]);
         if let NumVal::Int(i) = idx_val {
             if i >= 0 {
                 let val = args[2];
                 if interp.arrays.set_aref(vec_id, i as usize, val) {
                     return Ok(val);
                 }
                 return Err(crate::eval::ControlSignal::Error(format!("Array index out of bounds: {}", i)));
             }
         }
         return Err(crate::eval::ControlSignal::Error("Invalid array index".to_string()));
    }
    
    Err(crate::eval::ControlSignal::Error("Not an array".to_string()))
}

fn prim_set_macro_character(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    // (set-macro-character char function [non-terminating-p])
    // function: currently only accepts a SYMBOL naming a built-in macro.
    if args.len() < 2 || args.len() > 3 {
        return Err(crate::eval::ControlSignal::Error("set-macro-character requires 2 or 3 arguments".to_string()));
    }
    
    // 1. Character
    let char_val = extract_number(&interp.arena, args[0]);
    let ch = match char_val {
        NumVal::Int(n) => std::char::from_u32(n as u32).ok_or(crate::eval::ControlSignal::Error("Invalid character code".to_string()))?,
        _ => return Err(crate::eval::ControlSignal::Error("Character argument must be an integer (code point)".to_string())),
    };
    
    // 2. Function (Symbol)
    // We expect a symbol.
    let func_name = if let Some(sym_id) = interp.node_to_symbol(args[1]) {
        interp.symbols.get_symbol(sym_id).unwrap().name.clone()
    } else {
         return Err(crate::eval::ControlSignal::Error("Function argument must be a symbol naming a built-in macro".to_string()));
    };
    
    // Look up built-in
    let macro_fn = get_reader_macro(&func_name).ok_or_else(|| {
        crate::eval::ControlSignal::Error(format!("Unknown built-in reader macro: {}", func_name))
    })?;
    
    // 3. Non-terminating?
    let non_terminating = if args.len() > 2 {
        args[2] != interp.nil_node
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
    
    interp.readtable.set_syntax_type(ch, syntax);
    interp.readtable.set_macro_character(ch, Some(macro_fn));
    
    Ok(interp.t_node)
}

fn prim_get_macro_character(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.is_empty() {
        return interp.signal_error("get-macro-character: too few arguments");
    }
    
    let ch_code = if let Node::Leaf(OpaqueValue::Integer(n)) = interp.arena.get_unchecked(args[0]).clone() {
        n as u32
    } else {
        return interp.signal_error("get-macro-character: char code must be an integer");
    };
    
    let ch = std::char::from_u32(ch_code).ok_or_else(|| ControlSignal::Error(format!("Invalid char code: {}", ch_code)))?;
    
    if let Some(_func) = interp.readtable.get_macro_character(ch) {
        // We can't return the Rust function pointer directly as a Lisp object yet
        // For Phase 10, let's just return T if a macro is set, or NIL.
        // In next phases, we would return a special OpaqueValue for read-macros.
        Ok(interp.t_node)
    } else {
        Ok(interp.nil_node)
    }
}

fn prim_set_syntax_from_char(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.len() < 2 {
        return interp.signal_error("set-syntax-from-char: too few arguments");
    }
    
    let to_code = if let Node::Leaf(OpaqueValue::Integer(n)) = interp.arena.get_unchecked(args[0]).clone() {
        n as u32
    } else {
        return interp.signal_error("set-syntax-from-char: to-char code must be an integer");
    };
    
    let from_code = if let Node::Leaf(OpaqueValue::Integer(n)) = interp.arena.get_unchecked(args[1]).clone() {
        n as u32
    } else {
        return interp.signal_error("set-syntax-from-char: from-char code must be an integer");
    };
    
    let to_ch = std::char::from_u32(to_code).ok_or_else(|| ControlSignal::Error(format!("Invalid to-char code: {}", to_code)))?;
    let from_ch = std::char::from_u32(from_code).ok_or_else(|| ControlSignal::Error(format!("Invalid from-char code: {}", from_code)))?;
    
    let syntax = interp.readtable.get_syntax_type(from_ch);
    let macro_fn = interp.readtable.get_macro_character(from_ch);
    
    interp.readtable.set_syntax_type(to_ch, syntax);
    if let Some(f) = macro_fn {
        interp.readtable.set_macro_character(to_ch, Some(f));
    } else {
        interp.readtable.set_macro_character(to_ch, None);
    }
    
    Ok(interp.t_node)
}

fn get_reader_macro(name: &str) -> Option<crate::readtable::ReaderMacroFn> {
    match name {
        "READ-LEFT-BRACKET" => Some(wrap_read_left_bracket),
        "READ-RIGHT-BRACKET" => Some(wrap_read_right_bracket),
        _ => None,
    }
}

fn wrap_read_left_bracket(reader: &mut crate::reader::Reader, c: char) -> crate::reader::ReaderResult {
    reader.read_left_bracket(c)
}

fn wrap_read_right_bracket(reader: &mut crate::reader::Reader, c: char) -> crate::reader::ReaderResult {
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
            (NumVal::Int(a), NumVal::Int(b)) => {
                match a.checked_add(b) {
                    Some(res) => NumVal::Int(res),
                    None => NumVal::Big(BigInt::from(a) + BigInt::from(b)),
                }
            }
            (NumVal::Big(a), NumVal::Big(b)) => NumVal::Big(a + b),
            (NumVal::Int(a), NumVal::Big(b)) => NumVal::Big(BigInt::from(a) + b),
            (NumVal::Big(a), NumVal::Int(b)) => NumVal::Big(a + BigInt::from(b)),
            
            (NumVal::Float(a), NumVal::Float(b)) => NumVal::Float(a + b),
            (NumVal::Int(a), NumVal::Float(b)) => NumVal::Float(a as f64 + b),
            (NumVal::Float(a), NumVal::Int(b)) => NumVal::Float(a + b as f64),
            (NumVal::Big(a), NumVal::Float(b)) => NumVal::Float(a.to_f64().unwrap_or(f64::INFINITY) + b),
            (NumVal::Float(a), NumVal::Big(b)) => NumVal::Float(a + b.to_f64().unwrap_or(f64::INFINITY)),
            _ => NumVal::None,
        }
    }
    
    fn sub(self, other: NumVal) -> NumVal {
        match (self, other) {
            (NumVal::Int(a), NumVal::Int(b)) => {
                match a.checked_sub(b) {
                    Some(res) => NumVal::Int(res),
                    None => NumVal::Big(BigInt::from(a) - BigInt::from(b)),
                }
            }
            (NumVal::Big(a), NumVal::Big(b)) => NumVal::Big(a - b),
            (NumVal::Int(a), NumVal::Big(b)) => NumVal::Big(BigInt::from(a) - b),
            (NumVal::Big(a), NumVal::Int(b)) => NumVal::Big(a - BigInt::from(b)),

            (NumVal::Float(a), NumVal::Float(b)) => NumVal::Float(a - b),
            (NumVal::Int(a), NumVal::Float(b)) => NumVal::Float(a as f64 - b),
            (NumVal::Float(a), NumVal::Int(b)) => NumVal::Float(a - b as f64),
            (NumVal::Big(a), NumVal::Float(b)) => NumVal::Float(a.to_f64().unwrap_or(f64::INFINITY) - b),
            (NumVal::Float(a), NumVal::Big(b)) => NumVal::Float(a - b.to_f64().unwrap_or(f64::INFINITY)),
            _ => NumVal::None,
        }
    }
    
    fn mul(self, other: NumVal) -> NumVal {
        match (self, other) {
            (NumVal::Int(a), NumVal::Int(b)) => {
                match a.checked_mul(b) {
                    Some(res) => NumVal::Int(res),
                    None => NumVal::Big(BigInt::from(a) * BigInt::from(b)),
                }
            }
            (NumVal::Big(a), NumVal::Big(b)) => NumVal::Big(a * b),
            (NumVal::Int(a), NumVal::Big(b)) => NumVal::Big(BigInt::from(a) * b),
            (NumVal::Big(a), NumVal::Int(b)) => NumVal::Big(a * BigInt::from(b)),

            (NumVal::Float(a), NumVal::Float(b)) => NumVal::Float(a * b),
            (NumVal::Int(a), NumVal::Float(b)) => NumVal::Float(a as f64 * b),
            (NumVal::Float(a), NumVal::Int(b)) => NumVal::Float(a * b as f64),
            (NumVal::Big(a), NumVal::Float(b)) => NumVal::Float(a.to_f64().unwrap_or(f64::INFINITY) * b),
            (NumVal::Float(a), NumVal::Big(b)) => NumVal::Float(a * b.to_f64().unwrap_or(f64::INFINITY)),
            _ => NumVal::None,
        }
    }
    
    fn div(self, other: NumVal) -> NumVal {
        match (self, other) {
            (NumVal::Int(a), NumVal::Int(b)) if b != 0 => {
                // Use float division to match CL semantics
                NumVal::Float(a as f64 / b as f64)
            }
            (NumVal::Big(a), NumVal::Big(b)) if b != BigInt::from(0) => {
                 NumVal::Float(a.to_f64().unwrap_or(f64::INFINITY) / b.to_f64().unwrap_or(f64::INFINITY))
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
            (NumVal::Big(a), NumVal::Float(b)) => a.to_f64().unwrap_or(f64::INFINITY).partial_cmp(b),
            (NumVal::Float(a), NumVal::Big(b)) => a.partial_cmp(&b.to_f64().unwrap_or(f64::INFINITY)),
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

fn prim_compile(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        let node = interp.arena.get_unchecked(arg).clone();
            
        let target_closure = match node {
            Node::Leaf(OpaqueValue::Symbol(id)) => {
                let sym = SymbolId(id);
                if let Some(func_node) = interp.symbols.symbol_function(sym) {
                    if let Node::Leaf(OpaqueValue::Closure(idx)) = interp.arena.get_unchecked(func_node) {
                         Some(*idx)
                    } else {
                        return interp.signal_error("COMPILE: Symbol function is not a closure (maybe already compiled or primitive?)");
                    }
                } else {
                     return interp.signal_error("COMPILE: Symbol has no function definition");
                }
            }
            Node::Leaf(OpaqueValue::Closure(idx)) => {
                Some(idx)
            }
            _ => {
                return interp.signal_error("COMPILE: Argument must be a symbol or closure");
            }
        };
        
        if let Some(idx) = target_closure {
             let (params, body) = {
                 // Clone to avoid borrow conflict
                 let closure = &interp.closures[idx as usize];
                 (closure.params.clone(), closure.body)
             };
             
             match crate::compiler::compile_func(interp, &params, body) {
                 Ok(compiled_node) => return Ok(compiled_node),
                 Err(e) => return interp.signal_error(&format!("Compilation failed: {}", e)),
             }
        }
    }
    
    interp.signal_error("COMPILE: Invalid argument")
}



fn prim_tree_string(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if let Some(&arg) = args.first() {
        let s = crate::printer::tree_format(&interp.arena, arg);
        Ok(interp.arena.alloc(Node::Leaf(OpaqueValue::String(s))))
    } else {
        Err(crate::eval::ControlSignal::Error("TREE-STRING requires 1 argument".to_string()))
    }
}

/// (funcall function arg1 arg2 ...)
fn prim_funcall(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.is_empty() {
        return Err(crate::eval::ControlSignal::Error("FUNCALL requires at least 1 argument".to_string()));
    }
    
    let func = args[0];
    let func_args = if args.len() > 1 {
        interp.list(&args[1..])
    } else {
        interp.nil_node
    };
    
    // We need an environment for apply_function.
    // Primitives usually run in the current environment context, which is passed in?
    // Wait, prim functions signature is (interp, args). No env.
    // But apply_function takes env.
    // We can pass a new empty environment or try to get current?
    // Interpreter struct has ctx (EvalContext) but not Environment.
    // Closures capture environment.
    // Evaluated arguments are already values, so environment shouldn't matter for application unless it's a macro or special form that needs it?
    // But apply_function takes it.
    // Let's pass a new empty environment for now.
    
    let env = crate::eval::Environment::new();
    interp.apply_function(func, func_args, &env)
}

/// (apply function arg1 ... argn-1 list)
fn prim_apply(interp: &mut Interpreter, args: &[NodeId]) -> EvalResult {
    if args.len() < 2 {
         return Err(crate::eval::ControlSignal::Error("APPLY requires at least 2 arguments".to_string()));
    }
    
    let func = args[0];
    let last_arg = args[args.len() - 1]; // The list argument
    
    // Check if last_arg is a proper list?
    // We don't strictly enforce proper list for Tree Calculus, just use it.
    
    // Construct argument list. 
    // args[1..args.len()-1] are single arguments. last_arg is a list.
    let mut final_args = last_arg;
    for &arg in args[1..args.len()-1].iter().rev() {
        final_args = interp.cons(arg, final_args);
    }
    
    let env = crate::eval::Environment::new();
    interp.apply_function(func, final_args, &env)
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_add() {
        let mut interp = Interpreter::new();
        let a = interp.make_integer(1);
        let b = interp.make_integer(2);
        let c = interp.make_integer(3);
        
        let result = prim_add(&mut interp, &[a, b, c]).unwrap();
        match interp.arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(6)) => {}
            _ => panic!("Expected 6"),
        }
    }
    
    #[test]
    fn test_cons_car_cdr() {
        let mut interp = Interpreter::new();
        let a = interp.make_integer(1);
        let b = interp.make_integer(2);
        
        let cell = prim_cons(&mut interp, &[a, b]).unwrap();
        let car = prim_car(&mut interp, &[cell]).unwrap();
        let cdr = prim_cdr(&mut interp, &[cell]).unwrap();
        
        assert_eq!(car, a);
        assert_eq!(cdr, b);
    }
    
    #[test]
    fn test_length() {
        let mut interp = Interpreter::new();
        let a = interp.make_integer(1);
        let b = interp.make_integer(2);
        let c = interp.make_integer(3);
        let list = interp.list(&[a, b, c]);
        
        let len = prim_length(&mut interp, &[list]).unwrap();
        match interp.arena.get_unchecked(len) {
            Node::Leaf(OpaqueValue::Integer(3)) => {}
            _ => panic!("Expected length 3"),
        }
    }
    
    // === Extensive Arithmetic Tests ===
    
    #[test]
    fn test_add_empty() {
        let mut interp = Interpreter::new();
        let result = prim_add(&mut interp, &[]).unwrap();
        match interp.arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(0)) => {}
            _ => panic!("Expected 0"),
        }
    }
    
    #[test]
    fn test_add_single() {
        let mut interp = Interpreter::new();
        let a = interp.make_integer(42);
        let result = prim_add(&mut interp, &[a]).unwrap();
        match interp.arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(42)) => {}
            _ => panic!("Expected 42"),
        }
    }
    
    #[test]
    fn test_add_many() {
        let mut interp = Interpreter::new();
        let nums: Vec<_> = (1..=10).map(|i| interp.make_integer(i)).collect();
        let result = prim_add(&mut interp, &nums).unwrap();
        match interp.arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(55)) => {} // 1+2+...+10 = 55
            _ => panic!("Expected 55"),
        }
    }
    
    #[test]
    fn test_sub_unary() {
        let mut interp = Interpreter::new();
        let a = interp.make_integer(5);
        let result = prim_sub(&mut interp, &[a]).unwrap();
        match interp.arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(-5)) => {}
            _ => panic!("Expected -5"),
        }
    }
    
    #[test]
    fn test_sub_chain() {
        let mut interp = Interpreter::new();
        let a = interp.make_integer(100);
        let b = interp.make_integer(30);
        let c = interp.make_integer(20);
        let result = prim_sub(&mut interp, &[a, b, c]).unwrap();
        match interp.arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(50)) => {} // 100-30-20 = 50
            _ => panic!("Expected 50"),
        }
    }
    
    #[test]
    fn test_mul_empty() {
        let mut interp = Interpreter::new();
        let result = prim_mul(&mut interp, &[]).unwrap();
        match interp.arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(1)) => {}
            _ => panic!("Expected 1"),
        }
    }
    
    #[test]
    fn test_mul_chain() {
        let mut interp = Interpreter::new();
        let a = interp.make_integer(2);
        let b = interp.make_integer(3);
        let c = interp.make_integer(4);
        let d = interp.make_integer(5);
        let result = prim_mul(&mut interp, &[a, b, c, d]).unwrap();
        match interp.arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(120)) => {} // 2*3*4*5 = 120
            _ => panic!("Expected 120"),
        }
    }
    
    #[test]
    fn test_div_exact() {
        let mut interp = Interpreter::new();
        let a = interp.make_integer(20);
        let b = interp.make_integer(4);
        let result = prim_div(&mut interp, &[a, b]).unwrap();
        match interp.arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Float(f)) if (*f - 5.0).abs() < 0.001 => {}
            _ => panic!("Expected 5.0"),
        }
    }
    
    #[test]
    fn test_div_fractional() {
        let mut interp = Interpreter::new();
        let a = interp.make_integer(5);
        let b = interp.make_integer(19);
        let result = prim_div(&mut interp, &[a, b]).unwrap();
        match interp.arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Float(f)) if (*f - 0.2631578947368421).abs() < 0.0001 => {}
            other => panic!("Expected ~0.263, got {:?}", other),
        }
    }
    
    #[test]
    fn test_mixed_float_int() {
        let mut interp = Interpreter::new();
        let a = interp.make_integer(10);
        let b = interp.arena.alloc(Node::Leaf(OpaqueValue::Float(2.5)));
        let result = prim_add(&mut interp, &[a, b]).unwrap();
        match interp.arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Float(f)) if (*f - 12.5).abs() < 0.001 => {}
            _ => panic!("Expected 12.5"),
        }
    }
    
    #[test]
    fn test_comparison_lt() {
        let mut interp = Interpreter::new();
        let a = interp.make_integer(1);
        let b = interp.make_integer(2);
        let c = interp.make_integer(3);
        let result = prim_lt(&mut interp, &[a, b, c]).unwrap();
        assert_eq!(result, interp.t_node);
    }
    
    #[test]
    fn test_comparison_lt_false() {
        let mut interp = Interpreter::new();
        let a = interp.make_integer(1);
        let b = interp.make_integer(3);
        let c = interp.make_integer(2);
        let result = prim_lt(&mut interp, &[a, b, c]).unwrap();
        assert_eq!(result, interp.nil_node);
    }
    
    #[test]
    fn test_num_eq() {
        let mut interp = Interpreter::new();
        let a = interp.make_integer(42);
        let b = interp.make_integer(42);
        let result = prim_num_eq(&mut interp, &[a, b]).unwrap();
        assert_eq!(result, interp.t_node);
    }
    
    #[test]
    fn test_mod() {
        let mut interp = Interpreter::new();
        let a = interp.make_integer(17);
        let b = interp.make_integer(5);
        let result = prim_mod(&mut interp, &[a, b]).unwrap();
        match interp.arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(2)) => {} // 17 mod 5 = 2
            _ => panic!("Expected 2"),
        }
    }

    #[test]
    fn test_overflow() {
        let mut interp = Interpreter::new();
        // i64::MAX is 9,223,372,036,854,775,807
        let large = interp.make_integer(i64::MAX);
        let two = interp.make_integer(2);
        
        let result = prim_add(&mut interp, &[large, two]).unwrap();
        match interp.arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::BigInt(_)) => {
                // Success: it promoted to BigInt
            }
            _ => panic!("Expected overflow to BigInt, got {:?}", interp.arena.get_unchecked(result)),
        }
    }
}

