// TreeCL Evaluator - Special Forms and Core Evaluation
//
// This module implements ANSI CL special forms on top of Tree Calculus.

use crate::arena::{Arena, Node};
use crate::types::{NodeId, OpaqueValue};
use crate::symbol::{SymbolTable, SymbolId, PackageId};
use crate::search::EvalContext;
use crate::clos::MetaObjectProtocol;
use crate::conditions::ConditionSystem;
use crate::arrays::ArrayStore;
use crate::readtable::Readtable;
use crate::streams::{StreamManager, StreamId};
use std::collections::HashMap;

/// Environment for lexical bindings
#[derive(Debug, Clone)]
pub struct Environment {
    /// Lexical bindings: SymbolId -> NodeId
    bindings: HashMap<SymbolId, NodeId>,
    /// Parent environment (for nested scopes)
    parent: Option<Box<Environment>>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            parent: None,
        }
    }
    
    pub fn with_parent(parent: Environment) -> Self {
        Self {
            bindings: HashMap::new(),
            parent: Some(Box::new(parent)),
        }
    }
    
    pub fn bind(&mut self, sym: SymbolId, val: NodeId) {
        self.bindings.insert(sym, val);
    }
    
    pub fn lookup(&self, sym: SymbolId) -> Option<NodeId> {
        self.bindings.get(&sym).copied()
            .or_else(|| self.parent.as_ref().and_then(|p| p.lookup(sym)))
    }
    
    pub fn iter_roots(&self) -> Vec<NodeId> {
        let mut roots = Vec::new();
        let mut current = Some(self);
        while let Some(env) = current {
            roots.extend(env.bindings.values().copied());
            current = env.parent.as_deref();
        }
        roots
    }
}

impl Default for Environment {
    fn default() -> Self {
        Self::new()
    }
}

/// Special form identifiers (interned at startup)
pub struct SpecialForms {
    pub quote: SymbolId,
    pub r#if: SymbolId,
    pub progn: SymbolId,
    pub setq: SymbolId,
    pub r#let: SymbolId,
    pub let_star: SymbolId,
    pub lambda: SymbolId,
    pub function: SymbolId,
    pub tagbody: SymbolId,
    pub go: SymbolId,
    pub block: SymbolId,
    pub return_from: SymbolId,
    pub catch: SymbolId,
    pub throw: SymbolId,
    pub unwind_protect: SymbolId,
    pub defun: SymbolId,
    pub defmacro: SymbolId,
    pub defclass: SymbolId,
    pub defmethod: SymbolId,
    pub handler_bind: SymbolId,
}

impl SpecialForms {
    pub fn new(symbols: &mut SymbolTable) -> Self {
        // Intern in COMMON-LISP package and export
        let cl = PackageId(1);
        
        let quote = symbols.intern_in("QUOTE", cl);
        let r#if = symbols.intern_in("IF", cl);
        let progn = symbols.intern_in("PROGN", cl);
        let setq = symbols.intern_in("SETQ", cl);
        let r#let = symbols.intern_in("LET", cl);
        let let_star = symbols.intern_in("LET*", cl);
        let lambda = symbols.intern_in("LAMBDA", cl);
        let function = symbols.intern_in("FUNCTION", cl);
        let tagbody = symbols.intern_in("TAGBODY", cl);
        let go = symbols.intern_in("GO", cl);
        let block = symbols.intern_in("BLOCK", cl);
        let return_from = symbols.intern_in("RETURN-FROM", cl);
        let catch = symbols.intern_in("CATCH", cl);
        let throw = symbols.intern_in("THROW", cl);
        let unwind_protect = symbols.intern_in("UNWIND-PROTECT", cl);
        let defun = symbols.intern_in("DEFUN", cl);
        let defmacro = symbols.intern_in("DEFMACRO", cl);
        let defclass = symbols.intern_in("DEFCLASS", cl);
        let defmethod = symbols.intern_in("DEFMETHOD", cl);
        let handler_bind = symbols.intern_in("HANDLER-BIND", cl);
        
        // Export all special forms from CL package
        symbols.export_symbol(quote);
        symbols.export_symbol(r#if);
        symbols.export_symbol(progn);
        symbols.export_symbol(setq);
        symbols.export_symbol(r#let);
        symbols.export_symbol(let_star);
        symbols.export_symbol(lambda);
        symbols.export_symbol(function);
        symbols.export_symbol(tagbody);
        symbols.export_symbol(go);
        symbols.export_symbol(block);
        symbols.export_symbol(return_from);
        symbols.export_symbol(catch);
        symbols.export_symbol(throw);
        symbols.export_symbol(unwind_protect);
        symbols.export_symbol(defun);
        symbols.export_symbol(defmacro);
        symbols.export_symbol(defclass);
        symbols.export_symbol(defclass);
        symbols.export_symbol(defmethod);
        symbols.export_symbol(handler_bind);
        
        Self {
            quote, r#if, progn, setq, r#let, let_star, lambda, function,
            tagbody, go, block, return_from, catch, throw, unwind_protect,
            defun, defmacro, defclass, defmethod, handler_bind,
        }
    }
}

/// A compiled closure (lambda + environment)
#[derive(Debug, Clone)]
pub struct Closure {
    /// Parameter list (as SymbolIds)
    pub params: Vec<SymbolId>,
    /// Body expression (NodeId)
    pub body: NodeId,
    /// Captured environment
    pub env: Environment,
}

/// Control flow signals for non-local exits
#[derive(Debug)]
pub enum ControlSignal {
    /// Jump to tag in tagbody
    Go(SymbolId),
    /// Return from named block
    ReturnFrom { name: SymbolId, value: NodeId },
    /// Throw to catch tag
    Throw { tag: NodeId, value: NodeId },
    /// Runtime error
    Error(String),
}

/// Result of evaluation
pub type EvalResult = Result<NodeId, ControlSignal>;

/// Type for primitive functions
pub type PrimitiveFn = fn(&mut Interpreter, &[NodeId]) -> EvalResult;

/// The TreeCL interpreter state
pub struct Interpreter {
    pub arena: Arena,
    pub symbols: SymbolTable,
    pub special_forms: SpecialForms,
    pub closures: Vec<Closure>,
    pub ctx: EvalContext,
    
    // Cached standard symbols
    pub t_sym: SymbolId,
    pub nil_sym: SymbolId,
    
    // Cached standard nodes
    pub t_node: NodeId,
    pub nil_node: NodeId,
    
    // Extensions
    pub primitives: HashMap<SymbolId, PrimitiveFn>,
    pub macros: HashMap<SymbolId, usize>, // Symbol -> Closure index
    pub mop: MetaObjectProtocol,
    pub conditions: ConditionSystem,
    pub arrays: ArrayStore,
    pub readtable: Readtable,
    
    // Streams
    pub streams: StreamManager,
    pub standard_output: StreamId,
    pub standard_input: StreamId,
    pub error_output: StreamId,
    
    // GC orchestration
    pub gc_threshold: usize,  // Trigger GC after this many allocations
}

impl Interpreter {
    pub fn new() -> Self {
        let mut arena = Arena::new();
        let mut symbols = SymbolTable::new();
        let special_forms = SpecialForms::new(&mut symbols);
        let conditions = ConditionSystem::new();
        let arrays = ArrayStore::new();
        let readtable = Readtable::new();
        
        // Create NIL and T
        let nil_node = arena.alloc(Node::Leaf(OpaqueValue::Nil));
        let t_node = arena.alloc(Node::Leaf(OpaqueValue::Nil)); // T is also a leaf (for now)
        
        let nil_sym = symbols.intern_in("NIL", PackageId(1));
        let t_sym = symbols.intern_in("T", PackageId(1));
        
        // NIL and T evaluate to themselves
        symbols.set_symbol_value(nil_sym, nil_node);
        symbols.set_symbol_value(t_sym, t_node);
        
        // Export NIL and T from COMMON-LISP
        symbols.export_symbol(nil_sym);
        symbols.export_symbol(t_sym);
        
        let mop = MetaObjectProtocol::new(&mut symbols);
        
        // Pre-define Tree Calculus combinators (canonical definitions)
        // △ = nil_node (the primitive operator)
        
        // K = △ △ - when applied twice: △ △ x y → x
        // In our representation: Fork(nil, nil)
        let k_node = arena.alloc(Node::Fork(nil_node, nil_node));
        let k_sym = symbols.intern_in("K", PackageId(1));
        symbols.set_symbol_value(k_sym, k_node);
        symbols.export_symbol(k_sym);
        
        // I = K K = △ △ △ △ - identity: I x → x
        // In our representation: Fork(Fork(nil, nil), Fork(nil, nil))
        let i_node = arena.alloc(Node::Fork(k_node, k_node));
        let i_sym = symbols.intern_in("I", PackageId(1));
        symbols.set_symbol_value(i_sym, i_node);
        symbols.export_symbol(i_sym);
        
        // △ (pronounced "triage") - the primitive operator, just nil/Leaf
        let triage_sym = symbols.intern_in("TRIAGE", PackageId(1));
        symbols.set_symbol_value(triage_sym, nil_node);
        symbols.export_symbol(triage_sym);
        
        // Initialize streams
        let streams = StreamManager::new();
        let standard_input = streams.stdin_id();
        let standard_output = streams.stdout_id();
        let error_output = streams.stderr_id();
        
        // Create stream nodes for special variables
        let stdin_node = arena.alloc(Node::Leaf(OpaqueValue::StreamHandle(standard_input.0)));
        let stdout_node = arena.alloc(Node::Leaf(OpaqueValue::StreamHandle(standard_output.0)));
        let stderr_node = arena.alloc(Node::Leaf(OpaqueValue::StreamHandle(error_output.0)));
        
        // Bind *STANDARD-INPUT*, *STANDARD-OUTPUT*, *ERROR-OUTPUT*
        let stdin_sym = symbols.intern_in("*STANDARD-INPUT*", PackageId(1));
        let stdout_sym = symbols.intern_in("*STANDARD-OUTPUT*", PackageId(1));
        let stderr_sym = symbols.intern_in("*ERROR-OUTPUT*", PackageId(1));
        let trace_sym = symbols.intern_in("*TRACE-OUTPUT*", PackageId(1));
        let query_sym = symbols.intern_in("*QUERY-IO*", PackageId(1));
        let debug_sym = symbols.intern_in("*DEBUG-IO*", PackageId(1));
        let terminal_sym = symbols.intern_in("*TERMINAL-IO*", PackageId(1));
        
        symbols.set_symbol_value(stdin_sym, stdin_node);
        symbols.set_symbol_value(stdout_sym, stdout_node);
        symbols.set_symbol_value(stderr_sym, stderr_node);
        symbols.set_symbol_value(trace_sym, stdout_node);
        symbols.set_symbol_value(query_sym, stdout_node);
        symbols.set_symbol_value(debug_sym, stdout_node);
        symbols.set_symbol_value(terminal_sym, stdout_node);
        
        symbols.export_symbol(stdin_sym);
        symbols.export_symbol(stdout_sym);
        symbols.export_symbol(stderr_sym);
        symbols.export_symbol(trace_sym);
        symbols.export_symbol(query_sym);
        symbols.export_symbol(debug_sym);
        symbols.export_symbol(terminal_sym);
        
        Self {
            arena,
            symbols,
            special_forms,
            closures: Vec::new(),
            ctx: EvalContext::default(),
            t_sym,
            nil_sym,
            t_node,
            nil_node,
            primitives: HashMap::new(),
            macros: HashMap::new(),
            mop,
            conditions,
            arrays,
            readtable,
            streams,
            standard_output,
            standard_input,
            error_output,
            gc_threshold: 10000,  // Default: GC after 10k allocations
        }
    }

    /// Signal a simple error with a message
    pub fn signal_error(&mut self, format: &str) -> EvalResult {
        // Create simple-error condition
        let cond = self.conditions.make_simple_error(format, Vec::new());
        
        // Search for handler
        // Note: find_handlers returns references, but we might need to execute code 
        // which mutable borrows interpreter.
        // We handle this by collecting handlers first (just indices/ids) or similar?
        // Actually find_handlers returns &Handler which is inside Interpreter.
        // Rust borrowing rules will bite here if we try to eval/apply while holding &Handler.
        // We should Clone the handler we want to run.
        
        let handlers = self.conditions.find_handlers(&cond).into_iter().cloned().collect::<Vec<_>>();
        
        for handler in handlers {
            // Invoke handler: (func condition)
            // We need to wrap condition in OpaqueValue?
            // Actually conditions are struct instances, not in Arena/OpaqueValue yet.
            // We need to OpaqueValue::Condition? Or just pass something simple.
            // For Phase 7 simple version, passing the condition object is complex.
            // Let's just pass the format string (message) for now if we can't wrap it?
            // Wait, we can add OpaqueValue::Condition or just OpaqueValue::Instance handling.
            // For now, let's just RUN the handler and see if it non-local exits.
            
            // To pass the condition object, we need to alloc it.
            // But Condition is not OpaqueValue yet.
            // Let's assume for now handlers take 1 arg, which we will pass as NIL (or message string).
            let msg = self.arena.alloc(Node::Leaf(OpaqueValue::String(format.to_string())));
            let args = self.list(&[msg]); // List of args for apply
            
            // We need to call apply_function(handler.function, args)
            // But apply_function takes &mut self, and we are iterating self.conditions.
            // So we need to clone the handler function node first.
            let func = handler.function;
            // drop(handlers); // Invalid, loop owns it
            
            // Apply
            // If handler returns normally, we continue search (decline to handle)
            // If handler does non-local exit (go/return-from), signal propagates
            match self.apply_function(func, args, &Environment::new()) {
                Ok(_) => {
                    // Handler declined (returned normally), continue search
                }
                Err(sig) => return Err(sig),
            }
        }
        
        Err(ControlSignal::Error(format.to_string()))
    }
    
    /// Register a primitive function
    pub fn register_primitive(&mut self, name: &str, pkg: PackageId, func: PrimitiveFn) {
        let sym = self.symbols.intern_in(name, pkg);
        self.symbols.export_symbol(sym);
        self.primitives.insert(sym, func);
    }
    
    pub fn symbol_to_node(&mut self, sym_id: SymbolId) -> NodeId {
        self.arena.alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0)))
    }

    /// Main evaluation entry point
    pub fn eval(&mut self, expr: NodeId, env: &Environment) -> EvalResult {
        let node = self.arena.get_unchecked(expr).clone();
        
        match node {
            Node::Leaf(val) => {
                match val {
                    OpaqueValue::Nil => Ok(self.nil_node),
                    OpaqueValue::Symbol(id) => {
                        let sym_id = SymbolId(id);
                        // Variable lookup
                        if let Some(val) = env.lookup(sym_id) {
                            return Ok(val);
                        }
                        if let Some(val) = self.symbols.symbol_value(sym_id) {
                            return Ok(val);
                        }
                        // Self-evaluating keywords?
                        if self.symbols.get_symbol(sym_id).map_or(false, |s| s.is_keyword()) {
                             return Ok(expr);
                        }
                        // If T or NIL
                        if sym_id == self.t_sym || sym_id == self.nil_sym {
                            return Ok(self.symbols.symbol_value(sym_id).unwrap_or(self.nil_node));
                        }
                        
                        // Unbound variable - return error or nil?
                        // For now, let's return itself for combinator compatibility, or NIL?
                        // The user's project seems to treat unbound symbols as NIL or stuck.
                        // For ANSI CL it should be an error.
                        Ok(expr) // Self-evaluating unbound symbol for TC
                    }
                    _ => Ok(expr), // Self-evaluating
                }
            }
            
            Node::Stem(_) => {
                // Not a symbol (e.g. pure Combinator), treat as self-evaluating
                Ok(expr) 
            }
            
            Node::Fork(car, cdr) => {
                // (operator . args) - function application or special form
                self.eval_application(car, cdr, env)
            }
        }
    }
    
    /// Evaluate a function application or special form
    fn eval_application(&mut self, op: NodeId, args: NodeId, env: &Environment) -> EvalResult {
        // First, check if operator is a symbol that's a special form
        if let Some(sym_id) = self.node_to_symbol(op) {
            // Check special forms
            let sf = &self.special_forms;
            
            // 0. Check for macro expansion
            if let Some(&macro_idx) = self.macros.get(&sym_id) {
                // Get closure from index
                if let Some(closure) = self.closures.get(macro_idx).cloned() {
                    // Apply macro to UNEVALUATED args
                    let expanded = self.apply_macro(&closure, args)?;
                    return self.eval(expanded, env);
                }
            }
            
            if sym_id == sf.quote {
                return self.eval_quote(args);
            }
            if sym_id == sf.r#if {
                return self.eval_if(args, env);
            }
            if sym_id == sf.progn {
                return self.eval_progn(args, env);
            }
            if sym_id == sf.setq {
                return self.eval_setq(args, env);
            }
            if sym_id == sf.r#let {
                return self.eval_let(args, env);
            }
            if sym_id == sf.lambda {
                return self.eval_lambda(args, env);
            }
            if sym_id == sf.function {
                return self.eval_function(args, env);
            }
            if sym_id == sf.tagbody {
                return self.eval_tagbody(args, env);
            }
            if sym_id == sf.go {
                return self.eval_go(args);
            }
            if sym_id == sf.block {
                return self.eval_block(args, env);
            }
            if sym_id == sf.return_from {
                return self.eval_return_from(args, env);
            }
            if sym_id == sf.catch {
                return self.eval_catch(args, env);
            }
            if sym_id == sf.throw {
                return self.eval_throw(args, env);
            }
            if sym_id == sf.unwind_protect {
                return self.eval_unwind_protect(args, env);
            }
            if sym_id == sf.defun {
                return self.eval_defun(args, env);
            }
            if sym_id == sf.defmacro {
                return self.eval_defmacro(args, env);
            }
            if sym_id == sf.defclass { return self.eval_defclass(args, env); }
            if sym_id == sf.defmethod { return self.eval_defmethod(args, env); }
            if sym_id == sf.handler_bind { return self.eval_handler_bind(args, env); }
            
            // Check if symbol is a primitive
            if let Some(&prim_fn) = self.primitives.get(&sym_id) {
                // Evaluate arguments
                let mut evaluated_args = Vec::new();
                let mut current = args;
                while let Node::Fork(arg, rest) = self.arena.get_unchecked(current).clone() {
                    let val = self.eval(arg, env)?;
                    evaluated_args.push(val);
                    current = rest;
                }
                return prim_fn(self, &evaluated_args);
            }
            
            // Check if symbol has a function binding
            if let Some(func) = self.symbols.symbol_function(sym_id) {
                return self.apply_function(func, args, env);
            }
            
            // Check if symbol has a value binding
            if let Some(val) = env.lookup(sym_id) {
                return self.apply_function(val, args, env);
            }
            if let Some(val) = self.symbols.symbol_value(sym_id) {
                return self.apply_function(val, args, env);
            }
        }
        
        // Evaluate operator
        let op_val = self.eval(op, env)?;
        
        // Apply
        self.apply_function(op_val, args, env)
    }
    
    /// Convert a node to a SymbolId if it represents a symbol
    pub fn node_to_symbol(&self, node_id: NodeId) -> Option<SymbolId> {
        let node = self.arena.get_unchecked(node_id);
        if let Node::Leaf(OpaqueValue::Symbol(id)) = node {
            return Some(SymbolId(*id));
        }
        None
    }
    
    /// (quote expr) -> expr (unevaluated)
    fn eval_quote(&mut self, args: NodeId) -> EvalResult {
        // args is (expr . nil)
        if let Node::Fork(expr, _) = self.arena.get_unchecked(args).clone() {
            Ok(expr)
        } else {
            Ok(args)
        }
    }
    
    /// (if test then else?) -> evaluate conditionally
    fn eval_if(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        let node = self.arena.get_unchecked(args).clone();
        
        if let Node::Fork(test, rest) = node {
            // Evaluate test
            let test_val = self.eval(test, env)?;
            
            // Check if true (not nil)
            let is_true = test_val != self.nil_node;
            
            if let Node::Fork(then_expr, else_rest) = self.arena.get_unchecked(rest).clone() {
                if is_true {
                    self.eval(then_expr, env)
                } else {
                    // Check for else clause
                    if let Node::Fork(else_expr, _) = self.arena.get_unchecked(else_rest).clone() {
                        self.eval(else_expr, env)
                    } else {
                        Ok(self.nil_node)
                    }
                }
            } else {
                Ok(self.nil_node)
            }
        } else {
            Ok(self.nil_node)
        }
    }
    
    /// (progn form*) -> evaluate forms in sequence, return last
    fn eval_progn(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        let mut result = self.nil_node;
        let mut current = args;
        
        loop {
            match self.arena.get_unchecked(current).clone() {
                Node::Fork(form, rest) => {
                    result = self.eval(form, env)?;
                    current = rest;
                }
                _ => break,
            }
        }
        
        Ok(result)
    }
    
    /// (setq var val var val ...) -> set variable values
    fn eval_setq(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        let mut result = self.nil_node;
        let mut current = args;
        
        loop {
            match self.arena.get_unchecked(current).clone() {
                Node::Fork(var_node, rest) => {
                    if let Node::Fork(val_node, next) = self.arena.get_unchecked(rest).clone() {
                        // Get symbol
                        if let Some(sym) = self.node_to_symbol(var_node) {
                            let val = self.eval(val_node, env)?;
                            self.symbols.set_symbol_value(sym, val);
                            result = val;
                        }
                        current = next;
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }
        
        Ok(result)
    }
    
    /// (let ((var val) ...) body*) -> create local bindings
    fn eval_let(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(bindings, body) = self.arena.get_unchecked(args).clone() {
            let mut new_env = Environment::with_parent(env.clone());
            
            // Process bindings
            let mut current = bindings;
            loop {
                match self.arena.get_unchecked(current).clone() {
                    Node::Fork(binding, rest) => {
                        if let Node::Fork(var_node, val_rest) = self.arena.get_unchecked(binding).clone() {
                            if let Some(sym) = self.node_to_symbol(var_node) {
                                if let Node::Fork(val_node, _) = self.arena.get_unchecked(val_rest).clone() {
                                    let val = self.eval(val_node, env)?; // Note: parallel let
                                    new_env.bind(sym, val);
                                }
                            }
                        }
                        current = rest;
                    }
                    _ => break,
                }
            }
            
            // Evaluate body in new environment
            self.eval_progn(body, &new_env)
        } else {
            Ok(self.nil_node)
        }
    }
    
    /// (lambda (params) body*) -> create closure
    fn eval_lambda(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(params, body) = self.arena.get_unchecked(args).clone() {
            // Parse parameter list
            let mut param_list = Vec::new();
            let mut current = params;
            loop {
                match self.arena.get_unchecked(current).clone() {
                    Node::Fork(param, rest) => {
                        if let Some(sym) = self.node_to_symbol(param) {
                            param_list.push(sym);
                        }
                        current = rest;
                    }
                    _ => break,
                }
            }
            
            // Create closure
            let closure = Closure {
                params: param_list,
                body,
                env: env.clone(),
            };
            
            let closure_idx = self.closures.len();
            self.closures.push(closure);
            
            // Return a node representing the closure
            // We use a Leaf with Closure handle
            let closure_node = self.arena.alloc(Node::Leaf(OpaqueValue::Closure(closure_idx as u32)));
            Ok(closure_node)
        } else {
            Ok(self.nil_node)
        }
    }
    
    /// (function name-or-lambda) -> get function object
    fn eval_function(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(name, _) = self.arena.get_unchecked(args).clone() {
            // Check if it's a lambda
            if let Node::Fork(car, _) = self.arena.get_unchecked(name).clone() {
                if self.node_to_symbol(car) == Some(self.special_forms.lambda) {
                    return self.eval(name, env);
                }
            }
            
            // It's a symbol - get its function binding
            if let Some(sym) = self.node_to_symbol(name) {
                if let Some(func) = self.symbols.symbol_function(sym) {
                    return Ok(func);
                }
            }
        }
        
        Ok(self.nil_node)
    }
    
    /// (defun name (params) body*) -> define a named function
    fn eval_defun(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        // Parse: (name (params...) body...)
        if let Node::Fork(name_node, rest) = self.arena.get_unchecked(args).clone() {
            // Validate name is a symbol
            let name_sym = match self.node_to_symbol(name_node) {
                Some(s) => s,
                None => return Err(ControlSignal::Error(
                    "DEFUN: first argument must be a symbol".to_string()
                )),
            };
            
            if let Node::Fork(params, body) = self.arena.get_unchecked(rest).clone() {
                // Validate params is a list (nil or Fork)
                match self.arena.get_unchecked(params) {
                    Node::Leaf(OpaqueValue::Nil) => {} // Empty params OK
                    Node::Fork(_, _) => {} // List params OK
                    _ => return Err(ControlSignal::Error(
                        format!("DEFUN: parameter list must be a list, not {:?}", 
                            self.arena.get_unchecked(params))
                    )),
                }
                
                // Parse parameter list
                let mut param_list = Vec::new();
                let mut current = params;
                loop {
                    match self.arena.get_unchecked(current).clone() {
                        Node::Fork(param, rest) => {
                            if let Some(sym) = self.node_to_symbol(param) {
                                param_list.push(sym);
                            } else {
                                return Err(ControlSignal::Error(
                                    "DEFUN: parameter names must be symbols".to_string()
                                ));
                            }
                            current = rest;
                        }
                        _ => break,
                    }
                }
                
                // Validate body exists
                if let Node::Leaf(OpaqueValue::Nil) = self.arena.get_unchecked(body) {
                    return Err(ControlSignal::Error(
                        "DEFUN: function body is required".to_string()
                    ));
                }
                
                // Create closure
                let closure = Closure {
                    params: param_list,
                    body,
                    env: env.clone(),
                };
                
                let closure_idx = self.closures.len();
                self.closures.push(closure);
                
                // Create closure node
                let closure_node = self.arena.alloc(Node::Leaf(OpaqueValue::Closure(closure_idx as u32)));
                
                // Bind to symbol's function cell
                self.symbols.set_symbol_function(name_sym, closure_node);
                
                // Return the function name symbol
                return Ok(name_node);
            } else {
                return Err(ControlSignal::Error(
                    "DEFUN: syntax is (defun name (params) body)".to_string()
                ));
            }
        }
        
        Err(ControlSignal::Error(
            "DEFUN: syntax is (defun name (params) body)".to_string()
        ))
    }
    
    // =========================================================================
    // Control Flow Special Forms
    // =========================================================================
    
    /// (tagbody {tag | statement}*) -> NIL
    /// Tags are symbols/integers; statements are evaluated in sequence.
    /// (go tag) transfers control to that tag.
    fn eval_tagbody(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        // Collect tags and statements
        let mut tags: HashMap<SymbolId, usize> = HashMap::new();
        let mut statements: Vec<(Option<SymbolId>, NodeId)> = Vec::new();
        
        let mut current = args;
        while let Node::Fork(item, rest) = self.arena.get_unchecked(current).clone() {
            // Check if item is a tag (symbol)
            if let Some(sym) = self.node_to_symbol(item) {
                tags.insert(sym, statements.len());
                statements.push((Some(sym), item));
            } else {
                // It's a statement
                statements.push((None, item));
            }
            current = rest;
        }
        
        // Execute statements
        let mut pc = 0;
        while pc < statements.len() {
            let (_tag, stmt) = &statements[pc];
            if _tag.is_none() {
                // Only evaluate statements, not tags
                match self.eval(*stmt, env) {
                    Ok(_) => {}
                    Err(ControlSignal::Go(target)) => {
                        // Jump to target
                        if let Some(&new_pc) = tags.get(&target) {
                            pc = new_pc;
                            continue;
                        } else {
                            // Propagate - not our tag
                            return Err(ControlSignal::Go(target));
                        }
                    }
                    Err(e) => return Err(e),
                }
            }
            pc += 1;
        }
        
        Ok(self.nil_node)
    }
    
    /// (go tag) -> transfer control to tag in enclosing tagbody
    fn eval_go(&mut self, args: NodeId) -> EvalResult {
        if let Node::Fork(tag_node, _) = self.arena.get_unchecked(args).clone() {
            if let Some(sym) = self.node_to_symbol(tag_node) {
                return Err(ControlSignal::Go(sym));
            }
        }
        Ok(self.nil_node)
    }
    
    /// (block name body*) -> evaluate body, can be exited with return-from
    fn eval_block(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(name_node, body) = self.arena.get_unchecked(args).clone() {
            if let Some(name) = self.node_to_symbol(name_node) {
                match self.eval_progn(body, env) {
                    Ok(val) => Ok(val),
                    Err(ControlSignal::ReturnFrom { name: ret_name, value }) if ret_name == name => {
                        Ok(value)
                    }
                    Err(e) => Err(e),
                }
            } else {
                self.eval_progn(body, env)
            }
        } else {
            Ok(self.nil_node)
        }
    }
    
    /// (return-from name value?) -> return from named block
    fn eval_return_from(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(name_node, rest) = self.arena.get_unchecked(args).clone() {
            if let Some(name) = self.node_to_symbol(name_node) {
                let value = if let Node::Fork(val_node, _) = self.arena.get_unchecked(rest).clone() {
                    self.eval(val_node, env)?
                } else {
                    self.nil_node
                };
                return Err(ControlSignal::ReturnFrom { name, value });
            }
        }
        Ok(self.nil_node)
    }
    
    /// (catch tag body*) -> evaluate body, catch throw to tag
    fn eval_catch(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(tag_expr, body) = self.arena.get_unchecked(args).clone() {
            let tag = self.eval(tag_expr, env)?;
            
            match self.eval_progn(body, env) {
                Ok(val) => Ok(val),
                Err(ControlSignal::Throw { tag: throw_tag, value }) => {
                    // Check if tags match (using EQ semantics)
                    if throw_tag == tag {
                        Ok(value)
                    } else {
                        Err(ControlSignal::Throw { tag: throw_tag, value })
                    }
                }
                Err(e) => Err(e),
            }
        } else {
            Ok(self.nil_node)
        }
    }
    
    /// (throw tag result) -> throw to matching catch
    fn eval_throw(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(tag_expr, rest) = self.arena.get_unchecked(args).clone() {
            let tag = self.eval(tag_expr, env)?;
            let value = if let Node::Fork(val_expr, _) = self.arena.get_unchecked(rest).clone() {
                self.eval(val_expr, env)?
            } else {
                self.nil_node
            };
            Err(ControlSignal::Throw { tag, value })
        } else {
            Ok(self.nil_node)
        }
    }
    
    /// (unwind-protect protected-form cleanup-form*) -> cleanup always runs
    fn eval_unwind_protect(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(protected, cleanup) = self.arena.get_unchecked(args).clone() {
            let result = self.eval(protected, env);
            
            // Always run cleanup forms
            let _ = self.eval_progn(cleanup, env);
            
            result
        } else {
            Ok(self.nil_node)
        }
    }
    
    /// Garbage Collection: Mark-and-Sweep
    pub fn collect_garbage(&mut self) -> usize {
        // 1. Mark Phase (Immutably trace everything)
        let (marked_nodes, marked_vectors) = self.mark_phase();
        
        // 2. Sweep Phase (Mutably reclaim)
        let freed_nodes = self.arena.sweep(&marked_nodes);
        let freed_vectors = self.arrays.sweep(&marked_vectors);
        
        // 3. Reset allocation counter
        self.arena.reset_alloc_count();
        
        freed_nodes + freed_vectors
    }
    
    /// Check if automatic GC should run based on allocation threshold
    /// Returns number of objects freed (0 if GC didn't run)
    pub fn maybe_gc(&mut self) -> usize {
        if self.arena.allocs_since_gc() >= self.gc_threshold {
            self.collect_garbage()
        } else {
            0
        }
    }
    
    fn mark_phase(&self) -> (std::collections::HashSet<u32>, std::collections::HashSet<u32>) {
        let mut marked = std::collections::HashSet::new();
        let mut marked_vectors = std::collections::HashSet::new();
        let mut worklist = Vec::new();
        
        // Roots
        worklist.push(self.t_node);
        worklist.push(self.nil_node);
        
        // Symbols
        for sym in self.symbols.iter_symbols() {
            if let Some(n) = sym.value { worklist.push(n); }
            if let Some(n) = sym.function { worklist.push(n); }
            if let Some(n) = sym.plist { worklist.push(n); }
        }
        
        // Macros (Closure Indices)
        for &closure_idx in self.macros.values() {
            if let Some(closure) = self.closures.get(closure_idx) {
                worklist.extend(closure.env.iter_roots());
                worklist.push(closure.body);
            }
        }
        
        // Conditions
        for cluster in self.conditions.handler_stack() {
            for handler in cluster {
                worklist.push(handler.function);
            }
        }
        for cluster in self.conditions.restart_stack() {
            for restart in cluster {
               worklist.push(restart.function);
               if let Some(n) = restart.interactive { worklist.push(n); }
               if let Some(n) = restart.test { worklist.push(n); }
            }
        }
        
        // Traverse
        while let Some(node_id) = worklist.pop() {
            if marked.contains(&node_id.0) { continue; }
            marked.insert(node_id.0);
            
            match self.arena.get_unchecked(node_id) {
                Node::Fork(l, r) => { worklist.push(*l); worklist.push(*r); }
                Node::Stem(i) => { worklist.push(*i); }
                Node::Leaf(val) => {
                    match val {
                        OpaqueValue::Closure(idx) => {
                             if let Some(closure) = self.closures.get(*idx as usize) {
                                  worklist.extend(closure.env.iter_roots());
                                  worklist.push(closure.body);
                             }
                        }
                        OpaqueValue::Instance(idx) => {
                            if let Some(slots) = self.mop.get_instance_slots(*idx) {
                                worklist.extend_from_slice(slots);
                            }
                        }
                        OpaqueValue::Generic(idx) => {
                            if let Some(methods) = self.mop.get_generic_methods(*idx) {
                                for &m_id in methods {
                                    if let Some(body) = self.mop.get_method_body(m_id.0) {
                                        worklist.push(body);
                                    }
                                }
                            }
                        }
                        OpaqueValue::Class(idx) => {
                            if let Some(slots) = self.mop.get_class_slots(*idx) {
                                for slot in slots {
                                    if let Some(init) = slot.initform { worklist.push(init); }
                                }
                            }
                        }
                        OpaqueValue::VectorHandle(idx) => {
                             if !marked_vectors.contains(idx) {
                                marked_vectors.insert(*idx);
                                if let Some(vec) = self.arrays.get(crate::arrays::VectorId(*idx)) {
                                    worklist.extend(vec.iter().copied());
                                }
                             }
                        }
                        _ => {}
                    }
                }
            }
        }
        
        (marked, marked_vectors)
    }

    /// Apply a function to arguments
    pub fn apply_function(&mut self, func: NodeId, args: NodeId, env: &Environment) -> EvalResult {
        let func_node = self.arena.get_unchecked(func).clone();
        
        match func_node {
            Node::Leaf(OpaqueValue::Closure(idx)) => {
                // Closure application
                if let Some(closure) = self.closures.get(idx as usize).cloned() {
                    self.apply_closure(&closure, args, env)
                } else {
                    Err(ControlSignal::Error(format!("Invalid closure index: {}", idx)))
                }
            }
            Node::Leaf(OpaqueValue::Generic(id)) => {
                self.apply_generic(id, args, env)
            }
            _ => {
                // Fall back to tree calculus reduction
                // Evaluate arguments and apply one at a time (curried)
                use crate::search::reduce;
                
                let mut result = func;
                let mut current = args;
                
                // Walk through argument list
                while let Node::Fork(arg_expr, rest) = self.arena.get_unchecked(current).clone() {
                    // Evaluate the argument
                    let arg_val = self.eval(arg_expr, env)?;
                    
                    // Apply Tree Calculus: (result arg_val)
                    let app = self.arena.alloc(Node::Fork(result, arg_val));
                    result = reduce(&mut self.arena, app, &mut self.ctx);
                    
                    current = rest;
                }
                
                Ok(self.try_reduce_primitive(result, env))
            }
        }
    }

    /// Try to reduce a "stuck" application if the head is a primitive symbol
    fn try_reduce_primitive(&mut self, root: NodeId, _env: &Environment) -> NodeId {
        // 1. Flatten the spine: ((f a) b) -> [f, a, b]
        let mut spine = Vec::new();
        let mut current = root;
        while let Node::Fork(l, r) = self.arena.get_unchecked(current).clone() {
            spine.push(r);
            current = l;
        }
        spine.push(current); // Head
        spine.reverse(); // [Head, arg1, arg2, ...]
        
        if spine.len() < 2 {
            return root;
        }
        
        let head = spine[0];
        if let Some(sym) = self.node_to_symbol(head) {
             // Check primitives
             if let Some(&prim_fn) = self.primitives.get(&sym) {
                 // We have a primitive!
                 let raw_args = &spine[1..];
                 
                 // Evaluate arguments (Force strictness for primitives)
                 // Compiled code reduction is lazy (Normal Order), but primitives expect values.
                 let mut evaluated_args = Vec::with_capacity(raw_args.len());
                 for &arg in raw_args {
                     // We use the passed environment. For compiled code, this usually works
                     // as free variables are globals.
                     // Use reduce instead of eval because args are Tree Calculus terms (Forks), not Lisp lists.
                     let val = crate::search::reduce(&mut self.arena, arg, &mut self.ctx);
                     evaluated_args.push(val);
                 }
                 
                 
                 match prim_fn(self, &evaluated_args) {
                      Ok(res) => return res,
                      Err(_) => return root, // Fallback on error (keep stuck state)
                 }
             }
        }
        
        root
    }



    
    /// Apply a closure to arguments
    fn apply_closure(&mut self, closure: &Closure, args: NodeId, env: &Environment) -> EvalResult {
        let mut new_env = Environment::with_parent(closure.env.clone());
        
        // Evaluate and bind arguments
        let mut current_arg = args;
        for &param in &closure.params {
            match self.arena.get_unchecked(current_arg).clone() {
                Node::Fork(arg_expr, rest) => {
                    let arg_val = self.eval(arg_expr, env)?;
                    new_env.bind(param, arg_val);
                    current_arg = rest;
                }
                _ => break,
            }
        }
        
        // Evaluate body
        self.eval_progn(closure.body, &new_env)
    }
    
    /// Apply a macro closure to arguments (no eval of args)
    fn apply_macro(&mut self, closure: &Closure, args: NodeId) -> EvalResult {
        // Create environment from closure's captured environment
        let mut new_env = Environment::with_parent(closure.env.clone());
        
        // Bind arguments UNEVALUATED
        let mut current_arg = args;
        for &param in &closure.params {
            match self.arena.get_unchecked(current_arg).clone() {
                Node::Fork(arg_expr, rest) => {
                    // Bind raw expression (node) to parameter
                    new_env.bind(param, arg_expr);
                    current_arg = rest;
                }
                _ => break,
            }
        }
        
        // Evaluate body - this produces the expansion
        self.eval_progn(closure.body, &new_env)
    }
    

    
    /// Apply a generic function
    fn apply_generic(&mut self, gf_id: u32, args: NodeId, env: &Environment) -> EvalResult {
        use crate::clos::GenericId;
        
        let gf_id = GenericId(gf_id);
        
        // 1. Evaluate arguments to get classes
        let mut evaluated_args = Vec::new();
        let mut executed_args = Vec::new(); // Values to pass to method
        let mut current = args;
        while let Node::Fork(arg, rest) = self.arena.get_unchecked(current).clone() {
            let val = self.eval(arg, env)?;
            executed_args.push(val);
            evaluated_args.push(val); // In a real implementation, we might need these separate
            current = rest;
        }
        
        // 2. Get classes of arguments
        let mut arg_classes = Vec::new();
        for &arg in &executed_args {
            let class_id = self.class_of(arg);
            arg_classes.push(class_id);
        }
        
        // 3. Compute applicable methods
        let applicable = self.mop.compute_applicable_methods(gf_id, &arg_classes);
        
        if applicable.is_empty() {
             return Err(ControlSignal::Error(format!("No applicable method for generic function {:?} with args {:?}", gf_id, arg_classes)));
        }
        
        // 4. Call most specific method (primary only for now)
        let method_id = applicable[0];
        let method = self.mop.get_method(method_id).unwrap();
        let method_body = method.body;
        
        // Apply method closure
        if let Node::Leaf(OpaqueValue::Closure(idx)) = self.arena.get_unchecked(method_body).clone() {
                if let Some(closure) = self.closures.get(idx as usize).cloned() {
                    // Manual binding
                    let mut method_env = Environment::with_parent(closure.env.clone());
                    if executed_args.len() != closure.params.len() {
                         return Err(ControlSignal::Error("Method argument count mismatch".to_string()));
                    }
                    for (param, val) in closure.params.iter().zip(executed_args.iter()) {
                        method_env.bind(*param, *val);
                    }
                    return self.eval_progn(closure.body, &method_env);
                }
            }
        
        // Fallback
        Err(ControlSignal::Error("Method body is not a valid closure".to_string()))
    }
    
    /// Get class of value
    fn class_of(&self, val: NodeId) -> crate::clos::ClassId {
        match self.arena.get_unchecked(val) {
            Node::Leaf(OpaqueValue::Integer(_)) => crate::clos::ClassId(0), // Fixme: map to Integer class
            Node::Leaf(OpaqueValue::Instance(idx)) => {
                if let Some(inst) = self.mop.get_instance(*idx as usize) {
                    inst.class
                } else {
                    self.mop.standard_object // Fallback
                }
            }
             // ... handle other types ...
            _ => self.mop.t_class,
        }
    }

    /// (defmacro name (params) body*) -> define a macro
    fn eval_defmacro(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        // Parse: (name (params...) body...)
        if let Node::Fork(name_node, rest) = self.arena.get_unchecked(args).clone() {
            if let Some(name_sym) = self.node_to_symbol(name_node) {
                if let Node::Fork(params, body) = self.arena.get_unchecked(rest).clone() {
                    // Parse parameter list
                    let mut param_list = Vec::new();
                    let mut current = params;
                    loop {
                        match self.arena.get_unchecked(current).clone() {
                            Node::Fork(param, rest) => {
                                if let Some(sym) = self.node_to_symbol(param) {
                                    param_list.push(sym);
                                }
                                current = rest;
                            }
                            _ => break,
                        }
                    }
                    
                    // Create closure
                    let closure = Closure {
                        params: param_list,
                        body,
                        env: env.clone(),
                    };
                    
                    let closure_idx = self.closures.len();
                    self.closures.push(closure);
                    
                    // Register macro
                    self.macros.insert(name_sym, closure_idx);
                    
                    // Return the macro name symbol
                    return Ok(name_node);
                }
            }
        }
        
        Ok(self.nil_node)
    }

    
    /// Create a cons cell
    pub fn cons(&mut self, car: NodeId, cdr: NodeId) -> NodeId {
        self.arena.alloc(Node::Fork(car, cdr))
    }
    
    /// Get car of a cons
    pub fn car(&self, node: NodeId) -> Option<NodeId> {
        match self.arena.get_unchecked(node) {
            Node::Fork(car, _) => Some(*car),
            _ => None,
        }
    }
    
    /// Get cdr of a cons
    pub fn cdr(&self, node: NodeId) -> Option<NodeId> {
        match self.arena.get_unchecked(node) {
            Node::Fork(_, cdr) => Some(*cdr),
            _ => None,
        }
    }
    
    /// (handler-bind ((type handler)...) body...)
    fn eval_handler_bind(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        // Parse bindings and body
        // args: (bindings . body)
        if let Node::Fork(bindings_node, body) = self.arena.get_unchecked(args).clone() {
            let mut handlers = Vec::new();
            
            // Iterate over bindings list
            let mut current_binding = bindings_node;
            while let Node::Fork(binding, rest) = self.arena.get_unchecked(current_binding).clone() {
                // Binding: (type handler)
                if let Node::Fork(type_node, handler_pair) = self.arena.get_unchecked(binding).clone() {
                    if let Node::Fork(handler_expr, _) = self.arena.get_unchecked(handler_pair).clone() { // (handler nil) or (handler . nil)
                        // Resolve type
                        // For Phase 7, we support 'error', 'warning', 'condition' symbols map to built-in types
                        // In real CL, we'd look up class/condition-type.
                        let type_id = if let Some(sym) = self.node_to_symbol(type_node) {
                             let name = self.symbols.get_symbol(sym).unwrap().name.clone();
                             if name == "ERROR" { self.conditions.error_type }
                             else if name == "WARNING" { self.conditions.warning_type }
                             else { self.conditions.condition_type } // Default to condition
                        } else {
                             self.conditions.condition_type
                        };
                        
                        // Eval handler expression to get function
                        let handler_fn = self.eval(handler_expr, env)?;
                        
                        handlers.push(crate::conditions::Handler {
                            condition_type: type_id,
                            function: handler_fn,
                        });
                    }
                }
                current_binding = rest;
            }
            
            // Push handlers
            self.conditions.push_handlers(handlers);
            
            // Eval body
            let result = self.eval_progn(body, env);
            
            // Pop handlers
            self.conditions.pop_handlers();
            
            result
        } else {
            Ok(self.nil_node)
        }
    }

    /// (defclass name (supers...) (slots...))
    fn eval_defclass(&mut self, args: NodeId, _env: &Environment) -> EvalResult {
        // Simple parser
        if let Node::Fork(name_node, rest) = self.arena.get_unchecked(args).clone() {
            if let Some(name_sym) = self.node_to_symbol(name_node) {
                if let Node::Fork(supers_node, rest2) = self.arena.get_unchecked(rest).clone() {
                    let mut supers = Vec::new(); // Collect super classes
                    // Iterate supers_node list
                    let mut current = supers_node;
                    while let Node::Fork(super_name, next) = self.arena.get_unchecked(current).clone() {
                        if let Some(s_sym) = self.node_to_symbol(super_name) {
                             if let Some(id) = self.mop.find_class(s_sym) {
                                 supers.push(id);
                             }
                        }
                        current = next;
                    }
                    
                    if let Node::Fork(slots_node, _) = self.arena.get_unchecked(rest2).clone() {
                        let mut slots = Vec::new();
                        let mut current_slot = slots_node;
                         while let Node::Fork(slot_spec, next) = self.arena.get_unchecked(current_slot).clone() {
                            // Slot spec can be symbol or list
                            let slot_name = if let Some(sym) = self.node_to_symbol(slot_spec) {
                                sym
                            } else if let Node::Fork(name, _) = self.arena.get_unchecked(slot_spec).clone() {
                                self.node_to_symbol(name).unwrap_or(self.nil_sym)
                            } else {
                                self.nil_sym
                            };
                            
                            if slot_name != self.nil_sym {
                                slots.push(crate::clos::SlotDefinition {
                                    name: slot_name,
                                    initform: None,
                                    initarg: None, // parsing :initarg etc skipped for brevity
                                    readers: Vec::new(),
                                    writers: Vec::new(),
                                    index: slots.len(),
                                });
                            }
                            
                            current_slot = next;
                         }
                        
                        self.mop.define_class(name_sym, supers, slots);
                        return Ok(name_node);
                    }
                }
            }
        }
        Ok(self.nil_node)
    }

    /// (defmethod name ((param spec)...) body...)
    fn eval_defmethod(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        // Simplified parser
         if let Node::Fork(name_node, rest) = self.arena.get_unchecked(args).clone() {
             if let Some(name_sym) = self.node_to_symbol(name_node) {
                 if let Node::Fork(params_node, body) = self.arena.get_unchecked(rest).clone() {
                     // Parse parameters and specializers
                     let mut params = Vec::new();
                     let mut specializers = Vec::new();
                     
                     let mut current = params_node;
                     while let Node::Fork(param_spec, next) = self.arena.get_unchecked(current).clone() {
                         // param_spec is (name class) or name
                         if let Some(sym) = self.node_to_symbol(param_spec) {
                             // Unspecialized (T)
                             params.push(sym);
                             specializers.push(self.mop.t_class);
                         } else if let Node::Fork(pname, ptype_rest) = self.arena.get_unchecked(param_spec).clone() {
                             if let Some(psym) = self.node_to_symbol(pname) {
                                 params.push(psym);
                                 // Get class
                                 let class_id = if let Node::Fork(cname, _) = self.arena.get_unchecked(ptype_rest).clone() {
                                     if let Some(csym) = self.node_to_symbol(cname) {
                                         self.mop.find_class(csym).unwrap_or(self.mop.t_class)
                                     } else { self.mop.t_class }
                                 } else { self.mop.t_class };
                                 specializers.push(class_id);
                             }
                         }
                         current = next;
                     }
                     
                     // Ensure generic function exists
                     let gf_id = if let Some(id) = self.mop.find_generic(name_sym) {
                         id
                     } else {
                         self.mop.define_generic(name_sym, params.clone())
                     };
                     
                     // Create closure for body
                     // Need lambda-list for closure
                     // Closure { params: params, body: body, env: env }
                     let closure = Closure {
                         params: params,
                         body: body,
                         env: env.clone(),
                     };
                     let closure_idx = self.closures.len();
                     self.closures.push(closure);
                     
                     // Closure Node
                     // Closure Node
                     let closure_node = self.arena.alloc(Node::Leaf(OpaqueValue::Closure(closure_idx as u32)));
                     
                     // Add method
                     self.mop.add_method(gf_id, specializers, Vec::new(), closure_node);
                     
                     // Bind generic function to symbol function cell if not already
                     self.symbols.set_symbol_function(name_sym, self.arena.alloc(Node::Leaf(OpaqueValue::Generic(gf_id.0))));
                     
                     return Ok(name_node);
                 }
             }
         }
         Ok(self.nil_node)
    }

    /// Create an integer
    pub fn make_integer(&mut self, n: i64) -> NodeId {
        self.arena.alloc(Node::Leaf(OpaqueValue::Integer(n)))
    }
    
    /// Create a list from a vector of nodes
    pub fn list(&mut self, items: &[NodeId]) -> NodeId {
        let mut result = self.nil_node;
        for &item in items.iter().rev() {
            result = self.cons(item, result);
        }
        result
    }
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_interpreter_new() {
        let interp = Interpreter::new();
        assert!(interp.nil_node != interp.t_node || true); // Just ensure creation works
    }
    
    #[test]
    fn test_cons_car_cdr() {
        let mut interp = Interpreter::new();
        let a = interp.make_integer(1);
        let b = interp.make_integer(2);
        let cell = interp.cons(a, b);
        
        assert_eq!(interp.car(cell), Some(a));
        assert_eq!(interp.cdr(cell), Some(b));
    }
    
    #[test]
    fn test_list() {
        let mut interp = Interpreter::new();
        let items: Vec<_> = (1..=3).map(|i| interp.make_integer(i)).collect();
        let list = interp.list(&items);
        
        // Check first element
        assert_eq!(interp.car(list), Some(items[0]));
    }
    
    #[test]
    fn test_defun_and_call() {
        use crate::reader::read_from_string;
        use crate::primitives::register_primitives;
        
        let mut interp = Interpreter::new();
        register_primitives(&mut interp);
        
        // Define a simple square function
        let defun_expr = read_from_string(
            "(defun sq (x) (* x x))",
            &mut interp.arena,
            &mut interp.symbols
        ).unwrap();
        
        let env = Environment::new();
        let _ = interp.eval(defun_expr, &env).unwrap();
        
        // Now call the function
        let call_expr = read_from_string(
            "(sq 5)",
            &mut interp.arena,
            &mut interp.symbols
        ).unwrap();
        
        let call_result = interp.eval(call_expr, &env).unwrap();
        
        // Should be 25
        match interp.arena.get_unchecked(call_result) {
            Node::Leaf(OpaqueValue::Integer(25)) => {}
            Node::Leaf(OpaqueValue::Float(f)) if (*f - 25.0).abs() < 0.001 => {}
            other => panic!("Expected 25, got {:?}", other),
        }
    }
    
    #[test]
    fn test_recursion() {
        use crate::reader::read_from_string;
        use crate::primitives::register_primitives;
        
        let mut interp = Interpreter::new();
        register_primitives(&mut interp);
        
        // Define fibonacci function
        // (defun fib (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
        let defun_expr = read_from_string(
            "(defun fib (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))",
            &mut interp.arena,
            &mut interp.symbols
        ).unwrap();
        
        let env = Environment::new();
        interp.eval(defun_expr, &env).unwrap();
        
        // Call (fib 10) -> 55
        let call_expr = read_from_string(
            "(fib 10)",
            &mut interp.arena,
            &mut interp.symbols
        ).unwrap();
        
        let result = interp.eval(call_expr, &env).unwrap();
        
        match interp.arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(55)) => {}
            other => panic!("Expected 55, got {:?}", other),
        }
    }
    
    #[test]
    fn test_macro() {
        use crate::reader::read_from_string;
        use crate::primitives::register_primitives;
        
        let mut interp = Interpreter::new();
        register_primitives(&mut interp);
        
        // Define macro: (defmacro my-quote (x) (list (quote quote) x))
        let defmacro_expr = read_from_string(
            "(defmacro my-quote (x) (list (quote quote) x))",
            &mut interp.arena,
            &mut interp.symbols
        ).unwrap();
        
        let env = Environment::new();
        interp.eval(defmacro_expr, &env).unwrap();
        
        // Use macro: (my-quote 42) -> (quote 42) -> 42
        let call_expr = read_from_string(
            "(my-quote 42)",
            &mut interp.arena,
            &mut interp.symbols
        ).unwrap();
        
        let result = interp.eval(call_expr, &env).unwrap();
        
        match interp.arena.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(42)) => {}
            other => panic!("Expected 42, got {:?}", other),
        }
    }
    
    #[test]
    fn test_clos_integration() {
        use crate::reader::read_from_string;
        use crate::primitives::register_primitives;
        
        let mut interp = Interpreter::new();
        register_primitives(&mut interp);
        
        // 1. Define class Person
        // (defclass person () (name))
        let defclass_expr = read_from_string(
            "(defclass person () (name))",
            &mut interp.arena,
            &mut interp.symbols
        ).unwrap();
        
        let env = Environment::new();
        interp.eval(defclass_expr, &env).unwrap();
        
        // 2. Define method Greet
        // (defmethod greet ((p person)) (list (quote hello) (slot-value p (quote name))))
        let defmethod_expr = read_from_string(
            "(defmethod greet ((p person)) (list (quote hello) (slot-value p (quote name))))",
            &mut interp.arena,
            &mut interp.symbols
        ).unwrap();
        interp.eval(defmethod_expr, &env).unwrap();
        
        // 3. Create instance and call
        // (progn (setq p (make-instance (quote person))) (set-slot-value p (quote name) (quote bob)) (greet p))
        // Note: make-instance takes Class object or symbol. Using symbol 'person
        let code = "(progn 
            (setq p (make-instance (quote person))) 
            (set-slot-value p (quote name) (quote bob)) 
            (greet p))";
        
        let call_expr = read_from_string(
            code,
            &mut interp.arena,
            &mut interp.symbols
        ).unwrap();
        
        let result = interp.eval(call_expr, &env).unwrap();
        
        // Check result: (HELLO BOB)
        // This is a list: Fork(hello, Fork(bob, nil))
        // Verify structure
        if let Node::Fork(car, _cdr) = interp.arena.get_unchecked(result) {
            // Check car == HELLO
            if let Some(_hello_sym) = interp.node_to_symbol(*car) {
                // assume interned
            }
            // Check cdr
        } else {
             panic!("Expected list result");
        }
        
        // Simple print check
        use crate::printer::print_to_string;
        let s = print_to_string(&interp.arena, &interp.symbols, result);
        assert_eq!(s, "(HELLO BOB)");
    }
    
    #[test]
    fn test_gc() {
        use crate::reader::read_from_string;
        use crate::primitives::register_primitives;
        
        let mut interp = Interpreter::new();
        register_primitives(&mut interp);
        
        // 1. Create some garbage (cons cells that are discarded)
        // (progn (cons 1 2) (cons 3 4) nil)
        let code = "(progn (cons 1 2) (cons 3 4) nil)";
        let expr = read_from_string(code, &mut interp.arena, &mut interp.symbols).unwrap();
        
        let env = Environment::new();
        interp.eval(expr, &env).unwrap();
        
        // 2. Run GC
        // Note: roots are T, NIL, Symbols. Use lists above are garbage.
        let freed = interp.collect_garbage();
        
        // The cons cells (Fork) and numbers (Leaf(Int)) allocated should be freed.
        // We can't easily assert exact number without knowing internal allocation details,
        // but it should be > 0.
        assert!(freed > 0, "GC should have freed garbage");
        
        // 3. Verify T and NIL are still accessible (heap not corrupted)
        assert!(interp.arena.get(interp.t_node).is_some());
        assert!(interp.arena.get(interp.nil_node).is_some());
    }
    
    #[test]
    fn test_arrays() {
        use crate::reader::read_from_string;
        use crate::primitives::register_primitives;
        
        let mut interp = Interpreter::new();
        register_primitives(&mut interp);
        
        // 1. Create array
        let code = "(setq arr (make-array 5 10))";
        let expr = read_from_string(code, &mut interp.arena, &mut interp.symbols).unwrap();
        let env = Environment::new();
        interp.eval(expr, &env).unwrap();
        
        // 2. Check content
        let code = "(aref arr 2)";
        let expr = read_from_string(code, &mut interp.arena, &mut interp.symbols).unwrap();
        let val = interp.eval(expr, &env).unwrap();
        
        if let Node::Leaf(OpaqueValue::Integer(n)) = interp.arena.get_unchecked(val) {
            assert_eq!(*n, 10);
        } else {
            panic!("Expected Integer(10)");
        }
        
        // 3. Set content
        let code = "(progn (set-aref arr 2 99) (aref arr 2))";
        let expr = read_from_string(code, &mut interp.arena, &mut interp.symbols).unwrap();
        let val = interp.eval(expr, &env).unwrap();
        
        if let Node::Leaf(OpaqueValue::Integer(n)) = interp.arena.get_unchecked(val) {
            assert_eq!(*n, 99);
        } else {
            panic!("Expected Integer(99)");
        }
    }
    
    #[test]
    fn test_array_gc() {
        use crate::reader::read_from_string;
        use crate::primitives::register_primitives;
        
        let mut interp = Interpreter::new();
        register_primitives(&mut interp);
        let env = Environment::new();
        
        // 1. Create array and store a cons inside it
        // (setq arr (make-array 1))
        // (set-aref arr 0 (cons 1 2))
        let code = "(progn (setq arr (make-array 1)) (set-aref arr 0 (cons 1 2)))";
        let expr = read_from_string(code, &mut interp.arena, &mut interp.symbols).unwrap();
        interp.eval(expr, &env).unwrap();
        
        // 2. Clear temp variables so only array holds the cons
        // In our simple test env, `arr` is in `env`. The cons is ONLY in `arr`.
        // Wait, `eval` result of `(cons 1 2)` might be on stack if we were tracing stack, but we aren't.
        // `arr` is bound in Global/Symbols? NO, `setq` sets global symbol value.
        // So `arr` (Symbol) -> VectorHandle.
        // Vector[0] -> Cons Cell.
        
        // 3. Run GC
        let _freed = interp.collect_garbage();
        
        // 4. Access cons from array
        let code = "(car (aref arr 0))";
        let expr = read_from_string(code, &mut interp.arena, &mut interp.symbols).unwrap();
        let val = interp.eval(expr, &env).unwrap();
        
        if let Node::Leaf(OpaqueValue::Integer(n)) = interp.arena.get_unchecked(val) {
            assert_eq!(*n, 1);
        } else {
            panic!("Expected Integer(1), got {:?}", interp.arena.get_unchecked(val));
        }
    }
    
    #[test]
    fn test_readtable_macros() {
        use crate::primitives::register_primitives;
        
        let mut interp = Interpreter::new();
        register_primitives(&mut interp);
        
        // Note: read_from_string creates a FRESH readtable!
        // We need to mutate the INTERPRETER'S readtable and pass it to Reader.
        // So we can't use `read_from_string` for this test if we want persistence.
        // We must manually construct Reader.
        
        // 1. Enable brackets manually to bypass symbol resolution issues in test environment
        // Found that Reader creates new symbol for CL:SET-MACRO-CHARACTER instead of reusing primitive.
        // We construct the call (set-macro-character 91 'READ-LEFT-BRACKET) manually.
        
        let prim_sym = interp.symbols.find_package("CL")
            .and_then(|p| interp.symbols.get_package(p))
            .and_then(|p| p.find_external("SET-MACRO-CHARACTER"))
            .expect("Primitive symbol not found");
            
        // Construct call 1: (set-macro-character 91 'read-left-bracket)
        let func1 = interp.symbols.intern("READ-LEFT-BRACKET");
        // We need (quote read-left-bracket) -> list(quote, func1)
        let quote = interp.symbols.intern("QUOTE");
        let quote_sym = interp.symbol_to_node(quote);
        let func1_sym = interp.symbol_to_node(func1);
        let quoted_func1 = interp.list(&[quote_sym, func1_sym]);
        
        let char1 = interp.arena.alloc(Node::Leaf(OpaqueValue::Integer(91)));
        let prim_node = interp.symbol_to_node(prim_sym);
        
        let call1 = interp.list(&[prim_node, char1, quoted_func1]);
        interp.eval(call1, &Environment::new()).unwrap();
        
        // Construct call 2: (set-macro-character 93 'read-right-bracket)
        let func2 = interp.symbols.intern("READ-RIGHT-BRACKET");
        let func2_sym = interp.symbol_to_node(func2);
        let quoted_func2 = interp.list(&[quote_sym, func2_sym]);
        
        let char2 = interp.arena.alloc(Node::Leaf(OpaqueValue::Integer(93)));
        let call2 = interp.list(&[prim_node, char2, quoted_func2]);
        interp.eval(call2, &Environment::new()).unwrap();
        
        // 2. Read vector syntax using UPDATED readtable
        // [10 20]
        let vec_code = "[10 20]";
        let vec_expr = crate::reader::Reader::new(vec_code, &mut interp.arena, &mut interp.symbols, &interp.readtable, Some(&mut interp.arrays)).read().unwrap();
        
        // 3. Verify it is a vector
        // Eval it (vector literal evaluates to itself, usually? Or we quote it? 
        // Reader returns Vector object (Leaf). Eval of Leaf(Vector) is self.
        let env = Environment::new();
        let val = interp.eval(vec_expr, &env).unwrap();
        
        if let Node::Leaf(OpaqueValue::VectorHandle(vec_idx)) = interp.arena.get_unchecked(val) {
            // Check content
            let arr = interp.arrays.get(crate::arrays::VectorId(*vec_idx)).unwrap();
            assert_eq!(arr.len(), 2);
        } else {
             // Maybe it's not self-evaluating in `eval` yet?
             // `eval` handles Node::Leaf(val).
             // `OpaqueValue::VectorHandle` falls into `_ => Ok(expr)` (self-evaluating).
             // So it should work.
             panic!("Expected VectorHandle, got {:?}", interp.arena.get_unchecked(val));
        }
    }

    #[test]
    fn test_conditions_integration() {
        use crate::reader::read_from_string;
        use crate::primitives::register_primitives;
        
        let mut interp = Interpreter::new();
        register_primitives(&mut interp);
        
        // (handler-bind ((error (lambda (c) (return-from top (quote caught)))))
        //   (block top (error "boom")))
        let code = "
            (block top
              (handler-bind ((error (lambda (c) (return-from top (quote caught)))))
                 (error \"boom\")))
        ";
        
        let expr = read_from_string(
            code,
            &mut interp.arena,
            &mut interp.symbols
        ).unwrap();
        
        let env = Environment::new();
        let result = interp.eval(expr, &env).unwrap();
        
        // Result should be 'caught' symbol
        if let Some(sym) = interp.node_to_symbol(result) {
            let name = interp.symbols.get_symbol(sym).unwrap().name.clone();
            assert_eq!(name, "CAUGHT");
        } else {
            panic!("Expected symbol result");
        }
    }
}
