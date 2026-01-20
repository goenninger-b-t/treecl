// TreeCL Evaluator - Special Forms and Core Evaluation
//
// This module implements ANSI CL special forms on top of Tree Calculus.

use crate::arena::Node;
use crate::types::{NodeId, OpaqueValue};
use crate::symbol::{SymbolTable, SymbolId, PackageId};
use crate::process::Process;
use crate::context::GlobalContext;
use crate::reader::Reader;

use crate::context::PrimitiveFn;
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

/// Special form identifiers are now in Context


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
    /// System Call (Concurrency)
    SysCall(crate::syscall::SysCall),
}

/// Result of evaluation
pub type EvalResult = Result<NodeId, ControlSignal>;

/// The TreeCL interpreter wrapper
/// Holds references to the current Process state and Global Code context.
pub struct Interpreter<'a> {
    pub process: &'a mut Process,
    pub globals: &'a GlobalContext,
}

impl<'a> Interpreter<'a> {
    pub fn new(process: &'a mut Process, globals: &'a GlobalContext) -> Self {
        Self {
            process,
            globals,
        }
    }


    /// Signal a simple error with a message
    pub fn signal_error(&mut self, format: &str) -> EvalResult {
        // Create simple-error condition
        let cond = self.process.conditions.make_simple_error(format, Vec::new());
        
        let handlers = self.process.conditions.find_handlers(&cond).into_iter().cloned().collect::<Vec<_>>();
        
        for handler in handlers {
            // Invoke handler: (func condition)
            // Let's just pass the format string (message) for now.
            let msg = self.process.arena.alloc(Node::Leaf(OpaqueValue::String(format.to_string())));
            let args = self.list(&[msg]); // List of args for apply
            
            let func = handler.function;
            
            // Apply
            match self.apply_function(func, args, &Environment::new()) {
                Ok(_) => {
                    // Handler declined (returned normally), continue search
                }
                Err(sig) => return Err(sig),
            }
        }
        
        Err(ControlSignal::Error(format.to_string()))
    }
    
    // Register primitive is now in GlobalContext, but this helper might wrap it?
    // Or we remove it from Interpreter and use GlobalContext directly in startup.
    // Let's keep a wrapper for convenience if needed, but Context has it.
    // Actually, register_primitive should modify Globals. globals is &GlobalContext (Shared Read-Only?)
    // Wait. GlobalContext is Read-Only during execution?
    // CodeServer is usually static or has internal mutability.
    // If GlobalContext is `&`, we can't mutate primitives.
    // 
    // Fix: Interpreter needs `&mut GlobalContext` during BOOT, but `&GlobalContext` during Runtime.
    // Or GlobalContext needs internal mutability (RwLock). 
    // Since we are in `no_std` / single threaded verification for now, maybe `&mut` is fine?
    // But `Interpreter` carries `&'a GlobalContext`.
    
    // For now, let's assume we don't register primitives at Runtime via Interpreter.
    // We register them at Boot.
    // So remove `register_primitive` from Interpreter?
    // Or make Interpreter hold `&mut GlobalContext`.
    //
    // Let's check `process.rs` again. Process doesn't hold GlobalContext.
    // `Interpreter` is a wrapper.
    // If we want to support dynamic primitive loading, we need mutable globals.
    // But Beams usually load code separately.
    //
    // Let's remove `register_primitive` from here and rely on Context setup.
    
    pub fn symbol_to_node(&mut self, sym_id: SymbolId) -> NodeId {
        self.process.arena.alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0)))
    }

    /// Main evaluation entry point
    pub fn eval(&mut self, expr: NodeId, env: &Environment) -> EvalResult {
        let node = self.process.arena.get_unchecked(expr).clone();
        
        match node {
            Node::Leaf(val) => {
                match val {
                    OpaqueValue::Nil => Ok(self.process.make_nil()), // Need these in globals? Or retrieve?
                    // GlobalContext has nil_sym, but nodes are in arena?
                    // Ah, nil_node must be in EACH process arena? 
                    // Yes, separate heaps.
                    // So we must lookup NIL in current arena or allocate it?
                    // Or cache in Process?
                    // Process::new() should create NIL/T?
                    // Let's assume we can get them.
                    
                    OpaqueValue::Symbol(id) => {
                        let sym_id = SymbolId(id);
                        // Variable lookup
                        if let Some(val) = env.lookup(sym_id) {
                            return Ok(val);
                        }
                        // Check Process Dictionary
                        if let Some(val) = self.process.get_value(sym_id) {
                             return Ok(val);
                        }
                        
                        // Self-evaluating keywords?
                        // symbols is in Globals.
                        if self.globals.symbols.get_symbol(sym_id).map_or(false, |s| s.is_keyword()) {
                             return Ok(expr);
                        }
                        // If T or NIL
                        if sym_id == self.globals.t_sym || sym_id == self.globals.nil_sym {
                            // They evaluate to themselves (which should be bound in process or just return expr)
                             return Ok(expr);
                        }
                        
                        // Unbound variable
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
            let sf = &self.globals.special_forms;
            
            // 0. Check for macro expansion (Macros are in Globals or Process?)
            // We put Macros in Interpreter previously.
            // Let's assume macros are in GlobalContext for now? 
            // Or remove macros temporarily until we fix them.
            // If they are runtime defined, they need to be in Process (Dictionary?).
            // Let's check Process Dictionary for Macro-function?
            
            // For now, skip macros or comment out?
            // "self.process.macros" is missing.
            // Let's comment out macro expansion for this step.
            /*
            if let Some(&macro_idx) = self.process.macros.get(&sym_id) {
                if let Some(closure) = self.process.closures.get(macro_idx).cloned() {
                    let expanded = self.apply_macro(&closure, args)?;
                    return self.eval(expanded, env);
                }
            }
            */
            
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
            if let Some(&prim_fn) = self.globals.primitives.get(&sym_id) {
                // Evaluate arguments
                let mut evaluated_args = Vec::new();
                let mut current = args;
                while let Node::Fork(arg, rest) = self.process.arena.get_unchecked(current).clone() {
                    let val = self.eval(arg, env)?;
                    evaluated_args.push(val);
                    current = rest;
                }
                return prim_fn(self.process, self.globals, &evaluated_args);
            }
            
            // Check if symbol has a function binding
            if let Some(func) = self.process.get_function(sym_id) {
                return self.apply_function(func, args, env);
            }
            
            // Check if symbol has a value binding
            if let Some(val) = env.lookup(sym_id) {
                return self.apply_function(val, args, env);
            }
            if let Some(val) = self.process.get_value(sym_id) {
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
        let node = self.process.arena.get_unchecked(node_id);
        if let Node::Leaf(OpaqueValue::Symbol(id)) = node {
            return Some(SymbolId(*id));
        }
        None
    }
    
    /// (quote expr) -> expr (unevaluated)
    fn eval_quote(&mut self, args: NodeId) -> EvalResult {
        // args is (expr . nil)
        if let Node::Fork(expr, _) = self.process.arena.get_unchecked(args).clone() {
            Ok(expr)
        } else {
            Ok(args)
        }
    }
    
    /// (if test then else?) -> evaluate conditionally
    fn eval_if(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        let node = self.process.arena.get_unchecked(args).clone();
        
        if let Node::Fork(test, rest) = node {
            // Evaluate test
            let test_val = self.eval(test, env)?;
            
            // Check if true (not nil)
            let is_true = test_val != self.process.make_nil(); // Use globals.nil_node
            
            if let Node::Fork(then_expr, else_rest) = self.process.arena.get_unchecked(rest).clone() {
                if is_true {
                    self.eval(then_expr, env)
                } else {
                    // Check for else clause
                    if let Node::Fork(else_expr, _) = self.process.arena.get_unchecked(else_rest).clone() {
                        self.eval(else_expr, env)
                    } else {
                        Ok(self.process.make_nil())
                    }
                }
            } else {
                Ok(self.process.make_nil())
            }
        } else {
            Ok(self.process.make_nil())
        }
    }
    
    /// (progn form*) -> evaluate forms in sequence, return last
    fn eval_progn(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        let mut result = self.process.make_nil();
        let mut current = args;
        
        loop {
            match self.process.arena.get_unchecked(current).clone() {
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
        let mut result = self.process.make_nil();
        let mut current = args;
        
        loop {
            match self.process.arena.get_unchecked(current).clone() {
                Node::Fork(var_node, rest) => {
                    if let Node::Fork(val_node, next) = self.process.arena.get_unchecked(rest).clone() {
                        // Get symbol
                        if let Some(sym) = self.node_to_symbol(var_node) {
                            let val = self.eval(val_node, env)?;
                            // Set in Process Dictionary
                            self.process.set_value(sym, val);
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
        if let Node::Fork(bindings, body) = self.process.arena.get_unchecked(args).clone() {
            let mut new_env = Environment::with_parent(env.clone());
            
            // Process bindings
            let mut current = bindings;
            loop {
                match self.process.arena.get_unchecked(current).clone() {
                    Node::Fork(binding, rest) => {
                        if let Node::Fork(var_node, val_rest) = self.process.arena.get_unchecked(binding).clone() {
                            if let Some(sym) = self.node_to_symbol(var_node) {
                                if let Node::Fork(val_node, _) = self.process.arena.get_unchecked(val_rest).clone() {
                                    let val = self.eval(val_node, env)?; // Note: parallel let (eval in old env)
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
            Ok(self.process.make_nil())
        }
    }
    
    /// (lambda (params) body*) -> create closure
    fn eval_lambda(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(params, body) = self.process.arena.get_unchecked(args).clone() {
            // Parse parameter list
            let mut param_list = Vec::new();
            let mut current = params;
            loop {
                match self.process.arena.get_unchecked(current).clone() {
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
            
            let closure_idx = self.process.closures.len();
            self.process.closures.push(closure);
            
            // Return a node representing the closure
            // We use a Leaf with Closure handle
            let closure_node = self.process.arena.alloc(Node::Leaf(OpaqueValue::Closure(closure_idx as u32)));
            Ok(closure_node)
        } else {
            Ok(self.process.make_nil())
        }
    }
    
    /// (function name-or-lambda) -> get function object
    fn eval_function(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(name, _) = self.process.arena.get_unchecked(args).clone() {
            // Check if it's a lambda
            if let Node::Fork(car, _) = self.process.arena.get_unchecked(name).clone() {
                if self.node_to_symbol(car) == Some(self.globals.special_forms.lambda) {
                    return self.eval(name, env);
                }
            }
            
            // It's a symbol - get its function binding
            if let Some(sym) = self.node_to_symbol(name) {
                if let Some(func) = self.process.get_function(sym) {
                    return Ok(func);
                }
            }
        }
        
        Ok(self.process.make_nil())
    }
    
    /// (defun name (params) body*) -> define a named function
    fn eval_defun(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        // Parse: (name (params...) body...)
        if let Node::Fork(name_node, rest) = self.process.arena.get_unchecked(args).clone() {
            // Validate name is a symbol
            let name_sym = match self.node_to_symbol(name_node) {
                Some(s) => s,
                None => return Err(ControlSignal::Error(
                    "DEFUN: first argument must be a symbol".to_string()
                )),
            };
            
            if let Node::Fork(params, body) = self.process.arena.get_unchecked(rest).clone() {
                // Validate params is a list (nil or Fork)
                match self.process.arena.get_unchecked(params) {
                    Node::Leaf(OpaqueValue::Nil) => {} // Empty params OK
                    Node::Fork(_, _) => {} // List params OK
                    _ => return Err(ControlSignal::Error(
                        format!("DEFUN: parameter list must be a list, not {:?}", 
                            self.process.arena.get_unchecked(params))
                    )),
                }
                
                // Parse parameter list
                let mut param_list = Vec::new();
                let mut current = params;
                loop {
                    match self.process.arena.get_unchecked(current).clone() {
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
                if let Node::Leaf(OpaqueValue::Nil) = self.process.arena.get_unchecked(body) {
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
                
                let closure_idx = self.process.closures.len();
                self.process.closures.push(closure);
                
                // Create closure node
                let closure_node = self.process.arena.alloc(Node::Leaf(OpaqueValue::Closure(closure_idx as u32)));
                
                // Bind to process's function table (local defun)
                self.process.set_function(name_sym, closure_node);
                
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
        while let Node::Fork(item, rest) = self.process.arena.get_unchecked(current).clone() {
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
        
        Ok(self.process.make_nil())
    }
    
    /// (go tag) -> transfer control to tag in enclosing tagbody
    fn eval_go(&mut self, args: NodeId) -> EvalResult {
        if let Node::Fork(tag_node, _) = self.process.arena.get_unchecked(args).clone() {
            if let Some(sym) = self.node_to_symbol(tag_node) {
                return Err(ControlSignal::Go(sym));
            }
        }
        Ok(self.process.make_nil())
    }
    
    /// (block name body*) -> evaluate body, can be exited with return-from
    fn eval_block(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(name_node, body) = self.process.arena.get_unchecked(args).clone() {
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
            Ok(self.process.make_nil())
        }
    }
    
    /// (return-from name value?) -> return from named block
    fn eval_return_from(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(name_node, rest) = self.process.arena.get_unchecked(args).clone() {
            if let Some(name) = self.node_to_symbol(name_node) {
                let value = if let Node::Fork(val_node, _) = self.process.arena.get_unchecked(rest).clone() {
                    self.eval(val_node, env)?
                } else {
                    self.process.make_nil()
                };
                return Err(ControlSignal::ReturnFrom { name, value });
            }
        }
        Ok(self.process.make_nil())
    }
    
    /// (catch tag body*) -> evaluate body, catch throw to tag
    fn eval_catch(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(tag_expr, body) = self.process.arena.get_unchecked(args).clone() {
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
            Ok(self.process.make_nil())
        }
    }
    
    /// (throw tag result) -> throw to matching catch
    fn eval_throw(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(tag_expr, rest) = self.process.arena.get_unchecked(args).clone() {
            let tag = self.eval(tag_expr, env)?;
            let value = if let Node::Fork(val_expr, _) = self.process.arena.get_unchecked(rest).clone() {
                self.eval(val_expr, env)?
            } else {
                self.process.make_nil()
            };
            Err(ControlSignal::Throw { tag, value })
        } else {
            Ok(self.process.make_nil())
        }
    }
    
    /// (unwind-protect protected-form cleanup-form*) -> cleanup always runs
    fn eval_unwind_protect(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(protected, cleanup) = self.process.arena.get_unchecked(args).clone() {
            let result = self.eval(protected, env);
            
            // Always run cleanup forms
            let _ = self.eval_progn(cleanup, env);
            
            result
        } else {
            Ok(self.process.make_nil())
        }
    }
    
    /// Apply a function to arguments
    pub fn apply_function(&mut self, func: NodeId, args: NodeId, env: &Environment) -> EvalResult {
        let func_node = self.process.arena.get_unchecked(func).clone();
        
        match func_node {
            Node::Leaf(OpaqueValue::Closure(idx)) => {
                // Closure application
                if let Some(closure) = self.process.closures.get(idx as usize).cloned() {
                    self.apply_closure(&closure, args, env)
                } else {
                    Err(ControlSignal::Error(format!("Invalid closure index: {}", idx)))
                }
            }
            Node::Leaf(OpaqueValue::Generic(id)) => {
                // self.apply_generic(id, args, env) // TODO: Port MOP
                Ok(self.process.make_nil())
            }
            _ => {
                // Fall back to tree calculus reduction
                // Evaluate arguments and apply one at a time (curried)
                use crate::search::reduce;
                
                let mut result = func;
                let mut current = args;
                
                // Walk through argument list
                while let Node::Fork(arg_expr, rest) = self.process.arena.get_unchecked(current).clone() {
                    // Evaluate the argument
                    let arg_val = self.eval(arg_expr, env)?;
                    
                    // Apply Tree Calculus: (result arg_val)
                    let app = self.process.arena.alloc(Node::Fork(result, arg_val));
                    result = reduce(&mut self.process.arena.inner, app, &mut self.process.eval_context);
                    
                    current = rest;
                }
                
                Ok(self.try_reduce_primitive(result, env))
            }
        }
    }

    /// Try to reduce a "stuck" application if the head is a primitive symbol
    pub fn try_reduce_primitive(&mut self, root: NodeId, _env: &Environment) -> NodeId {
        // 1. Flatten the spine: ((f a) b) -> [f, a, b]
        let mut spine = Vec::new();
        let mut current = root;
        while let Node::Fork(l, r) = self.process.arena.get_unchecked(current).clone() {
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
             if let Some(&prim_fn) = self.globals.primitives.get(&sym) {
                 // We have a primitive!
                 let raw_args = &spine[1..];
                 
                 // Evaluate arguments (Force strictness for primitives)
                 // Compiled code reduction is lazy (Normal Order), but primitives expect values.
                 let mut evaluated_args = Vec::with_capacity(raw_args.len());
                 for &arg in raw_args {
                     // We use the passed environment. For compiled code, this usually works
                     // as free variables are globals.
                     // Use reduce instead of eval because args are Tree Calculus terms (Forks), not Lisp lists.
                     let val = crate::search::reduce(&mut self.process.arena.inner, arg, &mut self.process.eval_context);
                     evaluated_args.push(val);
                 }
                 
                 
                 let redex = root; // Capture current root as redex
                 match prim_fn(self.process, self.globals, &evaluated_args) {
                      Ok(res) => return res,
                      Err(ControlSignal::SysCall(sc)) => {
                          self.process.pending_redex = Some(redex);
                          self.process.pending_syscall = Some(sc);
                          return root;
                      }
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
            match self.process.arena.get_unchecked(current_arg).clone() {
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
            match self.process.arena.get_unchecked(current_arg).clone() {
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
        while let Node::Fork(arg, rest) = self.process.arena.inner.get_unchecked(current).clone() {
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
        let applicable = self.process.mop.compute_applicable_methods(gf_id, &arg_classes);
        
        if applicable.is_empty() {
             return Err(ControlSignal::Error(format!("No applicable method for generic function {:?} with args {:?}", gf_id, arg_classes)));
        }
        
        // 4. Call most specific method (primary only for now)
        let method_id = applicable[0];
        let method = self.process.mop.get_method(method_id).unwrap();
        let method_body = method.body;
        
        // Apply method closure
        if let Node::Leaf(OpaqueValue::Closure(idx)) = self.process.arena.inner.get_unchecked(method_body).clone() {
                if let Some(closure) = self.process.closures.get(idx as usize).cloned() {
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
        match self.process.arena.inner.get_unchecked(val) {
            Node::Leaf(OpaqueValue::Integer(_)) => crate::clos::ClassId(0), // Fixme: map to Integer class
            Node::Leaf(OpaqueValue::Instance(idx)) => {
                if let Some(inst) = self.process.mop.get_instance(*idx as usize) {
                    inst.class
                } else {
                    self.process.mop.standard_object // Fallback
                }
            }
             // ... handle other types ...
            _ => self.process.mop.t_class,
        }
    }

    /// (defmacro name (params) body*) -> define a macro
    fn eval_defmacro(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        // Parse: (name (params...) body...)
        if let Node::Fork(name_node, rest) = self.process.arena.inner.get_unchecked(args).clone() {
            if let Some(name_sym) = self.node_to_symbol(name_node) {
                if let Node::Fork(params, body) = self.process.arena.inner.get_unchecked(rest).clone() {
                    // Parse parameter list
                    let mut param_list = Vec::new();
                    let mut current = params;
                    loop {
                        match self.process.arena.inner.get_unchecked(current).clone() {
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
                    
                    let closure_idx = self.process.closures.len();
                    self.process.closures.push(closure);
                    
                    // Register macro
                    self.process.macros.insert(name_sym, closure_idx);
                    
                    // Return the macro name symbol
                    return Ok(name_node);
                }
            }
        }
        
        Ok(self.process.make_nil())
    }

    
    /// Create a cons cell
    pub fn cons(&mut self, car: NodeId, cdr: NodeId) -> NodeId {
        self.process.arena.inner.alloc(Node::Fork(car, cdr))
    }
    
    /// Get car of a cons
    pub fn car(&self, node: NodeId) -> Option<NodeId> {
        match self.process.arena.inner.get_unchecked(node) {
            Node::Fork(car, _) => Some(*car),
            _ => None,
        }
    }
    
    /// Get cdr of a cons
    pub fn cdr(&self, node: NodeId) -> Option<NodeId> {
        match self.process.arena.inner.get_unchecked(node) {
            Node::Fork(_, cdr) => Some(*cdr),
            _ => None,
        }
    }
    
    /// (handler-bind ((type handler)...) body...)
    fn eval_handler_bind(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        // Parse bindings and body
        // args: (bindings . body)
        if let Node::Fork(bindings_node, body) = self.process.arena.inner.get_unchecked(args).clone() {
            let mut handlers = Vec::new();
            
            // Iterate over bindings list
            let mut current_binding = bindings_node;
            while let Node::Fork(binding, rest) = self.process.arena.inner.get_unchecked(current_binding).clone() {
                // Binding: (type handler)
                if let Node::Fork(type_node, handler_pair) = self.process.arena.inner.get_unchecked(binding).clone() {
                    if let Node::Fork(handler_expr, _) = self.process.arena.inner.get_unchecked(handler_pair).clone() { // (handler nil) or (handler . nil)
                        // Resolve type
                        // For Phase 7, we support 'error', 'warning', 'condition' symbols map to built-in types
                        // In real CL, we'd look up class/condition-type.
                        let type_id = if let Some(sym) = self.node_to_symbol(type_node) {
                             let name = self.globals.symbols.get_symbol(sym).unwrap().name.clone();
                             if name == "ERROR" { self.process.conditions.error_type }
                             else if name == "WARNING" { self.process.conditions.warning_type }
                             else { self.process.conditions.condition_type } // Default to condition
                        } else {
                             self.process.conditions.condition_type
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
            self.process.conditions.push_handlers(handlers);
            
            // Eval body
            let result = self.eval_progn(body, env);
            
            // Pop handlers
            self.process.conditions.pop_handlers();
            
            result
        } else {
            Ok(self.process.make_nil())
        }
    }

    /// (defclass name (supers...) (slots...))
    fn eval_defclass(&mut self, args: NodeId, _env: &Environment) -> EvalResult {
        // Simple parser
        if let Node::Fork(name_node, rest) = self.process.arena.inner.get_unchecked(args).clone() {
            if let Some(name_sym) = self.node_to_symbol(name_node) {
                if let Node::Fork(supers_node, rest2) = self.process.arena.inner.get_unchecked(rest).clone() {
                    let mut supers = Vec::new(); // Collect super classes
                    // Iterate supers_node list
                    let mut current = supers_node;
                    while let Node::Fork(super_name, next) = self.process.arena.inner.get_unchecked(current).clone() {
                        if let Some(s_sym) = self.node_to_symbol(super_name) {
                             if let Some(id) = self.process.mop.find_class(s_sym) {
                                 supers.push(id);
                             }
                        }
                        current = next;
                    }
                    
                    if let Node::Fork(slots_node, _) = self.process.arena.inner.get_unchecked(rest2).clone() {
                        let mut slots = Vec::new();
                        let mut current_slot = slots_node;
                         while let Node::Fork(slot_spec, next) = self.process.arena.inner.get_unchecked(current_slot).clone() {
                            // Slot spec can be symbol or list
                            let slot_name = if let Some(sym) = self.node_to_symbol(slot_spec) {
                                sym
                            } else if let Node::Fork(name, _) = self.process.arena.inner.get_unchecked(slot_spec).clone() {
                                self.node_to_symbol(name).unwrap_or(self.globals.nil_sym)
                            } else {
                                self.globals.nil_sym
                            };
                            
                            if slot_name != self.globals.nil_sym {
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
                        
                        self.process.mop.define_class(name_sym, supers, slots);
                        return Ok(name_node);
                    }
                }
            }
        }
        Ok(self.process.make_nil())
    }

    /// (defmethod name ((param spec)...) body...)
    fn eval_defmethod(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        // Simplified parser
         if let Node::Fork(name_node, rest) = self.process.arena.inner.get_unchecked(args).clone() {
             if let Some(name_sym) = self.node_to_symbol(name_node) {
                 if let Node::Fork(params_node, body) = self.process.arena.inner.get_unchecked(rest).clone() {
                     // Parse parameters and specializers
                     let mut params = Vec::new();
                     let mut specializers = Vec::new();
                     
                     let mut current = params_node;
                     while let Node::Fork(param_spec, next) = self.process.arena.inner.get_unchecked(current).clone() {
                         // param_spec is (name class) or name
                         if let Some(sym) = self.node_to_symbol(param_spec) {
                             // Unspecialized (T)
                             params.push(sym);
                             specializers.push(self.process.mop.t_class);
                         } else if let Node::Fork(pname, ptype_rest) = self.process.arena.inner.get_unchecked(param_spec).clone() {
                             if let Some(psym) = self.node_to_symbol(pname) {
                                 params.push(psym);
                                 // Get class
                                 let class_id = if let Node::Fork(cname, _) = self.process.arena.inner.get_unchecked(ptype_rest).clone() {
                                     if let Some(csym) = self.node_to_symbol(cname) {
                                         self.process.mop.find_class(csym).unwrap_or(self.process.mop.t_class)
                                     } else { self.process.mop.t_class }
                                 } else { self.process.mop.t_class };
                                 specializers.push(class_id);
                             }
                         }
                         current = next;
                     }
                     
                     // Ensure generic function exists
                     let gf_id = if let Some(id) = self.process.mop.find_generic(name_sym) {
                         id
                     } else {
                         self.process.mop.define_generic(name_sym, params.clone())
                     };
                     
                     // Create closure for body
                     // Need lambda-list for closure
                     // Closure { params: params, body: body, env: env }
                     let closure = Closure {
                         params: params,
                         body: body,
                         env: env.clone(),
                     };
                     let closure_idx = self.process.closures.len();
                     self.process.closures.push(closure);
                     
                     // Closure Node
                     // Closure Node
                     let closure_node = self.process.arena.inner.alloc(Node::Leaf(OpaqueValue::Closure(closure_idx as u32)));
                     
                     // Add method
                     self.process.mop.add_method(gf_id, specializers, Vec::new(), closure_node);
                     
                     // Bind generic function to symbol function cell if not already
                     let gf_val = self.process.arena.inner.alloc(Node::Leaf(OpaqueValue::Generic(gf_id.0)));
                     self.process.set_function(name_sym, gf_val);
                     
                     return Ok(name_node);
                 }
             }
         }
         Ok(self.process.make_nil())
    }

    /// Create an integer
    pub fn make_integer(&mut self, n: i64) -> NodeId {
        self.process.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(n)))
    }
    
    /// Create a list from a vector of nodes
    pub fn list(&mut self, items: &[NodeId]) -> NodeId {
        let mut result = self.process.make_nil();
        for &item in items.iter().rev() {
            result = self.cons(item, result);
        }
        result
    }
}





/// Special Forms (Cached Symbol IDs)
pub struct SpecialForms {
    pub quote: SymbolId,
    pub r#if: SymbolId,
    pub progn: SymbolId,
    pub setq: SymbolId,
    pub r#let: SymbolId,
    pub lambda: SymbolId,
    pub function: SymbolId,
    pub defun: SymbolId,
    pub defclass: SymbolId,
    pub defmethod: SymbolId,
    pub definitions: SymbolId, 
    pub block: SymbolId,
    pub return_from: SymbolId,
    pub tagbody: SymbolId,
    pub go: SymbolId,
    pub catch: SymbolId,
    pub throw: SymbolId,
    pub unwind_protect: SymbolId,
    pub defmacro: SymbolId,
    pub handler_bind: SymbolId,
    pub eval_when: SymbolId,
    pub multiple_value_bind: SymbolId,
    pub multiple_value_call: SymbolId,
    pub values: SymbolId,
    pub locally: SymbolId,
    pub flet: SymbolId,
    pub labels: SymbolId,
    pub macrolet: SymbolId,
    pub symbol_macrolet: SymbolId,
    pub load_time_value: SymbolId,
    pub progression_list: SymbolId, // CLHS says progv
}

impl SpecialForms {
    pub fn new(symbols: &mut SymbolTable) -> Self {
        Self {
            quote: symbols.intern_in("QUOTE", PackageId(1)),
            r#if: symbols.intern_in("IF", PackageId(1)),
            progn: symbols.intern_in("PROGN", PackageId(1)),
            setq: symbols.intern_in("SETQ", PackageId(1)),
            r#let: symbols.intern_in("LET", PackageId(1)),
            lambda: symbols.intern_in("LAMBDA", PackageId(1)),
            function: symbols.intern_in("FUNCTION", PackageId(1)),
            defun: symbols.intern_in("DEFUN", PackageId(1)),
            defclass: symbols.intern_in("DEFCLASS", PackageId(1)),
            defmethod: symbols.intern_in("DEFMETHOD", PackageId(1)),
            definitions: symbols.intern_in("DEFINITIONS", PackageId(1)),
            block: symbols.intern_in("BLOCK", PackageId(1)),
            return_from: symbols.intern_in("RETURN-FROM", PackageId(1)),
            tagbody: symbols.intern_in("TAGBODY", PackageId(1)),
            go: symbols.intern_in("GO", PackageId(1)),
            catch: symbols.intern_in("CATCH", PackageId(1)),
            throw: symbols.intern_in("THROW", PackageId(1)),
            unwind_protect: symbols.intern_in("UNWIND-PROTECT", PackageId(1)),
            defmacro: symbols.intern_in("DEFMACRO", PackageId(1)),
            handler_bind: symbols.intern_in("HANDLER-BIND", PackageId(1)),
            eval_when: symbols.intern_in("EVAL-WHEN", PackageId(1)),
            multiple_value_bind: symbols.intern_in("MULTIPLE-VALUE-BIND", PackageId(1)),
            multiple_value_call: symbols.intern_in("MULTIPLE-VALUE-CALL", PackageId(1)),
            values: symbols.intern_in("VALUES", PackageId(1)),
            locally: symbols.intern_in("LOCALLY", PackageId(1)),
            flet: symbols.intern_in("FLET", PackageId(1)),
            labels: symbols.intern_in("LABELS", PackageId(1)),
            macrolet: symbols.intern_in("MACROLET", PackageId(1)),
            symbol_macrolet: symbols.intern_in("SYMBOL-MACROLET", PackageId(1)),
            load_time_value: symbols.intern_in("LOAD-TIME-VALUE", PackageId(1)),
            progression_list: symbols.intern_in("PROGV", PackageId(1)),
        }
    }
}
