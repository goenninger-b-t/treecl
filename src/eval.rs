// TreeCL Evaluator - Special Forms and Core Evaluation
//
// This module implements ANSI CL special forms on top of Tree Calculus.

use crate::arena::Node;
use crate::context::GlobalContext;
use crate::process::Process;
use crate::symbol::{PackageId, SymbolId, SymbolTable};
use crate::types::{NodeId, OpaqueValue};

use std::collections::HashMap;
use std::sync::{Arc, RwLock};

/// Environment for lexical bindings
#[derive(Debug, Clone)]
pub struct Environment {
    /// Lexical bindings: SymbolId -> NodeId
    bindings: Arc<RwLock<HashMap<SymbolId, NodeId>>>,
    /// Function bindings: SymbolId -> NodeId
    functions: Arc<RwLock<HashMap<SymbolId, NodeId>>>,
    /// Parent environment (for nested scopes)
    parent: Option<Box<Environment>>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            bindings: Arc::new(RwLock::new(HashMap::new())),
            functions: Arc::new(RwLock::new(HashMap::new())),
            parent: None,
        }
    }

    pub fn with_parent(parent: Environment) -> Self {
        Self {
            bindings: Arc::new(RwLock::new(HashMap::new())),
            functions: Arc::new(RwLock::new(HashMap::new())),
            parent: Some(Box::new(parent)),
        }
    }

    pub fn bind(&self, sym: SymbolId, val: NodeId) {
        self.bindings.write().unwrap().insert(sym, val);
    }

    pub fn set(&self, sym: SymbolId, val: NodeId) -> bool {
        // Try to set in current bindings
        let mut guard = self.bindings.write().unwrap();
        if guard.contains_key(&sym) {
            guard.insert(sym, val);
            return true;
        }
        drop(guard);

        // Try parent
        if let Some(parent) = &self.parent {
            return parent.set(sym, val);
        }
        false
    }

    pub fn set_function(&self, sym: SymbolId, val: NodeId) {
        self.functions.write().unwrap().insert(sym, val);
    }

    pub fn lookup(&self, sym: SymbolId) -> Option<NodeId> {
        if let Some(val) = self.bindings.read().unwrap().get(&sym) {
            return Some(*val);
        }
        self.parent.as_ref().and_then(|p| p.lookup(sym))
    }

    pub fn lookup_function(&self, sym: SymbolId) -> Option<NodeId> {
        if let Some(val) = self.functions.read().unwrap().get(&sym) {
            return Some(*val);
        }
        self.parent.as_ref().and_then(|p| p.lookup_function(sym))
    }

    pub fn iter_roots(&self) -> Vec<NodeId> {
        let mut roots = Vec::new();
        let mut current = Some(self);
        while let Some(env) = current {
            roots.extend(env.bindings.read().unwrap().values().copied());
            roots.extend(env.functions.read().unwrap().values().copied());
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
    /// Parsed lambda list info
    pub lambda_list: ParsedLambdaList,
    /// Body expression (NodeId)
    pub body: NodeId,
    /// Captured environment
    pub env: Environment,
}

#[derive(Debug, Clone, Default)]
pub struct ParsedLambdaList {
    /// Required parameters (Symbol or Destructuring Pattern)
    pub req: Vec<NodeId>,
    /// Optional parameters: (var-pattern, default, supplied-p)
    pub opt: Vec<(NodeId, NodeId, Option<SymbolId>)>,
    /// Rest parameter (Symbol for now? Or pattern?)
    /// ANSI: "The \rest parameter must be a symbol" (for functions). For macros?
    /// " destructuring-lambda-list = ... [&rest | &body] var" -> var is a symbol or a list (in some implementations)?
    /// CLHS 3.4.4.1: "&rest var". "var" is a symbol.
    /// So rest should remain SymbolId.
    pub rest: Option<SymbolId>,
    /// Keyword parameters
    pub key: Vec<(SymbolId, NodeId, NodeId, Option<SymbolId>)>, // key-name, var-pattern, init, sup
    /// Aux parameters
    pub aux: Vec<(SymbolId, NodeId)>,
    /// &allow-other-keys present
    pub allow_other_keys: bool,
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
    /// Uncaught Condition -> Debugger
    Debugger(crate::conditions::Condition),
    /// System Call (Concurrency)
    SysCall(crate::syscall::SysCall),
}

/// Result of evaluation
pub type EvalResult = Result<NodeId, ControlSignal>;

/// TCO Continuation Frames
#[derive(Debug, Clone)]
pub enum Continuation {
    /// Return to REPL/Caller
    Done,
    /// Evaluate arguments for function application
    /// (operator, remaining_args, evaluated_args)
    EvArgs {
        op: NodeId,
        args: Vec<NodeId>, // Pending args
        vals: Vec<NodeId>, // Evaluated args
        env: Environment,  // Caller environment
    },
    /// Apply function after args evaluated
    /// (function, args)
    Apply {
        func: NodeId,
        // Env is captured in closure or current?
        // Usually Apply just needs func and args.
        // Logic will handle dispatch (primitive or closure)
        saved_env: Environment,
    },
    /// Evaluate sequences (PROGN)
    /// (remaining_forms)
    EvProgn { rest: Vec<NodeId> },
    /// Evaluate Test for IF
    /// (then_branch, else_branch)
    EvIf {
        then_branch: NodeId,
        else_branch: NodeId,
        env: Environment,
    },
    EvMvb {
        vars: NodeId,
        body: NodeId,
        env: Environment,
    },
    /// Assignment (SETQ)
    /// (symbol, remaining_pairs)
    EvSetq {
        sym: SymbolId,
        rest: Vec<NodeId>, // Next var/val pairs
    },
    /// Definition (DEFUN/DEFMACRO) result handler
    /// (name) - just intern/bind and return name
    Defun { name: NodeId },
    /// Tagbody frame
    Tagbody {
        rest: Vec<NodeId>,
        tag_map: HashMap<TagKey, Vec<NodeId>>,
        env: Environment,
    },
    /// Block frame (named progn)
    /// (name, remaining_forms)
    Block { name: SymbolId, rest: Vec<NodeId> },
    /// Catch return value for return-from
    /// (target_block_name)
    // Actually, step_return_from evaluates the value.
    // Then the continuation receives the value and unwinds.
    ReturnFrom { target: SymbolId },
    /// Return to Debugger
    DebuggerRest {
        condition: crate::conditions::Condition,
    },
}

enum LambdaListMode {
    Req,
    Opt,
    Rest,
    Key,
    Aux,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum TagKey {
    Sym(SymbolId),
    Int(i64),
}

/// The TreeCL interpreter wrapper
/// Holds references to the current Process state and Global Code context.
pub struct Interpreter<'a> {
    pub process: &'a mut Process,
    pub globals: &'a GlobalContext,
}

impl<'a> Interpreter<'a> {
    pub fn new(process: &'a mut Process, globals: &'a GlobalContext) -> Self {
        Self { process, globals }
    }

    pub fn bind_pattern(
        &mut self,
        env: &mut Environment,
        pattern: NodeId,
        value: NodeId,
        allow_destructuring: bool,
    ) -> Result<(), ControlSignal> {
        if let Some(sym) = self.node_to_symbol(pattern) {
            let name = self
                .globals
                .symbols
                .read()
                .unwrap()
                .symbol_name(sym)
                .unwrap_or("?")
                .to_string();
            eprintln!("DEBUG: bind_pattern binding {:?} ({}) to value", sym, name);
            env.bind(sym, value);
            Ok(())
        } else if allow_destructuring {
            // Destructuring bind
            if let Node::Fork(p_head, p_tail) =
                self.process.arena.inner.get_unchecked(pattern).clone()
            {
                if let Node::Fork(v_head, v_tail) =
                    self.process.arena.inner.get_unchecked(value).clone()
                {
                    self.bind_pattern(env, p_head, v_head, true)?;
                    self.bind_pattern(env, p_tail, v_tail, true)?;
                    Ok(())
                } else if self.is_nil(value) {
                    // Bind against nil: nil for all vars
                    let nil_node = self.process.make_nil();
                    self.bind_pattern(env, p_head, nil_node, true)?;
                    let nil_node = self.process.make_nil();
                    self.bind_pattern(env, p_tail, nil_node, true)?;
                    Ok(())
                } else {
                    Err(ControlSignal::Error(format!(
                        "Destructuring mismatch: pattern {:?} value {:?}",
                        pattern, value
                    )))
                }
            } else {
                if self.is_nil(pattern) {
                    Ok(()) // Ignore nil pattern
                } else {
                    Err(ControlSignal::Error(format!(
                        "Invalid destructuring pattern: {:?}",
                        pattern
                    )))
                }
            }
        } else {
            Err(ControlSignal::Error(format!(
                "Function argument must be a symbol: {:?}",
                pattern
            )))
        }
    }

    pub fn parse_lambda_list(&mut self, list_node: NodeId) -> Result<ParsedLambdaList, String> {
        let list_vec = self.cons_to_vec(list_node);
        let mut parsed = ParsedLambdaList::default();

        let mut mode = LambdaListMode::Req;

        for node in list_vec.iter() {
            // Check if keyword
            let sym = self.node_to_symbol(*node);

            if let Some(s) = sym {
                if let Some(name) = self.globals.symbols.read().unwrap().symbol_name(s) {
                    match name {
                        "&OPTIONAL" => {
                            mode = LambdaListMode::Opt;
                            continue;
                        }
                        "&REST" => {
                            mode = LambdaListMode::Rest;
                            continue;
                        }
                        "&KEY" => {
                            mode = LambdaListMode::Key;
                            continue;
                        }
                        "&AUX" => {
                            mode = LambdaListMode::Aux;
                            continue;
                        }
                        "&ALLOW-OTHER-KEYS" => {
                            if !matches!(mode, LambdaListMode::Key) {
                                return Err("&ALLOW-OTHER-KEYS must follow &KEY".into());
                            }
                            parsed.allow_other_keys = true;
                            continue;
                        }
                        _ => {}
                    }
                }
            }

            match mode {
                LambdaListMode::Req => {
                    // Allow NodeId for destructuring support
                    parsed.req.push(*node);
                }
                LambdaListMode::Opt => {
                    if let Some(_s) = self.node_to_symbol(*node) {
                        parsed.opt.push((*node, self.process.make_nil(), None));
                    } else {
                        let parts = self.cons_to_vec(*node);
                        if parts.is_empty() {
                            return Err("Empty optional spec".into());
                        }
                        let var = parts[0]; // NodeId (pattern)
                        let init = if parts.len() > 1 {
                            parts[1]
                        } else {
                            self.process.make_nil()
                        };
                        let sup = if parts.len() > 2 {
                            self.node_to_symbol(parts[2])
                        } else {
                            None
                        };
                        parsed.opt.push((var, init, sup));
                    }
                }
                LambdaListMode::Rest => {
                    if parsed.rest.is_some() {
                        return Err("Multiple &rest arguments".into());
                    }
                    let s = self
                        .node_to_symbol(*node)
                        .ok_or("&rest argument must be a symbol")?;
                    parsed.rest = Some(s);
                }
                LambdaListMode::Key => {
                    if let Some(s) = self.node_to_symbol(*node) {
                        // Default logic: Key is valid keyword with same name as symbol
                        parsed.key.push((s, *node, self.process.make_nil(), None));
                    } else {
                        let parts = self.cons_to_vec(*node);
                        let spec = parts[0];

                        let (key_sym, var_node) = if let Some(s) = self.node_to_symbol(spec) {
                            (s, spec)
                        } else {
                            let spec_parts = self.cons_to_vec(spec);
                            let k = self
                                .node_to_symbol(spec_parts[0])
                                .ok_or("Key spec key must be symbol")?;
                            let v = spec_parts[1]; // NodeId
                            (k, v)
                        };

                        let init = if parts.len() > 1 {
                            parts[1]
                        } else {
                            self.process.make_nil()
                        };
                        let sup = if parts.len() > 2 {
                            self.node_to_symbol(parts[2])
                        } else {
                            None
                        };

                        parsed.key.push((key_sym, var_node, init, sup));
                    }
                }
                LambdaListMode::Aux => {
                    if let Some(s) = self.node_to_symbol(*node) {
                        parsed.aux.push((s, self.process.make_nil()));
                    } else {
                        let parts = self.cons_to_vec(*node);
                        let var = self
                            .node_to_symbol(parts[0])
                            .ok_or("Aux var must be symbol")?;
                        let init = if parts.len() > 1 {
                            parts[1]
                        } else {
                            self.process.make_nil()
                        };
                        parsed.aux.push((var, init));
                    }
                }
            }
        }

        Ok(parsed)
    }

    /// Fully evaluate a node (interleaving Tree Calculus and Primitives)
    fn eval_arg(&mut self, node: NodeId) -> NodeId {
        let mut current = node;
        let mut steps = 0;
        let max_steps = 1000; // Limit for argument evaluation loop

        loop {
            // 1. Pure reduction
            current = crate::search::reduce(
                &mut self.process.arena.inner,
                current,
                &mut self.process.eval_context,
            );

            if steps >= max_steps {
                return current;
            }

            // 2. Primitive reduction
            // We use an empty environment since primitives shouldn't rely on local env?
            // Actually, for free variables they rely on global lookup which doesn't need Env.
            let after_prim = self.try_reduce_primitive(current, &Environment::new());

            if after_prim == current {
                return current;
            }
            current = after_prim;
            steps += 1;
        }
    }

    /// Signal a simple error with a message
    pub fn signal_error(&mut self, format: &str) -> EvalResult {
        // Create simple-error condition
        let cond = self
            .process
            .conditions
            .make_simple_error(format, Vec::new());

        let handlers = self
            .process
            .conditions
            .find_handlers(&cond)
            .into_iter()
            .cloned()
            .collect::<Vec<_>>();

        for handler in handlers {
            // Invoke handler: (func condition)
            // Let's just pass the format string (message) for now.
            let msg = self
                .process
                .arena
                .alloc(Node::Leaf(OpaqueValue::String(format.to_string())));
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

        // If no handler handled it (or no handlers found), break to debugger
        self.process.status = crate::process::Status::Debugger(cond.clone());
        Err(ControlSignal::Debugger(cond))
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
        self.process
            .arena
            .alloc(Node::Leaf(OpaqueValue::Symbol(sym_id.0)))
    }

    /// Main evaluation entry point
    pub fn eval(&mut self, expr: NodeId, env: &Environment) -> EvalResult {
        // Check if expr is PROGN
        if let Some(sym) = self.node_to_symbol(expr) {
            if self
                .globals
                .symbols
                .read()
                .unwrap()
                .symbol_name(sym)
                .unwrap_or("")
                == "PROGN"
            {}
        }
        // Legacy recursive eval - eventually replace or wrap step
        let node = self.process.arena.get_unchecked(expr).clone();
        // ... (existing eval logic to be kept for reference or backup until full switch)
        // For now, let's keep eval as is, and add step separately.
        // But the user asked to refactor Eval.
        // Let's implement step and then make eval call step in a loop.

        // Save State for re-entrancy
        let saved_program = self.process.program;
        let saved_mode = self.process.execution_mode.clone();
        let saved_env = self.process.current_env.clone();
        if let Some(e) = &saved_env {
            println!(
                "DEBUG: eval wrapper SAVING env. Roots: {}",
                e.iter_roots().len()
            );
        } else {
            println!("DEBUG: eval wrapper SAVING env. Roots: None");
        }
        // Take the stack to avoid cloning.
        let saved_stack = std::mem::take(&mut self.process.continuation_stack);

        // Initialize TCO state for this execution
        self.process.program = expr;
        self.process.current_env = Some(env.clone());
        // Stack is already empty because we took it
        self.process.continuation_stack.push(Continuation::Done);
        self.process.execution_mode = crate::process::ExecutionMode::Eval;

        let mut result = Ok(self.process.make_nil()); // Default

        loop {
            match self.step() {
                Ok(true) => continue,
                Ok(false) => {
                    result = Ok(self.process.program);
                    break;
                }
                Err(e) => {
                    result = Err(e);
                    break;
                }
            }
        }

        // Restore State
        self.process.program = saved_program;
        self.process.execution_mode = saved_mode;
        self.process.current_env = saved_env;
        if let Some(e) = &self.process.current_env {
            println!(
                "DEBUG: eval wrapper RESTORED env. Roots: {}",
                e.iter_roots().len()
            );
        }
        self.process.continuation_stack = saved_stack;

        return result;
    }

    /// Perform one step of TCO evaluation
    /// Returns true if execution should continue, false if finished (result in process.program)
    pub fn step(&mut self) -> Result<bool, ControlSignal> {
        let mode = self.process.execution_mode.clone();

        match mode {
            crate::process::ExecutionMode::Eval => {
                let expr = self.process.program;
                self.process.pending_redex = Some(expr);
                let env = self.process.current_env.as_ref().unwrap().clone();
                // println!("DEBUG: step loop. Roots: {}", env.iter_roots().len());
                let node = self.process.arena.get_unchecked(expr).clone();

                match node {
                    Node::Leaf(val) => {
                        match val {
                            OpaqueValue::Symbol(id) => {
                                let sym_id = SymbolId(id);
                                if self.is_self_evaluating(sym_id) {
                                    // Program remains expr
                                } else if let Some(val) = env.lookup(sym_id) {
                                    self.process.program = val;
                                } else if let Some(val) = self.process.get_value(sym_id) {
                                    self.process.program = val;
                                } else {
                                    let name = self
                                        .globals
                                        .symbols
                                        .read()
                                        .unwrap()
                                        .symbol_name(sym_id)
                                        .unwrap_or("?")
                                        .to_string();

                                    // DEBUG: Check P
                                    if name == "P" {
                                        println!(
                                            "DEBUG: PAIRS lookup failure. SymId: {:?}.",
                                            sym_id
                                        );
                                        println!("DEBUG: Env bindings keys:");
                                        for key in env.bindings.read().unwrap().keys() {
                                            println!(
                                                "  Key: {:?} Name: {:?}",
                                                key,
                                                self.globals
                                                    .symbols
                                                    .read()
                                                    .unwrap()
                                                    .symbol_name(*key)
                                            );
                                        }
                                        if let Some(p) = &env.parent {
                                            println!("DEBUG: Parent env present.");
                                        } else {
                                            println!("DEBUG: No parent env.");
                                        }
                                    }

                                    // Retrieve symbol details for the missing symbol
                                    // Retrieve symbol details for the missing symbol
                                    let sym_info = {
                                        let globals = self.globals.symbols.read().unwrap();
                                        let name =
                                            globals.symbol_name(sym_id).unwrap_or("?").to_string();
                                        let pkg = globals
                                            .get_symbol(sym_id)
                                            .and_then(|s| s.package)
                                            .unwrap_or(crate::symbol::PackageId(0))
                                            .0;
                                        format!("{}:{} ({:?})", pkg, name, sym_id)
                                    };

                                    eprintln!("DEBUG: Unbound variable failure: {}", sym_info);

                                    // Dump environment roots to see what IS bound
                                    if let Some(env) = &self.process.current_env {
                                        eprintln!("DEBUG: Current Environment Bindings:");
                                        let globals = self.globals.symbols.read().unwrap();
                                        for key in env.bindings.read().unwrap().keys() {
                                            let name = globals
                                                .symbol_name(*key)
                                                .unwrap_or("?")
                                                .to_string();
                                            let pkg = globals
                                                .get_symbol(*key)
                                                .and_then(|s| s.package)
                                                .unwrap_or(crate::symbol::PackageId(0))
                                                .0;

                                            eprintln!("  Key: {}:{} ({:?})", pkg, name, key);
                                        }
                                    }

                                    return Err(ControlSignal::Error(format!(
                                        "Variable '{}' (ID: {:?}) is not bound. Info: {}",
                                        name, sym_id, sym_info
                                    )));
                                }
                            }
                            _ => {} // Self-evaluating
                        }
                        self.process.execution_mode = crate::process::ExecutionMode::Return;
                        Ok(true)
                    }
                    Node::Stem(_) => {
                        self.process.execution_mode = crate::process::ExecutionMode::Return;
                        Ok(true)
                    }
                    Node::Fork(op, args) => self.step_application(op, args, env),
                }
            }
            crate::process::ExecutionMode::Return => {
                if let Some(cont) = self.process.continuation_stack.pop() {
                    self.apply_continuation(cont)
                } else {
                    // println!("DEBUG: step stack empty. Returning Ok(false).");
                    Ok(false) // Done
                }
            }
        }
    }

    fn is_self_evaluating(&self, sym: SymbolId) -> bool {
        if sym == self.globals.t_sym || sym == self.globals.nil_sym {
            return true;
        }
        if let Some(s) = self.globals.symbols.read().unwrap().get_symbol(sym) {
            if s.is_keyword() {
                return true;
            }
        }
        false
    }

    fn step_application(
        &mut self,
        op: NodeId,
        args: NodeId,
        env: Environment,
    ) -> Result<bool, ControlSignal> {
        // Check Special Forms
        if let Some(sym_id) = self.node_to_symbol(op) {
            let sf = &self.globals.special_forms;
            if sym_id == sf.progn {
                println!("DEBUG: Matched PROGN in step_app for op={:?}", op);
            } else {
                if self
                    .globals
                    .symbols
                    .read()
                    .unwrap()
                    .symbol_name(sym_id)
                    .unwrap_or("")
                    == "PROGN"
                {
                    println!(
                        "DEBUG: step_app MISSED PROGN. sym: {:?}, sf.progn: {:?}",
                        sym_id, sf.progn
                    );
                }
            }

            if sym_id == sf.setq {
                return self.step_setq(args, env);
            }
            if sym_id == sf.r#if {
                return self.step_if(args, env);
            }
            if sym_id == sf.progn {
                return self.step_progn(args, env);
            }
            if sym_id == sf.quote {
                if let Node::Fork(arg, _) = self.process.arena.get_unchecked(args) {
                    self.process.program = *arg;
                } else {
                    self.process.program = self.process.make_nil();
                }
                self.process.execution_mode = crate::process::ExecutionMode::Return;
                return Ok(true);
            }
            if sym_id == sf.defmacro {
                return self.step_defmacro(args, env);
            }
            if sym_id == sf.defun {
                return self.step_defun(args, env);
            }
            if sym_id == sf.function {
                eprintln!("DEBUG: step_application matched FUNCTION");
                return self.step_function(args, env);
            }
            if sym_id == sf.defvar {
                let res = self.eval_defvar(args, &env)?;
                self.process.program = res;
                self.process.execution_mode = crate::process::ExecutionMode::Return;
                return Ok(true);
            }
            if sym_id == sf.defparameter {
                let res = self.eval_defparameter(args, &env)?;
                self.process.program = res;
                self.process.execution_mode = crate::process::ExecutionMode::Return;
                return Ok(true);
            }
            if sym_id == sf.r#let {
                return self.step_let(args, env);
            }
            if sym_id == sf.multiple_value_bind {
                return self.step_multiple_value_bind(args, env);
            }
            if sym_id == sf.block {
                return self.step_block(args, env);
            }
            if sym_id == sf.return_from {
                return self.step_return_from(args, env);
            }
            if sym_id == sf.tagbody {
                return self.step_tagbody(args, env);
            }
            if sym_id == sf.go {
                return self.step_go(args, env);
            }
            if sym_id == sf.quasiquote {
                return self.step_quasiquote(args, env);
            }
            if sym_id == sf.unquote {
                return Err(ControlSignal::Error("UNQUOTE outside of QUASIQUOTE".into()));
            }
            if sym_id == sf.unquote_splicing {
                return Err(ControlSignal::Error(
                    "UNQUOTE-SPLICING outside of QUASIQUOTE".into(),
                ));
            }
        }

        // Check for Macros
        if let Some(sym_id) = self.node_to_symbol(op) {
            if let Some(&macro_idx) = self.process.macros.get(&sym_id) {
                if let Some(closure) = self.process.closures.get(macro_idx).cloned() {
                    let expanded = self._apply_macro(&closure, args)?;
                    self.process.program = expanded;
                    self.process.execution_mode = crate::process::ExecutionMode::Eval;
                    return Ok(true);
                }
            }
        }

        // Function Application
        let arg_list = self.cons_to_vec(args);

        if arg_list.is_empty() {
            // Immediate Apply (no args)
            return self.step_apply(op, Vec::new(), env);
        } else {
            // Start evaluating first arg
            let first = arg_list[0];
            let rest = arg_list[1..].to_vec();
            self.process.continuation_stack.push(Continuation::EvArgs {
                op,
                args: rest,
                vals: Vec::new(),
                env: env.clone(),
            });
            self.process.program = first;
            self.process.execution_mode = crate::process::ExecutionMode::Eval;
        }
        Ok(true)
    }

    fn step_defmacro(&mut self, args: NodeId, _env: Environment) -> Result<bool, ControlSignal> {
        // (defmacro name lambda-list &rest body)
        let args_vec = self.cons_to_vec(args);
        if args_vec.len() < 2 {
            return Err(ControlSignal::Error("defmacro: too few args".into()));
        }
        let name_node = args_vec[0];
        let lambda_list_node = args_vec[1];

        let sym = self
            .node_to_symbol(name_node)
            .ok_or_else(|| ControlSignal::Error("defmacro name must be symbol".into()))?;

        // Create Closure Body: just the list of forms (implicit progn)
        // Do NOT wrap in PROGN symbol, as apply_closure uses eval_progn which expects a list of forms.
        let body_node = if args_vec.len() > 2 {
            self.process.make_list(&args_vec[2..])
        } else {
            self.process.make_nil()
        };

        // Parse lambda list
        let parsed_lambda_list = match self.parse_lambda_list(lambda_list_node) {
            Ok(l) => l,
            Err(e) => return Err(ControlSignal::Error(e)),
        };

        // Create Closure
        let closure = crate::eval::Closure {
            lambda_list: parsed_lambda_list,
            body: body_node,
            env: crate::eval::Environment::new(),
        };

        // Register
        let closure_idx = self.process.closures.len();
        self.process.closures.push(closure);
        self.process.macros.insert(sym, closure_idx);

        // Return Name
        self.process.program = name_node;
        self.process.execution_mode = crate::process::ExecutionMode::Return;
        Ok(true)
    }

    fn step_tagbody(&mut self, args: NodeId, _env: Environment) -> Result<bool, ControlSignal> {
        let body_list = self.cons_to_vec(args);

        // Scan for tags and build map
        let mut tag_map = HashMap::new();

        for (i, node) in body_list.iter().enumerate() {
            let n = self.process.arena.inner.get_unchecked(*node);
            let tag_key = match n {
                Node::Leaf(crate::types::OpaqueValue::Symbol(s)) => {
                    Some(TagKey::Sym(crate::symbol::SymbolId(*s)))
                }
                Node::Leaf(crate::types::OpaqueValue::Integer(v)) => Some(TagKey::Int(*v)),
                _ => None,
            };

            if let Some(key) = tag_key {
                // Map this tag to the suffix of the body list starting AFTER the tag
                let suffix = body_list[i + 1..].to_vec();
                tag_map.insert(key, suffix);
            }
        }

        // Push Continuation
        self.process.continuation_stack.push(Continuation::Tagbody {
            rest: body_list,
            tag_map,
            env: _env,
        });

        // Start execution (Return mode -> pop continuation -> run logic)
        self.process.execution_mode = crate::process::ExecutionMode::Return;
        Ok(true)
    }

    fn step_go(&mut self, args: NodeId, _env: Environment) -> Result<bool, ControlSignal> {
        let args_vec = self.cons_to_vec(args);
        if args_vec.is_empty() {
            return Err(ControlSignal::Error("go: missing tag".into()));
        }
        let tag_node = args_vec[0];
        let n = self.process.arena.inner.get_unchecked(tag_node).clone();

        let tag_key = match n {
            Node::Leaf(crate::types::OpaqueValue::Symbol(s)) => {
                Some(TagKey::Sym(crate::symbol::SymbolId(s)))
            }
            Node::Leaf(crate::types::OpaqueValue::Integer(v)) => Some(TagKey::Int(v)),
            _ => None,
        };

        if let Some(key) = tag_key {
            // Unwind stack looking for matching tagbody
            let mut found = false;
            let mut depth = 0;

            for (i, cont) in self.process.continuation_stack.iter().rev().enumerate() {
                if let Continuation::Tagbody { tag_map, .. } = cont {
                    if tag_map.contains_key(&key) {
                        found = true;
                        depth = i;
                        break;
                    }
                }
            }

            if found {
                // Drop 'depth' frames from the top (0 = current top)
                let new_len = self.process.continuation_stack.len() - depth;
                self.process.continuation_stack.truncate(new_len);

                // Now top is the Tagbody. Update its 'rest'.
                if let Some(Continuation::Tagbody { tag_map, rest, .. }) =
                    self.process.continuation_stack.last_mut()
                {
                    if let Some(target_rest) = tag_map.get(&key) {
                        *rest = target_rest.clone();
                    }
                }

                self.process.execution_mode = crate::process::ExecutionMode::Return;
                self.process.program = self.process.make_nil(); // Dummy
                return Ok(true);
            } else {
                return Err(ControlSignal::Error(format!(
                    "go: tag not found: {:?}",
                    tag_node
                )));
            }
        } else {
            return Err(ControlSignal::Error("go: invalid tag".into()));
        }
    }

    fn step_block(&mut self, args: NodeId, _env: Environment) -> Result<bool, ControlSignal> {
        let args_vec = self.cons_to_vec(args);
        if args_vec.is_empty() {
            return Err(ControlSignal::Error("block: missing name".into()));
        }
        let name_node = args_vec[0];
        let name_sym = self
            .node_to_symbol(name_node)
            .ok_or_else(|| ControlSignal::Error("block: name must be a symbol".into()))?;

        // Block body (implicit progn)
        let body_forms = if args_vec.len() > 1 {
            args_vec[1..].to_vec()
        } else {
            // Block with no body returns nil
            Vec::new()
        };

        self.process.continuation_stack.push(Continuation::Block {
            name: name_sym,
            rest: body_forms,
        });

        // Start execution
        self.process.execution_mode = crate::process::ExecutionMode::Return;
        Ok(true)
    }

    fn step_return_from(&mut self, args: NodeId, _env: Environment) -> Result<bool, ControlSignal> {
        let args_vec = self.cons_to_vec(args);
        if args_vec.is_empty() {
            return Err(ControlSignal::Error("return-from: missing name".into()));
        }
        let name_node = args_vec[0];
        let name_sym = self
            .node_to_symbol(name_node)
            .ok_or_else(|| ControlSignal::Error("return-from: name must be a symbol".into()))?;

        // Optional result form (defaults to nil)
        let result_form = if args_vec.len() > 1 {
            args_vec[1]
        } else {
            self.process.make_nil()
        };

        // We need to evaluate the result form first.
        // Then Unwind.
        self.process
            .continuation_stack
            .push(Continuation::ReturnFrom { target: name_sym });

        self.process.program = result_form;
        self.process.execution_mode = crate::process::ExecutionMode::Eval;
        Ok(true)
    }

    fn step_defun(&mut self, args: NodeId, _env: Environment) -> Result<bool, ControlSignal> {
        let args_vec = self.cons_to_vec(args);
        if args_vec.len() < 2 {
            return Err(ControlSignal::Error("defun: too few args".into()));
        }
        let name_node = args_vec[0];
        let lambda_list_node = args_vec[1];

        let sym = self
            .node_to_symbol(name_node)
            .ok_or_else(|| ControlSignal::Error("defun name must be symbol".into()))?;

        // Construct Body
        let body_forms = if args_vec.len() > 2 {
            self.process.make_list(&args_vec[2..])
        } else {
            self.process.make_nil()
        };

        let progn_sym = self.globals.special_forms.progn;
        let progn_sym_val = crate::types::OpaqueValue::Symbol(progn_sym.0);
        let progn_sym_node = self.process.arena.inner.alloc(Node::Leaf(progn_sym_val));

        let body_node = self
            .process
            .arena
            .inner
            .alloc(Node::Fork(progn_sym_node, body_forms));

        // Parse lambda list
        let parsed_lambda_list = match self.parse_lambda_list(lambda_list_node) {
            Ok(l) => l,
            Err(e) => return Err(ControlSignal::Error(e)),
        };
        // Removed explicit params loop
        // let mut params = Vec::new(); // placeholder to keep rest of file valid if needed temporarily
        /*
        let mut c = lambda_list_node;
        loop {
            let node = self.process.arena.get_unchecked(c).clone();
        */
        /*
            if let Node::Fork(head, tail) = node {
                if let Some(s) = self.node_to_symbol(head) {
                    params.push(s);
                }
                c = tail;
            } else {
                break;
            }
        }
        */

        // Create Closure
        let closure = crate::eval::Closure {
            lambda_list: parsed_lambda_list,
            body: body_node,
            env: crate::eval::Environment::new(),
        };

        // Register Global Function
        let closure_idx = self.process.closures.len();
        self.process.closures.push(closure);
        self.process.functions.insert(sym, closure_idx);

        // Return Name
        self.process.program = name_node;
        self.process.execution_mode = crate::process::ExecutionMode::Return;
        Ok(true)
    }

    fn step_function(&mut self, args: NodeId, _env: Environment) -> Result<bool, ControlSignal> {
        // (function name) or (function (lambda ...))
        let args_vec = self.cons_to_vec(args);
        if args_vec.is_empty() {
            return Err(ControlSignal::Error("function: too few args".into()));
        }
        let target = args_vec[0];

        // If target is symbol, just return symbol (treated as function designator in apply)?
        // Or resolve to closure handle?
        // My invoke logic handles Symbols.
        // But `functio`n special operator should return the FUNCTION OBJECT.
        // For now, returning the symbol is enough if `apply` handles symbols.
        // `step_apply` handles symbols by lookup.
        // But `(funcall (function foo) ...)`
        // `funcall` must handle symbols.
        // If target is (lambda ...), we need to create closure and return it.
        // Implementing full closure creation here is redundant with `step_defun` / `step_defmacro`.
        // Ideally factor out `make_closure`.

        // For TCO Test (defun sum-down ...), we don't use (function ...) directly usually.
        // But `init.lisp` might use it.
        // Let's handle Symbol case (return symbol) and Lambda case (create closure).

        if let Some(_) = self.node_to_symbol(target) {
            self.process.program = target;
            self.process.execution_mode = crate::process::ExecutionMode::Return;
            return Ok(true);
        }

        // Lambda case: (lambda args body)
        // Check if head is lambda
        let node = self.process.arena.get_unchecked(target).clone();
        if let Node::Fork(head, tail) = node {
            if let Some(s) = self.node_to_symbol(head) {
                if s == self.globals.special_forms.lambda {
                    // It is (lambda params body...)
                    let tail_node = self.process.arena.get_unchecked(tail).clone();
                    if let Node::Fork(params, body_forms) = tail_node {
                        let lambda_list = match self.parse_lambda_list(params) {
                            Ok(l) => l,
                            Err(e) => return Err(ControlSignal::Error(e)),
                        };

                        // Create Progn Body
                        let progn_sym = self.globals.special_forms.progn;
                        let progn_val = crate::types::OpaqueValue::Symbol(progn_sym.0);
                        let progn_node = self.process.arena.inner.alloc(Node::Leaf(progn_val));
                        let body_expr = self
                            .process
                            .arena
                            .inner
                            .alloc(Node::Fork(progn_node, body_forms));

                        // Capture Environment
                        let captured_env = self
                            .process
                            .current_env
                            .as_ref()
                            .cloned()
                            .unwrap_or_else(|| Environment::new());

                        let closure = Closure {
                            lambda_list,
                            body: body_expr,
                            env: captured_env,
                        };

                        let closure_idx = self.process.closures.len();
                        self.process.closures.push(closure);

                        let closure_handle_val =
                            crate::types::OpaqueValue::Closure(closure_idx as u32);
                        let closure_handle = self
                            .process
                            .arena
                            .inner
                            .alloc(Node::Leaf(closure_handle_val));

                        self.process.program = closure_handle;
                        self.process.execution_mode = crate::process::ExecutionMode::Return;
                        return Ok(true);
                    } else {
                        return Err(ControlSignal::Error("function: malformed lambda".into()));
                    }
                }
            }
        }

        // Fallback: return target as is (maybe it's already a closure handle?)
        self.process.program = target;
        self.process.execution_mode = crate::process::ExecutionMode::Return;
        Ok(true)
    }

    fn step_let(&mut self, args: NodeId, env: Environment) -> Result<bool, ControlSignal> {
        self.process.current_env = Some(env);
        // (let bindings &rest body)
        // Expand to ((lambda (vars...) body...) vals...)
        let args_vec = self.cons_to_vec(args);
        if args_vec.is_empty() {
            return Err(ControlSignal::Error("let: malformed".into()));
        }

        let bindings_node = args_vec[0];
        let body_nodes = if args_vec.len() > 1 {
            &args_vec[1..]
        } else {
            &[]
        };

        // Parse bindings
        let mut vars = Vec::new();
        let mut vals = Vec::new();

        let mut c = bindings_node;
        loop {
            let node = self.process.arena.get_unchecked(c).clone();
            if let Node::Fork(head, tail) = node {
                let binding_node = self.process.arena.get_unchecked(head).clone();
                match binding_node {
                    Node::Fork(var_n, val_n_tail) => {
                        // (var val)
                        vars.push(var_n);
                        let tail_node = self.process.arena.get_unchecked(val_n_tail).clone();
                        if let Node::Fork(val_n, _) = tail_node {
                            vals.push(val_n);
                        } else {
                            vals.push(self.process.make_nil());
                        }
                    }
                    Node::Leaf(crate::types::OpaqueValue::Symbol(_)) => {
                        // var
                        vars.push(head);
                        vals.push(self.process.make_nil());
                    }
                    _ => {} // Ignore malformed binding?
                }
                c = tail;
            } else {
                break;
            }
        }

        // Construct Body (progn ...)
        let progn_sym = self.globals.special_forms.progn;
        let body_list = self.process.make_list(body_nodes);

        let progn_sym_val = crate::types::OpaqueValue::Symbol(progn_sym.0);
        let progn_sym_node = self.process.arena.inner.alloc(Node::Leaf(progn_sym_val));

        let body_form = self
            .process
            .arena
            .inner
            .alloc(Node::Fork(progn_sym_node, body_list));

        // Construct Lambda
        let lambda_sym = self.globals.special_forms.lambda;
        let vars_list = self.process.make_list(&vars);

        let lambda_sym_val = crate::types::OpaqueValue::Symbol(lambda_sym.0);
        let lambda_sym_node = self.process.arena.inner.alloc(Node::Leaf(lambda_sym_val));

        // (lambda vars body)
        let lambda_form = self
            .process
            .make_list(&[lambda_sym_node, vars_list, body_form]);

        // Construct Application: (lambda_form vals...)
        let mut app_vec = vec![lambda_form];
        app_vec.extend(vals);
        let app_form = self.process.make_list(&app_vec);

        self.process.program = app_form;
        self.process.execution_mode = crate::process::ExecutionMode::Eval;
        Ok(true)
    }

    fn step_setq(&mut self, args: NodeId, env: Environment) -> Result<bool, ControlSignal> {
        println!(
            "DEBUG: step_setq called. Env roots: {}",
            env.iter_roots().len()
        );
        self.process.current_env = Some(env.clone());
        if let Node::Fork(var_node, rest) = self.process.arena.get_unchecked(args).clone() {
            if let Node::Fork(val_expr, next) = self.process.arena.get_unchecked(rest).clone() {
                if let Some(sym) = self.node_to_symbol(var_node) {
                    let next_pairs = self.cons_to_vec(next);
                    self.process.continuation_stack.push(Continuation::EvSetq {
                        sym,
                        rest: next_pairs,
                    });
                    self.process.program = val_expr;
                    self.process.execution_mode = crate::process::ExecutionMode::Eval;
                    return Ok(true);
                }
            }
        }
        self.process.program = self.process.make_nil();
        self.process.execution_mode = crate::process::ExecutionMode::Return;
        Ok(true)
    }

    fn step_if(&mut self, args: NodeId, env: Environment) -> Result<bool, ControlSignal> {
        let env_copy = env.clone();
        self.process.current_env = Some(env);
        if let Node::Fork(test, rest) = self.process.arena.get_unchecked(args).clone() {
            let (then_branch, else_branch) = if let Node::Fork(th, rest2) =
                self.process.arena.get_unchecked(rest).clone()
            {
                let el = if let Node::Fork(el, _) = self.process.arena.get_unchecked(rest2).clone()
                {
                    el
                } else {
                    self.process.make_nil()
                };
                (th, el)
            } else {
                (self.process.make_nil(), self.process.make_nil())
            };

            self.process.continuation_stack.push(Continuation::EvIf {
                then_branch,
                else_branch,
                env: env_copy,
            });
            self.process.program = test;
            self.process.execution_mode = crate::process::ExecutionMode::Eval;
            Ok(true)
        } else {
            self.process.program = self.process.make_nil();
            self.process.execution_mode = crate::process::ExecutionMode::Return;
            Ok(true)
        }
    }

    fn step_multiple_value_bind(
        &mut self,
        args: NodeId,
        env: Environment,
    ) -> Result<bool, ControlSignal> {
        let args_vec = self.cons_to_vec(args);
        if args_vec.len() < 2 {
            return Err(ControlSignal::Error(
                "multiple-value-bind: too few args".into(),
            ));
        }
        let vars_node = args_vec[0];
        let values_form = args_vec[1];
        let body = if args_vec.len() > 2 {
            self.process.make_list(&args_vec[2..])
        } else {
            self.process.make_nil()
        };

        self.process.continuation_stack.push(Continuation::EvMvb {
            vars: vars_node,
            body,
            env: env.clone(),
        });

        self.process.program = values_form;
        self.process.current_env = Some(env);
        self.process.execution_mode = crate::process::ExecutionMode::Eval;
        Ok(true)
    }

    fn step_progn(&mut self, args: NodeId, env: Environment) -> Result<bool, ControlSignal> {
        self.process.current_env = Some(env);
        let forms = self.cons_to_vec(args);
        if forms.is_empty() {
            self.process.program = self.process.make_nil();
            self.process.execution_mode = crate::process::ExecutionMode::Return;
        } else {
            let first = forms[0];
            let rest = forms[1..].to_vec();
            self.process
                .continuation_stack
                .push(Continuation::EvProgn { rest });
            self.process.program = first;
            self.process.execution_mode = crate::process::ExecutionMode::Eval;
        }
        Ok(true)
    }

    fn apply_continuation(&mut self, cont: Continuation) -> Result<bool, ControlSignal> {
        let result = self.process.program;

        match cont {
            Continuation::Done => Ok(false),
            Continuation::EvIf {
                then_branch,
                else_branch,
                env,
            } => {
                // RESTORE ENVIRONMENT
                self.process.current_env = Some(env);

                let true_val = match self.process.arena.get_unchecked(result) {
                    Node::Leaf(OpaqueValue::Nil) => false,
                    _ => true,
                };
                if true_val {
                    self.process.program = then_branch;
                } else {
                    self.process.program = else_branch;
                }
                self.process.execution_mode = crate::process::ExecutionMode::Eval;
                Ok(true)
            }
            Continuation::EvProgn { rest } => {
                if rest.is_empty() {
                    self.process.execution_mode = crate::process::ExecutionMode::Return;
                } else {
                    let next = rest[0];
                    let remaining = rest[1..].to_vec();
                    self.process
                        .continuation_stack
                        .push(Continuation::EvProgn { rest: remaining });
                    self.process.program = next;
                    self.process.execution_mode = crate::process::ExecutionMode::Eval;
                }
                Ok(true)
            }
            Continuation::Block { name, rest } => {
                if rest.is_empty() {
                    // Block finished normally. Return result.
                    self.process.execution_mode = crate::process::ExecutionMode::Return;
                } else {
                    let next = rest[0];
                    let remaining = rest[1..].to_vec();
                    self.process.continuation_stack.push(Continuation::Block {
                        name,
                        rest: remaining,
                    });
                    self.process.program = next;
                    self.process.execution_mode = crate::process::ExecutionMode::Eval;
                }
                Ok(true)
            }
            Continuation::ReturnFrom { target } => {
                // Return value is in 'result'.
                // Unwind to find Block { name == target }.

                let mut found_depth = None;
                for (i, cont) in self.process.continuation_stack.iter().rev().enumerate() {
                    if let Continuation::Block { name, .. } = cont {
                        if *name == target {
                            found_depth = Some(i);
                            break;
                        }
                    }
                }

                if let Some(depth) = found_depth {
                    // Truncate stack.
                    let new_len = self
                        .process
                        .continuation_stack
                        .len()
                        .saturating_sub(depth + 1);
                    self.process.continuation_stack.truncate(new_len);

                    // Result is already in 'program' (passed as 'result' to apply_continuation?)
                    // apply_continuation doesn't take 'result' arg, it assumes process.program holds result if returning?
                    // Wait, apply_continuation is called when ExecutionMode::Return.
                    // The 'result' is in process.program.

                    self.process.execution_mode = crate::process::ExecutionMode::Return;
                    Ok(true)
                } else {
                    Err(ControlSignal::Error(format!(
                        "return-from: block not found"
                    )))
                }
            }
            Continuation::DebuggerRest { condition } => {
                self.process.status = crate::process::Status::Debugger(condition.clone());
                Err(ControlSignal::Debugger(condition))
            }
            Continuation::Tagbody {
                mut rest,
                tag_map,
                env,
            } => {
                // Restore environment for tagbody execution (crucial for GO)
                self.process.current_env = Some(env.clone());

                // Return from a form inside tagbody (result ignored)
                // Need to find NEXT form to execute.
                // Loop through 'rest' until we find a form that is NOT a tag.
                // Tags are Symbols or Integers.

                // Note: The 'rest' stored in continuation is what remains AFTER the form that just finished.
                // But wait, step_tagbody pushed the WHOLE body.
                // So the first time we come here is via Return mode from step_tagbody?
                // Yes, step_tagbody sets Return mode with "dummy" result.

                // We better loop here.

                // If rest is empty, we return Nil.
                // But we must modify 'rest' to advance.

                let mut next_form = None;

                while !rest.is_empty() {
                    let candidate = rest[0];
                    let node = self.process.arena.inner.get_unchecked(candidate);
                    let is_tag = match node {
                        Node::Leaf(crate::types::OpaqueValue::Symbol(_))
                        | Node::Leaf(crate::types::OpaqueValue::Integer(_)) => true,
                        _ => false,
                    };

                    if is_tag {
                        // Skip tag
                        rest = rest[1..].to_vec();
                        continue;
                    } else {
                        // Found a form
                        next_form = Some(candidate);
                        rest = rest[1..].to_vec();
                        break;
                    }
                }

                if let Some(form) = next_form {
                    // Execute this form
                    self.process.continuation_stack.push(Continuation::Tagbody {
                        rest,
                        tag_map,
                        env,
                    });
                    self.process.program = form;
                    self.process.execution_mode = crate::process::ExecutionMode::Eval;
                } else {
                    // End of tagbody, return Nil
                    self.process.execution_mode = crate::process::ExecutionMode::Return;
                    self.process.program = self.process.make_nil();
                }
                Ok(true)
            }
            Continuation::EvSetq { sym, rest } => {
                let sym_info = {
                    let globals = self.globals.symbols.read().unwrap();
                    let name = globals.symbol_name(sym).unwrap_or("?").to_string();
                    let pkg = globals
                        .get_symbol(sym)
                        .and_then(|s| s.package)
                        .unwrap_or(crate::symbol::PackageId(0))
                        .0;
                    format!("{}:{} ({:?})", pkg, name, sym)
                };

                if sym_info.contains("REST") {
                    eprintln!("DEBUG: EvSetq handling {}", sym_info);
                }

                let mut set_lexical = false;
                if let Some(env) = &self.process.current_env {
                    if env.set(sym, result) {
                        set_lexical = true;
                    }
                }

                if !set_lexical {
                    // Check for protected symbol - since we are setting global
                    if self.globals.symbols.read().unwrap().is_protected(sym) {
                        return Err(ControlSignal::Error(format!(
                            "SETQ: cannot set protected symbol {:?}",
                            self.globals
                                .symbols
                                .read()
                                .unwrap()
                                .get_symbol(sym)
                                .map(|s| s.name.as_str())
                                .unwrap_or("?")
                        )));
                    }
                    self.process.set_value(sym, result);
                }

                if rest.is_empty() {
                    self.process.execution_mode = crate::process::ExecutionMode::Return;
                } else {
                    if rest.len() >= 2 {
                        let next_var_node = rest[0];
                        let next_val_node = rest[1];
                        let remaining = rest[2..].to_vec();

                        if let Some(next_sym) = self.node_to_symbol(next_var_node) {
                            self.process.continuation_stack.push(Continuation::EvSetq {
                                sym: next_sym,
                                rest: remaining,
                            });
                            self.process.program = next_val_node;
                            self.process.execution_mode = crate::process::ExecutionMode::Eval;
                        } else {
                            return Err(ControlSignal::Error("SETQ: expected symbol".to_string()));
                        }
                    } else {
                        self.process.execution_mode = crate::process::ExecutionMode::Return;
                    }
                }
                Ok(true)
            }
            Continuation::EvArgs {
                op,
                mut args,
                mut vals,
                env,
            } => {
                // Return from arg evaluation
                vals.push(result);

                if args.is_empty() {
                    // All args evaluated. Transition to Apply.

                    // Restore environment before Apply!
                    // Although Apply captures its own env?
                    // step_apply takes env.

                    // Actually, if we restore self.process.current_env = Some(env),
                    // Crucially, if we continue execution (e.g. if apply pushes more continuations),
                    // we want the environment to be clean (unpolluted by args).
                    self.process.current_env = Some(env.clone());

                    return self.step_apply(op, vals, env);
                } else {
                    let next = args[0];
                    let rest = args[1..].to_vec();
                    self.process.continuation_stack.push(Continuation::EvArgs {
                        op,
                        args: rest,
                        vals,
                        env: env.clone(),
                    });

                    // Restore environment for next arg evaluation!
                    self.process.current_env = Some(env);

                    self.process.program = next;
                    self.process.execution_mode = crate::process::ExecutionMode::Eval;
                }
                Ok(true)
            }
            Continuation::Apply { func, saved_env } => {
                // We arrived here via explicit transition (e.g. no args).
                // Logic handled in step_apply.
                // If we use Continuation::Apply, we need to store args in it?
                // EvArgs transforms to step_apply call.
                // So we don't strictly need Continuation::Apply unless we pause DURING apply init?
                // But step_apply will handle it.
                // The case where we push Apply manually in step_application (empty args):
                // We come here. We need to know args (empty).
                // So Apply needs args.
                // Update Continuation::Apply definition?
                // Or just handle empty args inside step_application by calling step_apply directly.
                Ok(false) // Should not happen if handled directly
            }
            _ => Ok(false),
        }
    }

    fn step_apply(
        &mut self,
        op: NodeId,
        args: Vec<NodeId>,
        env: Environment,
    ) -> Result<bool, ControlSignal> {
        // Resolve operator
        // op could be Symbol or Function Object (Closure/Primitive)
        // If symbol, lookup function.
        // If symbol, lookup function.
        let func_node = if let Some(sym) = self.node_to_symbol(op) {
            // Check Lexical Function Bindings first (Lisp-2)
            if let Some(f) = env.lookup_function(sym) {
                f
            } else if let Some(f) = self.process.get_function(sym) {
                f
            } else if self.globals.primitives.contains_key(&sym) {
                op
            } else {
                let name = self
                    .globals
                    .symbols
                    .read()
                    .unwrap()
                    .symbol_name(sym)
                    .unwrap_or("?")
                    .to_string();
                return Err(ControlSignal::Error(format!(
                    "Undefined function: {} ({:?})",
                    name, sym
                )));
            }
        } else {
            op // Lambda or Closure
        };

        // Check if Primitive
        if let Some(sym) = self.node_to_symbol(func_node) {
            if let Some(prim) = self.globals.primitives.get(&sym) {
                let result = prim(self.process, self.globals, &args)?;
                self.process.program = result;
                self.process.execution_mode = crate::process::ExecutionMode::Return;
                return Ok(true);
            }
        }

        // Check for Generic Function
        if let Node::Leaf(OpaqueValue::Generic(gid)) = self.process.arena.get_unchecked(func_node) {
            return self.apply_generic_function(crate::clos::GenericId(*gid), args, &env);
        }

        // Check for NextMethod (call-next-method invocation)
        if let Node::Leaf(OpaqueValue::NextMethod(state_idx)) =
            self.process.arena.get_unchecked(func_node)
        {
            let state_idx = *state_idx as usize;
            if state_idx >= self.process.next_method_states.len() {
                return Err(ControlSignal::Error("Invalid NextMethod state".into()));
            }

            let current_state = self.process.next_method_states[state_idx].clone();
            if current_state.methods.is_empty() {
                return Err(ControlSignal::Error("No next method".into()));
            }

            let next_method_id = current_state.methods[0];
            let remaining = current_state.methods[1..].to_vec();

            // Create new state for the NEXT method
            let next_args = if args.is_empty() {
                current_state.args.clone()
            } else {
                args // Use new args
            };

            let next_state = crate::clos::NextMethodState {
                methods: remaining,
                args: next_args.clone(),
            };

            self.process.next_method_states.push(next_state);
            let next_state_idx = (self.process.next_method_states.len() - 1) as u32;

            let method = self.process.mop.get_method(next_method_id).unwrap();
            let body = method.body;

            // Wrap
            if let Node::Leaf(OpaqueValue::Closure(idx)) = self.process.arena.get_unchecked(body) {
                let wrapper = OpaqueValue::MethodWrapper(*idx, next_state_idx);
                let wrapper_node = self.process.arena.inner.alloc(Node::Leaf(wrapper));
                // Apply wrapper with next_args
                // We use step_apply to ensure recursion/TCO is handled properly
                return self.step_apply(wrapper_node, next_args, env);
            } else {
                return Err(ControlSignal::Error(
                    "Next method body is not closure".into(),
                ));
            }
        }

        let mut inject_next_method = None;
        let effective_func_node = if let Node::Leaf(OpaqueValue::MethodWrapper(idx, state)) =
            self.process.arena.get_unchecked(func_node)
        {
            inject_next_method = Some(*state);
            // We need to fetch the closure node
            let c_node = self
                .process
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Closure(*idx)));
            c_node
        } else {
            func_node
        };

        // Check if Lambda Expression (List starting with LAMBDA)
        // (lambda params body...)
        // This is necessary because LET expands to ((lambda ...) ...)
        let lambda_sym = self.globals.special_forms.lambda;
        let mut is_lambda = false;
        if let Node::Fork(head, _) = self.process.arena.inner.get_unchecked(effective_func_node) {
            if let Some(s) = self.node_to_symbol(*head) {
                if s == lambda_sym {
                    is_lambda = true;
                }
            }
        }
        let closure = if is_lambda {
            // Parse Lambda List (Code copied/adapted from step_defun)
            // func_node is (lambda params body...)
            let parts = self.cons_to_vec(effective_func_node);
            if parts.len() < 2 {
                return Err(ControlSignal::Error("lambda: too few parts".into()));
            }
            let params_node = parts[1];

            // Body is rest
            let body_nodes = if parts.len() > 2 { &parts[2..] } else { &[] };

            // Construct body progn
            let progn_sym = self.globals.special_forms.progn;
            let body_list = self.process.make_list(body_nodes); // already list? no body_nodes is slice
            let progn_sym_val = crate::types::OpaqueValue::Symbol(progn_sym.0);
            let progn_sym_node = self.process.arena.inner.alloc(Node::Leaf(progn_sym_val));
            let body_node = self
                .process
                .arena
                .inner
                .alloc(Node::Fork(progn_sym_node, body_list));

            // Parse lambda list
            let parsed_lambda_list = match self.parse_lambda_list(params_node) {
                Ok(l) => l,
                Err(e) => return Err(ControlSignal::Error(e)),
            };

            // Create Closure capturing CURRENT environment
            crate::eval::Closure {
                lambda_list: parsed_lambda_list,
                body: body_node,
                env: {
                    env.clone() // Capture application env
                },
            }
        } else {
            // Check if Closure Object
            // Node might be Leaf(Closure(idx))
            let closure_idx = {
                let node = self
                    .process
                    .arena
                    .get_unchecked(effective_func_node)
                    .clone();
                if let Node::Leaf(crate::types::OpaqueValue::Closure(idx)) = node {
                    Some(idx as usize)
                } else {
                    None
                }
            };

            if let Some(idx) = closure_idx {
                if idx >= self.process.closures.len() {
                    return Err(ControlSignal::Error("Invalid closure index".into()));
                }
                self.process.closures[idx].clone()
            } else {
                // Fallthrough to error
                // Debug node type
                let node = self.process.arena.get_unchecked(effective_func_node);
                return Err(ControlSignal::Error(format!(
                    "TCO Apply not fully implemented for {:?} (Node ID: {:?} - {:?})",
                    effective_func_node, effective_func_node, node
                )));
            }
        };

        // Execute Closure (Shared logic)
        // Bind Arguments using ParsedLambdaList logic
        // We need a helper method to perform binding because it's complex.
        // But we can implement it here or as a method on Interpreter/ParsedLambdaList.
        // Implementing as method on Interpreter is better to access Arena/Globals.

        // REWRITE BINDING LOGIC using indices
        let mut new_env: Environment = Environment::with_parent(closure.env.clone());

        // Inject call-next-method if needed
        if let Some(state_idx) = inject_next_method {
            // Find/Register CALL-NEXT-METHOD symbol
            // For efficiency, we should cache this, but for now lookup
            // Actually it is in COMMON-LISP package.
            // Or we assume it is "CALL-NEXT-METHOD" in package of the method?
            // "The function call-next-method is lexically scoped."
            // So we bind it in the environment.
            // We need the symbol ID.
            // Let's search for it.
            let cnm_sym = {
                let syms = self.globals.symbols.read().unwrap();
                let cl_pkg = syms.get_package(crate::symbol::PackageId(1)); // CL package
                cl_pkg.and_then(|p| p.find_external("CALL-NEXT-METHOD"))
            };

            if let Some(sym) = cnm_sym {
                let nm_val = OpaqueValue::NextMethod(state_idx);
                let nm_node = self.process.arena.inner.alloc(Node::Leaf(nm_val));
                new_env.set_function(sym, nm_node);
            } else {
                eprintln!("DEBUG: Could not find CALL-NEXT-METHOD symbol for binding injection");
            }
        }

        /*
        println!(
            "DEBUG: step_apply applying closure. Base env roots: {}",
            new_env.iter_roots().len()
        );
        */
        let mut arg_idx = 0;

        // 1. Required
        for &param in &closure.lambda_list.req {
            if arg_idx >= args.len() {
                return Err(ControlSignal::Error("Too few arguments".into()));
            }
            self.bind_pattern(&mut new_env, param, args[arg_idx], false)?;
            arg_idx += 1;
        }

        // 2. Optional
        for (var, init, sup) in &closure.lambda_list.opt {
            if arg_idx < args.len() {
                self.bind_pattern(&mut new_env, *var, args[arg_idx], false)?;
                if let Some(s) = sup {
                    let t_node = self.process.make_t(&self.globals);
                    new_env.bind(*s, t_node);
                }
                arg_idx += 1;
            } else {
                let val = self.eval(*init, &new_env)?;
                self.bind_pattern(&mut new_env, *var, val, false)?;
                if let Some(s) = sup {
                    new_env.bind(*s, self.process.make_nil());
                }
            }
        }

        // 3. Rest
        let rest_args = if arg_idx < args.len() {
            &args[arg_idx..]
        } else {
            &[]
        };
        if let Some(rest_sym) = closure.lambda_list.rest {
            let val = self.process.make_list(rest_args);
            new_env.bind(rest_sym, val);
        }

        // 4. Keys
        if !closure.lambda_list.key.is_empty() {
            // Check even number of rest args
            if rest_args.len() % 2 != 0 {
                // Unless &rest captured them? ANSI says error if odd keys.
                // "Order of argument processing: 1. Req, 2. Opt, 3. Rest, 4. Key"
                // "If &key is specified, there must be an even number of remaining arguments."
                // But &allow-other-keys?
                if !closure.lambda_list.allow_other_keys {
                    // Check strictly?
                    // Actually, if allow-other-keys is true, odd length is still weird?
                    // No, key/value pairs must be pairs.
                    return Err(ControlSignal::Error(
                        "Odd number of keyword arguments".into(),
                    ));
                }
            }

            for (key_sym, var, init, sup) in &closure.lambda_list.key {
                // Scan rest_args for key_sym
                // key_sym is the VAR symbol?
                // No, in parse_lambda_list we stored (key, var, init...).
                // And we decided key is the symbol itself (simple) or derived.
                // We need to match against the keywords passed in args.
                // The args contain KEYWORD symbols (usually).
                // We need to check if arg matches key_sym.

                let mut found_val = None;

                // Linear scan for now (last win? OR first win?)
                // ANSI: "Leftmost occurrence of keyword"

                let mut i = 0;
                while i < rest_args.len() {
                    let k = rest_args[i];
                    let v = if i + 1 < rest_args.len() {
                        rest_args[i + 1]
                    } else {
                        self.process.make_nil()
                    };

                    // Compare k with key_sym (keyword)
                    // k is a NodeId. key_sym is SymbolId.
                    // Get symbol from k.
                    if let Some(ks) = self.node_to_symbol(k) {
                        // Robust comparison: Pkg + Name?
                        // Ideally exact symbol ID match if interned correctly.
                        // But caller used :KEY, def used &key (x y).
                        // x is symbol X. :X is keyword.
                        // We need to compare name?

                        // Check names
                        let k_name = self
                            .globals
                            .symbols
                            .read()
                            .unwrap()
                            .symbol_name(ks)
                            .unwrap_or("")
                            .to_string();
                        let target_name = self
                            .globals
                            .symbols
                            .read()
                            .unwrap()
                            .symbol_name(*key_sym)
                            .unwrap_or("")
                            .to_string();

                        if k_name.eq_ignore_ascii_case(&target_name) {
                            // Match! (Simple name match for now)
                            found_val = Some(v);
                            break;
                        }
                    }
                    i += 2;
                }

                if let Some(val) = found_val {
                    self.bind_pattern(&mut new_env, *var, val, false)?;
                    if let Some(s) = sup {
                        let t_node = self.process.make_t(&self.globals);
                        new_env.bind(*s, t_node);
                    }
                } else {
                    let val = self.eval(*init, &new_env)?;
                    self.bind_pattern(&mut new_env, *var, val, false)?;
                    if let Some(s) = sup {
                        new_env.bind(*s, self.process.make_nil());
                    }
                }
            }

            // Check &allow-other-keys or validity of keys?
            // If not allowed, check if all keys in args are valid?
            // Skip for now for simplicity.
        }

        // 5. Aux
        for (var, init) in &closure.lambda_list.aux {
            let val = self.eval(*init, &new_env)?;
            new_env.bind(*var, val);
        }

        // Apply Process
        self.process.program = closure.body;
        self.process.current_env = Some(new_env);
        self.process.execution_mode = crate::process::ExecutionMode::Eval;
        return Ok(true);
    }

    fn cons_to_vec(&self, list: NodeId) -> Vec<NodeId> {
        let mut v = Vec::new();
        let mut c = list;
        while let Node::Fork(head, tail) = self.process.arena.get_unchecked(c) {
            v.push(*head);
            c = *tail;
        }
        v
    }

    /// Evaluate a function application or special form
    pub fn eval_application(&mut self, op: NodeId, args: NodeId, env: &Environment) -> EvalResult {
        // First, check if operator is a symbol that's a special form
        if let Some(sym_id) = self.node_to_symbol(op) {
            // Check special forms
            let sf = &self.globals.special_forms;
            if let Some(name) = self.globals.symbols.read().unwrap().symbol_name(sym_id) {
                if name == "SETQ" {
                    eprintln!(
                        "DEBUG: SETQ dispatch: {:?} vs sf.setq {:?}",
                        sym_id, sf.setq
                    );
                }
            }
            if let Some(name) = self.globals.symbols.read().unwrap().symbol_name(sym_id) {
                if name == "LET" {
                    // eprintln!("DEBUG: eval_application evaluating LET symbol. ID={:?} SF.LET={:?} Match={}", sym_id, sf.r#let, sym_id == sf.r#let);
                }
            }

            // 0. Check for macro expansion
            if let Some(&macro_idx) = self.process.macros.get(&sym_id) {
                if let Some(closure) = self.process.closures.get(macro_idx).cloned() {
                    let expanded = self._apply_macro(&closure, args)?;
                    return self.eval(expanded, env);
                }
            }

            if sym_id == sf.quote {
                return self.eval_quote(args);
            }
            if sym_id == sf.r#let {
                // println!("DEBUG: eval matched let (ID {:?})", sym_id);
                return self.eval_let(args, env);
            }
            // Debug failure to match LET
            if self
                .globals
                .symbols
                .read()
                .unwrap()
                .symbol_name(sym_id)
                .unwrap_or("?")
                == "LET"
            {
                println!(
                    "DEBUG: Failed match LET. Got {:?}, Expected {:?}",
                    sym_id, sf.r#let
                );
                let sym_table = self.globals.symbols.read().unwrap();
                let s = sym_table.get_symbol(sym_id).unwrap();
                let sf_s = sym_table.get_symbol(sf.r#let).unwrap();
                println!("DEBUG: Got Sym: {:?} Pkg: {:?}", s.name, s.package);
                println!("DEBUG: Exp Sym: {:?} Pkg: {:?}", sf_s.name, sf_s.package);
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
                eprintln!("DEBUG: eval matched FUNCTION symbol");
                return self.eval_function(args, env);
            }
            // Check if name is "FUNCTION" string but not same ID
            let sym_name_debug = self
                .globals
                .symbols
                .read()
                .unwrap()
                .symbol_name(sym_id)
                .unwrap_or("?")
                .to_string();
            if sym_name_debug == "FUNCTION" {
                eprintln!(
                    "DEBUG: eval found FUNCTION symbol but ID mismatch! Got {:?} Expected {:?}",
                    sym_id, sf.function
                );
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
            if sym_id == sf.defclass {
                return self.eval_defclass(args, env);
            }
            if sym_id == sf.defmethod {
                return self.eval_defmethod(args, env);
            }
            if sym_id == sf.handler_bind {
                return self.eval_handler_bind(args, env);
            }
            if sym_id == sf.defvar {
                return self.eval_defvar(args, env);
            }
            if sym_id == sf.defparameter {
                return self.eval_defparameter(args, env);
            }
            if sym_id == sf.quasiquote {
                return self.eval_quasiquote(args, env);
            }
            if sym_id == sf.locally {
                return self.eval_locally(args, env);
            }

            // Check if symbol is a primitive
            if let Some(&prim_fn) = self.globals.primitives.get(&sym_id) {
                // Evaluate arguments
                let mut evaluated_args = Vec::new();
                let mut current = args;
                while let Node::Fork(arg, rest) = self.process.arena.get_unchecked(current).clone()
                {
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
        } else {
            // eprintln!("DEBUG: eval_application op is NOT a symbol! Op Node: {:?}", op);
            match self.process.arena.inner.get_unchecked(op) {
                // Node::Fork(_, _) => eprintln!("DEBUG: Op is a List (Fork)"),
                // Node::Leaf(val) => eprintln!("DEBUG: Op is a Leaf: {:?}", val),
                _ => {}
            }
        }

        // Evaluate operator
        let op_val = self.eval(op, env)?;

        // Apply
        self.apply_function(op_val, args, env)
    }

    /// Apply Generic Function
    fn apply_generic_function(
        &mut self,
        gid: crate::clos::GenericId,
        args: Vec<NodeId>,
        _env: &Environment,
    ) -> Result<bool, ControlSignal> {
        let arg_classes: Vec<_> = args.iter().map(|&a| self.get_arg_class(a)).collect();
        let methods = self
            .process
            .mop
            .compute_applicable_methods(gid, &arg_classes);

        if methods.is_empty() {
            return Err(ControlSignal::Error(format!(
                "No applicable method for generic function {:?} with args {:?}",
                gid, args
            )));
        }

        // Method Chain Logic
        let first_method_id = methods[0];
        let remaining_methods = methods[1..].to_vec();

        let state = crate::clos::NextMethodState {
            methods: remaining_methods,
            args: args.clone(),
        };

        self.process.next_method_states.push(state);
        let state_idx = (self.process.next_method_states.len() - 1) as u32;

        let method = self.process.mop.get_method(first_method_id).unwrap();

        // Method body is expected to be a Closure NodeId
        let method_body_node = method.body;

        // Check if method body is a closure
        let closure_idx = if let Node::Leaf(OpaqueValue::Closure(idx)) =
            self.process.arena.get_unchecked(method_body_node)
        {
            Some(*idx)
        } else {
            None
        };

        if let Some(idx) = closure_idx {
            // Create Wrapper
            let wrapper = OpaqueValue::MethodWrapper(idx, state_idx);
            let wrapper_node = self.process.arena.inner.alloc(Node::Leaf(wrapper));

            // Apply wrapper
            self.step_apply(wrapper_node, args, Environment::new())
        } else {
            let body_str = {
                let syms = self.globals.symbols.read().unwrap();
                crate::printer::print_to_string(&self.process.arena.inner, &syms, method_body_node)
            };
            Err(ControlSignal::Error(format!(
                "Method body is not a closure code: {} ({:?})",
                body_str,
                self.process.arena.get_unchecked(method_body_node)
            )))
        }
    }

    fn get_arg_class(&self, arg: NodeId) -> crate::clos::ClassId {
        match self.process.arena.get_unchecked(arg) {
            Node::Leaf(OpaqueValue::Instance(id)) => {
                if let Some(inst) = self.process.mop.get_instance(*id as usize) {
                    inst.class
                } else {
                    self.process.mop.standard_object
                }
            }
            _ => self.process.mop.t_class, // Fallback for now (should handle primitive mapping)
        }
    }

    /// Convert a node to a SymbolId if it represents a symbol
    pub fn node_to_symbol(&self, node_id: NodeId) -> Option<SymbolId> {
        let node = self.process.arena.get_unchecked(node_id);
        match node {
            Node::Leaf(OpaqueValue::Symbol(id)) => Some(SymbolId(*id)),
            Node::Leaf(OpaqueValue::Nil) => Some(self.globals.nil_sym),
            _ => None,
        }
    }

    /// Check if a node is NIL
    pub fn is_nil(&self, node_id: NodeId) -> bool {
        let node = self.process.arena.get_unchecked(node_id);
        matches!(node, Node::Leaf(OpaqueValue::Nil))
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
            // Check if true (not nil)
            let is_true = !self.is_nil(test_val);

            if let Node::Fork(then_expr, else_rest) = self.process.arena.get_unchecked(rest).clone()
            {
                if is_true {
                    self.eval(then_expr, env)
                } else {
                    // Check for else clause
                    if let Node::Fork(else_expr, _) =
                        self.process.arena.get_unchecked(else_rest).clone()
                    {
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
                    if let Node::Fork(val_node, next) =
                        self.process.arena.get_unchecked(rest).clone()
                    {
                        // Get symbol (handle compiled (SYMBOL-VALUE 'x) pattern)
                        let raw_sym_opt = self.node_to_symbol(var_node).or_else(|| {
                            if let Node::Fork(op, arg) = self.process.arena.get_unchecked(var_node)
                            {
                                if let Some(op_sym) = self.node_to_symbol(*op) {
                                    if let Some(name) =
                                        self.globals.symbols.read().unwrap().symbol_name(op_sym)
                                    {
                                        eprintln!("DEBUG: eval_setq saw fork with op: {}", name);
                                        if name == "SYMBOL-VALUE" {
                                            let res = self.node_to_symbol(*arg);
                                            eprintln!("DEBUG: eval_setq extracted arg: {:?}", res);
                                            return res;
                                        }
                                    } else {
                                        eprintln!("DEBUG: eval_setq op symbol has no name");
                                    }
                                } else {
                                    eprintln!("DEBUG: eval_setq op is not a symbol");
                                }
                            } else {
                                eprintln!("DEBUG: eval_setq var_node is not Fork or Symbol");
                            }
                            None
                        });

                        if let Some(sym) = raw_sym_opt {
                            let val = self.eval(val_node, env)?;

                            // DEBUG
                            let found = env.set(sym, val);
                            if found {
                                result = val;
                            } else {
                                eprintln!(
                                    "DEBUG: eval_setq symbol {:?} NOT found in lexical env",
                                    sym
                                );
                                // Check for protected symbol
                                if self.globals.symbols.read().unwrap().is_protected(sym) {
                                    return Err(ControlSignal::Error(format!(
                                        "SETQ: cannot set protected symbol {:?}",
                                        self.globals
                                            .symbols
                                            .read()
                                            .unwrap()
                                            .get_symbol(sym)
                                            .map(|s| s.name.as_str())
                                            .unwrap_or("?")
                                    )));
                                }

                                // Set in Process Dictionary
                                self.process.set_value(sym, val);
                                result = val;
                            }
                            result = val;
                        } else {
                            eprintln!(
                                "DEBUG: eval_setq failed to extract symbol from {:?}",
                                var_node
                            );
                        }
                        current = next;
                    } else {
                        eprintln!(
                            "DEBUG: eval_setq broke loop on val parsing. rest={:?}",
                            self.process.arena.get_unchecked(rest)
                        );
                        break;
                    }
                }
                _ => {
                    eprintln!(
                        "DEBUG: eval_setq broke loop on var parsing. current={:?}",
                        self.process.arena.get_unchecked(current)
                    );
                    break;
                }
            }
        }

        Ok(result)
    }

    /// Helper to separate declarations from body forms
    /// Returns (declarations, body_forms)
    /// Declarations are ignored for now, but we need to parse them to execution.
    fn parse_body(&self, body: NodeId) -> (Vec<NodeId>, NodeId) {
        let mut decls = Vec::new();
        let mut current = body;
        let mut body_start = body;

        while let Node::Fork(form, rest) = self.process.arena.get_unchecked(current).clone() {
            // Check if form is (declare ...)
            if let Node::Fork(car, _) = self.process.arena.get_unchecked(form).clone() {
                if let Some(sym) = self.node_to_symbol(car) {
                    if sym == self.globals.special_forms.declare {
                        decls.push(form);
                        current = rest;
                        body_start = rest;
                        continue;
                    }
                }
            }
            break;
        }

        (decls, body_start)
    }

    /// (locally declare* body*) -> evaluate body sequentially
    fn eval_locally(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        let (_decls, body) = self.parse_body(args);
        // We ignore declarations for now
        self.eval_progn(body, env)
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
                        if let Node::Fork(var_node, val_rest) =
                            self.process.arena.get_unchecked(binding).clone()
                        {
                            if let Some(sym) = self.node_to_symbol(var_node) {
                                if let Node::Fork(val_node, _) =
                                    self.process.arena.get_unchecked(val_rest).clone()
                                {
                                    let val = self.eval(val_node, env)?; // Note: parallel let (eval in old env)
                                    eprintln!("DEBUG: eval_let binding {:?} to value", sym);
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
            let (_decls, body_start) = self.parse_body(body);
            self.eval_progn(body_start, &new_env)
        } else {
            Ok(self.process.make_nil())
        }
    }

    /// (lambda (params) body*) -> create closure
    fn eval_lambda(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(params, body) = self.process.arena.get_unchecked(args).clone() {
            // Parse parameter list
            let parsed_lambda_list = match self.parse_lambda_list(params) {
                Ok(l) => l,
                Err(e) => return Err(ControlSignal::Error(e)),
            };

            // Create closure
            let closure = Closure {
                lambda_list: parsed_lambda_list,
                body,
                env: env.clone(),
            };

            let closure_idx = self.process.closures.len();
            self.process.closures.push(closure);

            // Return a node representing the closure
            // We use a Leaf with Closure handle
            let closure_node = self
                .process
                .arena
                .alloc(Node::Leaf(OpaqueValue::Closure(closure_idx as u32)));
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
                if let Some(s) = self.node_to_symbol(car) {
                    if s == self.globals.special_forms.lambda {
                        return self.eval(name, env);
                    } else {
                        eprintln!(
                            "DEBUG: eval_function found list but CAR {:?} is not LAMBDA {:?}",
                            s, self.globals.special_forms.lambda
                        );
                        // Debug print the car name
                        let sym_name = self
                            .globals
                            .symbols
                            .read()
                            .unwrap()
                            .symbol_name(s)
                            .unwrap_or("?")
                            .to_string();
                        eprintln!("DEBUG: eval_function CAR symbol name: {}", sym_name);
                    }
                } else {
                    eprintln!(
                        "DEBUG: eval_function found list but CAR is not symbol: {:?}",
                        car
                    );
                }
            } else {
                eprintln!("DEBUG: eval_function arg is not a list: {:?}", name);
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
                None => {
                    return Err(ControlSignal::Error(
                        "DEFUN: first argument must be a symbol".to_string(),
                    ))
                }
            };

            if let Node::Fork(params, body) = self.process.arena.get_unchecked(rest).clone() {
                // Validate params is a list (nil or Fork)
                match self.process.arena.get_unchecked(params) {
                    Node::Leaf(OpaqueValue::Nil) => {} // Empty params OK
                    Node::Fork(_, _) => {}             // List params OK
                    _ => {
                        return Err(ControlSignal::Error(format!(
                            "DEFUN: parameter list must be a list, not {:?}",
                            self.process.arena.get_unchecked(params)
                        )))
                    }
                }

                // Parse parameter list
                let parsed_lambda_list = match self.parse_lambda_list(params) {
                    Ok(l) => l,
                    Err(e) => return Err(ControlSignal::Error(e)),
                };

                // Validate body exists
                if let Node::Leaf(OpaqueValue::Nil) = self.process.arena.get_unchecked(body) {
                    return Err(ControlSignal::Error(
                        "DEFUN: function body is required".to_string(),
                    ));
                }

                // Parse declarations
                let (_decls, body_start) = self.parse_body(body);
                // Note: DEFUN body is an implicit block named 'name'.

                // Wrap body in BLOCK name
                let block_sym = self.globals.special_forms.block;
                let block_sym_node = self
                    .process
                    .arena
                    .inner
                    .alloc(Node::Leaf(crate::types::OpaqueValue::Symbol(block_sym.0)));
                // We need (BLOCK name body...)
                let block_args = self
                    .process
                    .arena
                    .inner
                    .alloc(Node::Fork(name_node, body_start));
                let block_form = self
                    .process
                    .arena
                    .inner
                    .alloc(Node::Fork(block_sym_node, block_args));

                // Create closure
                let closure = Closure {
                    lambda_list: parsed_lambda_list,
                    body: block_form,
                    env: env.clone(),
                };

                let closure_idx = self.process.closures.len();
                self.process.closures.push(closure);

                // Create closure node
                let closure_node = self
                    .process
                    .arena
                    .alloc(Node::Leaf(OpaqueValue::Closure(closure_idx as u32)));

                // Bind to process's function table (local defun)
                self.process.set_function(name_sym, closure_node);

                // Return the function name symbol
                return Ok(name_node);
            } else {
                return Err(ControlSignal::Error(
                    "DEFUN: syntax is (defun name (params) body)".to_string(),
                ));
            }
        }

        Err(ControlSignal::Error(
            "DEFUN: syntax is (defun name (params) body)".to_string(),
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
                    Err(ControlSignal::ReturnFrom {
                        name: ret_name,
                        value,
                    }) if ret_name == name => Ok(value),
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
                let value = if let Node::Fork(val_node, _) =
                    self.process.arena.get_unchecked(rest).clone()
                {
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
                Err(ControlSignal::Throw {
                    tag: throw_tag,
                    value,
                }) => {
                    // Check if tags match (using EQ semantics)
                    if throw_tag == tag {
                        Ok(value)
                    } else {
                        Err(ControlSignal::Throw {
                            tag: throw_tag,
                            value,
                        })
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
            let value =
                if let Node::Fork(val_expr, _) = self.process.arena.get_unchecked(rest).clone() {
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
                    Err(ControlSignal::Error(format!(
                        "Invalid closure index: {}",
                        idx
                    )))
                }
            }
            Node::Leaf(OpaqueValue::Generic(id)) => {
                self.apply_generic(id, args, env)
                // Ok(self.process.make_nil())
            }
            _ => {
                // Fall back to tree calculus reduction
                // Evaluate arguments and apply one at a time (curried)
                use crate::search::reduce;

                let mut result = func;
                let mut current = args;

                // Walk through argument list
                while let Node::Fork(arg_expr, rest) =
                    self.process.arena.get_unchecked(current).clone()
                {
                    // Evaluate the argument
                    let arg_val = self.eval(arg_expr, env)?;

                    // Apply Tree Calculus: (result arg_val)
                    let app = self.process.arena.alloc(Node::Fork(result, arg_val));
                    result = reduce(
                        &mut self.process.arena.inner,
                        app,
                        &mut self.process.eval_context,
                    );

                    current = rest;
                }

                Ok(self.try_reduce_primitive(result, env))
            }
        }
    }

    pub fn apply_values(&mut self, func: NodeId, args: NodeId, env: &Environment) -> EvalResult {
        let func_node = self.process.arena.get_unchecked(func).clone();

        match func_node {
            Node::Leaf(OpaqueValue::Closure(idx)) => {
                // Closure application
                if let Some(closure) = self.process.closures.get(idx as usize).cloned() {
                    self.apply_closure(&closure, args, env)
                } else {
                    Err(ControlSignal::Error(format!(
                        "Invalid closure index: {}",
                        idx
                    )))
                }
            }
            Node::Leaf(OpaqueValue::Generic(id)) => self.apply_generic(id, args, env),
            _ => {
                // Fall back to tree calculus reduction (without evaluation of args)
                use crate::search::reduce;

                let mut result = func;
                let mut current = args;

                // Walk through argument list
                while let Node::Fork(arg, rest) = self.process.arena.get_unchecked(current).clone()
                {
                    // Use argument as value directly
                    let arg_val = arg;

                    // Apply Tree Calculus: (result arg_val)
                    let app = self.process.arena.alloc(Node::Fork(result, arg_val));
                    result = reduce(
                        &mut self.process.arena.inner,
                        app,
                        &mut self.process.eval_context,
                    );

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
        // Resolve function symbol (handle compiled (SYMBOL-VALUE 'x) pattern)
        let resolved = if let Some(sym) = self.node_to_symbol(head) {
            Some((sym, head))
        } else {
            // Check for SYMBOL-VALUE
            if let Node::Fork(op, arg) = self.process.arena.get_unchecked(head) {
                if let Some(op_sym) = self.node_to_symbol(*op) {
                    if let Some(name) = self.globals.symbols.read().unwrap().symbol_name(op_sym) {
                        if name == "SYMBOL-VALUE" {
                            if let Some(sym) = self.node_to_symbol(*arg) {
                                // arg is the node containing the symbol
                                Some((sym, *arg))
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            }
        };

        if let Some((sym, real_head)) = resolved {
            // 0. Check for Special Forms (Lisp) via eval_application
            // Only if structure allows it (Head + args)
            // Tree Calculus Reader produces left-associative application: ((f a) b)
            // Spine: [f, a, b]
            // Lisp eval expects (f . (a . (b . nil)))
            if spine.len() >= 1 {
                // Check if symbol is a special form
                let is_sf = {
                    let sf = &self.globals.special_forms;
                    sym == sf.setq
                        || sym == sf.r#let
                        || sym == sf.quote
                        || sym == sf.r#if
                        || sym == sf.progn
                        || sym == sf.function
                        || sym == sf.defun
                        || sym == sf.defmacro
                        || sym == sf.defclass
                        || sym == sf.defmethod
                };

                if is_sf {
                    // Reconstruct Lisp-style arg list from spine[1..]
                    let args_list = self.process.make_list(&spine[1..]);

                    match self.eval_application(real_head, args_list, _env) {
                        Ok(res) => return res,
                        Err(ControlSignal::Error(msg)) => {
                            self.process.status = crate::process::Status::Failed(msg);
                            return root;
                        }
                        Err(_) => return root,
                    }
                }
            }

            // Check primitives
            if self
                .globals
                .symbols
                .read()
                .unwrap()
                .symbol_name(sym)
                .unwrap_or("")
                == "PROGN"
            {
                println!("DEBUG: CAUGHT eval(PROGN)! sym={:?}", sym);
                let bt = std::backtrace::Backtrace::capture();
                println!("Backtrace:\n{:?}", bt);
            }
            if let Some(name) = self.globals.symbols.read().unwrap().symbol_name(sym) {
                eprintln!("DEBUG: Checking primitive: {} ({:?})", name, sym);
            }
            if let Some(&prim_fn) = self.globals.primitives.get(&sym) {
                eprintln!("DEBUG: Primitive found: {:?}", sym);
                // We have a primitive!
                let raw_args = &spine[1..];

                // Evaluate arguments (Force strictness for primitives)
                // Compiled code reduction is lazy (Normal Order), but primitives expect values.
                let mut evaluated_args = Vec::with_capacity(raw_args.len());
                for &arg in raw_args {
                    // We use the passed environment. For compiled code, this usually works
                    // as free variables are globals.
                    // Use reduce instead of eval because args are Tree Calculus terms (Forks), not Lisp lists.
                    let val = self.eval_arg(arg);
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
                    Err(ControlSignal::Error(msg)) => {
                        eprintln!("DEBUG: Swallowed error in try_reduce_primitive: {}", msg);
                        self.process.status = crate::process::Status::Failed(msg);
                        return root;
                    }
                    Err(e) => {
                        eprintln!("DEBUG: Swallowed signal in try_reduce_primitive: {:?}", e);
                        return root; // Fallback on error (keep stuck state)
                    }
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
        // 1. Required
        for &param in &closure.lambda_list.req {
            if let Node::Fork(arg_expr, rest) =
                self.process.arena.inner.get_unchecked(current_arg).clone()
            {
                let val = self.eval(arg_expr, env)?;
                self.bind_pattern(&mut new_env, param, val, false)?;
                current_arg = rest;
            } else {
                return Err(ControlSignal::Error(format!(
                    "Too few arguments: expected at least {}",
                    closure.lambda_list.req.len()
                )));
            }
        }

        // 2. Optional
        for (var, init, sup) in &closure.lambda_list.opt {
            if let Node::Fork(arg_expr, rest) =
                self.process.arena.inner.get_unchecked(current_arg).clone()
            {
                let val = self.eval(arg_expr, env)?;
                self.bind_pattern(&mut new_env, *var, val, false)?;
                if let Some(s) = sup {
                    let t_val = self.process.make_t(&self.globals);
                    new_env.bind(*s, t_val);
                }
                current_arg = rest;
            } else {
                let val = self.eval(init.clone(), &new_env)?;
                self.bind_pattern(&mut new_env, *var, val, false)?;
                if let Some(s) = sup {
                    new_env.bind(*s, self.process.make_nil());
                }
            }
        }

        // 3. Collect Rest (Evaluated)
        let mut rest_vals = Vec::new();
        while let Node::Fork(arg_expr, rest) =
            self.process.arena.inner.get_unchecked(current_arg).clone()
        {
            let val = self.eval(arg_expr, env)?;
            rest_vals.push(val);
            current_arg = rest;
        }

        // Bind Rest
        if let Some(rest_sym) = closure.lambda_list.rest {
            let rest_list = self.process.make_list(&rest_vals);
            new_env.bind(rest_sym, rest_list);
        }

        // 4. Keys
        if !closure.lambda_list.key.is_empty() {
            if rest_vals.len() % 2 != 0 && !closure.lambda_list.allow_other_keys {
                return Err(ControlSignal::Error(
                    "Odd number of keyword arguments".into(),
                ));
            }

            for (key_sym, var, init, sup) in &closure.lambda_list.key {
                let mut found_val = None;
                let mut i = 0;
                while i < rest_vals.len() {
                    let k = rest_vals[i];
                    if let Some(ks) = self.node_to_symbol(k) {
                        let k_name = self
                            .globals
                            .symbols
                            .read()
                            .unwrap()
                            .symbol_name(ks)
                            .unwrap_or("")
                            .to_string();
                        let target_name = self
                            .globals
                            .symbols
                            .read()
                            .unwrap()
                            .symbol_name(*key_sym)
                            .unwrap_or("")
                            .to_string();
                        if k_name.eq_ignore_ascii_case(&target_name) {
                            if i + 1 < rest_vals.len() {
                                found_val = Some(rest_vals[i + 1]);
                            } else {
                                found_val = Some(self.process.make_nil());
                            }
                            break;
                        }
                    }
                    i += 2;
                }

                if let Some(val) = found_val {
                    self.bind_pattern(&mut new_env, *var, val, false)?;
                    if let Some(s) = sup {
                        let t_val = self.process.make_t(&self.globals);
                        new_env.bind(*s, t_val);
                    }
                } else {
                    let val = self.eval(*init, &new_env)?;
                    self.bind_pattern(&mut new_env, *var, val, false)?;
                    if let Some(s) = sup {
                        new_env.bind(*s, self.process.make_nil());
                    }
                }
            }
        }

        // 5. Aux
        for (var, init) in &closure.lambda_list.aux {
            let val = self.eval(*init, &new_env)?;
            new_env.bind(*var, val);
        }

        // Evaluate body
        self.eval_progn(closure.body, &new_env)
    }

    /// Apply a macro closure to arguments (no eval of args)
    pub fn _apply_macro(&mut self, closure: &Closure, args: NodeId) -> EvalResult {
        // Create environment from closure's captured environment
        let mut new_env = crate::eval::Environment::with_parent(closure.env.clone());

        // Bind arguments UNEVALUATED
        // Bind arguments UNEVALUATED using ParsedLambdaList
        let mut current_arg = args;

        // 1. Required
        for &param in &closure.lambda_list.req {
            match self.process.arena.inner.get_unchecked(current_arg).clone() {
                Node::Fork(arg_expr, rest) => {
                    self.bind_pattern(&mut new_env, param, arg_expr, true)?;
                    current_arg = rest;
                }
                _ => {
                    // Macro missing required arg?
                    // Bind nil or error?
                    let nil_node = self.process.make_nil();
                    self.bind_pattern(&mut new_env, param, nil_node, true)?;
                }
            }
        }

        // 2. Optional
        for (param, _init, _sup) in &closure.lambda_list.opt {
            match self.process.arena.inner.get_unchecked(current_arg).clone() {
                Node::Fork(arg_expr, rest) => {
                    self.bind_pattern(&mut new_env, *param, arg_expr, true)?;
                    current_arg = rest;
                }
                _ => {
                    let nil_node = self.process.make_nil();
                    self.bind_pattern(&mut new_env, *param, nil_node, true)?;
                }
            }
        }

        // 3. Rest
        if let Some(rest_sym) = closure.lambda_list.rest {
            println!("DEBUG: bind rest {:?} to {:?}", rest_sym, current_arg);
            new_env.bind(rest_sym, current_arg);
        }

        // Evaluate body - this produces the expansion
        println!(
            "DEBUG: apply_macro calling eval_progn. Env keys count: {}",
            new_env.bindings.read().unwrap().len()
        );
        let expansion = self.eval_progn(closure.body, &new_env)?;
        Ok(expansion)
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
        let applicable = self
            .process
            .mop
            .compute_applicable_methods(gf_id, &arg_classes);

        if applicable.is_empty() {
            return Err(ControlSignal::Error(format!(
                "No applicable method for generic function {:?} with args {:?}",
                gf_id, arg_classes
            )));
        }

        // 4. Call most specific method (primary only for now)
        let method_id = applicable[0];
        let method = self.process.mop.get_method(method_id).unwrap();
        let method_body = method.body;

        // Apply method closure
        if let Node::Leaf(OpaqueValue::Closure(idx)) =
            self.process.arena.inner.get_unchecked(method_body).clone()
        {
            if let Some(closure) = self.process.closures.get(idx as usize).cloned() {
                // Manual binding
                let mut method_env = Environment::with_parent(closure.env.clone());
                if executed_args.len() != closure.lambda_list.req.len() {
                    return Err(ControlSignal::Error(
                        "Method argument count mismatch".to_string(),
                    ));
                }
                for (param, val) in closure.lambda_list.req.iter().zip(executed_args.iter()) {
                    self.bind_pattern(&mut method_env, *param, *val, false)?;
                }
                return self.eval_progn(closure.body, &method_env);
            }
        }

        // Fallback
        Err(ControlSignal::Error(
            "Method body is not a valid closure".to_string(),
        ))
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
                if let Node::Fork(params, body) =
                    self.process.arena.inner.get_unchecked(rest).clone()
                {
                    // Parse parameter list
                    let parsed_lambda_list = match self.parse_lambda_list(params) {
                        Ok(l) => l,
                        Err(e) => return Err(ControlSignal::Error(e)),
                    };

                    // Create closure
                    let closure = Closure {
                        lambda_list: parsed_lambda_list,
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
        if let Node::Fork(bindings_node, body) =
            self.process.arena.inner.get_unchecked(args).clone()
        {
            let mut handlers = Vec::new();

            // Iterate over bindings list
            let mut current_binding = bindings_node;
            while let Node::Fork(binding, rest) = self
                .process
                .arena
                .inner
                .get_unchecked(current_binding)
                .clone()
            {
                // Binding: (type handler)
                if let Node::Fork(type_node, handler_pair) =
                    self.process.arena.inner.get_unchecked(binding).clone()
                {
                    if let Node::Fork(handler_expr, _) =
                        self.process.arena.inner.get_unchecked(handler_pair).clone()
                    {
                        // (handler nil) or (handler . nil)
                        // Resolve type
                        // For Phase 7, we support 'error', 'warning', 'condition' symbols map to built-in types
                        // In real CL, we'd look up class/condition-type.
                        let type_id = if let Some(sym) = self.node_to_symbol(type_node) {
                            let name = self
                                .globals
                                .symbols
                                .read()
                                .unwrap()
                                .get_symbol(sym)
                                .unwrap()
                                .name
                                .clone();
                            if name == "ERROR" {
                                self.process.conditions.error_type
                            } else if name == "WARNING" {
                                self.process.conditions.warning_type
                            } else {
                                self.process.conditions.condition_type
                            } // Default to condition
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
                if let Node::Fork(supers_node, rest2) =
                    self.process.arena.inner.get_unchecked(rest).clone()
                {
                    let mut supers = Vec::new(); // Collect super classes
                                                 // Iterate supers_node list
                    let mut current = supers_node;
                    while let Node::Fork(super_name, next) =
                        self.process.arena.inner.get_unchecked(current).clone()
                    {
                        if let Some(s_sym) = self.node_to_symbol(super_name) {
                            if let Some(id) = self.process.mop.find_class(s_sym) {
                                supers.push(id);
                            }
                        }
                        current = next;
                    }

                    if let Node::Fork(slots_node, _) =
                        self.process.arena.inner.get_unchecked(rest2).clone()
                    {
                        let mut slots = Vec::new();
                        let mut current_slot = slots_node;
                        while let Node::Fork(slot_spec, next) =
                            self.process.arena.inner.get_unchecked(current_slot).clone()
                        {
                            // Slot spec can be symbol or list
                            let slot_name = if let Some(sym) = self.node_to_symbol(slot_spec) {
                                sym
                            } else if let Node::Fork(name, _) =
                                self.process.arena.inner.get_unchecked(slot_spec).clone()
                            {
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
                if let Node::Fork(params_node, body) =
                    self.process.arena.inner.get_unchecked(rest).clone()
                {
                    // Parse parameters and specializers
                    let mut params = Vec::new();
                    let mut params_nodes = Vec::new(); // For Closure
                    let mut specializers = Vec::new();

                    let mut current = params_node;
                    while let Node::Fork(param_spec, next) =
                        self.process.arena.inner.get_unchecked(current).clone()
                    {
                        // param_spec is (name class) or name
                        if let Some(sym) = self.node_to_symbol(param_spec) {
                            // Unspecialized (T)
                            params.push(sym);
                            params_nodes.push(param_spec);
                            specializers.push(self.process.mop.t_class);
                        } else if let Node::Fork(pname, ptype_rest) =
                            self.process.arena.inner.get_unchecked(param_spec).clone()
                        {
                            if let Some(psym) = self.node_to_symbol(pname) {
                                params.push(psym);
                                params_nodes.push(pname);
                                // Get class
                                let class_id = if let Node::Fork(cname, _) =
                                    self.process.arena.inner.get_unchecked(ptype_rest).clone()
                                {
                                    if let Some(csym) = self.node_to_symbol(cname) {
                                        self.process
                                            .mop
                                            .find_class(csym)
                                            .unwrap_or(self.process.mop.t_class)
                                    } else {
                                        self.process.mop.t_class
                                    }
                                } else {
                                    self.process.mop.t_class
                                };
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
                    let mut lambda_list = ParsedLambdaList::default();
                    lambda_list.req = params_nodes;
                    let closure = Closure {
                        lambda_list,
                        body: body,
                        env: env.clone(),
                    };
                    let closure_idx = self.process.closures.len();
                    self.process.closures.push(closure);

                    // Closure Node
                    // Closure Node
                    let closure_node = self
                        .process
                        .arena
                        .inner
                        .alloc(Node::Leaf(OpaqueValue::Closure(closure_idx as u32)));

                    // Add method
                    self.process
                        .mop
                        .add_method(gf_id, specializers, Vec::new(), closure_node);

                    // Bind generic function to symbol function cell if not already
                    let gf_val = self
                        .process
                        .arena
                        .inner
                        .alloc(Node::Leaf(OpaqueValue::Generic(gf_id.0)));
                    self.process.set_function(name_sym, gf_val);

                    return Ok(name_node);
                }
            }
        }
        Ok(self.process.make_nil())
    }

    fn eval_defvar(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(name_node, rest) = self.process.arena.inner.get_unchecked(args).clone() {
            if let Some(name_sym) = self.node_to_symbol(name_node) {
                // Check if variable is already bound in Process Dictionary (Global)
                if self.process.get_value(name_sym).is_none() {
                    if let Node::Fork(init_node, _rest2) =
                        self.process.arena.inner.get_unchecked(rest).clone()
                    {
                        let val = self.eval(init_node, env)?;
                        self.process.set_value(name_sym, val);
                    }
                    // If no init-value, variable remains unbound but declared "special".
                    // We don't track "special" declarations strictly yet, but existing in dict (even as none?)
                    // Process.get_value returns Option<NodeId>. If None, unbound.
                    // But defvar with no value should declare it.
                    // For now, if no init value, do nothing (it's unbound).
                }
                return Ok(name_node);
            }
        }
        Ok(self.process.make_nil())
    }

    fn eval_defparameter(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(name_node, rest) = self.process.arena.inner.get_unchecked(args).clone() {
            if let Some(name_sym) = self.node_to_symbol(name_node) {
                if let Node::Fork(init_node, _rest2) =
                    self.process.arena.inner.get_unchecked(rest).clone()
                {
                    let val = self.eval(init_node, env)?;
                    self.process.set_value(name_sym, val);
                    return Ok(name_node);
                } else {
                    return Err(ControlSignal::Error(
                        "DEFPARAMETER requires an initial value".to_string(),
                    ));
                }
            }
        }
        Err(ControlSignal::Error(
            "DEFPARAMETER requires a name".to_string(),
        ))
    }

    fn step_quasiquote(&mut self, args: NodeId, env: Environment) -> Result<bool, ControlSignal> {
        let result = self.eval_quasiquote(args, &env)?;
        self.process.program = result;
        self.process.execution_mode = crate::process::ExecutionMode::Return;
        Ok(true)
    }

    fn step_multiple_value_bind_DUP(
        &mut self,
        args: NodeId,
        env: Environment,
    ) -> Result<bool, ControlSignal> {
        // (multiple-value-bind (vars...) values-form body...)
        // 1. Eval values-form
        // 2. Bind vars to values (lexical new env)
        // 3. Eval body (tail)

        let args_vec = self.cons_to_vec(args);
        if args_vec.len() < 2 {
            return Err(ControlSignal::Error(
                "multiple-value-bind: too few args".into(),
            ));
        }
        let vars_node = args_vec[0];
        let values_form = args_vec[1];
        let body = if args_vec.len() > 2 {
            self.process.make_list(&args_vec[2..])
        } else {
            self.process.make_nil()
        };

        // Push continuation to bind variables
        self.process.continuation_stack.push(Continuation::EvMvb {
            vars: vars_node,
            body,
            env: env.clone(),
        });

        self.process.program = values_form;
        self.process.current_env = Some(env);
        self.process.execution_mode = crate::process::ExecutionMode::Eval;
        Ok(true)
    }

    /// (quasiquote form) -> expand and evaluate
    fn eval_quasiquote(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(form, _) = self.process.arena.inner.get_unchecked(args).clone() {
            self.eval_quasiquote_internal(form, env)
        } else {
            // (quasiquote) -> nil?
            Ok(self.process.make_nil())
        }
    }

    fn eval_quasiquote_internal(&mut self, form: NodeId, env: &Environment) -> EvalResult {
        let node = self.process.arena.inner.get_unchecked(form).clone();
        match node {
            Node::Leaf(_) => Ok(form), // self-evaluating leaves (including symbols inside qq unless unquoted?)
            // Wait, symbols are constant in QQ.
            Node::Fork(car, cdr) => {
                // Check if car is UNQUOTE or UNQUOTE-SPLICING
                if let Some(sym) = self.node_to_symbol(car) {
                    println!(
                        "DEBUG: eval_qq inner sym={:?} unquote={:?}",
                        sym, self.globals.special_forms.unquote
                    );
                    if sym == self.globals.special_forms.unquote {
                        // (unquote x) -> eval x
                        // (unquote . (x . nil))
                        if let Node::Fork(x, _) =
                            self.process.arena.inner.get_unchecked(cdr).clone()
                        {
                            return self.eval(x, env);
                        }
                        return Ok(self.process.make_nil()); // Malformed
                    }
                    if sym == self.globals.special_forms.unquote_splicing {
                        return Err(ControlSignal::Error(
                            "UNQUOTE-SPLICING not allowed at head of QUASIQUOTE".to_string(),
                        ));
                    }
                }

                // It's a list. We need to construct it.
                // We walk the list and handle unquoting.
                // This is complex because of splicing.
                // (a ,b c) -> (cons 'a (cons b '(c)))
                // We are implementing EVAL here, so we just build the result structure directly.

                // Handle cons:
                // Recursively eval car and cdr.
                // BUT if car is UNQUOTE-SPLICING make-list-splicing

                // Check car for splicing
                let car_val_opt = self.process.arena.inner.get_unchecked(car).clone();
                if let Node::Fork(caar, cdar) = car_val_opt {
                    if let Some(s) = self.node_to_symbol(caar) {
                        if s == self.globals.special_forms.unquote_splicing {
                            // (unquote-splicing x)
                            if let Node::Fork(x, _) =
                                self.process.arena.inner.get_unchecked(cdar).clone()
                            {
                                let list_val = self.eval(x, env)?;
                                // Append this list to the processing of the rest
                                let rest_val = self.eval_quasiquote_internal(cdr, env)?;

                                // append list_val ++ rest_val
                                // We need a helper to append two lists in memory
                                return self.append_nodes(list_val, rest_val);
                            }
                        }
                    }
                }

                let new_car = self.eval_quasiquote_internal(car, env)?;
                let new_cdr = self.eval_quasiquote_internal(cdr, env)?;

                Ok(self.process.arena.inner.alloc(Node::Fork(new_car, new_cdr)))
            }
            _ => Ok(form),
        }
    }

    fn append_nodes(&mut self, list1: NodeId, list2: NodeId) -> EvalResult {
        // Copy list1 structure and point tail to list2
        if let Node::Leaf(OpaqueValue::Nil) = self.process.arena.inner.get_unchecked(list1) {
            return Ok(list2);
        }

        if let Node::Fork(car, cdr) = self.process.arena.inner.get_unchecked(list1).clone() {
            let new_cdr = self.append_nodes(cdr, list2)?;
            Ok(self.process.arena.inner.alloc(Node::Fork(car, new_cdr)))
        } else {
            // Dotted list or atom in splice position? using list2 as cdr?
            // (foo . bar) ,@baz -> error? or just cons?
            // Append usually expects proper list.
            Ok(self.process.arena.inner.alloc(Node::Fork(list1, list2)))
        }
    }

    /// Create an integer
    pub fn make_integer(&mut self, n: i64) -> NodeId {
        self.process
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Integer(n)))
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
    pub defvar: SymbolId,
    pub defparameter: SymbolId,
    pub quasiquote: SymbolId,
    pub unquote: SymbolId,
    pub unquote_splicing: SymbolId,
    pub declare: SymbolId,
}

impl SpecialForms {
    pub fn new(symbols: &mut SymbolTable) -> Self {
        let mut intern_exported = |name: &str| {
            let sym = symbols.intern_in(name, PackageId(1)); // COMMON-LISP
            symbols.export_symbol(sym);
            sym
        };

        Self {
            quote: intern_exported("QUOTE"),
            r#if: intern_exported("IF"),
            progn: intern_exported("PROGN"),
            setq: intern_exported("SETQ"),
            r#let: intern_exported("LET"),
            lambda: intern_exported("LAMBDA"),
            function: intern_exported("FUNCTION"),
            defun: intern_exported("DEFUN"),
            defclass: intern_exported("DEFCLASS"),
            defmethod: intern_exported("DEFMETHOD"),
            definitions: intern_exported("DEFINITIONS"),
            block: intern_exported("BLOCK"),
            return_from: intern_exported("RETURN-FROM"),
            tagbody: intern_exported("TAGBODY"),
            go: intern_exported("GO"),
            catch: intern_exported("CATCH"),
            throw: intern_exported("THROW"),
            unwind_protect: intern_exported("UNWIND-PROTECT"),
            defmacro: intern_exported("DEFMACRO"),
            handler_bind: intern_exported("HANDLER-BIND"),
            eval_when: intern_exported("EVAL-WHEN"),
            multiple_value_bind: intern_exported("MULTIPLE-VALUE-BIND"),
            multiple_value_call: intern_exported("MULTIPLE-VALUE-CALL"),
            values: intern_exported("VALUES"),
            locally: intern_exported("LOCALLY"),
            flet: intern_exported("FLET"),
            labels: intern_exported("LABELS"),
            macrolet: intern_exported("MACROLET"),
            symbol_macrolet: intern_exported("SYMBOL-MACROLET"),
            load_time_value: intern_exported("LOAD-TIME-VALUE"),
            progression_list: intern_exported("PROGV"),
            defvar: intern_exported("DEFVAR"),
            defparameter: intern_exported("DEFPARAMETER"),
            quasiquote: intern_exported("QUASIQUOTE"),
            unquote: intern_exported("UNQUOTE"),
            unquote_splicing: intern_exported("UNQUOTE-SPLICING"),
            declare: intern_exported("DECLARE"),
        }
    }
    pub fn contains(&self, id: SymbolId) -> bool {
        id == self.quote
            || id == self.r#if
            || id == self.progn
            || id == self.setq
            || id == self.r#let
            || id == self.lambda
            || id == self.function
            || id == self.defun
            || id == self.defclass
            || id == self.defmethod
            || id == self.definitions
            || id == self.block
            || id == self.return_from
            || id == self.tagbody
            || id == self.go
            || id == self.catch
            || id == self.throw
            || id == self.unwind_protect
            || id == self.defmacro
            || id == self.handler_bind
            || id == self.eval_when
            || id == self.multiple_value_bind
            || id == self.multiple_value_call
            || id == self.values
            || id == self.locally
            || id == self.flet
            || id == self.labels
            || id == self.macrolet
            || id == self.symbol_macrolet
            || id == self.load_time_value
            || id == self.progression_list
            || id == self.defvar
            || id == self.defparameter
            || id == self.quasiquote
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::process::Pid;
    use crate::reader::read_from_string;

    fn setup_env() -> (Process, GlobalContext) {
        let mut globals = GlobalContext::new();
        // Register primitives if needed, but for special forms handled in eval, maybe not strictly required
        // unless compiled code uses them.
        let proc = Process::new(
            Pid {
                node: 0,
                id: 1,
                serial: 0,
            },
            NodeId(0),
            &mut globals,
        );
        (proc, globals)
    }

    #[test]
    fn test_setq_protected_symbol() {
        let (mut proc, mut globals) = setup_env();

        // Ensure we are in CL-USER (Package 2)
        globals
            .symbols
            .write()
            .unwrap()
            .set_current_package(PackageId(2));

        // Input: (setq :s-combinator 1)
        // :s-combinator is protected in GlobalContext::new
        let input = "(setq :s-combinator 1)";
        let expr = read_from_string(
            input,
            &mut proc.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();

        // Use Interpreter directly on parsing output (no need to compile for this test if we use eval)
        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let env = Environment::new();

        let result = interpreter.eval(expr, &env);

        match result {
            Err(ControlSignal::Error(msg)) => {
                assert!(
                    msg.to_string().contains("protected symbol"),
                    "Expected protected symbol error, got: {}",
                    msg
                );
            }
            Ok(_) => panic!("Refused to fail! :s-combinator should be protected"),
            Err(e) => panic!("Unexpected error type: {:?}", e),
        }
    }

    #[test]
    fn test_setq_unprotected_symbol() {
        let (mut proc, mut globals) = setup_env();
        globals
            .symbols
            .write()
            .unwrap()
            .set_current_package(PackageId(2));

        let input = "(setq x 1)";
        let expr = read_from_string(
            input,
            &mut proc.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let env = Environment::new();

        let result = interpreter.eval(expr, &env);
        // Should succeed (returns 1)
        assert!(result.is_ok());
    }

    #[test]
    fn test_undefined_variable_error() {
        let (mut proc, mut globals) = setup_env();
        globals
            .symbols
            .write()
            .unwrap()
            .set_current_package(PackageId(2));

        let input = "some-undefined-var";
        let expr = read_from_string(
            input,
            &mut proc.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let env = Environment::new();

        let result = interpreter.eval(expr, &env);

        match result {
            Err(ControlSignal::Error(msg)) => {
                assert!(
                    msg.to_string().contains("not bound"),
                    "Expected 'not bound' error, got: {}",
                    msg
                );
            }
            Ok(_) => panic!("Refused to fail! Undefined variable should error."),
            Err(e) => panic!("Unexpected error type: {:?}", e),
        }
    }

    #[test]
    fn test_let_star_manual() {
        let (mut proc, mut globals) = setup_env();
        globals
            .symbols
            .write()
            .unwrap()
            .set_current_package(PackageId(2));

        // Test explicit nested let
        let input = "(let ((a 1)) (let ((b 2)) b))";
        let expr = read_from_string(
            input,
            &mut proc.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let env = Environment::new();

        let result = interpreter.eval(expr, &env);
        assert!(
            result.is_ok(),
            "Explicit nested let failed: {:?}",
            result.err()
        );
        if let Ok(val) = result {
            // Should be 2
            match interpreter.process.arena.inner.get_unchecked(val) {
                Node::Leaf(OpaqueValue::Integer(2)) => {}
                n => panic!("Expected 2, got {:?}", n),
            }
        }
    }
}
