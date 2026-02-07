// TreeCL Evaluator - Special Forms and Core Evaluation
//
// This module implements ANSI CL special forms on top of Tree Calculus.

use crate::arena::Node;
use crate::context::GlobalContext;
use crate::process::Process;
use crate::symbol::{PackageId, SymbolId, SymbolTable};
use crate::types::{NodeId, OpaqueValue};

use crate::fastmap::HashMap;
use std::sync::{Arc, OnceLock, RwLock};

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
            bindings: Arc::new(RwLock::new(HashMap::default())),
            functions: Arc::new(RwLock::new(HashMap::default())),
            parent: None,
        }
    }

    pub fn with_parent(parent: Environment) -> Self {
        Self {
            bindings: Arc::new(RwLock::new(HashMap::default())),
            functions: Arc::new(RwLock::new(HashMap::default())),
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
    /// Destructuring lambda list for macros (if applicable)
    pub destructuring: Option<DestructuringLambdaList>,
    /// Body expression (NodeId)
    pub body: NodeId,
    /// Captured environment
    pub env: Environment,
}

impl Closure {
    pub fn iter_roots(&self) -> Vec<NodeId> {
        let mut roots = Vec::new();
        roots.push(self.body);
        roots.extend(self.env.iter_roots());
        roots.extend(self.lambda_list.iter_roots());
        if let Some(d) = &self.destructuring {
            roots.extend(d.iter_roots());
        }
        roots
    }
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

impl ParsedLambdaList {
    pub fn iter_roots(&self) -> Vec<NodeId> {
        let mut roots = Vec::new();
        roots.extend(self.req.iter().copied());
        for (var, init, _) in &self.opt {
            roots.push(*var);
            roots.push(*init);
        }
        for (_, var, init, _) in &self.key {
            roots.push(*var);
            roots.push(*init);
        }
        for (_, init) in &self.aux {
            roots.push(*init);
        }
        roots
    }
}

#[derive(Debug, Clone)]
pub struct DestructuringLambdaList {
    pattern: DListPattern,
}

impl DestructuringLambdaList {
    pub fn iter_roots(&self) -> Vec<NodeId> {
        self.pattern.iter_roots()
    }
}

#[derive(Debug, Clone, Default)]
struct DListPattern {
    req: Vec<DPattern>,
    opt: Vec<DOptSpec>,
    rest: Option<Box<DPattern>>,
    key: Vec<DKeySpec>,
    aux: Vec<DAuxSpec>,
    allow_other_keys: bool,
}

impl DListPattern {
    fn iter_roots(&self) -> Vec<NodeId> {
        let mut roots = Vec::new();
        for req in &self.req {
            roots.extend(req.iter_roots());
        }
        for opt in &self.opt {
            roots.extend(opt.iter_roots());
        }
        if let Some(rest) = &self.rest {
            roots.extend(rest.iter_roots());
        }
        for key in &self.key {
            roots.extend(key.iter_roots());
        }
        for aux in &self.aux {
            roots.extend(aux.iter_roots());
        }
        roots
    }
}

#[derive(Debug, Clone)]
struct DOptSpec {
    pattern: DPattern,
    init: Option<NodeId>,
    supplied: Option<SymbolId>,
}

impl DOptSpec {
    fn iter_roots(&self) -> Vec<NodeId> {
        let mut roots = self.pattern.iter_roots();
        if let Some(init) = self.init {
            roots.push(init);
        }
        roots
    }
}

#[derive(Debug, Clone)]
struct DKeySpec {
    key: SymbolId,
    pattern: DPattern,
    init: Option<NodeId>,
    supplied: Option<SymbolId>,
}

impl DKeySpec {
    fn iter_roots(&self) -> Vec<NodeId> {
        let mut roots = self.pattern.iter_roots();
        if let Some(init) = self.init {
            roots.push(init);
        }
        roots
    }
}

#[derive(Debug, Clone)]
struct DAuxSpec {
    sym: SymbolId,
    init: Option<NodeId>,
}

impl DAuxSpec {
    fn iter_roots(&self) -> Vec<NodeId> {
        let mut roots = Vec::new();
        if let Some(init) = self.init {
            roots.push(init);
        }
        roots
    }
}

#[derive(Debug, Clone)]
enum DPattern {
    Var(SymbolId),
    Wildcard,
    Literal(NodeId),
    List(DListPattern),
}

impl DPattern {
    fn iter_roots(&self) -> Vec<NodeId> {
        match self {
            DPattern::Var(_) | DPattern::Wildcard => Vec::new(),
            DPattern::Literal(node) => vec![*node],
            DPattern::List(list) => list.iter_roots(),
        }
    }
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
        // Restore caller environment after a function application.
        saved_env: Environment,
    },
    /// Timing frame for macro expansion and expanded-form evaluation.
    MacroTiming {
        label: String,
        expand_ns: u64,
        eval_started_at: std::time::Instant,
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
    /// MULTIPLE-VALUE-CALL: evaluate function then forms, collecting values
    EvMvcFunc {
        forms: Vec<NodeId>,
        env: Environment,
    },
    EvMvcArgs {
        func: NodeId,
        forms: Vec<NodeId>,
        collected: Vec<NodeId>,
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

enum DListMode {
    Req,
    Opt,
    Rest,
    PostRest,
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
        if !allow_destructuring {
            if let Some(sym) = self.node_to_symbol(pattern) {
                env.bind(sym, value);
                return Ok(());
            }
            return Err(ControlSignal::Error(format!(
                "Function argument must be a symbol: {:?}",
                pattern
            )));
        }
        // Destructuring + pattern matching (Erlang-style)
        let quote_sym = self.globals.special_forms.quote;
        let symbols = self.globals.symbols.read().unwrap();
        if let Some(bindings) = crate::pattern::match_pattern(
            &self.process.arena.inner,
            &self.process.arrays,
            &self.process.hashtables,
            &symbols,
            quote_sym,
            pattern,
            value,
        ) {
            for (sym, val) in bindings {
                env.bind(sym, val);
            }
            return Ok(());
        }

        // Legacy destructuring fallback (handles short lists by binding NILs).
        if let Node::Fork(p_head, p_tail) = self.process.arena.inner.get_unchecked(pattern).clone()
        {
            if let Node::Fork(v_head, v_tail) =
                self.process.arena.inner.get_unchecked(value).clone()
            {
                self.bind_pattern(env, p_head, v_head, true)?;
                self.bind_pattern(env, p_tail, v_tail, true)?;
                return Ok(());
            }
            if self.is_nil(value) {
                let nil_node = self.process.make_nil();
                self.bind_pattern(env, p_head, nil_node, true)?;
                let nil_node = self.process.make_nil();
                self.bind_pattern(env, p_tail, nil_node, true)?;
                return Ok(());
            }
        } else if self.is_nil(pattern) {
            return Ok(());
        }

        Err(ControlSignal::Error(format!(
            "Pattern mismatch: pattern {:?} value {:?}",
            pattern, value
        )))
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

    pub fn parse_destructuring_lambda_list(
        &mut self,
        list_node: NodeId,
    ) -> Result<DestructuringLambdaList, String> {
        let pattern = self.parse_dlist_pattern(list_node)?;
        Ok(DestructuringLambdaList { pattern })
    }

    fn parse_dlist_pattern(&mut self, list_node: NodeId) -> Result<DListPattern, String> {
        let (items, tail) = self.list_items_with_tail(list_node);
        let mut has_keyword = false;
        for item in &items {
            if let Some(sym) = self.node_to_symbol(*item) {
                if let Some(name) = self.globals.symbols.read().unwrap().symbol_name(sym) {
                    if matches!(
                        name,
                        "&OPTIONAL" | "&REST" | "&BODY" | "&KEY" | "&AUX" | "&ALLOW-OTHER-KEYS"
                    ) {
                        has_keyword = true;
                        break;
                    }
                }
            }
        }

        if has_keyword && !self.is_nil(tail) {
            return Err("Improper destructuring lambda list".into());
        }

        let mut pattern = DListPattern::default();
        if !has_keyword {
            for item in items {
                pattern.req.push(self.parse_dpattern(item)?);
            }
            if !self.is_nil(tail) {
                pattern.rest = Some(Box::new(self.parse_dpattern(tail)?));
            }
            return Ok(pattern);
        }

        let mut mode = DListMode::Req;
        for item in items {
            if let Some(sym) = self.node_to_symbol(item) {
                if let Some(name) = self.globals.symbols.read().unwrap().symbol_name(sym) {
                    match name {
                        "&OPTIONAL" => {
                            mode = DListMode::Opt;
                            continue;
                        }
                        "&REST" | "&BODY" => {
                            mode = DListMode::Rest;
                            continue;
                        }
                        "&KEY" => {
                            mode = DListMode::Key;
                            continue;
                        }
                        "&AUX" => {
                            mode = DListMode::Aux;
                            continue;
                        }
                        "&ALLOW-OTHER-KEYS" => {
                            if !matches!(mode, DListMode::Key) {
                                return Err("&ALLOW-OTHER-KEYS must follow &KEY".into());
                            }
                            pattern.allow_other_keys = true;
                            continue;
                        }
                        _ => {}
                    }
                }
            }

            match mode {
                DListMode::Req => pattern.req.push(self.parse_dpattern(item)?),
                DListMode::Opt => pattern.opt.push(self.parse_opt_spec(item)?),
                DListMode::Rest => {
                    if pattern.rest.is_some() {
                        return Err("Multiple &rest arguments".into());
                    }
                    pattern.rest = Some(Box::new(self.parse_dpattern(item)?));
                    mode = DListMode::PostRest;
                }
                DListMode::PostRest => {
                    return Err("Only &key or &aux may follow &rest".into());
                }
                DListMode::Key => pattern.key.push(self.parse_key_spec(item)?),
                DListMode::Aux => pattern.aux.push(self.parse_aux_spec(item)?),
            }
        }

        Ok(pattern)
    }

    fn parse_dpattern(&mut self, node: NodeId) -> Result<DPattern, String> {
        if self.is_nil(node) {
            return Ok(DPattern::Literal(node));
        }
        if let Some(lit) = self.quoted_literal_pattern(node) {
            return Ok(DPattern::Literal(lit));
        }
        if let Some(sym) = self.node_to_symbol(node) {
            if self.is_wildcard_symbol(sym) {
                return Ok(DPattern::Wildcard);
            }
            if self.is_keyword_symbol(sym) {
                return Ok(DPattern::Literal(node));
            }
            return Ok(DPattern::Var(sym));
        }
        match self.process.arena.get_unchecked(node) {
            Node::Fork(_, _) => Ok(DPattern::List(self.parse_dlist_pattern(node)?)),
            _ => Ok(DPattern::Literal(node)),
        }
    }

    fn parse_opt_spec(&mut self, node: NodeId) -> Result<DOptSpec, String> {
        if self.quoted_literal_pattern(node).is_some() {
            return Ok(DOptSpec {
                pattern: self.parse_dpattern(node)?,
                init: None,
                supplied: None,
            });
        }
        if matches!(self.process.arena.get_unchecked(node), Node::Fork(_, _)) {
            let (parts, tail) = self.list_items_with_tail(node);
            if !self.is_nil(tail) {
                return Err("Improper &optional spec".into());
            }
            if parts.is_empty() {
                return Err("Empty &optional spec".into());
            }
            let pattern = self.parse_dpattern(parts[0])?;
            let init = parts.get(1).copied();
            let supplied = if parts.len() > 2 {
                self.node_to_symbol(parts[2])
            } else {
                None
            };
            if parts.len() > 3 {
                return Err("Too many elements in &optional spec".into());
            }
            return Ok(DOptSpec {
                pattern,
                init,
                supplied,
            });
        }

        Ok(DOptSpec {
            pattern: self.parse_dpattern(node)?,
            init: None,
            supplied: None,
        })
    }

    fn parse_key_spec(&mut self, node: NodeId) -> Result<DKeySpec, String> {
        if !matches!(self.process.arena.get_unchecked(node), Node::Fork(_, _)) {
            let key_sym = self
                .node_to_symbol(node)
                .ok_or("Key parameter must be symbol")?;
            return Ok(DKeySpec {
                key: key_sym,
                pattern: self.parse_dpattern(node)?,
                init: None,
                supplied: None,
            });
        }

        let (parts, tail) = self.list_items_with_tail(node);
        if !self.is_nil(tail) {
            return Err("Improper &key spec".into());
        }
        if parts.is_empty() {
            return Err("Empty &key spec".into());
        }

        let spec = parts[0];
        let (key_sym, var_node) = if let Some(sym) = self.node_to_symbol(spec) {
            (sym, spec)
        } else if matches!(self.process.arena.get_unchecked(spec), Node::Fork(_, _)) {
            let (spec_parts, spec_tail) = self.list_items_with_tail(spec);
            if !self.is_nil(spec_tail) || spec_parts.len() != 2 {
                return Err("Key spec must be (key var)".into());
            }
            let key_sym = self
                .node_to_symbol(spec_parts[0])
                .ok_or("Key name must be symbol")?;
            (key_sym, spec_parts[1])
        } else {
            return Err("Key spec must be symbol or (key var)".into());
        };

        let init = parts.get(1).copied();
        let supplied = if parts.len() > 2 {
            self.node_to_symbol(parts[2])
        } else {
            None
        };
        if parts.len() > 3 {
            return Err("Too many elements in &key spec".into());
        }

        Ok(DKeySpec {
            key: key_sym,
            pattern: self.parse_dpattern(var_node)?,
            init,
            supplied,
        })
    }

    fn parse_aux_spec(&mut self, node: NodeId) -> Result<DAuxSpec, String> {
        if !matches!(self.process.arena.get_unchecked(node), Node::Fork(_, _)) {
            let sym = self
                .node_to_symbol(node)
                .ok_or("Aux var must be symbol")?;
            return Ok(DAuxSpec { sym, init: None });
        }

        let (parts, tail) = self.list_items_with_tail(node);
        if !self.is_nil(tail) {
            return Err("Improper &aux spec".into());
        }
        if parts.is_empty() {
            return Err("Empty &aux spec".into());
        }
        let sym = self
            .node_to_symbol(parts[0])
            .ok_or("Aux var must be symbol")?;
        let init = parts.get(1).copied();
        if parts.len() > 2 {
            return Err("Too many elements in &aux spec".into());
        }
        Ok(DAuxSpec { sym, init })
    }

    fn list_items_with_tail(&self, list: NodeId) -> (Vec<NodeId>, NodeId) {
        let mut items = Vec::new();
        let mut current = list;
        loop {
            match self.process.arena.get_unchecked(current) {
                Node::Fork(head, tail) => {
                    items.push(*head);
                    current = *tail;
                }
                _ => break,
            }
        }
        (items, current)
    }

    fn quoted_literal_pattern(&self, node: NodeId) -> Option<NodeId> {
        let Node::Fork(head, tail) = self.process.arena.get_unchecked(node) else {
            return None;
        };
        let Node::Leaf(OpaqueValue::Symbol(sym)) = self.process.arena.get_unchecked(*head) else {
            return None;
        };
        if SymbolId(*sym) != self.globals.special_forms.quote {
            return None;
        }
        match self.process.arena.get_unchecked(*tail) {
            Node::Fork(arg, rest) if self.is_nil(*rest) => Some(*arg),
            _ => None,
        }
    }

    fn is_keyword_symbol(&self, sym: SymbolId) -> bool {
        self.globals
            .symbols
            .read()
            .unwrap()
            .get_symbol(sym)
            .map(|s| s.is_keyword())
            .unwrap_or(false)
    }

    fn is_wildcard_symbol(&self, sym: SymbolId) -> bool {
        self.globals
            .symbols
            .read()
            .unwrap()
            .symbol_name(sym)
            .map(|name| name == "_")
            .unwrap_or(false)
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
        // ... (existing eval logic to be kept for reference or backup until full switch)
        // For now, let's keep eval as is, and add step separately.
        // But the user asked to refactor Eval.
        // Let's implement step and then make eval call step in a loop.

        // Save State for re-entrancy
        let saved_program = self.process.program;
        let saved_mode = self.process.execution_mode.clone();
        let saved_env = self.process.current_env.clone();
        // Take the stack to avoid cloning.
        let saved_stack = std::mem::take(&mut self.process.continuation_stack);

        // Initialize TCO state for this execution
        self.process.program = expr;
        self.process.current_env = Some(env.clone());
        // Stack is already empty because we took it
        self.process.continuation_stack.push(Continuation::Done);
        self.process.execution_mode = crate::process::ExecutionMode::Eval;

        let result = loop {
            match self.step() {
                Ok(true) => continue,
                Ok(false) => break Ok(self.process.program),
                Err(e) => break Err(e),
            }
        };

        // Restore State
        self.process.program = saved_program;
        self.process.execution_mode = saved_mode;
        self.process.current_env = saved_env;
        self.process.continuation_stack = saved_stack;

        result
    }

    /// Perform one step of TCO evaluation
    /// Returns true if execution should continue, false if finished (result in process.program)
    pub fn step(&mut self) -> Result<bool, ControlSignal> {
        let mode = self.process.execution_mode.clone();

        match mode {
            crate::process::ExecutionMode::Eval => {
                // Each evaluation establishes a fresh values context.
                // If a form doesn't explicitly set multiple values, we will
                // populate a single primary value on return.
                self.process.values_are_set = false;
                self.process.values.clear();

                let expr = self.process.program;
                self.process.pending_redex = Some(expr);
                let env = self.process.current_env.as_ref().unwrap().clone();
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

            if sym_id == sf.setq {
                return self.step_setq(args, env);
            }
            if sym_id == sf.r#if {
                return self.step_if(args, env);
            }
            if sym_id == sf.progn {
                return self.step_progn(args, env);
            }
            if sym_id == sf.lambda {
                let res = self.eval_lambda(args, &env)?;
                self.process.program = res;
                self.process.execution_mode = crate::process::ExecutionMode::Return;
                return Ok(true);
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
            if self.is_common_lisp_let_star_symbol(sym_id) {
                return self.step_let_star(args, env);
            }
            if sym_id == sf.multiple_value_bind {
                return self.step_multiple_value_bind(args, env);
            }
            if sym_id == sf.multiple_value_call {
                return self.step_multiple_value_call(args, env);
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
            if self.is_common_lisp_cond_symbol(sym_id) {
                return self.step_cond(args, env);
            }
            if self.is_common_lisp_or_symbol(sym_id) {
                return self.step_or(args, env);
            }
        }

        // Handle CALL-METHOD when it is lexically bound.
        if let Some(sym_id) = self.node_to_symbol(op) {
            if let Some(func_node) = env.lookup_function(sym_id) {
                if let Node::Leaf(OpaqueValue::CallMethod(state_idx)) =
                    self.process.arena.get_unchecked(func_node)
                {
                    return self.step_call_method_form(*state_idx as usize, args, env);
                }
            }
        }

        // Check for Macros
        if let Some(sym_id) = self.node_to_symbol(op) {
            if let Some(&macro_idx) = self.process.macros.get(&sym_id) {
                if let Some(closure) = self.process.closures.get(macro_idx).cloned() {
                    let macro_timing_label = self.macro_timing_label(sym_id, args);
                    let macro_started_at = std::time::Instant::now();
                    let expanded =
                        if let Some(fast) = self.try_fast_macro_expand(sym_id, args, &env)?
                    {
                        fast
                    } else {
                        self._apply_macro(&closure, args)?
                    };
                    if let Some(label) = macro_timing_label {
                        let expand_ns = macro_started_at
                            .elapsed()
                            .as_nanos()
                            .min(u128::from(u64::MAX)) as u64;
                        self.process
                            .continuation_stack
                            .push(Continuation::MacroTiming {
                                label,
                                expand_ns,
                                eval_started_at: std::time::Instant::now(),
                            });
                    }
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
            self.process
                .continuation_stack
                .push(Continuation::Apply { saved_env: env.clone() });
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

        // Parse lambda list (both plain + destructuring for macros)
        let parsed_lambda_list = match self.parse_lambda_list(lambda_list_node) {
            Ok(l) => l,
            Err(e) => return Err(ControlSignal::Error(e)),
        };
        let destructuring = match self.parse_destructuring_lambda_list(lambda_list_node) {
            Ok(d) => d,
            Err(e) => return Err(ControlSignal::Error(e)),
        };

        // Create Closure
        let closure = crate::eval::Closure {
            lambda_list: parsed_lambda_list,
            destructuring: Some(destructuring),
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
        let mut tag_map = HashMap::default();

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

        let (_decls, body_start) = self.parse_body(body_forms);
        let body_node = self
            .process
            .arena
            .inner
            .alloc(Node::Fork(progn_sym_node, body_start));

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
            destructuring: None,
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

        if let Some(sym) = self.node_to_symbol(target) {
            // If it is a known function (lexical or global generic/closure), resolve it!
            // First check lexical env (flet/labels)
            if let Some(func_node) = _env.lookup_function(sym) {
                self.process.program = func_node;
                self.process.execution_mode = crate::process::ExecutionMode::Return;
                return Ok(true);
            }
            // Then check global functions (defun/defgeneric)
            // Note: primitives are not stored in global functions map usually.
            // If function is not found, return symbol (for primitives via try_reduce_primitive fallback)
            if let Some(func_node) = self.process.get_function(sym) {
                self.process.program = func_node;
                self.process.execution_mode = crate::process::ExecutionMode::Return;
                return Ok(true);
            }
            // Fallback: Return Symbol (Designator)
            self.process.program = target;
            self.process.execution_mode = crate::process::ExecutionMode::Return;
            return Ok(true);
        }

        // (setf name) case: resolve setf function binding or generic
        let node = self.process.arena.get_unchecked(target).clone();
        if let Node::Fork(head, tail) = node {
            if let Some(s) = self.node_to_symbol(head) {
                if s == self.process.mop.setf_symbol {
                    if let Node::Fork(base_node, _) =
                        self.process.arena.get_unchecked(tail).clone()
                    {
                        if let Some(base_sym) = self.node_to_symbol(base_node) {
                            if let Some(func_node) = self.process.get_setf_function(base_sym) {
                                self.process.program = func_node;
                                self.process.execution_mode = crate::process::ExecutionMode::Return;
                                return Ok(true);
                            }
                            if let Some(gid) = self.process.mop.find_setf_generic(base_sym) {
                                let gf_node = self.process.arena.inner.alloc(Node::Leaf(
                                    crate::types::OpaqueValue::Generic(gid.0),
                                ));
                                self.process.program = gf_node;
                                self.process.execution_mode = crate::process::ExecutionMode::Return;
                                return Ok(true);
                            }
                        }
                    }
                }
            }
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

                        // Create Progn Body (strip declarations)
                        let progn_sym = self.globals.special_forms.progn;
                        let progn_val = crate::types::OpaqueValue::Symbol(progn_sym.0);
                        let progn_node = self.process.arena.inner.alloc(Node::Leaf(progn_val));
                        let (_decls, body_start) = self.parse_body(body_forms);
                        let body_expr = self
                            .process
                            .arena
                            .inner
                            .alloc(Node::Fork(progn_node, body_start));

                        // Capture Environment
                        let captured_env = self
                            .process
                            .current_env
                            .as_ref()
                            .cloned()
                            .unwrap_or_else(|| Environment::new());

                        let closure = Closure {
                            lambda_list,
                            destructuring: None,
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
        self.process.current_env = Some(env.clone());
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

        // If any binding is special, fall back to the full let evaluator so
        // dynamic bindings (e.g. *package*) are handled correctly.
        let mut has_special = false;
        for var_node in &vars {
            if let Some(sym) = self.node_to_symbol(*var_node) {
                if self.is_special_symbol(sym) {
                    has_special = true;
                    break;
                }
            }
        }
        if has_special {
            let result = self.eval_let(args, &env)?;
            self.process.program = result;
            self.process.execution_mode = crate::process::ExecutionMode::Return;
            return Ok(true);
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

    fn step_let_star(&mut self, args: NodeId, env: Environment) -> Result<bool, ControlSignal> {
        self.process.current_env = Some(env.clone());
        let result = self.eval_let_star(args, &env)?;
        self.process.program = result;
        self.process.execution_mode = crate::process::ExecutionMode::Return;
        Ok(true)
    }

    fn step_setq(&mut self, args: NodeId, env: Environment) -> Result<bool, ControlSignal> {
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

    fn step_cond(&mut self, args: NodeId, env: Environment) -> Result<bool, ControlSignal> {
        self.process.current_env = Some(env.clone());
        let result = self.eval_cond(args, &env)?;
        self.process.program = result;
        self.process.execution_mode = crate::process::ExecutionMode::Return;
        Ok(true)
    }

    fn step_or(&mut self, args: NodeId, env: Environment) -> Result<bool, ControlSignal> {
        self.process.current_env = Some(env.clone());
        let result = self.eval_or(args, &env)?;
        self.process.program = result;
        self.process.execution_mode = crate::process::ExecutionMode::Return;
        Ok(true)
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

    fn step_multiple_value_call(
        &mut self,
        args: NodeId,
        env: Environment,
    ) -> Result<bool, ControlSignal> {
        let args_vec = self.cons_to_vec(args);
        if args_vec.is_empty() {
            return Err(ControlSignal::Error(
                "multiple-value-call: too few args".into(),
            ));
        }
        let func_expr = args_vec[0];
        let forms = if args_vec.len() > 1 {
            args_vec[1..].to_vec()
        } else {
            Vec::new()
        };

        self.process.continuation_stack.push(Continuation::EvMvcFunc {
            forms,
            env: env.clone(),
        });

        self.process.program = func_expr;
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

        if !self.process.values_are_set {
            self.process.values.clear();
            self.process.values.push(result);
            self.process.values_are_set = true;
        }

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
            Continuation::EvMvb { vars, body, env } => {
                self.process.current_env = Some(env.clone());
                let mut new_env = Environment::with_parent(env);

                let mut values_iter = self.process.values.iter().copied();
                let mut cur = vars;
                loop {
                    match self.process.arena.get_unchecked(cur).clone() {
                        Node::Leaf(OpaqueValue::Nil) => break,
                        Node::Fork(var_node, rest) => {
                            let sym = self.node_to_symbol(var_node).ok_or_else(|| {
                                ControlSignal::Error(
                                    "multiple-value-bind: expected symbol".into(),
                                )
                            })?;
                            let val = values_iter.next().unwrap_or_else(|| self.process.make_nil());
                            new_env.bind(sym, val);
                            cur = rest;
                        }
                        _ => {
                            return Err(ControlSignal::Error(
                                "multiple-value-bind: malformed variable list".into(),
                            ))
                        }
                    }
                }

                if matches!(
                    self.process.arena.get_unchecked(body),
                    Node::Leaf(OpaqueValue::Nil)
                ) {
                    self.process.program = self.process.make_nil();
                    self.process.execution_mode = crate::process::ExecutionMode::Return;
                    return Ok(true);
                }

                let progn_sym = self.globals.special_forms.progn;
                let progn_sym_val = crate::types::OpaqueValue::Symbol(progn_sym.0);
                let progn_sym_node =
                    self.process.arena.inner.alloc(Node::Leaf(progn_sym_val));
                let progn_form = self
                    .process
                    .arena
                    .inner
                    .alloc(Node::Fork(progn_sym_node, body));

                self.process.program = progn_form;
                self.process.current_env = Some(new_env);
                self.process.execution_mode = crate::process::ExecutionMode::Eval;
                Ok(true)
            }
            Continuation::EvMvcFunc { forms, env } => {
                self.process.current_env = Some(env.clone());
                let func = result;

                if forms.is_empty() {
                    self.process
                        .continuation_stack
                        .push(Continuation::Apply { saved_env: env.clone() });
                    return self.step_apply(func, Vec::new(), env);
                }

                let first = forms[0];
                let rest = forms[1..].to_vec();
                self.process.continuation_stack.push(Continuation::EvMvcArgs {
                    func,
                    forms: rest,
                    collected: Vec::new(),
                    env: env.clone(),
                });
                self.process.program = first;
                self.process.execution_mode = crate::process::ExecutionMode::Eval;
                Ok(true)
            }
            Continuation::EvMvcArgs {
                func,
                forms,
                mut collected,
                env,
            } => {
                let mut values = self.process.values.clone();
                collected.append(&mut values);

                if forms.is_empty() {
                    self.process.current_env = Some(env.clone());
                    self.process
                        .continuation_stack
                        .push(Continuation::Apply { saved_env: env.clone() });
                    return self.step_apply(func, collected, env);
                }

                let next = forms[0];
                let rest = forms[1..].to_vec();
                self.process.continuation_stack.push(Continuation::EvMvcArgs {
                    func,
                    forms: rest,
                    collected,
                    env: env.clone(),
                });
                self.process.program = next;
                self.process.execution_mode = crate::process::ExecutionMode::Eval;
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
                args,
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
                    self.process
                        .continuation_stack
                        .push(Continuation::Apply { saved_env: env.clone() });
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
            Continuation::Apply { saved_env } => {
                // Restore caller environment after function application.
                self.process.current_env = Some(saved_env);
                self.process.execution_mode = crate::process::ExecutionMode::Return;
                Ok(true)
            }
            Continuation::MacroTiming {
                label,
                expand_ns,
                eval_started_at,
            } => {
                let eval_ns = eval_started_at
                    .elapsed()
                    .as_nanos()
                    .min(u128::from(u64::MAX)) as u64;
                self.log_macro_split_timing(&label, expand_ns, eval_ns);
                self.process.execution_mode = crate::process::ExecutionMode::Return;
                Ok(true)
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

        // Check for Funcallable Instance
        if let Node::Leaf(OpaqueValue::Instance(idx)) =
            self.process.arena.get_unchecked(func_node)
        {
            let inst_idx = *idx as usize;
            let class_id = self
                .process
                .mop
                .get_instance(inst_idx)
                .map(|i| i.class)
                .unwrap_or(self.process.mop.standard_object);
            if !self.process.mop.class_is_funcallable(class_id) {
                return Err(ControlSignal::Error(
                    "Attempt to call non-funcallable instance".into(),
                ));
            }
            let func = self.process.mop.get_instance_function(inst_idx).ok_or_else(|| {
                ControlSignal::Error("Funcallable instance has no function".into())
            })?;
            return self.step_apply(func, args, env);
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
        // Check for NextMethodP (next-method-p invocation)
        if let Node::Leaf(OpaqueValue::NextMethodP(state_idx)) =
            self.process.arena.get_unchecked(func_node)
        {
            let state_idx = *state_idx as usize;
            if state_idx >= self.process.next_method_states.len() {
                return Err(ControlSignal::Error("Invalid NextMethod state".into()));
            }

            let has_next = !self.process.next_method_states[state_idx].methods.is_empty();
            self.process.program = if has_next {
                self.process.make_t(&self.globals)
            } else {
                self.process.make_nil()
            };
            self.process.execution_mode = crate::process::ExecutionMode::Return;
            return Ok(true);
        }

        // Check for CallMethod (call-method invocation)
        if let Node::Leaf(OpaqueValue::CallMethod(state_idx)) =
            self.process.arena.get_unchecked(func_node)
        {
            let state_idx = *state_idx as usize;
            if state_idx >= self.process.next_method_states.len() {
                return Err(ControlSignal::Error("Invalid CallMethod state".into()));
            }

            if args.is_empty() {
                return Err(ControlSignal::Error(
                    "CALL-METHOD requires a method".into(),
                ));
            }

            let method_node = args[0];
            let next_methods_node = if args.len() > 1 {
                args[1]
            } else {
                self.process.make_nil()
            };

            let method_id = self.method_id_from_node(method_node)?;
            let next_methods = self.collect_method_ids(next_methods_node)?;

            let call_args = self.process.next_method_states[state_idx].args.clone();
            return self.call_method_with_next_methods(
                method_id,
                next_methods,
                call_args,
                env,
            );
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
                destructuring: None,
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
                // Fall back to tree calculus reduction for non-closure function objects.
                use crate::search::reduce;

                let mut result = effective_func_node;
                for arg in &args {
                    let app = self.process.arena.alloc(Node::Fork(result, *arg));
                    result = reduce(
                        &mut self.process.arena.inner,
                        app,
                        &mut self.process.eval_context,
                    );
                }

                let reduced = self.try_reduce_primitive(result, &env);
                self.process.program = reduced;
                self.process.execution_mode = crate::process::ExecutionMode::Return;
                return Ok(true);
            }
        };

        let new_env = self.bind_lambda_list(&closure, &args, inject_next_method)?;

        // Apply Process
        self.process.program = closure.body;
        self.process.current_env = Some(new_env);
        self.process.execution_mode = crate::process::ExecutionMode::Eval;
        return Ok(true);
    }

    fn bind_lambda_list(
        &mut self,
        closure: &Closure,
        args: &[NodeId],
        inject_next_method: Option<u32>,
    ) -> Result<Environment, ControlSignal> {
        let mut new_env: Environment = Environment::with_parent(closure.env.clone());

        // Inject call-next-method / next-method-p if needed
        if let Some(state_idx) = inject_next_method {
            // "The function call-next-method is lexically scoped."
            // Bind both CALL-NEXT-METHOD and NEXT-METHOD-P.
            let cnm_sym = self.ensure_cl_symbol("CALL-NEXT-METHOD");
            let nmp_sym = self.ensure_cl_symbol("NEXT-METHOD-P");
            let cm_sym = self.ensure_cl_symbol("CALL-METHOD");

            let nm_val = OpaqueValue::NextMethod(state_idx);
            let nm_node = self.process.arena.inner.alloc(Node::Leaf(nm_val));
            new_env.set_function(cnm_sym, nm_node);

            let nmp_val = OpaqueValue::NextMethodP(state_idx);
            let nmp_node = self.process.arena.inner.alloc(Node::Leaf(nmp_val));
            new_env.set_function(nmp_sym, nmp_node);

            let cm_val = OpaqueValue::CallMethod(state_idx);
            let cm_node = self.process.arena.inner.alloc(Node::Leaf(cm_val));
            new_env.set_function(cm_sym, cm_node);
        }

        let mut arg_idx = 0;

        // 1. Required
        for &param in &closure.lambda_list.req {
            if arg_idx >= args.len() {
                return Err(ControlSignal::Error("Too few arguments".into()));
            }
            self.bind_pattern(&mut new_env, param, args[arg_idx], true)?;
            arg_idx += 1;
        }

        // 2. Optional
        for (var, init, sup) in &closure.lambda_list.opt {
            if arg_idx < args.len() {
                self.bind_pattern(&mut new_env, *var, args[arg_idx], true)?;
                if let Some(s) = sup {
                    let t_node = self.process.make_t(&self.globals);
                    new_env.bind(*s, t_node);
                }
                arg_idx += 1;
            } else {
                let val = self.eval(*init, &new_env)?;
                self.bind_pattern(&mut new_env, *var, val, true)?;
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
            if rest_args.len() % 2 != 0 && !closure.lambda_list.allow_other_keys {
                return Err(ControlSignal::Error(
                    "Odd number of keyword arguments".into(),
                ));
            }

            for (key_sym, var, init, sup) in &closure.lambda_list.key {
                let mut found_val = None;
                let mut i = 0;
                while i < rest_args.len() {
                    let k = rest_args[i];
                    let v = if i + 1 < rest_args.len() {
                        rest_args[i + 1]
                    } else {
                        self.process.make_nil()
                    };

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
                            found_val = Some(v);
                            break;
                        }
                    }
                    i += 2;
                }

                if let Some(val) = found_val {
                    self.bind_pattern(&mut new_env, *var, val, true)?;
                    if let Some(s) = sup {
                        let t_node = self.process.make_t(&self.globals);
                        new_env.bind(*s, t_node);
                    }
                } else {
                    let val = self.eval(*init, &new_env)?;
                    self.bind_pattern(&mut new_env, *var, val, true)?;
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

        Ok(new_env)
    }

    fn bind_destructuring_lambda_list(
        &mut self,
        pattern: &DestructuringLambdaList,
        args: NodeId,
        env: &mut Environment,
    ) -> Result<(), ControlSignal> {
        let mut bindings = HashMap::default();
        let mut shape = crate::pattern::ShapeClassifier::new();
        self.match_dlist_pattern(&pattern.pattern, args, env, &mut bindings, &mut shape)
    }

    fn match_dlist_pattern(
        &mut self,
        pattern: &DListPattern,
        value: NodeId,
        env: &mut Environment,
        bindings: &mut HashMap<SymbolId, NodeId>,
        shape: &mut crate::pattern::ShapeClassifier,
    ) -> Result<(), ControlSignal> {
        let mut current = value;

        for req in &pattern.req {
            let (head, tail) = self
                .next_list_cell(current, shape)?
                .ok_or_else(|| ControlSignal::Error("Too few arguments".into()))?;
            self.match_dpattern(req, head, env, bindings, shape)?;
            current = tail;
        }

        for opt in &pattern.opt {
            if let Some((head, tail)) = self.next_list_cell(current, shape)? {
                self.match_dpattern(&opt.pattern, head, env, bindings, shape)?;
                if let Some(sup) = opt.supplied {
                    let t_node = self.process.make_t(&self.globals);
                    self.bind_symbol(env, bindings, sup, t_node)?;
                }
                current = tail;
            } else {
                let val = if let Some(init) = opt.init {
                    self.eval(init, env)?
                } else {
                    self.process.make_nil()
                };
                self.match_dpattern(&opt.pattern, val, env, bindings, shape)?;
                if let Some(sup) = opt.supplied {
                    let nil_node = self.process.make_nil();
                    self.bind_symbol(env, bindings, sup, nil_node)?;
                }
            }
        }

        let rest_list = current;

        if let Some(rest_pat) = &pattern.rest {
            self.match_dpattern(rest_pat, rest_list, env, bindings, shape)?;
        } else if pattern.key.is_empty() && !self.is_nil(rest_list) {
            return Err(ControlSignal::Error("Too many arguments".into()));
        }

        if !pattern.key.is_empty() || pattern.allow_other_keys {
            let (pairs, odd) = self.collect_key_pairs(rest_list, shape)?;
            if odd && !pattern.allow_other_keys {
                return Err(ControlSignal::Error(
                    "Odd number of keyword arguments".into(),
                ));
            }

            if !pattern.allow_other_keys {
                for (key_node, _) in &pairs {
                    let key_sym = self
                        .node_to_symbol(*key_node)
                        .ok_or_else(|| ControlSignal::Error("Keyword must be a symbol".into()))?;
                    let mut recognized = false;
                    for spec in &pattern.key {
                        if self.key_matches(spec.key, key_sym) {
                            recognized = true;
                            break;
                        }
                    }
                    if !recognized {
                        return Err(ControlSignal::Error("Unknown keyword argument".into()));
                    }
                }
            }

            for spec in &pattern.key {
                let mut found_val = None;
                for (key_node, val) in &pairs {
                    if let Some(key_sym) = self.node_to_symbol(*key_node) {
                        if self.key_matches(spec.key, key_sym) {
                            found_val = Some(*val);
                            break;
                        }
                    } else {
                        return Err(ControlSignal::Error(
                            "Keyword arguments must be symbols".into(),
                        ));
                    }
                }

                if let Some(val) = found_val {
                    self.match_dpattern(&spec.pattern, val, env, bindings, shape)?;
                    if let Some(sup) = spec.supplied {
                        let t_node = self.process.make_t(&self.globals);
                        self.bind_symbol(env, bindings, sup, t_node)?;
                    }
                } else {
                    let val = if let Some(init) = spec.init {
                        self.eval(init, env)?
                    } else {
                        self.process.make_nil()
                    };
                    self.match_dpattern(&spec.pattern, val, env, bindings, shape)?;
                    if let Some(sup) = spec.supplied {
                        let nil_node = self.process.make_nil();
                        self.bind_symbol(env, bindings, sup, nil_node)?;
                    }
                }
            }
        }

        for aux in &pattern.aux {
            let val = if let Some(init) = aux.init {
                self.eval(init, env)?
            } else {
                self.process.make_nil()
            };
            self.bind_symbol(env, bindings, aux.sym, val)?;
        }

        Ok(())
    }

    fn match_dpattern(
        &mut self,
        pattern: &DPattern,
        value: NodeId,
        env: &mut Environment,
        bindings: &mut HashMap<SymbolId, NodeId>,
        shape: &mut crate::pattern::ShapeClassifier,
    ) -> Result<(), ControlSignal> {
        match pattern {
            DPattern::Wildcard => Ok(()),
            DPattern::Var(sym) => self.bind_symbol(env, bindings, *sym, value),
            DPattern::Literal(lit) => {
                if crate::pattern::literal_equal(
                    &self.process.arena.inner,
                    &self.process.arrays,
                    &self.process.hashtables,
                    *lit,
                    value,
                ) {
                    Ok(())
                } else {
                    Err(ControlSignal::Error("Pattern mismatch".into()))
                }
            }
            DPattern::List(list) => self.match_dlist_pattern(list, value, env, bindings, shape),
        }
    }

    fn bind_symbol(
        &mut self,
        env: &mut Environment,
        bindings: &mut HashMap<SymbolId, NodeId>,
        sym: SymbolId,
        value: NodeId,
    ) -> Result<(), ControlSignal> {
        if let Some(bound) = bindings.get(&sym) {
            if crate::pattern::literal_equal(
                &self.process.arena.inner,
                &self.process.arrays,
                &self.process.hashtables,
                *bound,
                value,
            ) {
                return Ok(());
            }
            return Err(ControlSignal::Error("Pattern mismatch".into()));
        }
        bindings.insert(sym, value);
        env.bind(sym, value);
        Ok(())
    }

    fn next_list_cell(
        &self,
        list: NodeId,
        shape: &mut crate::pattern::ShapeClassifier,
    ) -> Result<Option<(NodeId, NodeId)>, ControlSignal> {
        match shape.classify(&self.process.arena.inner, list) {
            crate::pattern::Shape::Leaf => {
                if self.is_nil(list) {
                    Ok(None)
                } else {
                    Err(ControlSignal::Error("Expected list".into()))
                }
            }
            crate::pattern::Shape::Fork => match self.process.arena.inner.get_unchecked(list) {
                Node::Fork(head, tail) => Ok(Some((*head, *tail))),
                _ => Err(ControlSignal::Error("Expected list".into())),
            },
            crate::pattern::Shape::Stem => Err(ControlSignal::Error("Expected list".into())),
        }
    }

    fn collect_key_pairs(
        &mut self,
        list: NodeId,
        shape: &mut crate::pattern::ShapeClassifier,
    ) -> Result<(Vec<(NodeId, NodeId)>, bool), ControlSignal> {
        let mut pairs = Vec::new();
        let mut current = list;
        let nil_node = self.process.make_nil();
        loop {
            match self.next_list_cell(current, shape)? {
                Some((key, rest)) => match self.next_list_cell(rest, shape)? {
                    Some((val, tail)) => {
                        pairs.push((key, val));
                        current = tail;
                    }
                    None => {
                        pairs.push((key, nil_node));
                        return Ok((pairs, true));
                    }
                },
                None => return Ok((pairs, false)),
            }
        }
    }

    fn key_matches(&self, expected: SymbolId, actual: SymbolId) -> bool {
        let symbols = self.globals.symbols.read().unwrap();
        let expected_name = symbols.symbol_name(expected).unwrap_or("");
        let actual_name = symbols.symbol_name(actual).unwrap_or("");
        expected_name.eq_ignore_ascii_case(actual_name)
    }

    fn looks_like_method_list(&self, node: NodeId) -> bool {
        if self.is_nil(node) {
            return true;
        }

        match self.process.arena.get_unchecked(node) {
            Node::Fork(head, tail) => match self.process.arena.get_unchecked(*head) {
                Node::Leaf(OpaqueValue::Method(_)) => self.looks_like_method_list(*tail),
                _ => false,
            },
            _ => false,
        }
    }

    fn step_call_method_form(
        &mut self,
        state_idx: usize,
        args: NodeId,
        env: Environment,
    ) -> Result<bool, ControlSignal> {
        if state_idx >= self.process.next_method_states.len() {
            return Err(ControlSignal::Error("Invalid CallMethod state".into()));
        }

        let args_vec = self.cons_to_vec(args);
        if args_vec.is_empty() {
            return Err(ControlSignal::Error(
                "CALL-METHOD requires a method".into(),
            ));
        }

        let method_form = args_vec[0];
        let next_form = args_vec.get(1).copied();

        let method_val = self.eval(method_form, &env)?;
        let next_val = match next_form {
            Some(form) => {
                if self.looks_like_method_list(form) {
                    form
                } else {
                    self.eval(form, &env)?
                }
            }
            None => self.process.make_nil(),
        };

        let method_id = self.method_id_from_node(method_val)?;
        let next_ids = self.collect_method_ids(next_val)?;
        let call_args = self.process.next_method_states[state_idx].args.clone();

        self.call_method_with_next_methods(method_id, next_ids, call_args, env)
    }

    fn eval_call_method_form(
        &mut self,
        state_idx: usize,
        args: NodeId,
        env: &Environment,
    ) -> EvalResult {
        if state_idx >= self.process.next_method_states.len() {
            return Err(ControlSignal::Error("Invalid CallMethod state".into()));
        }

        let args_vec = self.cons_to_vec(args);
        if args_vec.is_empty() {
            return Err(ControlSignal::Error(
                "CALL-METHOD requires a method".into(),
            ));
        }

        let method_form = args_vec[0];
        let next_form = args_vec.get(1).copied();

        let method_val = self.eval(method_form, env)?;
        let next_val = match next_form {
            Some(form) => {
                if self.looks_like_method_list(form) {
                    form
                } else {
                    self.eval(form, env)?
                }
            }
            None => self.process.make_nil(),
        };

        let method_id = self.method_id_from_node(method_val)?;
        let next_ids = self.collect_method_ids(next_val)?;
        let call_args = self.process.next_method_states[state_idx].args.clone();

        self.call_method_with_next_methods(method_id, next_ids, call_args, env.clone())?;

        loop {
            match self.step() {
                Ok(true) => continue,
                Ok(false) => return Ok(self.process.program),
                Err(e) => return Err(e),
            }
        }
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
            if self.is_common_lisp_let_star_symbol(sym_id) {
                return self.eval_let_star(args, env);
            }
            if self.is_common_lisp_cond_symbol(sym_id) {
                return self.eval_cond(args, env);
            }
            if self.is_common_lisp_or_symbol(sym_id) {
                return self.eval_or(args, env);
            }
            // Check special forms
            let sf = &self.globals.special_forms;
            // 0. Check for macro expansion
            if let Some(&macro_idx) = self.process.macros.get(&sym_id) {
                if let Some(closure) = self.process.closures.get(macro_idx).cloned() {
                    let macro_timing_label = self.macro_timing_label(sym_id, args);
                    let expand_started_at = std::time::Instant::now();
                    let expanded = if let Some(fast) = self.try_fast_macro_expand(sym_id, args, env)?
                    {
                        fast
                    } else {
                        self._apply_macro(&closure, args)?
                    };
                    if let Some(label) = macro_timing_label {
                        let expand_ns = expand_started_at
                            .elapsed()
                            .as_nanos()
                            .min(u128::from(u64::MAX)) as u64;
                        let eval_started_at = std::time::Instant::now();
                        let result = self.eval(expanded, env)?;
                        let eval_ns = eval_started_at
                            .elapsed()
                            .as_nanos()
                            .min(u128::from(u64::MAX)) as u64;
                        self.log_macro_split_timing(&label, expand_ns, eval_ns);
                        return Ok(result);
                    }
                    return self.eval(expanded, env);
                }
            }

            if sym_id == sf.quote {
                return self.eval_quote(args);
            }
            if sym_id == sf.r#let {
                return self.eval_let(args, env);
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
            if sym_id == sf.multiple_value_bind {
                return self.eval_multiple_value_bind(args, env);
            }
            if sym_id == sf.multiple_value_call {
                return self.eval_multiple_value_call(args, env);
            }

            if let Some(func_node) = env.lookup_function(sym_id) {
                if let Node::Leaf(OpaqueValue::CallMethod(state_idx)) =
                    self.process.arena.get_unchecked(func_node)
                {
                    return self.eval_call_method_form(*state_idx as usize, args, env);
                }
            }

            // Check lexical function bindings (Lisp-2)
            if let Some(func) = env.lookup_function(sym_id) {
                return self.apply_function(func, args, env);
            }

            // Check if symbol has a function binding
            if let Some(func) = self.process.get_function(sym_id) {
                return self.apply_function(func, args, env);
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

            // Check if symbol has a value binding
            if let Some(val) = env.lookup(sym_id) {
                return self.apply_function(val, args, env);
            }
            if let Some(val) = self.process.get_value(sym_id) {
                return self.apply_function(val, args, env);
            }
        } else {
            match self.process.arena.inner.get_unchecked(op) {
                _ => {}
            }
        }

        // Evaluate operator
        let op_val = self.eval(op, env)?;

        // Apply
        self.apply_function(op_val, args, env)
    }

    /// Apply Generic Function (MOP-aware)
    fn apply_generic_function(
        &mut self,
        gid: crate::clos::GenericId,
        args: Vec<NodeId>,
        _env: &Environment,
    ) -> Result<bool, ControlSignal> {
        if self.is_fast_make_instance_target(gid) {
            let ok = match self.process.fast_make_instance_ok {
                Some(val) => val,
                None => {
                    let val = self.can_fast_make_instance();
                    self.process.fast_make_instance_ok = Some(val);
                    val
                }
            };
            if ok {
                return self.fast_make_instance(args);
            }
        }

        if !self.process.mop.generic_uses_eql_specializers(gid) {
            let arg_classes: Vec<_> = args.iter().map(|&v| self.arg_class_id(v)).collect();
            if let Some(effective_fn) =
                self.process.mop.get_cached_effective_method(gid, &arg_classes)
            {
                return self.step_apply(effective_fn, args, _env.clone());
            }
        }

        if self.is_internal_mop_generic(gid) {
            return self.apply_generic_function_raw(gid, args, _env);
        }

        let df = if let Some(df) = self
            .process
            .mop
            .get_generic_discriminating_function(gid)
        {
            df
        } else {
            let df = self.compute_discriminating_function(gid)?;
            self.process.mop.set_generic_discriminating_function(gid, df);
            df
        };

        // Apply the discriminating function to evaluated arguments.
        self.step_apply(df, args, _env.clone())
    }

    fn arg_class_id(&self, node: NodeId) -> crate::clos::ClassId {
        match self.process.arena.get_unchecked(node) {
            Node::Leaf(OpaqueValue::Instance(id)) => self
                .process
                .mop
                .get_instance(*id as usize)
                .map(|i| i.class)
                .unwrap_or(self.process.mop.standard_object),
            Node::Leaf(OpaqueValue::Class(_)) => self.process.mop.standard_class,
            Node::Leaf(OpaqueValue::Symbol(_)) => self.process.mop.symbol_class,
            Node::Leaf(OpaqueValue::Integer(_)) => self.process.mop.integer_class,
            Node::Leaf(OpaqueValue::Generic(_)) => self.process.mop.standard_generic_function,
            Node::Leaf(OpaqueValue::Method(_)) => self.process.mop.standard_method,
            Node::Leaf(OpaqueValue::SlotDefinition(_, _, direct)) => {
                if *direct {
                    self.process.mop.standard_direct_slot_definition
                } else {
                    self.process.mop.standard_effective_slot_definition
                }
            }
            Node::Leaf(OpaqueValue::EqlSpecializer(_)) => self.process.mop.eql_specializer_class,
            _ => self.process.mop.t_class,
        }
    }

    fn is_fast_make_instance_target(&self, gid: crate::clos::GenericId) -> bool {
        let gf = match self.process.mop.get_generic(gid) {
            Some(gf) => gf,
            None => return false,
        };
        let name = match gf.name {
            crate::clos::GenericName::Symbol(sym) => {
                let syms = self.globals.symbols.read().unwrap();
                syms.symbol_name(sym)
                    .unwrap_or("")
                    .to_ascii_uppercase()
            }
            crate::clos::GenericName::Setf(_) => return false,
        };
        name == "MAKE-INSTANCE"
    }

    fn can_fast_make_instance(&mut self) -> bool {
        let make_sym = self
            .lookup_symbol_any("MAKE-INSTANCE")
            .unwrap_or_else(|| self.ensure_cl_symbol("MAKE-INSTANCE"));
        let alloc_sym = self
            .lookup_symbol_any("ALLOCATE-INSTANCE")
            .unwrap_or_else(|| self.ensure_cl_symbol("ALLOCATE-INSTANCE"));
        let init_sym = self
            .lookup_symbol_any("INITIALIZE-INSTANCE")
            .unwrap_or_else(|| self.ensure_cl_symbol("INITIALIZE-INSTANCE"));
        let shared_sym = self
            .lookup_symbol_any("SHARED-INITIALIZE")
            .unwrap_or_else(|| self.ensure_cl_symbol("SHARED-INITIALIZE"));

        let make_gid = match self.process.mop.find_generic(make_sym) {
            Some(id) => id,
            None => return false,
        };

        let make_gf = match self.process.mop.get_generic(make_gid) {
            Some(gf) => gf,
            None => return false,
        };

        if make_gf.methods.len() != 2 {
            return false;
        }

        let mut has_standard = false;
        let mut has_symbol = false;
        for mid in &make_gf.methods {
            let method = match self.process.mop.get_method(*mid) {
                Some(m) => m,
                None => return false,
            };
            if !method.qualifiers.is_empty() || method.specializers.len() != 1 {
                return false;
            }
            match method.specializers[0] {
                crate::clos::Specializer::Class(cid)
                    if cid == self.process.mop.standard_class =>
                {
                    has_standard = true;
                }
                crate::clos::Specializer::Class(cid) if cid == self.process.mop.symbol_class => {
                    has_symbol = true;
                }
                _ => return false,
            }
        }
        if !(has_standard && has_symbol) {
            return false;
        }

        if !self.generic_is_simple(alloc_sym, self.process.mop.standard_class) {
            return false;
        }
        if !self.generic_is_simple(init_sym, self.process.mop.standard_object) {
            return false;
        }
        if !self.generic_is_simple(shared_sym, self.process.mop.standard_object) {
            return false;
        }

        true
    }

    fn generic_is_simple(
        &self,
        name: SymbolId,
        class_id: crate::clos::ClassId,
    ) -> bool {
        let gid = match self.process.mop.find_generic(name) {
            Some(id) => id,
            None => return false,
        };
        let gf = match self.process.mop.get_generic(gid) {
            Some(gf) => gf,
            None => return false,
        };
        if gf.methods.len() != 1 {
            return false;
        }
        let method = match self.process.mop.get_method(gf.methods[0]) {
            Some(m) => m,
            None => return false,
        };
        if !method.qualifiers.is_empty() || method.specializers.is_empty() {
            return false;
        }
        for (idx, spec) in method.specializers.iter().enumerate() {
            match spec {
                crate::clos::Specializer::Class(cid) if idx == 0 && *cid == class_id => {}
                crate::clos::Specializer::Class(cid)
                    if idx > 0 && *cid == self.process.mop.t_class => {}
                _ => return false,
            }
        }
        true
    }

    fn fast_make_instance(&mut self, args: Vec<NodeId>) -> Result<bool, ControlSignal> {
        if args.is_empty() {
            return Err(ControlSignal::Error(
                "MAKE-INSTANCE requires class".to_string(),
            ));
        }

        let class_node = args[0];
        let class_id = match self.process.arena.get_unchecked(class_node) {
            Node::Leaf(OpaqueValue::Class(id)) => Some(crate::clos::ClassId(*id)),
            Node::Leaf(OpaqueValue::Symbol(id)) => {
                self.process.mop.find_class(SymbolId(*id))
            }
            _ => None,
        }
        .ok_or_else(|| ControlSignal::Error("MAKE-INSTANCE: invalid class".to_string()))?;

        let unbound = self.process.make_unbound();
        let inst_idx = self
            .process
            .mop
            .make_instance(class_id, unbound)
            .ok_or_else(|| ControlSignal::Error("Failed to allocate instance".to_string()))?;
        let instance_node = self
            .process
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Instance(inst_idx as u32)));

        let mut shared_args = Vec::with_capacity(args.len() + 1);
        shared_args.push(instance_node);
        shared_args.push(self.process.make_t(self.globals));
        if args.len() > 1 {
            shared_args.extend_from_slice(&args[1..]);
        }
        let _ = crate::primitives::prim_shared_initialize(
            self.process,
            self.globals,
            &shared_args,
        )?;

        self.process.program = instance_node;
        self.process.execution_mode = crate::process::ExecutionMode::Return;
        Ok(true)
    }

    /// Apply Generic Function (raw dispatch, no MOP indirection)
    fn apply_generic_function_raw(
        &mut self,
        gid: crate::clos::GenericId,
        args: Vec<NodeId>,
        _env: &Environment,
    ) -> Result<bool, ControlSignal> {
        let methods = self
            .process
            .mop
            .compute_applicable_methods(gid, &args, &self.process.arena.inner);

        if methods.is_empty() {
            let gf_name = self
                .process
                .mop
                .get_generic(gid)
                .map(|g| match g.name {
                    crate::clos::GenericName::Symbol(sym) => self
                        .globals
                        .symbols
                        .read()
                        .unwrap()
                        .symbol_name(sym)
                        .map(|s| s.to_string())
                        .unwrap_or_else(|| "?".to_string()),
                    crate::clos::GenericName::Setf(sym) => {
                        let base = self
                            .globals
                            .symbols
                            .read()
                            .unwrap()
                            .symbol_name(sym)
                            .map(|s| s.to_string())
                            .unwrap_or_else(|| "?".to_string());
                        format!("(SETF {})", base)
                    }
                })
                .unwrap_or_else(|| "?".to_string());
            return Err(ControlSignal::Error(format!(
                "No applicable method for generic function {} {:?} with args {:?}",
                gf_name, gid, args
            )));
        }

        self.apply_methods_with_combination(gid, methods, args)
    }

    pub(crate) fn apply_methods_with_combination(
        &mut self,
        gid: crate::clos::GenericId,
        methods: Vec<crate::clos::MethodId>,
        args: Vec<NodeId>,
    ) -> Result<bool, ControlSignal> {
        // Ensure CALL-NEXT-METHOD is present in COMMON-LISP for lexical binding.
        let _ = self.ensure_cl_symbol("CALL-NEXT-METHOD");

        if methods.is_empty() {
            return Err(ControlSignal::Error(format!(
                "No applicable method for generic function {:?} with args {:?}",
                gid, args
            )));
        }

        let kw_before = self.ensure_keyword_symbol("BEFORE");
        let kw_after = self.ensure_keyword_symbol("AFTER");
        let kw_around = self.ensure_keyword_symbol("AROUND");

        let method_combination = self
            .process
            .mop
            .get_generic(gid)
            .map(|g| g.method_combination.clone())
            .unwrap_or(crate::clos::MethodCombination::Standard);

        // Build method chain based on method combination.
        let mut chain: Vec<crate::clos::MethodId> = Vec::new();

        match &method_combination {
            crate::clos::MethodCombination::Standard => {
                // Standard Method Combination (around, before, primary, after)
                let mut arounds = Vec::new();
                let mut befores = Vec::new();
                let mut primaries = Vec::new();
                let mut afters = Vec::new();

                for &mid in &methods {
                    let method = self.process.mop.get_method(mid).unwrap();
                    let has_around = method.qualifiers.iter().any(|q| *q == kw_around);
                    let has_before = method.qualifiers.iter().any(|q| *q == kw_before);
                    let has_after = method.qualifiers.iter().any(|q| *q == kw_after);

                    if has_around {
                        arounds.push(mid);
                    } else if has_before {
                        befores.push(mid);
                    } else if has_after {
                        afters.push(mid);
                    } else {
                        primaries.push(mid);
                    }
                }

                if primaries.is_empty() && arounds.is_empty() {
                    return Err(ControlSignal::Error(format!(
                        "No applicable primary method for generic function {:?} with args {:?}",
                        gid, args
                    )));
                }

                chain.extend(arounds);

                for mid in befores {
                    let wrapper = self.get_or_create_wrapper(mid, crate::clos::WrapperKind::Before);
                    chain.push(wrapper);
                }

                for mid in afters {
                    let wrapper = self.get_or_create_wrapper(mid, crate::clos::WrapperKind::After);
                    chain.push(wrapper);
                }

                chain.extend(primaries);
            }
            crate::clos::MethodCombination::Operator {
                name,
                operator,
                identity_with_one_arg,
            } => {
                let mut arounds = Vec::new();
                let mut primaries = Vec::new();

                for &mid in &methods {
                    let method = self.process.mop.get_method(mid).unwrap();
                    let has_around = method.qualifiers.iter().any(|q| *q == kw_around);
                    if has_around {
                        arounds.push(mid);
                        continue;
                    }

                    if method.qualifiers.len() == 1 && method.qualifiers[0] == *name {
                        primaries.push(mid);
                    }
                }

                if primaries.is_empty() && arounds.is_empty() {
                    return Err(ControlSignal::Error(format!(
                        "No applicable primary method for generic function {:?} with args {:?}",
                        gid, args
                    )));
                }

                if primaries.is_empty() {
                    return Err(ControlSignal::Error(format!(
                        "No applicable primary method for operator method combination {:?}",
                        gid
                    )));
                }

                let comb_method =
                    self.build_operator_wrapper(&primaries, *operator, *identity_with_one_arg);
                chain.extend(arounds);
                chain.push(comb_method);
            }
            crate::clos::MethodCombination::UserLong {
                expander,
                options,
                ..
            } => {
                // Build list of method objects (most specific first).
                let mut method_nodes = Vec::with_capacity(methods.len());
                for &mid in &methods {
                    let mnode = self
                        .process
                        .arena
                        .inner
                        .alloc(Node::Leaf(OpaqueValue::Method(mid.0)));
                    method_nodes.push(mnode);
                }
                let methods_list = self.process.make_list(&method_nodes);

                let gf_node = self
                    .process
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Generic(gid.0)));
                let options_list = *options;
                let args_list = self.process.make_list(&args);

                // Invoke expander with evaluated arguments.
                let expander_args = vec![gf_node, methods_list, options_list, args_list];
                let expansion = match self.process.arena.get_unchecked(*expander) {
                    Node::Leaf(OpaqueValue::Closure(idx)) => {
                        let closure = self.process.closures[*idx as usize].clone();
                        let new_env = self.bind_lambda_list(&closure, &expander_args, None)?;
                        self.eval(closure.body, &new_env)?
                    }
                    _ => {
                        return Err(ControlSignal::Error(
                            "Method combination expander is not a closure".into(),
                        ))
                    }
                };

                // Wrap expansion in a closure that receives &rest args.
                let args_sym = {
                    let mut syms = self.globals.symbols.write().unwrap();
                    syms.make_symbol("ARGS")
                };
                let progn_sym = self.globals.special_forms.progn;
                let progn_sym_node = self
                    .process
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Symbol(progn_sym.0)));
                let body_list = self.process.make_list(&[expansion]);
                let body_node = self
                    .process
                    .arena
                    .inner
                    .alloc(Node::Fork(progn_sym_node, body_list));

                let mut lambda_list = ParsedLambdaList::default();
                lambda_list.rest = Some(args_sym);
                let closure = Closure {
                    lambda_list,
                    destructuring: None,
                    body: body_node,
                    env: Environment::new(),
                };
                let closure_idx = self.process.closures.len();
                self.process.closures.push(closure);

                // Bind call-method in the expansion evaluation context.
                let next_state = crate::clos::NextMethodState {
                    methods: Vec::new(),
                    args: args.clone(),
                };
                self.process.next_method_states.push(next_state);
                let next_state_idx = (self.process.next_method_states.len() - 1) as u32;

                let wrapper = OpaqueValue::MethodWrapper(closure_idx as u32, next_state_idx);
                let wrapper_node = self
                    .process
                    .arena
                    .inner
                    .alloc(Node::Leaf(wrapper));

                return self.step_apply(wrapper_node, args.clone(), Environment::new());
            }
        }

        // Method Chain Logic
        let first_method_id = chain[0];
        let remaining_methods = chain[1..].to_vec();

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

    fn is_internal_mop_generic(&self, gid: crate::clos::GenericId) -> bool {
        let gf = match self.process.mop.get_generic(gid) {
            Some(gf) => gf,
            None => return false,
        };
        let name = match gf.name {
            crate::clos::GenericName::Symbol(sym) => {
                let syms = self.globals.symbols.read().unwrap();
                syms.symbol_name(sym)
                    .unwrap_or("")
                    .to_ascii_uppercase()
            }
            crate::clos::GenericName::Setf(_) => return false,
        };
        matches!(
            name.as_str(),
            "COMPUTE-DISCRIMINATING-FUNCTION"
                | "COMPUTE-EFFECTIVE-METHOD"
                | "COMPUTE-EFFECTIVE-METHOD-FUNCTION"
                | "METHOD-FUNCTION"
                | "MAKE-METHOD-LAMBDA"
                | "GENERIC-FUNCTION-ARGUMENT-PRECEDENCE-ORDER"
        )
    }

    fn resolve_function_by_name(&mut self, name: &str) -> Option<NodeId> {
        let (sym_user, sym_cl) = {
            let mut syms = self.globals.symbols.write().unwrap();
            let sym_user = syms.intern_in(name, crate::symbol::PackageId(2));
            let sym_cl = syms.intern_in(name, crate::symbol::PackageId(1));
            (sym_user, sym_cl)
        };
        self.process
            .get_function(sym_user)
            .or_else(|| self.process.get_function(sym_cl))
    }

    fn compute_discriminating_function(
        &mut self,
        gid: crate::clos::GenericId,
    ) -> Result<NodeId, ControlSignal> {
        let func_node = self
            .resolve_function_by_name("COMPUTE-DISCRIMINATING-FUNCTION")
            .ok_or_else(|| {
                ControlSignal::Error("Undefined function: COMPUTE-DISCRIMINATING-FUNCTION".into())
            })?;

        let gf_node = self
            .process
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Generic(gid.0)));
        let args_list = self.process.make_list(&[gf_node]);

        let env = Environment::new();
        let saved_program = self.process.program;
        let saved_mode = self.process.execution_mode.clone();
        let saved_env = self.process.current_env.clone();
        let saved_stack = std::mem::take(&mut self.process.continuation_stack);
        let saved_pending = self.process.pending_redex;
        let saved_next_methods = std::mem::take(&mut self.process.next_method_states);
        let result = self.apply_values(func_node, args_list, &env);
        self.process.program = saved_program;
        self.process.execution_mode = saved_mode;
        self.process.current_env = saved_env;
        self.process.continuation_stack = saved_stack;
        self.process.pending_redex = saved_pending;
        self.process.next_method_states = saved_next_methods;
        let df = result?;

        match self.process.arena.get_unchecked(df) {
            Node::Leaf(OpaqueValue::Closure(_))
            | Node::Leaf(OpaqueValue::Generic(_))
            | Node::Leaf(OpaqueValue::Symbol(_)) => Ok(df),
            _ => Err(ControlSignal::Error(
                "COMPUTE-DISCRIMINATING-FUNCTION did not return a function".into(),
            )),
        }
    }

    fn ensure_keyword_symbol(&mut self, name: &str) -> SymbolId {
        let mut syms = self.globals.symbols.write().unwrap();
        let sym = syms.intern_in(name, crate::symbol::PackageId(0));
        sym
    }

    fn ensure_cl_symbol(&mut self, name: &str) -> SymbolId {
        let mut syms = self.globals.symbols.write().unwrap();
        let sym = syms.intern_in(name, crate::symbol::PackageId(1));
        syms.export_symbol(sym);
        sym
    }

    fn lookup_symbol_any(&self, name: &str) -> Option<SymbolId> {
        let syms = self.globals.symbols.read().unwrap();
        let name_upper = name.to_ascii_uppercase();
        syms.get_package(crate::symbol::PackageId(2))
            .and_then(|p| p.find_symbol(&name_upper))
            .or_else(|| {
                syms.get_package(crate::symbol::PackageId(1))
                    .and_then(|p| p.find_symbol(&name_upper))
            })
    }

    fn sym_node(&mut self, sym: SymbolId) -> NodeId {
        self.process
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(sym.0)))
    }

    fn parse_specializer(&mut self, spec_node: NodeId) -> crate::clos::Specializer {
        // Handle (eql <object>) specializers
        if let Node::Fork(car, rest) = self.process.arena.inner.get_unchecked(spec_node).clone() {
            if let Some(sym) = self.node_to_symbol(car) {
                if sym == self.ensure_cl_symbol("EQL") {
                    if let Node::Fork(obj, _) =
                        self.process.arena.inner.get_unchecked(rest).clone()
                    {
                        let idx = self
                            .process
                            .mop
                            .intern_eql_specializer(&self.process.arena.inner, obj);
                        return crate::clos::Specializer::Eql(idx);
                    }
                }
            }
        }

        match self.process.arena.inner.get_unchecked(spec_node) {
            Node::Leaf(OpaqueValue::EqlSpecializer(idx)) => {
                crate::clos::Specializer::Eql(*idx)
            }
            Node::Leaf(OpaqueValue::Class(id)) => {
                crate::clos::Specializer::Class(crate::clos::ClassId(*id))
            }
            Node::Leaf(OpaqueValue::Symbol(id)) => {
                let sym = SymbolId(*id);
                let class_id = self
                    .process
                    .mop
                    .find_class(sym)
                    .unwrap_or(self.process.mop.t_class);
                crate::clos::Specializer::Class(class_id)
            }
            _ => crate::clos::Specializer::Class(self.process.mop.t_class),
        }
    }

    fn get_or_create_wrapper(
        &mut self,
        method_id: crate::clos::MethodId,
        kind: crate::clos::WrapperKind,
    ) -> crate::clos::MethodId {
        if let Some(w) = self.process.mop.get_wrapper(kind, method_id) {
            return w;
        }

        let method = self.process.mop.get_method(method_id).unwrap();
        let method_body = method.body;

        // Build wrapper closure with (&rest args)
        let args_sym = {
            let mut syms = self.globals.symbols.write().unwrap();
            syms.make_symbol("ARGS")
        };
        let args_node = self.sym_node(args_sym);

        let apply_sym = self.ensure_cl_symbol("APPLY");
        let call_next_sym = self.ensure_cl_symbol("CALL-NEXT-METHOD");
        let progn_sym = self.ensure_cl_symbol("PROGN");
        let let_sym = self.ensure_cl_symbol("LET");

        let apply_sym_node = self.sym_node(apply_sym);
        let call_next_sym_node = self.sym_node(call_next_sym);
        let progn_sym_node = self.sym_node(progn_sym);
        let let_sym_node = self.sym_node(let_sym);

        let apply_call = self
            .process
            .make_list(&[apply_sym_node, method_body, args_node]);
        let call_next_call = self.process.make_list(&[call_next_sym_node]);

        let body_node = match kind {
            crate::clos::WrapperKind::Before => {
                self.process
                    .make_list(&[progn_sym_node, apply_call, call_next_call])
            }
            crate::clos::WrapperKind::After => {
                let result_sym = {
                    let mut syms = self.globals.symbols.write().unwrap();
                    syms.make_symbol("RESULT")
                };
                let result_node = self.sym_node(result_sym);

                // (let ((result (call-next-method))) (apply method args) result)
                let binding = self.process.make_list(&[result_node, call_next_call]);
                let bindings = self.process.make_list(&[binding]);
                self.process
                    .make_list(&[let_sym_node, bindings, apply_call, result_node])
            }
        };

        let mut lambda_list = ParsedLambdaList::default();
        lambda_list.rest = Some(args_sym);

        let closure = Closure {
            lambda_list,
            destructuring: None,
            body: body_node,
            env: Environment::new(),
        };
        let closure_idx = self.process.closures.len();
        self.process.closures.push(closure);
        let closure_node = self
            .process
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Closure(closure_idx as u32)));

        let wrapper_id = self
            .process
            .mop
            .add_method_raw(Vec::new(), Vec::new(), closure_node);
        self.process.mop.set_wrapper(kind, method_id, wrapper_id);
        wrapper_id
    }

    fn build_operator_wrapper(
        &mut self,
        primaries: &[crate::clos::MethodId],
        operator: SymbolId,
        identity_with_one_arg: bool,
    ) -> crate::clos::MethodId {
        // Build wrapper closure with (&rest args)
        let args_sym = {
            let mut syms = self.globals.symbols.write().unwrap();
            syms.make_symbol("ARGS")
        };
        let args_node = self.sym_node(args_sym);

        let apply_sym = self.ensure_cl_symbol("APPLY");
        let apply_sym_node = self.sym_node(apply_sym);
        let operator_node = self.sym_node(operator);

        let mut calls = Vec::new();
        for &mid in primaries {
            let method = self.process.mop.get_method(mid).unwrap();
            let method_body = method.body;
            let apply_call = self
                .process
                .make_list(&[apply_sym_node, method_body, args_node]);
            calls.push(apply_call);
        }

        let body_node = if identity_with_one_arg && calls.len() == 1 {
            calls[0]
        } else {
            let mut elems = Vec::with_capacity(calls.len() + 1);
            elems.push(operator_node);
            elems.extend(calls);
            self.process.make_list(&elems)
        };

        let mut lambda_list = ParsedLambdaList::default();
        lambda_list.rest = Some(args_sym);

        let closure = Closure {
            lambda_list,
            destructuring: None,
            body: body_node,
            env: Environment::new(),
        };
        let closure_idx = self.process.closures.len();
        self.process.closures.push(closure);
        let closure_node = self
            .process
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Closure(closure_idx as u32)));

        self.process
            .mop
            .add_method_raw(Vec::new(), Vec::new(), closure_node)
    }

    fn method_id_from_node(
        &mut self,
        node: NodeId,
    ) -> Result<crate::clos::MethodId, ControlSignal> {
        match self.process.arena.get_unchecked(node) {
            Node::Leaf(OpaqueValue::Method(id)) => Ok(crate::clos::MethodId(*id)),
            Node::Leaf(OpaqueValue::Closure(_)) => {
                let mid = self.process.mop.add_method_raw(Vec::new(), Vec::new(), node);
                Ok(mid)
            }
            other => Err(ControlSignal::Error(format!(
                "CALL-METHOD requires a method object, got {:?}",
                other
            ))),
        }
    }

    fn collect_method_ids(
        &mut self,
        list: NodeId,
    ) -> Result<Vec<crate::clos::MethodId>, ControlSignal> {
        if self.is_nil(list) {
            return Ok(Vec::new());
        }

        let mut out = Vec::new();
        let mut current = list;
        while let Node::Fork(head, tail) = self.process.arena.get_unchecked(current).clone() {
            let mid = self.method_id_from_node(head)?;
            out.push(mid);
            current = tail;
        }
        Ok(out)
    }

    fn call_method_with_next_methods(
        &mut self,
        method_id: crate::clos::MethodId,
        next_methods: Vec<crate::clos::MethodId>,
        args: Vec<NodeId>,
        env: Environment,
    ) -> Result<bool, ControlSignal> {
        let next_state = crate::clos::NextMethodState {
            methods: next_methods,
            args: args.clone(),
        };

        self.process.next_method_states.push(next_state);
        let next_state_idx = (self.process.next_method_states.len() - 1) as u32;

        let method = self
            .process
            .mop
            .get_method(method_id)
            .ok_or_else(|| ControlSignal::Error("Invalid method object".into()))?;
        let body = method.body;

        if let Node::Leaf(OpaqueValue::Closure(idx)) = self.process.arena.get_unchecked(body) {
            let wrapper = OpaqueValue::MethodWrapper(*idx, next_state_idx);
            let wrapper_node = self.process.arena.inner.alloc(Node::Leaf(wrapper));
            return self.step_apply(wrapper_node, args, env);
        }

        Err(ControlSignal::Error(
            "Call-method body is not closure".into(),
        ))
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

    fn debug_deftest_timing_enabled(&self) -> bool {
        static ENABLED: OnceLock<bool> = OnceLock::new();
        *ENABLED.get_or_init(|| std::env::var("TREECL_DEBUG_DEFTEST_TIMING").is_ok())
    }

    fn debug_rt_macro_timing_enabled(&self) -> bool {
        static ENABLED: OnceLock<bool> = OnceLock::new();
        *ENABLED.get_or_init(|| std::env::var("TREECL_DEBUG_RT_MACRO_TIMING").is_ok())
    }

    fn deftest_timing_match_pattern(&self) -> Option<&str> {
        static PATTERN: OnceLock<Option<String>> = OnceLock::new();
        PATTERN
            .get_or_init(|| std::env::var("TREECL_DEBUG_DEFTEST_MATCH").ok())
            .as_deref()
    }

    fn rt_macro_timing_match_pattern(&self) -> Option<&str> {
        static PATTERN: OnceLock<Option<String>> = OnceLock::new();
        PATTERN
            .get_or_init(|| std::env::var("TREECL_DEBUG_RT_MACRO_MATCH").ok())
            .as_deref()
    }

    fn is_regression_deftest_symbol(&self, sym: SymbolId) -> bool {
        let symbols = self.globals.symbols.read().unwrap();
        if symbols.symbol_name(sym) != Some("DEFTEST") {
            return false;
        }
        let Some(pkg_id) = symbols.symbol_package(sym) else {
            return false;
        };
        let Some(pkg) = symbols.get_package(pkg_id) else {
            return false;
        };
        pkg.name == "REGRESSION-TEST"
    }

    fn format_deftest_name_from_args(&self, args: NodeId) -> String {
        let first_arg = match self.process.arena.inner.get_unchecked(args) {
            Node::Fork(head, _) => *head,
            _ => return "<missing-name>".to_string(),
        };
        let symbols = self.globals.symbols.read().unwrap();
        if let Some(sym) = self.node_to_symbol(first_arg) {
            let name = symbols.symbol_name(sym).unwrap_or("<unnamed>");
            if let Some(pkg_id) = symbols.symbol_package(sym) {
                if let Some(pkg) = symbols.get_package(pkg_id) {
                    return format!("{}:{}", pkg.name, name);
                }
            }
            return name.to_string();
        }
        crate::printer::print_to_string(&self.process.arena.inner, &symbols, first_arg)
    }

    fn should_time_deftest(&self, sym: SymbolId, args: NodeId) -> Option<String> {
        if !self.debug_deftest_timing_enabled() {
            return None;
        }
        if !self.is_regression_deftest_symbol(sym) {
            return None;
        }
        let test_name = self.format_deftest_name_from_args(args);
        if let Some(pattern) = self.deftest_timing_match_pattern() {
            if !pattern.is_empty() && !test_name.contains(pattern) {
                return None;
            }
        }
        Some(test_name)
    }

    fn format_macro_name(&self, sym: SymbolId) -> String {
        let symbols = self.globals.symbols.read().unwrap();
        let sym_name = symbols.symbol_name(sym).unwrap_or("<unnamed>");
        if let Some(pkg_id) = symbols.symbol_package(sym) {
            if let Some(pkg) = symbols.get_package(pkg_id) {
                return format!("{}:{}", pkg.name, sym_name);
            }
        }
        sym_name.to_string()
    }

    fn should_time_rt_macro(&self, sym: SymbolId) -> Option<String> {
        if !self.debug_rt_macro_timing_enabled() {
            return None;
        }
        let macro_name = self.format_macro_name(sym);
        if let Some(pattern) = self.rt_macro_timing_match_pattern() {
            if !pattern.is_empty() && !macro_name.contains(pattern) {
                return None;
            }
        }
        Some(macro_name)
    }

    fn macro_timing_label(&self, sym: SymbolId, args: NodeId) -> Option<String> {
        if let Some(test_name) = self.should_time_deftest(sym, args) {
            return Some(format!("DEFTEST TIMING [{}]", test_name));
        }
        self.should_time_rt_macro(sym)
            .map(|name| format!("MACRO TIMING [{}]", name))
    }

    fn log_macro_split_timing(&self, label: &str, expand_ns: u64, eval_ns: u64) {
        let expand_ms = expand_ns as f64 / 1_000_000.0;
        let eval_ms = eval_ns as f64 / 1_000_000.0;
        let total_ms = (expand_ns.saturating_add(eval_ns)) as f64 / 1_000_000.0;
        eprintln!(
            "{}: expand={:.3}ms eval={:.3}ms total={:.3}ms",
            label, expand_ms, eval_ms, total_ms
        );
    }

    fn make_quote_form(&mut self, value: NodeId) -> NodeId {
        let quote_sym = self.globals.special_forms.quote;
        let quote_node = self
            .process
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(quote_sym.0)));
        let arg_list = self.process.make_list(&[value]);
        self.process.arena.inner.alloc(Node::Fork(quote_node, arg_list))
    }

    fn make_call_form(&mut self, operator: NodeId, args: &[NodeId]) -> NodeId {
        let arg_list = self.process.make_list(args);
        self.process.arena.inner.alloc(Node::Fork(operator, arg_list))
    }

    fn make_string_form(&mut self, value: &str) -> NodeId {
        self.process
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::String(value.to_string())))
    }

    fn try_fast_macro_expand(
        &mut self,
        sym: SymbolId,
        args: NodeId,
        env: &Environment,
    ) -> Result<Option<NodeId>, ControlSignal> {
        if self.is_regression_deftest_symbol(sym) {
            return Ok(Some(self.expand_regression_deftest(args)?));
        }
        if self.is_common_lisp_setf_symbol(sym) {
            if let Some(expanded) = self.expand_common_lisp_setf(args)? {
                return Ok(Some(expanded));
            }
        }
        if self.is_common_lisp_defmethod_symbol(sym) {
            if let Some(expanded) = self.expand_common_lisp_defmethod(args)? {
                return Ok(Some(expanded));
            }
        }
        if self.is_cl_test_signals_error_symbol(sym) {
            return Ok(Some(self.expand_cl_test_signals_error(args, env)?));
        }
        Ok(None)
    }

    fn expand_common_lisp_defmethod(
        &mut self,
        args: NodeId,
    ) -> Result<Option<NodeId>, ControlSignal> {
        let args_vec = self.cons_to_vec(args);
        if args_vec.len() < 2 {
            return Ok(None);
        }

        let name_node = args_vec[0];

        // Parse qualifiers the same way as parse-defmethod-qualifiers:
        // consume non-NIL symbols until the lambda-list starts.
        let mut qualifiers = Vec::new();
        let mut idx = 1usize;
        while idx < args_vec.len() {
            let arg = args_vec[idx];
            let Some(_sym) = self.node_to_symbol(arg) else {
                break;
            };
            if self.is_nil(arg) {
                break;
            }
            qualifiers.push(arg);
            idx += 1;
        }

        if idx >= args_vec.len() {
            return Ok(None);
        }
        let lambda_list_node = args_vec[idx];
        let body_nodes = &args_vec[idx + 1..];

        let Some((clean_ll_node, specs_node)) =
            self.parse_defmethod_lambda_list_fast(lambda_list_node)
        else {
            return Ok(None);
        };
        let qualifiers_node = self.process.make_list(&qualifiers);

        let let_star_sym = self.ensure_cl_symbol("LET*");
        let if_sym = self.ensure_cl_symbol("IF");
        let and_sym = self.ensure_cl_symbol("AND");
        let fboundp_sym = self.ensure_cl_symbol("FBOUNDP");
        let symbol_function_sym = self.ensure_cl_symbol("SYMBOL-FUNCTION");
        let ensure_generic_function_sym = self.ensure_cl_symbol("ENSURE-GENERIC-FUNCTION");
        let function_sym = self.ensure_cl_symbol("FUNCTION");
        let lambda_sym = self.ensure_cl_symbol("LAMBDA");
        let ensure_method_sym = self.ensure_cl_symbol("ENSURE-METHOD");
        let generic_function_methods_sym = self.ensure_cl_symbol("GENERIC-FUNCTION-METHODS");
        let make_method_lambda_sym = self.ensure_cl_symbol("MAKE-METHOD-LAMBDA");
        let use_make_method_lambda_sym = self.ensure_cl_symbol("*USE-MAKE-METHOD-LAMBDA*");
        let gf_sym = self.ensure_cl_symbol("GF");
        let fn_sym = self.ensure_cl_symbol("FN");
        let kw_lambda_list_sym = self.ensure_keyword_symbol("LAMBDA-LIST");
        let kw_qualifiers_sym = self.ensure_keyword_symbol("QUALIFIERS");
        let kw_specializers_sym = self.ensure_keyword_symbol("SPECIALIZERS");
        let kw_body_sym = self.ensure_keyword_symbol("BODY");

        let let_star_node = self.sym_node(let_star_sym);
        let if_node = self.sym_node(if_sym);
        let and_node = self.sym_node(and_sym);
        let fboundp_node = self.sym_node(fboundp_sym);
        let symbol_function_node = self.sym_node(symbol_function_sym);
        let ensure_generic_function_node = self.sym_node(ensure_generic_function_sym);
        let function_node = self.sym_node(function_sym);
        let lambda_node = self.sym_node(lambda_sym);
        let ensure_method_node = self.sym_node(ensure_method_sym);
        let generic_function_methods_node = self.sym_node(generic_function_methods_sym);
        let make_method_lambda_node = self.sym_node(make_method_lambda_sym);
        let use_make_method_lambda_node = self.sym_node(use_make_method_lambda_sym);
        let gf_node = self.sym_node(gf_sym);
        let fn_node = self.sym_node(fn_sym);
        let kw_lambda_list_node = self.sym_node(kw_lambda_list_sym);
        let kw_qualifiers_node = self.sym_node(kw_qualifiers_sym);
        let kw_specializers_node = self.sym_node(kw_specializers_sym);
        let kw_body_node = self.sym_node(kw_body_sym);

        let quoted_name = self.make_quote_form(name_node);
        let quoted_clean_ll = self.make_quote_form(clean_ll_node);
        let quoted_qualifiers = self.make_quote_form(qualifiers_node);
        let quoted_specs = self.make_quote_form(specs_node);

        let fboundp_call = self.make_call_form(fboundp_node, &[quoted_name]);
        let symbol_function_name = self.make_call_form(symbol_function_node, &[quoted_name]);
        let ensure_generic_call = self.make_call_form(
            ensure_generic_function_node,
            &[quoted_name, kw_lambda_list_node, quoted_clean_ll],
        );
        let gf_init = self.make_call_form(if_node, &[fboundp_call, symbol_function_name, ensure_generic_call]);

        let lambda_args = {
            let mut v = Vec::with_capacity(1 + body_nodes.len());
            v.push(clean_ll_node);
            v.extend_from_slice(body_nodes);
            v
        };
        let lambda_form = self.make_call_form(lambda_node, &lambda_args);
        let fn_init = self.make_call_form(function_node, &[lambda_form]);

        let gf_binding = self.process.make_list(&[gf_node, gf_init]);
        let fn_binding = self.process.make_list(&[fn_node, fn_init]);
        let bindings = self.process.make_list(&[gf_binding, fn_binding]);

        let quoted_make_method_lambda = self.make_quote_form(make_method_lambda_node);
        let make_method_symbol_fn =
            self.make_call_form(symbol_function_node, &[quoted_make_method_lambda]);
        let make_method_methods =
            self.make_call_form(generic_function_methods_node, &[make_method_symbol_fn]);
        let make_method_guard =
            self.make_call_form(and_node, &[use_make_method_lambda_node, make_method_methods]);
        let make_method_call = self.make_call_form(
            make_method_lambda_node,
            &[gf_node, self.process.make_nil(), fn_node, self.process.make_nil()],
        );
        let method_body = self.make_call_form(if_node, &[make_method_guard, make_method_call, fn_node]);

        let ensure_method_call = self.make_call_form(
            ensure_method_node,
            &[
                gf_node,
                kw_lambda_list_node,
                quoted_clean_ll,
                kw_qualifiers_node,
                quoted_qualifiers,
                kw_specializers_node,
                quoted_specs,
                kw_body_node,
                method_body,
            ],
        );

        Ok(Some(
            self.make_call_form(let_star_node, &[bindings, ensure_method_call]),
        ))
    }

    fn parse_defmethod_lambda_list_fast(&mut self, lambda_list: NodeId) -> Option<(NodeId, NodeId)> {
        let mut clean_ll = Vec::new();
        let mut specs = Vec::new();
        let mut current = lambda_list;

        loop {
            match self.process.arena.get_unchecked(current).clone() {
                Node::Leaf(OpaqueValue::Nil) => {
                    return Some((self.process.make_list(&clean_ll), self.process.make_list(&specs)));
                }
                Node::Fork(arg, rest) => {
                    if let Some(sym) = self.node_to_symbol(arg) {
                        if self.is_defmethod_lambda_keyword(sym) {
                            let mut clean_with_tail = clean_ll;
                            clean_with_tail.extend(self.cons_to_vec(current));
                            return Some((
                                self.process.make_list(&clean_with_tail),
                                self.process.make_list(&specs),
                            ));
                        }
                    }

                    match self.process.arena.get_unchecked(arg).clone() {
                        Node::Fork(param_name, param_tail) => {
                            clean_ll.push(param_name);
                            let spec = match self.process.arena.get_unchecked(param_tail).clone() {
                                Node::Fork(spec, _) => spec,
                                _ => self.process.make_nil(),
                            };
                            specs.push(spec);
                        }
                        _ => {
                            clean_ll.push(arg);
                            specs.push(self.sym_node(self.globals.t_sym));
                        }
                    }

                    current = rest;
                }
                _ => return None,
            }
        }
    }

    fn is_defmethod_lambda_keyword(&mut self, sym: SymbolId) -> bool {
        sym == self.ensure_cl_symbol("&OPTIONAL")
            || sym == self.ensure_cl_symbol("&REST")
            || sym == self.ensure_cl_symbol("&KEY")
            || sym == self.ensure_cl_symbol("&AUX")
    }

    fn expand_common_lisp_setf(&mut self, args: NodeId) -> Result<Option<NodeId>, ControlSignal> {
        let args_vec = self.cons_to_vec(args);
        if args_vec.is_empty() {
            return Ok(Some(self.process.make_nil()));
        }
        if args_vec.len() % 2 != 0 {
            let error_sym = self.ensure_cl_symbol("ERROR");
            let error_node = self.sym_node(error_sym);
            let msg = self.make_string_form("SETF: Odd number of arguments");
            return Ok(Some(self.make_call_form(error_node, &[msg])));
        }

        let mut assignment_forms = Vec::new();
        for pair in args_vec.chunks_exact(2) {
            let Some(assignment) = self.expand_common_lisp_setf_assignment(pair[0], pair[1])? else {
                return Ok(None);
            };
            assignment_forms.push(assignment);
        }

        if assignment_forms.len() == 1 {
            return Ok(Some(assignment_forms[0]));
        }

        let progn_sym = self.globals.special_forms.progn;
        let progn_node = self.sym_node(progn_sym);
        let body_list = self.process.make_list(&assignment_forms);
        Ok(Some(self.process.arena.inner.alloc(Node::Fork(progn_node, body_list))))
    }

    fn expand_common_lisp_setf_assignment(
        &mut self,
        place: NodeId,
        value: NodeId,
    ) -> Result<Option<NodeId>, ControlSignal> {
        if let Some(_) = self.node_to_symbol(place) {
            let setq_sym = self.globals.special_forms.setq;
            let setq_node = self.sym_node(setq_sym);
            let pair_list = self.process.make_list(&[place, value]);
            return Ok(Some(self.process.arena.inner.alloc(Node::Fork(setq_node, pair_list))));
        }

        let (op_node, place_args_node) = match self.process.arena.get_unchecked(place).clone() {
            Node::Fork(op, place_args) => (op, place_args),
            _ => return Ok(None),
        };
        let Some(op_sym) = self.node_to_symbol(op_node) else {
            return Ok(None);
        };
        let op_name = {
            let symbols = self.globals.symbols.read().unwrap();
            symbols.symbol_name(op_sym).unwrap_or("").to_string()
        };
        let place_args = self.cons_to_vec(place_args_node);

        let writer_call = match op_name.as_str() {
            "CAR" if place_args.len() == 1 => {
                let writer_sym = self.ensure_cl_symbol("RPLACA");
                let writer = self.sym_node(writer_sym);
                self.make_call_form(writer, &[place_args[0], value])
            }
            "CDR" if place_args.len() == 1 => {
                let writer_sym = self.ensure_cl_symbol("RPLACD");
                let writer = self.sym_node(writer_sym);
                self.make_call_form(writer, &[place_args[0], value])
            }
            "GETHASH" if place_args.len() >= 2 => {
                let writer_sym = self.ensure_cl_symbol("SET-GETHASH");
                let writer = self.sym_node(writer_sym);
                self.make_call_form(writer, &[place_args[0], place_args[1], value])
            }
            "READTABLE-CASE" if place_args.len() == 1 => {
                let writer_sym = self.ensure_cl_symbol("SET-READTABLE-CASE");
                let writer = self.sym_node(writer_sym);
                self.make_call_form(writer, &[place_args[0], value])
            }
            "SLOT-VALUE" if place_args.len() == 2 => {
                let writer_sym = self.ensure_cl_symbol("SET-SLOT-VALUE");
                let writer = self.sym_node(writer_sym);
                self.make_call_form(writer, &[place_args[0], place_args[1], value])
            }
            "FUNCALLABLE-STANDARD-INSTANCE-ACCESS" if place_args.len() == 2 => {
                let writer_sym =
                    self.ensure_cl_symbol("SET-FUNCALLABLE-STANDARD-INSTANCE-ACCESS");
                let writer = self.sym_node(writer_sym);
                self.make_call_form(writer, &[place_args[0], place_args[1], value])
            }
            "SYMBOL-VALUE" if place_args.len() == 1 => {
                let writer_sym = self.ensure_cl_symbol("SET");
                let writer = self.sym_node(writer_sym);
                self.make_call_form(writer, &[place_args[0], value])
            }
            "GET" if place_args.len() == 2 => {
                let writer_sym = self.ensure_cl_symbol("PUT");
                let writer = self.sym_node(writer_sym);
                self.make_call_form(writer, &[place_args[0], place_args[1], value])
            }
            "LOGICAL-PATHNAME-TRANSLATIONS" if place_args.len() == 1 => {
                let writer_sym = self.ensure_cl_symbol("SET-LOGICAL-PATHNAME-TRANSLATIONS");
                let writer = self.sym_node(writer_sym);
                self.make_call_form(writer, &[place_args[0], value])
            }
            _ => return Ok(None),
        };
        Ok(Some(writer_call))
    }

    fn is_cl_test_signals_error_symbol(&self, sym: SymbolId) -> bool {
        self.is_symbol_named_in_package(sym, "CL-TEST", "SIGNALS-ERROR")
    }

    fn is_common_lisp_setf_symbol(&self, sym: SymbolId) -> bool {
        self.is_symbol_named_in_package(sym, "COMMON-LISP", "SETF")
    }

    fn is_common_lisp_defmethod_symbol(&self, sym: SymbolId) -> bool {
        self.is_symbol_named_in_package(sym, "COMMON-LISP", "DEFMETHOD")
    }

    fn is_common_lisp_let_star_symbol(&self, sym: SymbolId) -> bool {
        self.is_symbol_named_in_package(sym, "COMMON-LISP", "LET*")
    }

    fn is_common_lisp_cond_symbol(&self, sym: SymbolId) -> bool {
        self.is_symbol_named_in_package(sym, "COMMON-LISP", "COND")
    }

    fn is_common_lisp_or_symbol(&self, sym: SymbolId) -> bool {
        self.is_symbol_named_in_package(sym, "COMMON-LISP", "OR")
    }

    fn is_symbol_named_in_package(&self, sym: SymbolId, pkg_name: &str, symbol_name: &str) -> bool {
        let symbols = self.globals.symbols.read().unwrap();
        if symbols.symbol_name(sym) != Some(symbol_name) {
            return false;
        }
        let Some(pkg_id) = symbols.symbol_package(sym) else {
            return false;
        };
        let Some(pkg) = symbols.get_package(pkg_id) else {
            return false;
        };
        pkg.name == pkg_name
    }

    fn regression_compile_tests_enabled(&self) -> bool {
        let compile_sym = {
            let symbols = self.globals.symbols.read().unwrap();
            let Some(rt_pkg) = symbols.find_package("REGRESSION-TEST") else {
                return false;
            };
            symbols
                .get_package(rt_pkg)
                .and_then(|pkg| pkg.find_symbol("*COMPILE-TESTS*"))
        };
        compile_sym
            .and_then(|sym| self.process.get_value(sym))
            .map(|node| !self.is_nil(node))
            .unwrap_or(false)
    }

    fn expand_cl_test_signals_error(
        &mut self,
        args: NodeId,
        _env: &Environment,
    ) -> Result<NodeId, ControlSignal> {
        let args_vec = self.cons_to_vec(args);
        if args_vec.len() < 2 {
            return Err(ControlSignal::Error(
                "SIGNALS-ERROR: missing FORM and ERROR-NAME".into(),
            ));
        }

        let form = args_vec[0];
        let error_name = args_vec[1];
        let mut safety = self.process.make_integer(3);
        let mut name_arg = self.process.make_nil();
        let mut name_supplied = false;
        let mut inline = self.process.make_nil();

        let mut idx = 2usize;
        while idx < args_vec.len() {
            if idx + 1 >= args_vec.len() {
                return Err(ControlSignal::Error(
                    "SIGNALS-ERROR: missing value for keyword argument".into(),
                ));
            }

            let key_node = args_vec[idx];
            let value_node = args_vec[idx + 1];
            let key_sym = self.node_to_symbol(key_node).ok_or_else(|| {
                ControlSignal::Error("SIGNALS-ERROR: expected keyword argument".into())
            })?;
            if !self.is_keyword_symbol(key_sym) {
                return Err(ControlSignal::Error(
                    "SIGNALS-ERROR: expected keyword argument".into(),
                ));
            }

            let key_name = {
                let symbols = self.globals.symbols.read().unwrap();
                symbols.symbol_name(key_sym).unwrap_or("").to_string()
            };
            match key_name.as_str() {
                "SAFETY" => safety = value_node,
                "NAME" => {
                    name_arg = value_node;
                    name_supplied = true;
                }
                "INLINE" => inline = value_node,
                _ => {
                    return Err(ControlSignal::Error(format!(
                        "SIGNALS-ERROR: unknown keyword :{}",
                        key_name
                    )));
                }
            }
            idx += 2;
        }

        let (
            handler_bind_sym,
            warning_sym,
            function_sym,
            lambda_sym,
            declare_sym,
            ignore_sym,
            muffle_warning_sym,
            proclaim_sym,
            optimize_sym,
            safety_sym,
            handler_case_sym,
            apply_sym,
            values_sym,
            multiple_value_list_sym,
            funcall_sym,
            compile_sym,
            eval_sym,
            cond_sym,
            typep_sym,
            type_error_datum_sym,
            type_error_expected_type_sym,
            list_sym,
            eq_sym,
            cell_error_name_sym,
            not_sym,
            streamp_sym,
            stream_error_stream_sym,
            pathnamep_sym,
            pathname_sym,
            file_error_pathname_sym,
            printable_p_sym,
            c_sym,
        ) = {
            let mut symbols = self.globals.symbols.write().unwrap();
            let cl_pkg = PackageId(1);
            let cl_test_pkg = symbols.find_package("CL-TEST").unwrap_or(PackageId(2));
            (
                symbols.intern_in("HANDLER-BIND", cl_pkg),
                symbols.intern_in("WARNING", cl_pkg),
                symbols.intern_in("FUNCTION", cl_pkg),
                symbols.intern_in("LAMBDA", cl_pkg),
                symbols.intern_in("DECLARE", cl_pkg),
                symbols.intern_in("IGNORE", cl_pkg),
                symbols.intern_in("MUFFLE-WARNING", cl_pkg),
                symbols.intern_in("PROCLAIM", cl_pkg),
                symbols.intern_in("OPTIMIZE", cl_pkg),
                symbols.intern_in("SAFETY", cl_pkg),
                symbols.intern_in("HANDLER-CASE", cl_pkg),
                symbols.intern_in("APPLY", cl_pkg),
                symbols.intern_in("VALUES", cl_pkg),
                symbols.intern_in("MULTIPLE-VALUE-LIST", cl_pkg),
                symbols.intern_in("FUNCALL", cl_pkg),
                symbols.intern_in("COMPILE", cl_pkg),
                symbols.intern_in("EVAL", cl_pkg),
                symbols.intern_in("COND", cl_pkg),
                symbols.intern_in("TYPEP", cl_pkg),
                symbols.intern_in("TYPE-ERROR-DATUM", cl_pkg),
                symbols.intern_in("TYPE-ERROR-EXPECTED-TYPE", cl_pkg),
                symbols.intern_in("LIST", cl_pkg),
                symbols.intern_in("EQ", cl_pkg),
                symbols.intern_in("CELL-ERROR-NAME", cl_pkg),
                symbols.intern_in("NOT", cl_pkg),
                symbols.intern_in("STREAMP", cl_pkg),
                symbols.intern_in("STREAM-ERROR-STREAM", cl_pkg),
                symbols.intern_in("PATHNAMEP", cl_pkg),
                symbols.intern_in("PATHNAME", cl_pkg),
                symbols.intern_in("FILE-ERROR-PATHNAME", cl_pkg),
                symbols.intern_in("PRINTABLE-P", cl_test_pkg),
                symbols.intern_in("C", cl_test_pkg),
            )
        };

        let handler_bind_node = self.sym_node(handler_bind_sym);
        let warning_node = self.sym_node(warning_sym);
        let function_node = self.sym_node(function_sym);
        let lambda_node = self.sym_node(lambda_sym);
        let declare_node = self.sym_node(declare_sym);
        let ignore_node = self.sym_node(ignore_sym);
        let muffle_warning_node = self.sym_node(muffle_warning_sym);
        let proclaim_node = self.sym_node(proclaim_sym);
        let optimize_node = self.sym_node(optimize_sym);
        let safety_node = self.sym_node(safety_sym);
        let handler_case_node = self.sym_node(handler_case_sym);
        let apply_node = self.sym_node(apply_sym);
        let values_node = self.sym_node(values_sym);
        let multiple_value_list_node = self.sym_node(multiple_value_list_sym);
        let funcall_node = self.sym_node(funcall_sym);
        let compile_node = self.sym_node(compile_sym);
        let eval_node = self.sym_node(eval_sym);
        let cond_node = self.sym_node(cond_sym);
        let typep_node = self.sym_node(typep_sym);
        let type_error_datum_node = self.sym_node(type_error_datum_sym);
        let type_error_expected_type_node = self.sym_node(type_error_expected_type_sym);
        let list_node = self.sym_node(list_sym);
        let eq_node = self.sym_node(eq_sym);
        let cell_error_name_node = self.sym_node(cell_error_name_sym);
        let not_node = self.sym_node(not_sym);
        let streamp_node = self.sym_node(streamp_sym);
        let stream_error_stream_node = self.sym_node(stream_error_stream_sym);
        let pathnamep_node = self.sym_node(pathnamep_sym);
        let pathname_node = self.sym_node(pathname_sym);
        let file_error_pathname_node = self.sym_node(file_error_pathname_sym);
        let printable_p_node = self.sym_node(printable_p_sym);
        let c_node = self.sym_node(c_sym);
        let quote_node = self.sym_node(self.globals.special_forms.quote);
        let nil_node = self.process.make_nil();
        let t_node = self.process.make_t(self.globals);

        let ignore_form = self.make_call_form(ignore_node, &[c_node]);
        let declare_ignore_form = self.make_call_form(declare_node, &[ignore_form]);
        let muffle_warning_form = self.make_call_form(muffle_warning_node, &[]);
        let lambda_params = self.process.make_list(&[c_node]);
        let warning_lambda = self.make_call_form(
            lambda_node,
            &[lambda_params, declare_ignore_form, muffle_warning_form],
        );
        let warning_handler = self.make_call_form(function_node, &[warning_lambda]);
        let warning_binding = self.process.make_list(&[warning_node, warning_handler]);
        let handler_bindings = self.process.make_list(&[warning_binding]);

        let safety_three_node = self.process.make_integer(3);
        let safety_three_form = self.process.make_list(&[safety_node, safety_three_node]);
        let optimize_3_form = self.process.make_list(&[optimize_node, safety_three_form]);
        let quoted_optimize_3 = self.make_quote_form(optimize_3_form);
        let proclaim_form = self.make_call_form(proclaim_node, &[quoted_optimize_3]);

        let protected_eval_target = if !self.is_nil(inline) {
            form
        } else if self.regression_compile_tests_enabled() {
            let optimize_compile_tail = self.process.make_list(&[safety_node, safety]);
            let optimize_compile_form = self.process.make_list(&[optimize_node, optimize_compile_tail]);
            let declare_compile_form = self.make_call_form(declare_node, &[optimize_compile_form]);
            let lambda_form =
                self.make_call_form(lambda_node, &[self.process.make_nil(), declare_compile_form, form]);
            let quoted_lambda = self.make_quote_form(lambda_form);
            let compile_call = self.make_call_form(compile_node, &[self.process.make_nil(), quoted_lambda]);
            self.make_call_form(funcall_node, &[compile_call])
        } else {
            let quoted_form = self.make_quote_form(form);
            self.make_call_form(eval_node, &[quoted_form])
        };

        let function_values = self.make_call_form(function_node, &[values_node]);
        let mv_list_form = self.make_call_form(multiple_value_list_node, &[protected_eval_target]);
        let apply_values_form = self.make_call_form(apply_node, &[function_values, nil_node, mv_list_form]);

        let error_name_key = self.node_to_symbol(error_name).and_then(|sym| {
            self.globals
                .symbols
                .read()
                .unwrap()
                .symbol_name(sym)
                .map(str::to_string)
        });

        let mut cond_clauses = Vec::new();
        match error_name_key.as_deref() {
            Some("TYPE-ERROR") => {
                let datum_form = self.make_call_form(type_error_datum_node, &[c_node]);
                let expected_form = self.make_call_form(type_error_expected_type_node, &[c_node]);
                let typep_test = self.make_call_form(typep_node, &[datum_form, expected_form]);

                let quoted_typep = self.make_quote_form(typep_node);
                let quoted_quote = self.make_quote_form(quote_node);
                let quoted_datum = self.make_call_form(list_node, &[quoted_quote, datum_form]);
                let quoted_expected = self.make_call_form(list_node, &[quoted_quote, expected_form]);
                let typep_form =
                    self.make_call_form(list_node, &[quoted_typep, quoted_datum, quoted_expected]);
                let arrow_true = self.make_string_form("==> true");
                let details = self.make_call_form(list_node, &[typep_form, arrow_true]);
                let values_form = self.make_call_form(values_node, &[nil_node, details]);
                cond_clauses.push(self.process.make_list(&[typep_test, values_form]));
            }
            Some("UNDEFINED-FUNCTION") | Some("UNBOUND-VARIABLE") if name_supplied => {
                let cell_name_form = self.make_call_form(cell_error_name_node, &[c_node]);
                let expected_name = self.make_quote_form(name_arg);
                let eq_form = self.make_call_form(eq_node, &[cell_name_form, expected_name]);
                let mismatch_test = self.make_call_form(not_node, &[eq_form]);
                let quoted_cell_name = self.make_quote_form(cell_error_name_node);
                let arrow = self.make_string_form("==>");
                let details = self.make_call_form(list_node, &[quoted_cell_name, arrow, cell_name_form]);
                let values_form = self.make_call_form(values_node, &[nil_node, details]);
                cond_clauses.push(self.process.make_list(&[mismatch_test, values_form]));
            }
            Some("STREAM-ERROR") | Some("END-OF-FILE") | Some("READER-ERROR") => {
                let stream_form = self.make_call_form(stream_error_stream_node, &[c_node]);
                let stream_ok = self.make_call_form(streamp_node, &[stream_form]);
                let mismatch_test = self.make_call_form(not_node, &[stream_ok]);
                let quoted_stream = self.make_quote_form(stream_error_stream_node);
                let arrow = self.make_string_form("==>");
                let details = self.make_call_form(list_node, &[quoted_stream, arrow, stream_form]);
                let values_form = self.make_call_form(values_node, &[nil_node, details]);
                cond_clauses.push(self.process.make_list(&[mismatch_test, values_form]));
            }
            Some("FILE-ERROR") => {
                let file_path_form = self.make_call_form(file_error_pathname_node, &[c_node]);
                let pathname_form = self.make_call_form(pathname_node, &[file_path_form]);
                let pathname_ok = self.make_call_form(pathnamep_node, &[pathname_form]);
                let mismatch_test = self.make_call_form(not_node, &[pathname_ok]);
                let quoted_file_path = self.make_quote_form(file_error_pathname_node);
                let arrow = self.make_string_form("==>");
                let details = self.make_call_form(list_node, &[quoted_file_path, arrow, file_path_form]);
                let values_form = self.make_call_form(values_node, &[nil_node, details]);
                cond_clauses.push(self.process.make_list(&[mismatch_test, values_form]));
            }
            _ => {}
        }

        let printable_form = self.make_call_form(printable_p_node, &[c_node]);
        cond_clauses.push(self.process.make_list(&[t_node, printable_form]));
        let cond_form = self.make_call_form(cond_node, &cond_clauses);

        let handler_bind_vars = self.process.make_list(&[c_node]);
        let handler_clause = self.process.make_list(&[error_name, handler_bind_vars, cond_form]);
        let handler_case_form = self.make_call_form(handler_case_node, &[apply_values_form, handler_clause]);

        Ok(self.make_call_form(handler_bind_node, &[handler_bindings, proclaim_form, handler_case_form]))
    }

    fn expand_regression_deftest(&mut self, args: NodeId) -> Result<NodeId, ControlSignal> {
        let args_vec = self.cons_to_vec(args);
        if args_vec.is_empty() {
            return Err(ControlSignal::Error("DEFTEST: missing name".into()));
        }

        let name_form = args_vec[0];
        let body = &args_vec[1..];
        let mut idx = 0usize;
        let mut properties_flat = Vec::new();

        while idx < body.len() {
            let is_kw = self
                .node_to_symbol(body[idx])
                .map(|sym| self.is_keyword_symbol(sym))
                .unwrap_or(false);
            if !is_kw {
                break;
            }
            if idx + 1 >= body.len() {
                return Err(ControlSignal::Error(
                    "Poorly formed deftest: missing value for keyword property".into(),
                ));
            }
            properties_flat.push(body[idx]);
            properties_flat.push(body[idx + 1]);
            idx += 2;
        }

        if idx >= body.len() {
            return Err(ControlSignal::Error(
                "Poorly formed deftest: missing test form".into(),
            ));
        }

        let form = body[idx];
        idx += 1;
        let vals = &body[idx..];

        let properties_list = self.process.make_list(&properties_flat);
        let vals_list = self.process.make_list(vals);

        let (
            add_entry_sym,
            make_entry_sym,
            kw_pend_sym,
            kw_name_sym,
            kw_props_sym,
            kw_form_sym,
            kw_vals_sym,
        ) = {
            let mut symbols = self.globals.symbols.write().unwrap();
            let rt_pkg = symbols
                .find_package("REGRESSION-TEST")
                .ok_or_else(|| ControlSignal::Error("DEFTEST: REGRESSION-TEST package missing".into()))?;
            (
                symbols.intern_in("ADD-ENTRY", rt_pkg),
                symbols.intern_in("MAKE-ENTRY", rt_pkg),
                symbols.intern_keyword("PEND"),
                symbols.intern_keyword("NAME"),
                symbols.intern_keyword("PROPS"),
                symbols.intern_keyword("FORM"),
                symbols.intern_keyword("VALS"),
            )
        };

        let add_entry_node = self
            .process
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(add_entry_sym.0)));
        let make_entry_node = self
            .process
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(make_entry_sym.0)));
        let kw_pend_node = self
            .process
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(kw_pend_sym.0)));
        let kw_name_node = self
            .process
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(kw_name_sym.0)));
        let kw_props_node = self
            .process
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(kw_props_sym.0)));
        let kw_form_node = self
            .process
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(kw_form_sym.0)));
        let kw_vals_node = self
            .process
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(kw_vals_sym.0)));

        let quoted_name = self.make_quote_form(name_form);
        let quoted_props = self.make_quote_form(properties_list);
        let quoted_form = self.make_quote_form(form);
        let quoted_vals = self.make_quote_form(vals_list);

        let make_entry_args = [
            kw_pend_node,
            self.process.make_t(self.globals),
            kw_name_node,
            quoted_name,
            kw_props_node,
            quoted_props,
            kw_form_node,
            quoted_form,
            kw_vals_node,
            quoted_vals,
        ];
        let make_entry_args_list = self.process.make_list(&make_entry_args);
        let make_entry_call = self
            .process
            .arena
            .inner
            .alloc(Node::Fork(make_entry_node, make_entry_args_list));
        let add_entry_args = [make_entry_call];
        let add_entry_args_list = self.process.make_list(&add_entry_args);
        Ok(self
            .process
            .arena
            .inner
            .alloc(Node::Fork(add_entry_node, add_entry_args_list)))
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

    /// (let* ((var val) ...) body*) -> sequential local bindings
    fn eval_let_star(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        if let Node::Fork(bindings, body) = self.process.arena.get_unchecked(args).clone() {
            let new_env = Environment::with_parent(env.clone());
            let mut special_bindings: Vec<(SymbolId, Option<NodeId>)> = Vec::new();

            let mut current = bindings;
            loop {
                match self.process.arena.get_unchecked(current).clone() {
                    Node::Fork(binding, rest) => {
                        let (var_node, val_expr) =
                            match self.process.arena.get_unchecked(binding).clone() {
                                Node::Fork(var_node, val_rest) => {
                                    let val_expr =
                                        if let Node::Fork(val_node, _) =
                                            self.process.arena.get_unchecked(val_rest).clone()
                                        {
                                            val_node
                                        } else {
                                            self.process.make_nil()
                                        };
                                    (var_node, val_expr)
                                }
                                Node::Leaf(OpaqueValue::Symbol(_)) => {
                                    (binding, self.process.make_nil())
                                }
                                _ => {
                                    current = rest;
                                    continue;
                                }
                            };

                        if let Some(sym) = self.node_to_symbol(var_node) {
                            // LET* evaluates each init in the environment that already has prior bindings.
                            let val = self.eval(val_expr, &new_env)?;
                            if self.is_special_symbol(sym) {
                                let old = self.process.get_value(sym);
                                special_bindings.push((sym, old));
                                self.process.set_value(sym, val);
                                self.maybe_update_current_package(sym, val);
                            } else {
                                new_env.bind(sym, val);
                            }
                        }
                        current = rest;
                    }
                    _ => break,
                }
            }

            let (_decls, body_start) = self.parse_body(body);
            let result = self.eval_progn(body_start, &new_env);

            for (sym, old) in special_bindings.into_iter().rev() {
                match old {
                    Some(val) => {
                        self.process.set_value(sym, val);
                        self.maybe_update_current_package(sym, val);
                    }
                    None => {
                        self.process.unbind_value(sym);
                    }
                }
            }

            result
        } else {
            Ok(self.process.make_nil())
        }
    }

    /// (cond (test form*)*) -> conditional clauses
    fn eval_cond(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        let mut current = args;
        loop {
            match self.process.arena.get_unchecked(current).clone() {
                Node::Leaf(OpaqueValue::Nil) => return Ok(self.process.make_nil()),
                Node::Fork(clause, rest_clauses) => {
                    current = rest_clauses;

                    let Node::Fork(test, body) = self.process.arena.get_unchecked(clause).clone() else {
                        continue;
                    };

                    let test_val = self.eval(test, env)?;
                    if self.is_nil(test_val) {
                        continue;
                    }

                    match self.process.arena.get_unchecked(body).clone() {
                        Node::Leaf(OpaqueValue::Nil) => {
                            // Match macro semantics `(let ((temp test)) (if temp temp ...))`,
                            // which returns only the primary value.
                            self.process.values_are_set = false;
                            self.process.values.clear();
                            return Ok(test_val);
                        }
                        _ => return self.eval_progn(body, env),
                    }
                }
                _ => return Err(ControlSignal::Error("COND: malformed clause list".into())),
            }
        }
    }

    /// (or form*) -> left-to-right short-circuit
    fn eval_or(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        let mut current = args;
        loop {
            match self.process.arena.get_unchecked(current).clone() {
                Node::Leaf(OpaqueValue::Nil) => return Ok(self.process.make_nil()),
                Node::Fork(form, rest) => {
                    let value = self.eval(form, env)?;
                    if self.is_nil(value) {
                        current = rest;
                        continue;
                    }
                    if let Node::Leaf(OpaqueValue::Nil) = self.process.arena.get_unchecked(rest) {
                        return Ok(value);
                    }
                    // Match macro semantics `(let ((g first)) (if g g ...))`:
                    // only the primary value is propagated for non-final winning forms.
                    self.process.values_are_set = false;
                    self.process.values.clear();
                    return Ok(value);
                }
                _ => return Err(ControlSignal::Error("OR: malformed argument list".into())),
            }
        }
    }

    fn eval_multiple_value_bind(&mut self, args: NodeId, env: &Environment) -> EvalResult {
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

        let _ = self.eval(values_form, env)?;
        let values = if self.process.values_are_set {
            self.process.values.clone()
        } else {
            vec![self.process.program]
        };

        let mut new_env = Environment::with_parent(env.clone());
        let mut values_iter = values.into_iter();
        let mut cur = vars_node;
        loop {
            match self.process.arena.get_unchecked(cur).clone() {
                Node::Leaf(OpaqueValue::Nil) => break,
                Node::Fork(var_node, rest) => {
                    let sym = self.node_to_symbol(var_node).ok_or_else(|| {
                        ControlSignal::Error(
                            "multiple-value-bind: expected symbol".into(),
                        )
                    })?;
                    let val = values_iter.next().unwrap_or_else(|| self.process.make_nil());
                    new_env.bind(sym, val);
                    cur = rest;
                }
                _ => {
                    return Err(ControlSignal::Error(
                        "multiple-value-bind: malformed variable list".into(),
                    ))
                }
            }
        }

        self.eval_progn(body, &new_env)
    }

    fn eval_multiple_value_call(&mut self, args: NodeId, env: &Environment) -> EvalResult {
        let args_vec = self.cons_to_vec(args);
        if args_vec.is_empty() {
            return Err(ControlSignal::Error(
                "multiple-value-call: too few args".into(),
            ));
        }
        let func_expr = args_vec[0];
        let forms = if args_vec.len() > 1 {
            args_vec[1..].to_vec()
        } else {
            Vec::new()
        };

        let func = self.eval(func_expr, env)?;

        let mut collected = Vec::new();
        for form in forms {
            let _ = self.eval(form, env)?;
            if self.process.values_are_set {
                collected.extend(self.process.values.iter().copied());
            } else {
                collected.push(self.process.program);
            }
        }

        let args_list = self.process.make_list(&collected);
        self.apply_values(func, args_list, env)
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
                                        if name == "SYMBOL-VALUE" {
                                            let res = self.node_to_symbol(*arg);
                                            return res;
                                        }
                                    }
                                }
                            }
                            None
                        });

                        if let Some(sym) = raw_sym_opt {
                            let val = self.eval(val_node, env)?;

                            let found = env.set(sym, val);
                            if !found {
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
                                self.maybe_update_current_package(sym, val);
                            }
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
            let new_env = Environment::with_parent(env.clone());
            let mut special_bindings: Vec<(SymbolId, Option<NodeId>)> = Vec::new();

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
                                    if self.is_special_symbol(sym) {
                                        let old = self.process.get_value(sym);
                                        special_bindings.push((sym, old));
                                        self.process.set_value(sym, val);
                                        self.maybe_update_current_package(sym, val);
                                    } else {
                                        new_env.bind(sym, val);
                                    }
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
            let result = self.eval_progn(body_start, &new_env);

            for (sym, old) in special_bindings {
                match old {
                    Some(val) => {
                        self.process.set_value(sym, val);
                        self.maybe_update_current_package(sym, val);
                    }
                    None => {
                        self.process.unbind_value(sym);
                    }
                }
            }

            result
        } else {
            Ok(self.process.make_nil())
        }
    }

    fn is_special_symbol(&self, sym: SymbolId) -> bool {
        if sym == self.globals.package_sym {
            return true;
        }
        if let Some(name) = self.globals.symbols.read().unwrap().symbol_name(sym) {
            if name.starts_with('*') && name.ends_with('*') && name.len() > 1 {
                return true;
            }
        }
        false
    }

    fn package_id_from_node(&self, node: NodeId) -> Option<crate::symbol::PackageId> {
        match self.process.arena.get_unchecked(node) {
            Node::Leaf(OpaqueValue::Package(id)) => Some(crate::symbol::PackageId(*id)),
            Node::Leaf(OpaqueValue::Symbol(id)) => self
                .globals
                .symbols
                .read()
                .unwrap()
                .symbol_name(SymbolId(*id))
                .and_then(|name| self.globals.symbols.read().unwrap().find_package(name)),
            Node::Leaf(OpaqueValue::String(s)) => {
                self.globals.symbols.read().unwrap().find_package(s)
            }
            Node::Leaf(OpaqueValue::Char(c)) => self
                .globals
                .symbols
                .read()
                .unwrap()
                .find_package(&c.to_string()),
            _ => None,
        }
    }

    fn maybe_update_current_package(&mut self, sym: SymbolId, val: NodeId) {
        let is_package_sym = sym == self.globals.package_sym;
        let is_named_package = !is_package_sym
            && self
                .globals
                .symbols
                .read()
                .unwrap()
                .symbol_name(sym)
                .map(|name| name == "*PACKAGE*")
                .unwrap_or(false);

        if !is_package_sym && !is_named_package {
            return;
        }

        if let Some(pkg_id) = self.package_id_from_node(val) {
            self.globals
                .symbols
                .write()
                .unwrap()
                .set_current_package(pkg_id);

            if !is_package_sym {
                let pkg_node = self
                    .process
                    .arena
                    .inner
                    .alloc(Node::Leaf(OpaqueValue::Package(pkg_id.0)));
                self.process.set_value(self.globals.package_sym, pkg_node);
            }
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

            // Wrap body in PROGN so multiple forms evaluate correctly.
            let progn_sym = self.globals.special_forms.progn;
            let progn_sym_node = self
                .process
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(progn_sym.0)));
            let (_decls, body_start) = self.parse_body(body);
            let body_node = self
                .process
                .arena
                .inner
                .alloc(Node::Fork(progn_sym_node, body_start));

            // Create closure
            let closure = Closure {
                lambda_list: parsed_lambda_list,
                destructuring: None,
                body: body_node,
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
                    }
                }
            }

            // It's a symbol - get its function binding
            if let Some(sym) = self.node_to_symbol(name) {
                if let Some(func) = self.process.get_function(sym) {
                    return Ok(func);
                }
            } else if let Node::Fork(car, rest) = self.process.arena.get_unchecked(name).clone() {
                if let Some(sym) = self.node_to_symbol(car) {
                    if sym == self.process.mop.setf_symbol {
                        if let Node::Fork(target, _) =
                            self.process.arena.get_unchecked(rest).clone()
                        {
                            if let Some(base_sym) = self.node_to_symbol(target) {
                                if let Some(func) = self.process.get_setf_function(base_sym) {
                                    return Ok(func);
                                }
                                if let Some(gid) =
                                    self.process.mop.find_setf_generic(base_sym)
                                {
                                    return Ok(self.process.arena.inner.alloc(Node::Leaf(
                                        OpaqueValue::Generic(gid.0),
                                    )));
                                }
                            }
                        }
                    }
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
                    destructuring: None,
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
        let mut tags: HashMap<SymbolId, usize> = HashMap::default();
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
            Node::Leaf(OpaqueValue::Instance(idx)) => {
                let inst_idx = idx as usize;
                let class_id = self
                    .process
                    .mop
                    .get_instance(inst_idx)
                    .map(|i| i.class)
                    .unwrap_or(self.process.mop.standard_object);
                if !self.process.mop.class_is_funcallable(class_id) {
                    return Err(ControlSignal::Error(
                        "Attempt to call non-funcallable instance".into(),
                    ));
                }
                let func = self.process.mop.get_instance_function(inst_idx).ok_or_else(|| {
                    ControlSignal::Error(
                        "Funcallable instance has no function".into(),
                    )
                })?;

                // Evaluate arguments
                let mut evaluated_args = Vec::new();
                let mut current = args;
                while let Node::Fork(arg, rest) =
                    self.process.arena.inner.get_unchecked(current).clone()
                {
                    let val = self.eval(arg, env)?;
                    evaluated_args.push(val);
                    current = rest;
                }

                self.step_apply(func, evaluated_args, env.clone())?;
                loop {
                    match self.step() {
                        Ok(true) => continue,
                        Ok(false) => return Ok(self.process.program),
                        Err(e) => return Err(e),
                    }
                }
            }
            Node::Leaf(OpaqueValue::NextMethod(state_idx)) => {
                let state_idx = state_idx as usize;
                if state_idx >= self.process.next_method_states.len() {
                    return Err(ControlSignal::Error("Invalid NextMethod state".into()));
                }

                let current_state = self.process.next_method_states[state_idx].clone();
                if current_state.methods.is_empty() {
                    return Err(ControlSignal::Error("No next method".into()));
                }

                let next_method_id = current_state.methods[0];
                let remaining = current_state.methods[1..].to_vec();

                let raw_args = self.cons_to_vec(args);
                let next_args = if raw_args.is_empty() {
                    current_state.args.clone()
                } else {
                    let mut evaluated_args = Vec::with_capacity(raw_args.len());
                    for arg in raw_args {
                        evaluated_args.push(self.eval(arg, env)?);
                    }
                    evaluated_args
                };

                let next_state = crate::clos::NextMethodState {
                    methods: remaining,
                    args: next_args.clone(),
                };

                self.process.next_method_states.push(next_state);
                let next_state_idx = (self.process.next_method_states.len() - 1) as u32;

                let method = self.process.mop.get_method(next_method_id).unwrap();
                let body = method.body;

                if let Node::Leaf(OpaqueValue::Closure(idx)) =
                    self.process.arena.get_unchecked(body)
                {
                    let wrapper = OpaqueValue::MethodWrapper(*idx, next_state_idx);
                    let wrapper_node = self.process.arena.inner.alloc(Node::Leaf(wrapper));
                    self.step_apply(wrapper_node, next_args, env.clone())?;

                    loop {
                        match self.step() {
                            Ok(true) => continue,
                            Ok(false) => return Ok(self.process.program),
                            Err(e) => return Err(e),
                        }
                    }
                } else {
                    Err(ControlSignal::Error(
                        "Next method body is not closure".into(),
                    ))
                }
            }
            Node::Leaf(OpaqueValue::NextMethodP(state_idx)) => {
                let state_idx = state_idx as usize;
                if state_idx >= self.process.next_method_states.len() {
                    return Err(ControlSignal::Error("Invalid NextMethod state".into()));
                }
                let has_next = !self.process.next_method_states[state_idx].methods.is_empty();
                Ok(if has_next {
                    self.process.make_t(&self.globals)
                } else {
                    self.process.make_nil()
                })
            }
            Node::Leaf(OpaqueValue::CallMethod(state_idx)) => {
                let state_idx = state_idx as usize;
                if state_idx >= self.process.next_method_states.len() {
                    return Err(ControlSignal::Error("Invalid CallMethod state".into()));
                }

                let raw_args = self.cons_to_vec(args);
                if raw_args.is_empty() {
                    return Err(ControlSignal::Error(
                        "CALL-METHOD requires a method".into(),
                    ));
                }

                let method_node = self.eval(raw_args[0], env)?;
                let next_methods_node = if raw_args.len() > 1 {
                    self.eval(raw_args[1], env)?
                } else {
                    self.process.make_nil()
                };

                let method_id = self.method_id_from_node(method_node)?;
                let next_methods = self.collect_method_ids(next_methods_node)?;

                let call_args = self.process.next_method_states[state_idx].args.clone();
                self.call_method_with_next_methods(method_id, next_methods, call_args, env.clone())?;

                loop {
                    match self.step() {
                        Ok(true) => continue,
                        Ok(false) => return Ok(self.process.program),
                        Err(e) => return Err(e),
                    }
                }
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

        // If FUNC is a symbol designator, prefer direct primitive/definition dispatch
        if let Some(sym) = self.node_to_symbol(func) {
            if let Some(&prim_fn) = self.globals.primitives.get(&sym) {
                let mut arg_vec = Vec::new();
                let mut curr = args;
                while let Node::Fork(h, t) = self.process.arena.inner.get_unchecked(curr).clone() {
                    arg_vec.push(h);
                    curr = t;
                }
                return prim_fn(self.process, self.globals, &arg_vec);
            }
            if let Some(func_node) = self.process.get_function(sym) {
                // Re-dispatch on resolved function node (closure/generic)
                return self.apply_values(func_node, args, env);
            }
        }

        match func_node {
            Node::Leaf(OpaqueValue::Closure(_)) | Node::Leaf(OpaqueValue::Generic(_)) => {
                let mut arg_vec = Vec::new();
                let mut curr = args;
                while let Node::Fork(h, t) = self.process.arena.inner.get_unchecked(curr).clone() {
                    arg_vec.push(h);
                    curr = t;
                }
                self.step_apply(func, arg_vec, env.clone())?;

                // Drive the evaluator until the continuation stack completes.
                loop {
                    match self.step() {
                        Ok(true) => continue,
                        Ok(false) => return Ok(self.process.program),
                        Err(e) => return Err(e),
                    }
                }
            }
            Node::Leaf(OpaqueValue::Instance(idx)) => {
                let inst_idx = idx as usize;
                let class_id = self
                    .process
                    .mop
                    .get_instance(inst_idx)
                    .map(|i| i.class)
                    .unwrap_or(self.process.mop.standard_object);
                if !self.process.mop.class_is_funcallable(class_id) {
                    return Err(ControlSignal::Error(
                        "Attempt to call non-funcallable instance".into(),
                    ));
                }
                let func = self.process.mop.get_instance_function(inst_idx).ok_or_else(|| {
                    ControlSignal::Error("Funcallable instance has no function".into())
                })?;

                let mut arg_vec = Vec::new();
                let mut curr = args;
                while let Node::Fork(h, t) = self.process.arena.inner.get_unchecked(curr).clone() {
                    arg_vec.push(h);
                    curr = t;
                }
                self.step_apply(func, arg_vec, env.clone())?;

                loop {
                    match self.step() {
                        Ok(true) => continue,
                        Ok(false) => return Ok(self.process.program),
                        Err(e) => return Err(e),
                    }
                }
            }
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
                        || sym == sf.multiple_value_bind
                        || sym == sf.multiple_value_call
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
                        self.process.status = crate::process::Status::Failed(msg);
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
        // 1. Required
        for &param in &closure.lambda_list.req {
            if let Node::Fork(arg_expr, rest) =
                self.process.arena.inner.get_unchecked(current_arg).clone()
            {
                let val = self.eval(arg_expr, env)?;
                self.bind_pattern(&mut new_env, param, val, true)?;
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
                self.bind_pattern(&mut new_env, *var, val, true)?;
                if let Some(s) = sup {
                    let t_val = self.process.make_t(&self.globals);
                    new_env.bind(*s, t_val);
                }
                current_arg = rest;
            } else {
                let val = self.eval(init.clone(), &new_env)?;
                self.bind_pattern(&mut new_env, *var, val, true)?;
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
                    self.bind_pattern(&mut new_env, *var, val, true)?;
                    if let Some(s) = sup {
                        let t_val = self.process.make_t(&self.globals);
                        new_env.bind(*s, t_val);
                    }
                } else {
                    let val = self.eval(*init, &new_env)?;
                    self.bind_pattern(&mut new_env, *var, val, true)?;
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

        // Evaluate body. Functions are stored as a single expression, usually a PROGN list.
        let body = closure.body;
        if let Node::Fork(head, tail) = self.process.arena.inner.get_unchecked(body).clone() {
            if let Some(sym) = self.node_to_symbol(head) {
                if sym == self.globals.special_forms.progn {
                    return self.eval_progn(tail, &new_env);
                }
            }
        }
        self.eval_progn(body, &new_env)
    }

    /// Apply a macro closure to arguments (no eval of args)
    pub fn _apply_macro(&mut self, closure: &Closure, args: NodeId) -> EvalResult {
        // Create environment from closure's captured environment
        let mut new_env = crate::eval::Environment::with_parent(closure.env.clone());

        // Bind arguments UNEVALUATED using destructuring lambda list when available.
        if let Some(destructuring) = &closure.destructuring {
            self.bind_destructuring_lambda_list(destructuring, args, &mut new_env)?;
        } else {
            let mut current_arg = args;

            // 1. Required
            for &param in &closure.lambda_list.req {
                match self.process.arena.inner.get_unchecked(current_arg).clone() {
                    Node::Fork(arg_expr, rest) => {
                        self.bind_pattern(&mut new_env, param, arg_expr, true)?;
                        current_arg = rest;
                    }
                    _ => {
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
                new_env.bind(rest_sym, current_arg);
            }
        }

        // Evaluate body - this produces the expansion
        let expansion = self.eval_progn(closure.body, &new_env)?;
        Ok(expansion)
    }

    /// Apply a generic function
    /// Apply a generic function
    fn apply_generic(&mut self, gf_id: u32, args: NodeId, env: &Environment) -> EvalResult {
        // 1. Evaluate arguments (Generic Function application expects evaluated args)
        let mut evaluated_args = Vec::new();
        let mut current = args;
        while let Node::Fork(arg, rest) = self.process.arena.inner.get_unchecked(current).clone() {
            let val = self.eval(arg, env)?;
            evaluated_args.push(val);
            current = rest;
        }

        // 2. Delegate to apply_generic_function (TCO logic)
        use crate::clos::GenericId;
        self.apply_generic_function(GenericId(gf_id), evaluated_args, env)?;

        // 3. Adapter: Run the interpreter loop until return (Simulate synchronous execution)
        loop {
            match self.step() {
                Ok(true) => continue,
                Ok(false) => return Ok(self.process.program),
                Err(e) => return Err(e),
            }
        }
    }

    /// Get class of value
    #[allow(dead_code)]
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
            Node::Leaf(OpaqueValue::EqlSpecializer(_)) => self.process.mop.eql_specializer_class,
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
                    let destructuring = match self.parse_destructuring_lambda_list(params) {
                        Ok(d) => d,
                        Err(e) => return Err(ControlSignal::Error(e)),
                    };

                    // Create closure
                    let closure = Closure {
                        lambda_list: parsed_lambda_list,
                        destructuring: Some(destructuring),
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
        // Delegate to ENSURE-CLASS primitive to keep CLOS/MOP behavior consistent.
        if let Node::Fork(name_node, rest) = self.process.arena.inner.get_unchecked(args).clone() {
            if let Node::Fork(supers_node, rest2) =
                self.process.arena.inner.get_unchecked(rest).clone()
            {
                if let Node::Fork(slots_node, _rest3) =
                    self.process.arena.inner.get_unchecked(rest2).clone()
                {
                    let kw_supers = self.ensure_keyword_symbol("DIRECT-SUPERCLASSES");
                    let kw_slots = self.ensure_keyword_symbol("DIRECT-SLOTS");
                    let kw_supers_node = self
                        .process
                        .arena
                        .inner
                        .alloc(Node::Leaf(OpaqueValue::Symbol(kw_supers.0)));
                    let kw_slots_node = self
                        .process
                        .arena
                        .inner
                        .alloc(Node::Leaf(OpaqueValue::Symbol(kw_slots.0)));

                    let args_vec = vec![
                        name_node,
                        kw_supers_node,
                        supers_node,
                        kw_slots_node,
                        slots_node,
                    ];

                    return crate::primitives::prim_ensure_class(
                        self.process,
                        self.globals,
                        &args_vec,
                    );
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
                            specializers.push(crate::clos::Specializer::Class(
                                self.process.mop.t_class,
                            ));
                        } else if let Node::Fork(pname, ptype_rest) =
                            self.process.arena.inner.get_unchecked(param_spec).clone()
                        {
                            if let Some(psym) = self.node_to_symbol(pname) {
                                params.push(psym);
                                params_nodes.push(pname);
                                // Get specializer (class or (eql ...))
                                let spec = if let Node::Fork(spec_node, _) =
                                    self.process.arena.inner.get_unchecked(ptype_rest).clone()
                                {
                                    self.parse_specializer(spec_node)
                                } else {
                                    crate::clos::Specializer::Class(self.process.mop.t_class)
                                };
                                specializers.push(spec);
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
                        destructuring: None,
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
                        .add_method(gf_id, specializers, Vec::new(), params.clone(), closure_node);

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
                        self.maybe_update_current_package(name_sym, val);
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
                    self.maybe_update_current_package(name_sym, val);
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

    #[allow(dead_code)]
    fn step_multiple_value_bind_dup(
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
    use crate::reader::Reader;
    use crate::reader::ReaderError;
    use crate::tree_calculus;

    fn setup_env() -> (Process, GlobalContext) {
        let mut globals = GlobalContext::new();
        crate::primitives::register_primitives(&mut globals);
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

    fn load_init_lisp(proc: &mut Process, globals: &GlobalContext) {
        let init_src = include_str!("init_new.lisp");
        globals
            .symbols
            .write()
            .unwrap()
            .set_current_package(PackageId(1));

        let mut exprs = Vec::new();
        {
            let readtable = proc.current_readtable().clone();
            let mut symbols_guard = globals.symbols.write().unwrap();
            let mut reader = Reader::new(
                init_src,
                &mut proc.arena.inner,
                &mut *symbols_guard,
                &readtable,
                Some(&mut proc.arrays),
            );
            loop {
                match reader.read() {
                    Ok(expr) => exprs.push(expr),
                    Err(ReaderError::UnexpectedEof) => break,
                    Err(e) => panic!("init_new.lisp read error: {:?}", e),
                }
            }
        }

        let mut interpreter = Interpreter::new(proc, globals);
        let env = Environment::new();
        for expr in exprs {
            interpreter.eval(expr, &env).unwrap();
        }

        globals
            .symbols
            .write()
            .unwrap()
            .set_current_package(PackageId(2));
        let pkg_node = interpreter
            .process
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Package(2)));
        interpreter
            .process
            .set_value(globals.package_sym, pkg_node);
    }

    fn list_to_ints(proc: &Process, list: NodeId) -> Vec<i64> {
        let mut out = Vec::new();
        let mut cur = list;
        loop {
            match proc.arena.inner.get_unchecked(cur) {
                Node::Fork(car, cdr) => {
                    match proc.arena.inner.get_unchecked(*car) {
                        Node::Leaf(OpaqueValue::Integer(n)) => out.push(*n),
                        other => panic!("Expected integer list item, got {:?}", other),
                    }
                    cur = *cdr;
                }
                Node::Leaf(OpaqueValue::Nil) => break,
                other => panic!("Expected list, got {:?}", other),
            }
        }
        out
    }

    #[test]
    fn test_setq_protected_symbol() {
        let (mut proc, globals) = setup_env();

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
        let (mut proc, globals) = setup_env();
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
    fn test_special_package_symbol_updates_current_package() {
        let (mut proc, globals) = setup_env();

        let reg_pkg = globals
            .symbols
            .write()
            .unwrap()
            .make_package("REGRESSION-TEST", Vec::new(), vec![PackageId(1)], None)
            .expect("failed to make REGRESSION-TEST package");

        let reg_pkg_sym = globals
            .symbols
            .write()
            .unwrap()
            .create_symbol_in_package("*PACKAGE*", reg_pkg);

        let pkg_node = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Package(reg_pkg.0)));

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        interpreter.maybe_update_current_package(reg_pkg_sym, pkg_node);

        let current_pkg = globals.symbols.read().unwrap().current_package();
        assert_eq!(current_pkg, reg_pkg);

        let cl_pkg_val = proc.get_value(globals.package_sym).expect("missing *PACKAGE*");
        match proc.arena.inner.get_unchecked(cl_pkg_val) {
            Node::Leaf(OpaqueValue::Package(id)) => assert_eq!(*id, reg_pkg.0),
            other => panic!("Expected package node, got {:?}", other),
        }
    }

    #[test]
    fn test_let_special_binding_updates_dynamic_value() {
        let (mut proc, globals) = setup_env();

        let expr = read_from_string(
            "(progn (setq *foo* 1) (let ((*foo* 2)) (symbol-value '*foo*)))",
            &mut proc.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();

        let expr2 = read_from_string(
            "(symbol-value '*foo*)",
            &mut proc.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let env = Environment::new();
        let result = interpreter.eval(expr, &env).unwrap();
        match interpreter.process.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(2)) => {}
            other => panic!("Expected 2 from special binding, got {:?}", other),
        }

        let result2 = interpreter.eval(expr2, &env).unwrap();
        match interpreter.process.arena.inner.get_unchecked(result2) {
            Node::Leaf(OpaqueValue::Integer(1)) => {}
            other => panic!("Expected 1 after binding restore, got {:?}", other),
        }
    }

    #[test]
    fn test_loop_macro_subset() {
        let (mut proc, globals) = setup_env();
        load_init_lisp(&mut proc, &globals);

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let env = Environment::new();

        let expr = read_from_string(
            "(loop for i from 0 below 3 collect i)",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let result = interpreter.eval(expr, &env).unwrap();
        assert_eq!(list_to_ints(&interpreter.process, result), vec![0, 1, 2]);

        let expr2 = read_from_string(
            "(loop for x in '(1 2 1) count (= x 1))",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let result2 = interpreter.eval(expr2, &env).unwrap();
        match interpreter.process.arena.inner.get_unchecked(result2) {
            Node::Leaf(OpaqueValue::Integer(n)) => assert_eq!(*n, 2),
            other => panic!("Expected count integer, got {:?}", other),
        }

        let expr3 = read_from_string(
            "(loop repeat 3 collect 7)",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let result3 = interpreter.eval(expr3, &env).unwrap();
        assert_eq!(list_to_ints(&interpreter.process, result3), vec![7, 7, 7]);

        let expr4 = read_from_string(
            "(loop for x in '(nil nil 5) thereis x)",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let result4 = interpreter.eval(expr4, &env).unwrap();
        match interpreter.process.arena.inner.get_unchecked(result4) {
            Node::Leaf(OpaqueValue::Integer(n)) => assert_eq!(*n, 5),
            other => panic!("Expected thereis result 5, got {:?}", other),
        }
    }

    #[test]
    fn test_defstruct_copier() {
        let (mut proc, globals) = setup_env();
        load_init_lisp(&mut proc, &globals);

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let env = Environment::new();

        let expr = read_from_string(
            "(progn (defstruct foo a b) (let* ((x (make-foo :a 1 :b 2)) (y (copy-foo x))) (list (foo-a y) (foo-b y))))",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let result = interpreter.eval(expr, &env).unwrap();
        assert_eq!(list_to_ints(&interpreter.process, result), vec![1, 2]);
    }

    #[test]
    fn test_expand_signals_error_eval_branch() {
        let (mut proc, globals) = setup_env();

        let rt_pkg = globals
            .symbols
            .write()
            .unwrap()
            .make_package("REGRESSION-TEST", Vec::new(), vec![PackageId(1)], None)
            .expect("failed to create REGRESSION-TEST package");
        let _cl_test_pkg = globals
            .symbols
            .write()
            .unwrap()
            .make_package("CL-TEST", Vec::new(), vec![PackageId(1)], None)
            .expect("failed to create CL-TEST package");
        let compile_tests_sym = globals
            .symbols
            .write()
            .unwrap()
            .intern_in("*COMPILE-TESTS*", rt_pkg);
        proc.set_value(compile_tests_sym, proc.make_nil());

        let call = read_from_string(
            "(signals-error (+ 1 2) type-error)",
            &mut proc.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let args = match proc.arena.inner.get_unchecked(call) {
            Node::Fork(_, tail) => *tail,
            other => panic!("Expected call form, got {:?}", other),
        };

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let expanded = interpreter
            .expand_cl_test_signals_error(args, &Environment::new())
            .expect("signals-error expansion failed");
        let printed = {
            let syms = globals.symbols.read().unwrap();
            crate::printer::print_to_string(&interpreter.process.arena.inner, &syms, expanded)
        };
        assert!(printed.contains("HANDLER-BIND"));
        assert!(printed.contains("EVAL"));
        assert!(!printed.contains("COMPILE"));
    }

    #[test]
    fn test_expand_signals_error_compile_branch() {
        let (mut proc, globals) = setup_env();

        let rt_pkg = globals
            .symbols
            .write()
            .unwrap()
            .make_package("REGRESSION-TEST", Vec::new(), vec![PackageId(1)], None)
            .expect("failed to create REGRESSION-TEST package");
        let _cl_test_pkg = globals
            .symbols
            .write()
            .unwrap()
            .make_package("CL-TEST", Vec::new(), vec![PackageId(1)], None)
            .expect("failed to create CL-TEST package");
        let compile_tests_sym = globals
            .symbols
            .write()
            .unwrap()
            .intern_in("*COMPILE-TESTS*", rt_pkg);
        proc.set_value(compile_tests_sym, proc.make_t(&globals));

        let call = read_from_string(
            "(signals-error (+ 1 2) type-error :safety 0)",
            &mut proc.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let args = match proc.arena.inner.get_unchecked(call) {
            Node::Fork(_, tail) => *tail,
            other => panic!("Expected call form, got {:?}", other),
        };

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let expanded = interpreter
            .expand_cl_test_signals_error(args, &Environment::new())
            .expect("signals-error expansion failed");
        let printed = {
            let syms = globals.symbols.read().unwrap();
            crate::printer::print_to_string(&interpreter.process.arena.inner, &syms, expanded)
        };
        assert!(printed.contains("HANDLER-BIND"));
        assert!(printed.contains("COMPILE"));
    }

    #[test]
    fn test_expand_defmethod_fast_path_shape() {
        let (mut proc, globals) = setup_env();
        load_init_lisp(&mut proc, &globals);

        let form = read_from_string(
            "(defmethod dm-fast-shape ((x t)) x)",
            &mut proc.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let args = match proc.arena.inner.get_unchecked(form) {
            Node::Fork(_, tail) => *tail,
            other => panic!("Expected defmethod form, got {:?}", other),
        };

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let expanded = interpreter
            .expand_common_lisp_defmethod(args)
            .expect("defmethod fast expansion should not error")
            .expect("defmethod fast expansion should produce a form");
        let printed = {
            let syms = globals.symbols.read().unwrap();
            crate::printer::print_to_string(&interpreter.process.arena.inner, &syms, expanded)
        };
        assert!(printed.contains("LET*"));
        assert!(printed.contains("ENSURE-METHOD"));
        assert!(printed.contains(":SPECIALIZERS"));
    }

    #[test]
    fn test_eval_defmethod_fast_path_with_qualifier() {
        let (mut proc, globals) = setup_env();
        load_init_lisp(&mut proc, &globals);

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let env = Environment::new();

        let expr = read_from_string(
            "(progn
               (defgeneric dm-fast-qual (x))
               (defmethod dm-fast-qual ((x t)) 10)
               (defmethod dm-fast-qual :around ((x t)) (+ 1 (call-next-method)))
               (dm-fast-qual 0))",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let result = interpreter.eval(expr, &env).unwrap();
        match interpreter.process.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(n)) => assert_eq!(*n, 11),
            other => panic!("Expected 11, got {:?}", other),
        }
    }

    #[test]
    fn test_setf_fast_path_symbol_places() {
        let (mut proc, globals) = setup_env();
        load_init_lisp(&mut proc, &globals);

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let env = Environment::new();

        let expr = read_from_string(
            "(progn (setq a 1 b 2) (setf a 7 b 8) (list a b))",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let result = interpreter.eval(expr, &env).unwrap();
        assert_eq!(list_to_ints(&interpreter.process, result), vec![7, 8]);
    }

    #[test]
    fn test_setf_fast_path_handles_car_place() {
        let (mut proc, globals) = setup_env();
        load_init_lisp(&mut proc, &globals);

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let env = Environment::new();

        let expr = read_from_string(
            "(let ((x (cons 1 2))) (setf (car x) 9) (car x))",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let result = interpreter.eval(expr, &env).unwrap();
        match interpreter.process.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(n)) => assert_eq!(*n, 9),
            other => panic!("Expected 9, got {:?}", other),
        }
    }

    #[test]
    fn test_setf_fast_path_handles_gethash_get_and_symbol_value() {
        let (mut proc, globals) = setup_env();
        load_init_lisp(&mut proc, &globals);

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let env = Environment::new();

        let expr_hash = read_from_string(
            "(let ((h (make-hash-table)) (k (cons 1 nil))) (setf (gethash k h) 5) (gethash k h))",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let hash_result = interpreter.eval(expr_hash, &env).unwrap();
        match interpreter.process.arena.inner.get_unchecked(hash_result) {
            Node::Leaf(OpaqueValue::Integer(n)) => assert_eq!(*n, 5),
            other => panic!("Expected hash result 5, got {:?}", other),
        }

        let expr_get = read_from_string(
            "(let ((s (gensym))) (setf (get s 'k) 9) (get s 'k))",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let get_result = interpreter.eval(expr_get, &env).unwrap();
        match interpreter.process.arena.inner.get_unchecked(get_result) {
            Node::Leaf(OpaqueValue::Integer(n)) => assert_eq!(*n, 9),
            other => panic!("Expected property result 9, got {:?}", other),
        }

        let expr_symbol_value = read_from_string(
            "(progn (setf (symbol-value 'zz-fast-path) 12) (symbol-value 'zz-fast-path))",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let symbol_value_result = interpreter.eval(expr_symbol_value, &env).unwrap();
        match interpreter.process.arena.inner.get_unchecked(symbol_value_result) {
            Node::Leaf(OpaqueValue::Integer(n)) => assert_eq!(*n, 12),
            other => panic!("Expected symbol-value result 12, got {:?}", other),
        }
    }

    #[test]
    fn test_setf_fast_path_handles_logical_pathname_translations_place() {
        let (mut proc, globals) = setup_env();
        load_init_lisp(&mut proc, &globals);

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let env = Environment::new();

        let expr = read_from_string(
            "(progn
               (setf (logical-pathname-translations \"TLPFAST\")
                     '((\"**;*.*.*\" \"tmp/logical-fast/**/*.*\")))
               (namestring (translate-logical-pathname \"TLPFAST:foo;bar.txt\")))",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let result = interpreter.eval(expr, &env).unwrap();
        let out = match interpreter.process.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::String(s)) => s.clone(),
            other => panic!("Expected translated namestring, got {:?}", other),
        };
        let normalized = out.replace('\\', "/");
        assert!(normalized.contains("tmp/logical-fast"));
        assert!(normalized.ends_with("foo/bar.txt"));
    }

    #[test]
    fn test_setf_fast_path_unknown_place_returns_none() {
        let (mut proc, globals) = setup_env();
        load_init_lisp(&mut proc, &globals);
        let mut interpreter = Interpreter::new(&mut proc, &globals);

        let place = read_from_string(
            "(foo x)",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let value = interpreter.process.make_integer(1);
        let expanded = interpreter
            .expand_common_lisp_setf_assignment(place, value)
            .expect("setf assignment expansion failed");
        assert!(expanded.is_none(), "unsupported place should fall back to macro body");
    }

    #[test]
    fn test_eval_let_star_sequential_bindings() {
        let (mut proc, globals) = setup_env();
        load_init_lisp(&mut proc, &globals);

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let env = Environment::new();

        let expr = read_from_string(
            "(let* ((x 1) (y (+ x 2))) y)",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let result = interpreter.eval(expr, &env).unwrap();
        match interpreter.process.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(n)) => assert_eq!(*n, 3),
            other => panic!("Expected 3, got {:?}", other),
        }
    }

    #[test]
    fn test_eval_let_star_special_binding_restore() {
        let (mut proc, globals) = setup_env();
        load_init_lisp(&mut proc, &globals);

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let env = Environment::new();

        let expr = read_from_string(
            "(progn (setq *foo* 10) (let* ((*foo* 20) (x *foo*)) (list x *foo*)))",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let result = interpreter.eval(expr, &env).unwrap();
        assert_eq!(list_to_ints(&interpreter.process, result), vec![20, 20]);

        let expr2 = read_from_string(
            "(symbol-value '*foo*)",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let result2 = interpreter.eval(expr2, &env).unwrap();
        match interpreter.process.arena.inner.get_unchecked(result2) {
            Node::Leaf(OpaqueValue::Integer(n)) => assert_eq!(*n, 10),
            other => panic!("Expected restored *foo* value 10, got {:?}", other),
        }
    }

    #[test]
    fn test_eval_cond_direct_handling() {
        let (mut proc, globals) = setup_env();
        load_init_lisp(&mut proc, &globals);

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let env = Environment::new();

        let expr = read_from_string(
            "(cond ((eql 1 2) 9) ((eql 2 2) 11 12) (t 99))",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let result = interpreter.eval(expr, &env).unwrap();
        match interpreter.process.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(n)) => assert_eq!(*n, 12),
            other => panic!("Expected 12, got {:?}", other),
        }

        let expr2 = read_from_string(
            "(cond (() 1) ((+ 2 3)) (t 0))",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let result2 = interpreter.eval(expr2, &env).unwrap();
        match interpreter.process.arena.inner.get_unchecked(result2) {
            Node::Leaf(OpaqueValue::Integer(n)) => assert_eq!(*n, 5),
            other => panic!("Expected 5, got {:?}", other),
        }
    }

    #[test]
    fn test_eval_or_direct_handling() {
        let (mut proc, globals) = setup_env();
        load_init_lisp(&mut proc, &globals);

        let mut interpreter = Interpreter::new(&mut proc, &globals);
        let env = Environment::new();

        let expr = read_from_string(
            "(or nil nil 7)",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let result = interpreter.eval(expr, &env).unwrap();
        match interpreter.process.arena.inner.get_unchecked(result) {
            Node::Leaf(OpaqueValue::Integer(n)) => assert_eq!(*n, 7),
            other => panic!("Expected 7, got {:?}", other),
        }

        let expr2 = read_from_string(
            "(multiple-value-list (or (values 1 2) 9))",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let result2 = interpreter.eval(expr2, &env).unwrap();
        assert_eq!(list_to_ints(&interpreter.process, result2), vec![1]);

        let expr3 = read_from_string(
            "(multiple-value-list (or nil (values 3 4)))",
            &mut interpreter.process.arena.inner,
            &mut *globals.symbols.write().unwrap(),
        )
        .unwrap();
        let result3 = interpreter.eval(expr3, &env).unwrap();
        assert_eq!(list_to_ints(&interpreter.process, result3), vec![3, 4]);
    }

    #[test]
    fn test_step_apply_tree_calculus_fallback() {
        let (mut proc, globals) = setup_env();
        let mut interpreter = Interpreter::new(&mut proc, &globals);

        // Apply K combinator to two delta arguments; result should be a delta (nil).
        let k_node = tree_calculus::k(&mut interpreter.process.arena.inner);
        let arg1 = tree_calculus::delta(&mut interpreter.process.arena.inner);
        let arg2 = tree_calculus::delta(&mut interpreter.process.arena.inner);

        let env = Environment::new();
        let res = interpreter.step_apply(k_node, vec![arg1, arg2], env);
        assert!(res.is_ok());

        let result_node = interpreter.process.program;
        match interpreter.process.arena.inner.get_unchecked(result_node) {
            Node::Leaf(OpaqueValue::Nil) => {}
            other => panic!("Expected nil from tree calculus fallback, got {:?}", other),
        }
    }

    #[test]
    fn test_undefined_variable_error() {
        let (mut proc, globals) = setup_env();
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
        let (mut proc, globals) = setup_env();
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
