use crate::arena::{Arena, Node};
use crate::search::EvalContext;
use crate::types::{NodeId, OpaqueValue, SymbolId};
use std::collections::{HashMap, HashSet, VecDeque};

/// Process ID
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Pid {
    pub node: u32,
    pub id: u32,
    pub serial: u32,
}

impl std::fmt::Display for Pid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<{},{},{}>", self.node, self.id, self.serial)
    }
}

impl std::fmt::Debug for Pid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<{},{},{}>", self.node, self.id, self.serial)
    }
}

/// Process Priority
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Priority {
    Low,
    Normal,
    High,
    Realtime, // System processes (drivers)
}

/// Process Status
#[derive(Debug, Clone, PartialEq)]
pub enum Status {
    Runnable,
    Waiting(Option<NodeId>), // Waiting for message (optional pattern)
    Sleeping(u64),           // Timer
    Terminated,
    Failed(String),                         // Crash reason
    Debugger(crate::conditions::Condition), // Condition causing the break
}

/// Result of a time slice execution
#[derive(Debug, Clone, PartialEq)]
pub enum ExecutionResult {
    Yielded,                          // Budget exhausted, still runnable
    Terminated,                       // Finished (Normal Form)
    Blocked,                          // Waiting for IO/Message
    SysCall(crate::syscall::SysCall), // Kernel request
}

/// A message sent between processes
#[derive(Debug, Clone)]
pub struct Message {
    pub sender: Pid,
    pub payload: NodeId, // Root of the message tree in Receiver's arena (copied on send)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExecutionMode {
    Eval,   // Evaluate `program` in `current_env`
    Return, // `program` is a result, continue mechanism
}

/// Symbol Bindings (Process-Local)
#[derive(Debug, Clone, Default)]
pub struct SymbolBindings {
    pub value: Option<NodeId>,
    pub function: Option<NodeId>,
    pub plist: Option<NodeId>,
}

/// Process-Local Arena Wrapper
///
/// In the future, this can be optimized (bump pointer).
/// For now, it wraps the existing Arena.
pub struct ProcessArena {
    pub inner: Arena,
    pub gc_threshold: usize,
}

impl ProcessArena {
    pub fn new() -> Self {
        Self {
            inner: Arena::new(),
            gc_threshold: 10000,
        }
    }

    pub fn alloc(&mut self, node: Node) -> NodeId {
        self.inner.alloc(node)
    }

    pub fn get(&self, id: NodeId) -> Option<&Node> {
        self.inner.get(id)
    }

    pub fn get_unchecked(&self, id: NodeId) -> &Node {
        self.inner.get_unchecked(id)
    }

    // Garbage Collection methods will go here
}

/// The Process Control Block (PCB)
pub struct Process {
    pub pid: Pid,
    pub priority: Priority,
    pub status: Status,
    /// Debugger stack for nested debugger levels (outermost first).
    pub debugger_stack: Vec<crate::conditions::Condition>,
    /// Last scheduler worker thread id/name that entered the debugger.
    pub debugger_thread_id: Option<u64>,
    pub debugger_thread_name: Option<String>,

    /// Process-Local Memory
    pub arena: ProcessArena,
    /// Cached NIL node in this process arena
    pub nil_node: NodeId,
    /// Cached T node in this process arena
    pub t_node: NodeId,
    /// Cached Unbound node in this process arena
    pub unbound_node: NodeId,
    /// Garbage collection stats
    pub gc_count: u64,
    pub gc_time_sec: f64,
    pub gc_freed_total: usize,

    /// Program Counter (Pointer to current root of reduction)
    pub program: NodeId,

    /// Mailbox (Inbox)
    pub mailbox: VecDeque<Message>, // TODO: Use lock-free queue or channel

    /// Pending Redex (for SysCall resumption)
    /// If we yielded in a syscall, this is the NodeId to replace with the result.
    pub pending_redex: Option<NodeId>,

    /// Process Dictionary (Local Symbol Table / State)
    /// Maps SymbolId (global name) -> Bindings (local value/func)
    pub dictionary: HashMap<SymbolId, SymbolBindings>,

    /// Closures (Heap for Closure structs)
    /// Note: In a real VM, these might be in the Arena or Code Heap.
    pub closures: Vec<crate::eval::Closure>,

    /// Macros (SymbolId -> Closure Index)
    pub macros: HashMap<SymbolId, usize>,

    /// Global Functions (SymbolId -> Closure Index)
    pub functions: HashMap<SymbolId, usize>,
    /// SETF Functions (SymbolId -> Function Node)
    pub setf_functions: HashMap<SymbolId, NodeId>,
    pub fast_make_instance_ok: Option<bool>,

    /// Condition System State
    pub conditions: crate::conditions::ConditionSystem,

    /// Stream Manager
    pub streams: crate::streams::StreamManager,

    /// Array Store (Heap for Vectors/Arrays)
    pub arrays: crate::arrays::ArrayStore,

    /// Readtable Store (Reader Macro Configuration)
    pub readtables: crate::readtable::ReadtableStore,
    /// Current readtable id
    pub current_readtable: crate::readtable::ReadtableId,
    /// Standard readtable id
    pub standard_readtable: crate::readtable::ReadtableId,

    /// Hash Table Store
    pub hashtables: crate::hashtables::HashTableStore,

    /// Links (Bidirectional failure propagation)
    pub links: HashSet<Pid>,

    /// Monitors (Unidirectional observation)
    pub monitors: HashMap<u64, Pid>, // Ref -> Pid

    /// Execution Budget (Reductions)
    pub reduction_count: usize,

    /// Evaluation Context (Stack depth, limits)
    pub eval_context: EvalContext,

    /// TCO Stack for Interpreter
    pub continuation_stack: Vec<crate::eval::Continuation>,

    /// Current Environment for TCO
    // Using Option so we can take/replace without dummy
    pub current_env: Option<crate::eval::Environment>,

    /// TCO Execution Mode
    pub execution_mode: ExecutionMode,

    /// MetaObject Protocol (CLOS)
    pub mop: crate::clos::MetaObjectProtocol,

    /// Multiple values storage
    pub values: Vec<NodeId>,
    pub values_are_set: bool,

    /// Pending SysCall info (if stopped)
    pub pending_syscall: Option<crate::syscall::SysCall>,

    /// Next Method States (CLOS call-next-method)
    pub next_method_states: Vec<crate::clos::NextMethodState>,
}

impl Process {
    pub fn new(pid: Pid, program: NodeId, globals: &crate::context::GlobalContext) -> Self {
        let mut arena = ProcessArena::new();
        let nil_node = arena.inner.alloc(Node::Leaf(OpaqueValue::Nil));
        let t_node = arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(globals.t_sym.0)));
        let unbound_node = arena.inner.alloc(Node::Leaf(OpaqueValue::Unbound));

        // Initialize streams (Stdio)
        let streams = crate::streams::StreamManager::new();

        let closures = Vec::new(); // Closures are now rooted indices
        let dictionary = HashMap::new();
        let conditions = crate::conditions::ConditionSystem::new();
        let arrays = crate::arrays::ArrayStore::new();
        let mut readtables = crate::readtable::ReadtableStore::new();
        let standard_readtable = readtables.alloc(crate::readtable::Readtable::new());
        let current_readtable = standard_readtable;
        let hashtables = crate::hashtables::HashTableStore::new();

        let mop = crate::clos::MetaObjectProtocol::new(&mut *globals.symbols.write().unwrap()); // MOP needs global symbols for class definitions

        // Initialize evaluation context
        let eval_context = EvalContext::new();

        let mut proc = Self {
            pid,
            priority: Priority::Normal,
            status: Status::Runnable,
            debugger_stack: Vec::new(),
            debugger_thread_id: None,
            debugger_thread_name: None,
            arena,
            nil_node,
            t_node,
            unbound_node,
            gc_count: 0,
            gc_time_sec: 0.0,
            gc_freed_total: 0,
            program,
            mailbox: VecDeque::new(),
            dictionary,
            streams,
            closures,
            macros: HashMap::new(), // Initialize macros
            functions: HashMap::new(),
            setf_functions: HashMap::new(),
            fast_make_instance_ok: None,
            conditions,
            arrays,
            readtables,
            current_readtable,
            standard_readtable,
            hashtables,
            links: HashSet::new(),    // Initialize links
            monitors: HashMap::new(), // Initialize monitors
            mop,
            eval_context,
            continuation_stack: Vec::new(),
            current_env: Some(crate::eval::Environment::new()),
            execution_mode: ExecutionMode::Eval,
            reduction_count: 0,
            pending_redex: None,
            pending_syscall: None,
            next_method_states: Vec::new(),
            values: Vec::new(),
            values_are_set: false,
        };

        // Initialize standard dynamic variables
        let intern_cl = |name: &str| -> SymbolId {
            globals
                .symbols
                .write()
                .unwrap()
                .intern_in(name, crate::symbol::PackageId(1))
        };

        // Standard streams
        let stdin_sym = intern_cl("*STANDARD-INPUT*");
        let stdout_sym = intern_cl("*STANDARD-OUTPUT*");
        let stderr_sym = intern_cl("*ERROR-OUTPUT*");
        let trace_sym = intern_cl("*TRACE-OUTPUT*");
        let terminal_sym = intern_cl("*TERMINAL-IO*");

        let stdin_node = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::StreamHandle(
            proc.streams.stdin_id().0,
        )));
        let stdout_node = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::StreamHandle(
            proc.streams.stdout_id().0,
        )));
        let stderr_node = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::StreamHandle(
            proc.streams.stderr_id().0,
        )));

        let terminal_id = proc.streams.alloc(crate::streams::Stream::TwoWayStream {
            input: proc.streams.stdin_id(),
            output: proc.streams.stdout_id(),
        });
        let terminal_node =
            proc.arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::StreamHandle(terminal_id.0)));

        proc.set_value(stdin_sym, stdin_node);
        proc.set_value(stdout_sym, stdout_node);
        proc.set_value(stderr_sym, stderr_node);
        proc.set_value(trace_sym, stdout_node);
        proc.set_value(terminal_sym, terminal_node);

        // Reader control variables
        let readtable_sym = intern_cl("*READTABLE*");
        let read_base_sym = intern_cl("*READ-BASE*");
        let read_eval_sym = intern_cl("*READ-EVAL*");
        let read_suppress_sym = intern_cl("*READ-SUPPRESS*");
        let read_default_float_sym = intern_cl("*READ-DEFAULT-FLOAT-FORMAT*");
        let features_sym = intern_cl("*FEATURES*");

        let readtable_node = proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Readtable(
            proc.current_readtable.0,
        )));
        proc.set_value(readtable_sym, readtable_node);

        let read_base_node = proc
            .arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Integer(10)));
        proc.set_value(read_base_sym, read_base_node);
        proc.set_value(read_eval_sym, proc.t_node);
        proc.set_value(read_suppress_sym, proc.nil_node);

        // Default float format (symbol)
        let single_float_sym = intern_cl("SINGLE-FLOAT");
        let single_float_node =
            proc.arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(single_float_sym.0)));
        proc.set_value(read_default_float_sym, single_float_node);

        // *FEATURES* list
        let mut features = Vec::new();
        let intern_kw = |name: &str| -> SymbolId {
            globals
                .symbols
                .write()
                .unwrap()
                .intern_in(name, crate::symbol::PackageId(0))
        };
        for feat in [
            "COMMON-LISP",
            "ANSI-CL",
            "TREECL",
            "IEEE-FLOATING-POINT",
            "LITTLE-ENDIAN",
            "X86-64",
        ] {
            let sym = intern_kw(feat);
            let node = proc
                .arena
                .inner
                .alloc(Node::Leaf(OpaqueValue::Symbol(sym.0)));
            features.push(node);
        }
        let features_list = proc.make_list(&features);
        proc.set_value(features_sym, features_list);

        // Create T and NIL in local arena
        // We use globals to get symbols, but we create nodes locally.
        // T_SYM and NIL_SYM are in Global Symbol Table.
        // We just wrap them in leaf nodes.
        // Optimization: Cache them?

        proc
    }

    pub fn current_readtable(&self) -> &crate::readtable::Readtable {
        self.readtables
            .get(self.current_readtable)
            .expect("current readtable missing")
    }

    pub fn current_readtable_mut(&mut self) -> &mut crate::readtable::Readtable {
        self.readtables
            .get_mut(self.current_readtable)
            .expect("current readtable missing")
    }

    pub fn readtable_by_id(&self, id: crate::readtable::ReadtableId) -> Option<&crate::readtable::Readtable> {
        self.readtables.get(id)
    }

    pub fn readtable_by_id_mut(&mut self, id: crate::readtable::ReadtableId) -> Option<&mut crate::readtable::Readtable> {
        self.readtables.get_mut(id)
    }

    pub fn set_current_readtable(&mut self, id: crate::readtable::ReadtableId) -> bool {
        if self.readtables.get(id).is_some() {
            self.current_readtable = id;
            true
        } else {
            false
        }
    }

    /// Check if process has pending messages
    pub fn has_messages(&self) -> bool {
        !self.mailbox.is_empty()
    }

    pub fn collect_garbage(&mut self) -> usize {
        let start = std::time::Instant::now();
        let mut marked = HashSet::new();

        // 1. Mark Roots
        self.mark_node(self.nil_node, &mut marked);
        self.mark_node(self.t_node, &mut marked);
        self.mark_node(self.unbound_node, &mut marked);

        // Program Counter
        self.mark_node(self.program, &mut marked);

        // Mailbox
        for msg in &self.mailbox {
            self.mark_node(msg.payload, &mut marked);
        }

        // Waiting receive pattern
        if let Status::Waiting(Some(pat)) = &self.status {
            self.mark_node(*pat, &mut marked);
        }

        // Dictionary (Symbol Values/Functions)
        for binding in self.dictionary.values() {
            if let Some(val) = binding.value {
                self.mark_node(val, &mut marked);
            }
            if let Some(func) = binding.function {
                self.mark_node(func, &mut marked);
            }
            if let Some(plist) = binding.plist {
                self.mark_node(plist, &mut marked);
            }
        }

        // Multiple values
        for &val in &self.values {
            self.mark_node(val, &mut marked);
        }

        // Mark Condition System Roots
        for root in self.conditions.iter_roots() {
            self.mark_node(root, &mut marked);
        }

        if let Status::Debugger(cond) = &self.status {
            self.mark_condition(cond, &mut marked);
        }
        for cond in &self.debugger_stack {
            self.mark_condition(cond, &mut marked);
        }

        // Mark MOP Roots
        for root in self.mop.iter_roots() {
            self.mark_node(root, &mut marked);
        }

        // Mark Macros
        for &closure_idx in self.macros.values() {
            if let Some(closure) = self.closures.get(closure_idx) {
                // Mark macro body
                self.mark_node(closure.body, &mut marked);
                // Mark macro environment
                for root in closure.env.iter_roots() {
                    self.mark_node(root, &mut marked);
                }
            }
        }

        // Mark Global Functions
        // Note: Functions in 'functions' map are usually also in 'dictionary',
        // but we mark them here for safety/completeness if not bound to symbol in dict.
        for &closure_idx in self.functions.values() {
            if let Some(closure) = self.closures.get(closure_idx) {
                self.mark_node(closure.body, &mut marked);
                for root in closure.env.iter_roots() {
                    self.mark_node(root, &mut marked);
                }
            }
        }

        // Mark SETF Functions
        for &func in self.setf_functions.values() {
            self.mark_node(func, &mut marked);
        }

        // Mark Next Method States
        for state in &self.next_method_states {
            for &arg in &state.args {
                self.mark_node(arg, &mut marked);
            }
        }

        // Closures are now traced via reachability in mark_node.
        // We do NOT scan all closures to allow collecting unreachable ones.

        // 2. Sweep
        let freed = self.arena.inner.sweep(&marked);
        self.arena.inner.reset_alloc_count();
        let elapsed = start.elapsed().as_secs_f64();
        self.gc_count = self.gc_count.saturating_add(1);
        self.gc_time_sec += elapsed;
        self.gc_freed_total = self.gc_freed_total.saturating_add(freed);
        freed
    }

    fn mark_node(&self, node_id: NodeId, marked: &mut HashSet<u32>) {
        // Iterative marking to avoid stack overflow on deep trees
        let mut stack = Vec::new();
        stack.push(node_id);

        while let Some(current) = stack.pop() {
            if marked.contains(&current.0) {
                continue;
            }

            marked.insert(current.0);

            if let Some(node) = self.arena.inner.get(current) {
                match node {
                    Node::Fork(left, right) => {
                        stack.push(*right);
                        stack.push(*left);
                    }
                    Node::Stem(child) => {
                        stack.push(*child);
                    }
                    Node::Leaf(val) => {
                        // Trace complex leaves
                        match val {
                            OpaqueValue::VectorHandle(id) => {
                                // Trace vector content
                                if let Some(vec) = self.arrays.get(crate::arrays::VectorId(*id)) {
                                    for &child in vec {
                                        stack.push(child);
                                    }
                                }
                            }
                            OpaqueValue::Instance(id) => {
                                // Trace instance slots
                                if let Some(inst) = self.mop.get_instance(*id as usize) {
                                    for &slot in &inst.slots {
                                        stack.push(slot);
                                    }
                                }
                            }
                            OpaqueValue::Closure(id) => {
                                // Trace closure environment
                                if let Some(closure) = self.closures.get(*id as usize) {
                                    for root in closure.env.iter_roots() {
                                        stack.push(root);
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
    }

    fn mark_condition(
        &self,
        condition: &crate::conditions::Condition,
        marked: &mut HashSet<u32>,
    ) {
        for &arg in &condition.format_arguments {
            self.mark_node(arg, marked);
        }
        for &val in condition.slots.values() {
            self.mark_node(val, marked);
        }
    }

    /// Enqueue a message (called by Scheduler/Sender)
    pub fn send(&mut self, sender: Pid, msg_root: NodeId) {
        self.mailbox.push_back(Message {
            sender,
            payload: msg_root,
        });
        // Wakeup logic is handled by Scheduler (checking patterns)
    }

    // Symbol Helpers
    pub fn get_value(&self, sym: SymbolId) -> Option<NodeId> {
        self.dictionary.get(&sym).and_then(|b| b.value)
    }

    pub fn set_value(&mut self, sym: SymbolId, val: NodeId) {
        self.dictionary.entry(sym).or_default().value = Some(val);
    }

    pub fn get_function(&mut self, sym: crate::symbol::SymbolId) -> Option<NodeId> {
        if let Some(&idx) = self.functions.get(&sym) {
            let val = crate::types::OpaqueValue::Closure(idx as u32);
            Some(self.arena.inner.alloc(crate::arena::Node::Leaf(val)))
        } else {
            // Fallback to dictionary
            self.dictionary.get(&sym).and_then(|b| b.function)
        }
    }

    pub fn set_function(&mut self, sym: SymbolId, func: NodeId) {
        self.dictionary.entry(sym).or_default().function = Some(func);
    }

    pub fn get_setf_function(&self, sym: SymbolId) -> Option<NodeId> {
        self.setf_functions.get(&sym).copied()
    }

    pub fn set_setf_function(&mut self, sym: SymbolId, func: NodeId) {
        self.setf_functions.insert(sym, func);
    }

    pub fn clear_setf_function(&mut self, sym: SymbolId) {
        self.setf_functions.remove(&sym);
    }

    pub fn unbind_value(&mut self, sym: SymbolId) {
        if let Some(binding) = self.dictionary.get_mut(&sym) {
            binding.value = None;
        }
    }

    /// Make a NIL node
    pub fn make_nil(&self) -> NodeId {
        self.nil_node
    }

    /// Make a T node
    pub fn make_t(&self, _globals: &crate::context::GlobalContext) -> NodeId {
        self.t_node
    }

    /// Make an Unbound node
    pub fn make_unbound(&self) -> NodeId {
        self.unbound_node
    }

    /// Make an Integer node
    pub fn make_integer(&mut self, val: i64) -> NodeId {
        self.arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Integer(val)))
    }

    /// Make a Pid node
    pub fn make_pid(&mut self, pid: Pid) -> NodeId {
        self.arena.inner.alloc(Node::Leaf(OpaqueValue::Pid(pid)))
    }

    /// Create a list from a slice of nodes
    pub fn make_list(&mut self, elements: &[NodeId]) -> NodeId {
        let mut result = self.make_nil();
        for &elem in elements.iter().rev() {
            result = self.arena.inner.alloc(Node::Fork(elem, result));
        }
        result
    }

    /// Execute the process for a given budget (reductions)
    pub fn execute_slice(
        &mut self,
        globals: &crate::context::GlobalContext,
        budget: usize,
    ) -> ExecutionResult {
        if self.status != Status::Runnable {
            return ExecutionResult::Blocked;
        }

        let mut steps = 0;

        // We use the Interpreter to drive the TCO state machine
        let mut interpreter = crate::eval::Interpreter::new(self, globals);

        while steps < budget {
            // Check for pending syscalls (shouldn't happen if we check inside step, but mostly for safety)
            if let Some(syscall) = interpreter.process.pending_syscall.take() {
                return ExecutionResult::SysCall(syscall);
            }

            match interpreter.step() {
                Ok(continue_exec) => {
                    steps += 1;
                    interpreter.process.reduction_count += 1;

                    if !continue_exec {
                        // Execution Finished
                        return ExecutionResult::Terminated;
                    }
                }
                Err(crate::eval::ControlSignal::Error(msg)) => {
                    match interpreter.signal_error(&msg) {
                        Err(crate::eval::ControlSignal::Debugger(cond)) => {
                            interpreter.process.status = Status::Debugger(cond);
                            return ExecutionResult::Blocked;
                        }
                        Err(crate::eval::ControlSignal::Error(m)) => {
                            interpreter.process.status = Status::Failed(m);
                            return ExecutionResult::Terminated;
                        }
                        Ok(_) => {
                            // Should not be reachable as signal_error currently always returns Err
                            interpreter.process.status =
                                Status::Failed(format!("Error handler declined: {}", msg));
                            return ExecutionResult::Terminated;
                        }
                        Err(e) => {
                            let m = format!("Unhandled signal from error handler: {:?}", e);
                            interpreter.process.status = Status::Failed(m);
                            return ExecutionResult::Terminated;
                        }
                    }
                }
                Err(crate::eval::ControlSignal::SysCall(sys)) => {
                    return ExecutionResult::SysCall(sys);
                }
                Err(crate::eval::ControlSignal::Debugger(cond)) => {
                    interpreter.process.status = Status::Debugger(cond);
                    return ExecutionResult::Blocked; // Or a specific result? Blocked works for now.
                }
                Err(e) => {
                    // Unhandled signal (Go, ReturnFrom, Throw) at top level
                    let msg = format!("Unhandled signal: {:?}", e);
                    interpreter.process.status = Status::Failed(msg);
                    return ExecutionResult::Terminated;
                }
            }
        }

        ExecutionResult::Yielded
    }
}
