use crate::arena::{Arena, Node};
use crate::search::EvalContext;
use crate::types::{NodeId, OpaqueValue, SymbolId};
use std::collections::{HashMap, HashSet, VecDeque};

/// Process ID
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Pid {
    pub node: u32,
    pub id: u32,
    pub serial: u32,
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
    Failed(String), // Crash reason
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

    /// Process-Local Memory
    pub arena: ProcessArena,

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

    /// Condition System State
    pub conditions: crate::conditions::ConditionSystem,

    /// Stream Manager
    pub streams: crate::streams::StreamManager,

    /// Array Store (Heap for Vectors/Arrays)
    pub arrays: crate::arrays::ArrayStore,

    /// Readtable (Reader Macro Configuration)
    pub readtable: crate::readtable::Readtable,

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

    /// Pending SysCall info (if stopped)
    pub pending_syscall: Option<crate::syscall::SysCall>,
}

impl Process {
    pub fn new(pid: Pid, program: NodeId, globals: &crate::context::GlobalContext) -> Self {
        let arena = ProcessArena::new();

        // Initialize streams (Stdio)
        let streams = crate::streams::StreamManager::new();

        let closures = Vec::new(); // Closures are now rooted indices
        let dictionary = HashMap::new();
        let conditions = crate::conditions::ConditionSystem::new();
        let arrays = crate::arrays::ArrayStore::new();
        let readtable = crate::readtable::Readtable::new();
        let hashtables = crate::hashtables::HashTableStore::new();

        let mop = crate::clos::MetaObjectProtocol::new(&mut *globals.symbols.write().unwrap()); // MOP needs global symbols for class definitions

        // Initialize evaluation context
        let eval_context = EvalContext::new();

        let proc = Self {
            pid,
            priority: Priority::Normal,
            status: Status::Runnable,
            arena,
            program,
            mailbox: VecDeque::new(),
            dictionary,
            streams,
            closures,
            macros: HashMap::new(), // Initialize macros
            functions: HashMap::new(),
            conditions,
            arrays,
            readtable,
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
        };

        // Create T and NIL in local arena
        // We use globals to get symbols, but we create nodes locally.
        // T_SYM and NIL_SYM are in Global Symbol Table.
        // We just wrap them in leaf nodes.
        // Optimization: Cache them?

        proc
    }

    /// Check if process has pending messages
    pub fn has_messages(&self) -> bool {
        !self.mailbox.is_empty()
    }

    pub fn collect_garbage(&mut self) -> usize {
        let mut marked = HashSet::new();

        // 1. Mark Roots

        // Program Counter
        self.mark_node(self.program, &mut marked);

        // Mailbox
        for msg in &self.mailbox {
            self.mark_node(msg.payload, &mut marked);
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

        // Mark Condition System Roots
        for root in self.conditions.iter_roots() {
            self.mark_node(root, &mut marked);
        }

        // Mark MOP Roots
        for root in self.mop.iter_roots() {
            self.mark_node(root, &mut marked);
        }

        // Closures are now traced via reachability in mark_node.
        // We do NOT scan all closures to allow collecting unreachable ones.

        // 2. Sweep
        let freed = self.arena.inner.sweep(&marked);
        self.arena.inner.reset_alloc_count();
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
            None
        }
    }

    pub fn set_function(&mut self, sym: SymbolId, func: NodeId) {
        self.dictionary.entry(sym).or_default().function = Some(func);
    }

    pub fn unbind_value(&mut self, sym: SymbolId) {
        if let Some(binding) = self.dictionary.get_mut(&sym) {
            binding.value = None;
        }
    }

    /// Make a NIL node
    pub fn make_nil(&mut self) -> NodeId {
        self.arena.inner.alloc(Node::Leaf(OpaqueValue::Nil))
    }

    /// Make a T node
    pub fn make_t(&mut self, globals: &crate::context::GlobalContext) -> NodeId {
        self.arena
            .inner
            .alloc(Node::Leaf(OpaqueValue::Symbol(globals.t_sym.0)))
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
                    interpreter.process.status = Status::Failed(msg);
                    return ExecutionResult::Terminated;
                }
                Err(crate::eval::ControlSignal::SysCall(sys)) => {
                    return ExecutionResult::SysCall(sys);
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
