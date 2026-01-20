use crate::arena::{Arena, Node};
use crate::types::{NodeId, OpaqueValue, SymbolId};
use crate::search::EvalContext;
use std::collections::{VecDeque, HashMap, HashSet};

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
    Sleeping(u64), // Timer
    Terminated,
    Failed(String), // Crash reason
    Paused,         // Debugger paused
}

/// Stepping mode for debugger
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StepMode {
    Continue,
    StepInto,
    StepOver(usize), // Target stack depth
    StepOut(usize),  // Target stack depth
}

/// Result of a time slice execution
#[derive(Debug, Clone, PartialEq)]
pub enum ExecutionResult {
    Yielded,      // Budget exhausted, still runnable
    Terminated,   // Finished (Normal Form)
    Blocked,      // Waiting for IO/Message
    SysCall(crate::syscall::SysCall), // Kernel request
    Paused,       // Debugger pause
}

/// A message sent between processes
#[derive(Debug, Clone)]
pub struct Message {
    pub sender: Pid,
    pub payload: NodeId, // Root of the message tree in Receiver's arena (copied on send)
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

    /// Condition System State
    pub conditions: crate::conditions::ConditionSystem,
    
    /// Stream Manager
    pub streams: crate::streams::StreamManager,
    
    /// Array Store (Heap for Vectors/Arrays)
    pub arrays: crate::arrays::ArrayStore,
    
    /// Readtable (Reader Macro Configuration)
    pub readtable: crate::readtable::Readtable,
    
    /// Links (Bidirectional failure propagation)
    pub links: HashSet<Pid>,
    
    /// Monitors (Unidirectional observation)
    pub monitors: HashMap<u64, Pid>, // Ref -> Pid
    
    /// Execution Budget (Reductions)
    pub reduction_count: usize,
    
    /// Evaluation Context (Stack depth, limits)
    pub eval_context: EvalContext,
    
    /// MetaObject Protocol (CLOS)
    pub mop: crate::clos::MetaObjectProtocol,
    
    /// Pending SysCall info (if stopped)
    pub pending_syscall: Option<crate::syscall::SysCall>,

    /// Debugger State
    pub debug_mode: bool,
    pub step_mode: StepMode,
    pub paused: bool,
}

impl Process {
    pub fn new(pid: Pid, program: NodeId, globals: &mut crate::context::GlobalContext) -> Self {
        let arena = ProcessArena::new();
        
        // Initialize streams (Stdio)
        let streams = crate::streams::StreamManager::new();
        
        let closures = Vec::new(); // Closures are now rooted indices
        let dictionary = HashMap::new();
        let conditions = crate::conditions::ConditionSystem::new();
        let arrays = crate::arrays::ArrayStore::new();
        let readtable = crate::readtable::Readtable::new();
        
        let mop = crate::clos::MetaObjectProtocol::new(&mut globals.symbols); // MOP needs global symbols for class definitions
        
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
            conditions,
            arrays,
            readtable,
            links: HashSet::new(), // Initialize links
            monitors: HashMap::new(), // Initialize monitors
            mop,
            eval_context,
            reduction_count: 0,
            pending_redex: None,
            pending_syscall: None,
            debug_mode: false,
            step_mode: StepMode::Continue,
            paused: false,
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

        // Stack (EvalContext)
        for &node in &self.eval_context.stack {
            self.mark_node(node, &mut marked);
        }

        // 2. Mark Heap
        // We use a simple mark-and-sweep or just counting for now?
        // Arena doesn't support sweep well unless strict freelist.
        // For now, these roots are just "kept alive".
        // Real GC requires moving collector or freelist sweep.
        

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
        // Array Store Sweep (stub)
        self.arrays.sweep(&marked);
        
        let freed = self.arena.inner.sweep(&marked);
        self.arena.inner.reset_alloc_count();
        freed
    }

    /// introspection: Get current stack frames
    pub fn get_stack_frames(&self) -> Vec<NodeId> {
        self.eval_context.stack.clone()
    }

    /// introspection: Get current bindings
    pub fn get_bindings(&self) -> &HashMap<SymbolId, SymbolBindings> {
        &self.dictionary
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
    
    pub fn get_function(&self, sym: SymbolId) -> Option<NodeId> {
        self.dictionary.get(&sym).and_then(|b| b.function)
    }
    
    pub fn set_function(&mut self, sym: SymbolId, func: NodeId) {
        self.dictionary.entry(sym).or_default().function = Some(func);
    }
    
    /// Make a NIL node
    pub fn make_nil(&mut self) -> NodeId {
        self.arena.inner.alloc(Node::Leaf(OpaqueValue::Nil))
    }
    
    /// Make a T node
    pub fn make_t(&mut self, globals: &crate::context::GlobalContext) -> NodeId {
        self.arena.inner.alloc(Node::Leaf(OpaqueValue::Symbol(globals.t_sym.0)))
    }
    
    /// Make an Integer node
    pub fn make_integer(&mut self, val: i64) -> NodeId {
        self.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(val)))
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
    pub fn execute_slice(&mut self, globals: &crate::context::GlobalContext, budget: usize) -> ExecutionResult {
        if self.paused {
            return ExecutionResult::Paused;
        }
        
        if self.status != Status::Runnable {
            return ExecutionResult::Blocked;
        }
        
        let start_total_steps = self.eval_context.steps;
        let mut steps_left = budget;
        
        while steps_left > 0 {
            // Setup step limit
            if self.debug_mode && (self.step_mode == StepMode::StepInto || matches!(self.step_mode, StepMode::StepOver(_)) || matches!(self.step_mode, StepMode::StepOut(_))) {
                // In debug stepping modes, we run 1 reduction at a time
                self.eval_context.max_steps = self.eval_context.steps + 1;
            } else {
                // Batch execution
                self.eval_context.max_steps = self.eval_context.steps + steps_left;
            }
            
            // Run Reduction
            self.program = crate::search::reduce(&mut self.arena.inner, self.program, &mut self.eval_context);
            self.reduction_count = self.eval_context.steps;
            
            // Calculate steps taken in this iteration
            let steps_taken = self.reduction_count - start_total_steps - (budget - steps_left);
            if steps_taken > steps_left {
                steps_left = 0; // Should not happen if logic is correct
            } else {
                steps_left -= steps_taken;
            }
            
            // Check for SysCall from Primitives (set during reduction?)
            // Normally primitives are handled below, but if reduce calls something that sets it? 
            if let Some(syscall) = self.pending_syscall.take() {
                 return ExecutionResult::SysCall(syscall);
            }
            
            // Check for Primitives (Stuck state) or Normal Form
            let stopped_early = self.eval_context.steps < self.eval_context.max_steps;
            
                if stopped_early {
                // Check if head is primitive
                 {
                     let mut interpreter = crate::eval::Interpreter::new(self, globals);
                     let old_root = interpreter.process.program;
                     
                     // Try one primitive reduction
                     let new_root = interpreter.try_reduce_primitive(interpreter.process.program, &crate::eval::Environment::new());
                     
                     // Check if THAT triggered syscall
                     if let Some(syscall) = interpreter.process.pending_syscall.take() {
                          return ExecutionResult::SysCall(syscall);
                     }
                     
                     if new_root == old_root {
                         // No primitive reduction happened either.
                         // Steps taken was 0 (stopped_early) and no primitive. 
                         // We are DONE.
                         return ExecutionResult::Terminated;
                     }
                     
                     interpreter.process.program = new_root;
                 }
            }
            
            // Debugger Pausing Logic
            if self.debug_mode {
                match self.step_mode {
                    StepMode::StepInto => {
                        self.paused = true;
                        return ExecutionResult::Paused;
                    }
                    StepMode::StepOver(_) | StepMode::StepOut(_) => {
                        // Fallback to StepInto behavior for now as we don't track stack frames yet
                        self.paused = true;
                        return ExecutionResult::Paused;
                    }
                    _ => {}
                }
                
                // If we are single stepping but budget ran out (e.g. 1 step took 1 budget), break loop
                if steps_left == 0 {
                    break;
                }
            } else {
                // If not debugging, and we finished a batch, we are done with this slice
                 break;
            }
            
            // If we stopped early (Normal Form) and Primitive didn't run effectively (or it did), 
            // check if we are truly done.
            if self.eval_context.steps < self.eval_context.max_steps && self.status == Status::Runnable {
                 // Terminated (Normal Form)
                 self.status = Status::Terminated;
                 return ExecutionResult::Terminated;
            }
        }
        
        if self.status != Status::Runnable {
             // Status changed (e.g. Failed, Blocked)
             return ExecutionResult::Terminated;
        }
        
        ExecutionResult::Yielded
    }
}
