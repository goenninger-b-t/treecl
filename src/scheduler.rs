use crate::process::{Process, Pid, Priority, Status, ExecutionResult};
use crate::types::{NodeId, OpaqueValue};
use crate::syscall::SysCall;
use std::collections::{HashMap, VecDeque};

/// Scheduler managing processes
pub struct Scheduler {
    /// Process Registry
    pub registry: HashMap<Pid, Process>,
    
    /// Run Queues (per priority)
    pub low_queue: VecDeque<Pid>,
    pub normal_queue: VecDeque<Pid>,
    pub high_queue: VecDeque<Pid>,
    
    /// PID Counter
    next_pid: u32,

    /// Node ID (for distributed PID)
    node_id: u32,
    
    /// Current Tick (for timing/preemption context)
    tick: u64,
}

impl Scheduler {
    pub fn new() -> Self {
        Self {
            registry: HashMap::new(),
            low_queue: VecDeque::new(),
            normal_queue: VecDeque::new(),
            high_queue: VecDeque::new(),

            next_pid: 1,
            node_id: 0,
            tick: 0,
        }
    }
    
    /// Spawn a new process
    /// Returns the Pid of the spawned process. 
    /// The process is NOT started automatically. Caller must setup arena/program and call schedule().
    pub fn spawn(&mut self, globals: &mut crate::context::GlobalContext) -> Pid {
        let pid = Pid { node: self.node_id, id: self.next_pid, serial: 0 };
        self.next_pid += 1;
        
        // Initialize with placeholder program (will be overwritten by loader)
        let process = Process::new(pid, NodeId(0), globals); 
        self.registry.insert(pid, process);
        
        pid
    }
    
    /// Schedule a process for execution
    pub fn schedule(&mut self, pid: Pid) {
        if let Some(proc) = self.registry.get(&pid) {
             match proc.priority {
                 Priority::High => self.high_queue.push_back(pid),
                 Priority::Normal => self.normal_queue.push_back(pid),
                 Priority::Low => self.low_queue.push_back(pid),
                 Priority::Realtime => {}, 
             }
        }
    }
    
    /// Send a message from one process to another
    /// Note: Uses deep copy to ensure memory safety between Process Arenas.
    pub fn send_message(&mut self, sender: Pid, receiver: Pid, msg_root: NodeId) -> bool {
        // Handle Loopback case: sender == receiver
        if sender == receiver {
             if let Some(proc) = self.registry.get_mut(&receiver) {
                 // For loopback, we currently share the node (unsafe/simple).
                 // Ideally deep_copy within same arena.
                 proc.send(sender, msg_root);
                 
                 // Add to queue if runnable
                 if proc.status == Status::Runnable {
                    let prio = proc.priority;
                    match prio {
                        Priority::High => self.high_queue.push_back(receiver),
                        Priority::Normal => self.normal_queue.push_back(receiver),
                        Priority::Low => self.low_queue.push_back(receiver),
                        _ => {}
                    }
                 }
                 return true;
             }
             return false;
        }

        // Cross-Process Send: Detailed locking/borrowing dance
        if let Some(mut target_proc) = self.registry.remove(&receiver) {
            let success = if let Some(sender_proc) = self.registry.get(&sender) {
                let copied_root = crate::arena::deep_copy(
                    &sender_proc.arena.inner, 
                    msg_root, 
                    &mut target_proc.arena.inner
                );
                
                target_proc.send(sender, copied_root);
                true
            } else {
                false
            };
            
            self.registry.insert(receiver, target_proc);
            
            if success {
                 // Re-acquire reference to check status and schedule
                 if let Some(proc) = self.registry.get(&receiver) {
                     if proc.status == Status::Runnable {
                         let prio = proc.priority;
                         match prio {
                             Priority::High => self.high_queue.push_back(receiver),
                             Priority::Normal => self.normal_queue.push_back(receiver),
                             Priority::Low => self.low_queue.push_back(receiver),
                             _ => {},
                         }
                     }
                 }
            }
            
            success
        } else {
            false
        }
    }
    
    fn resume_process(&mut self, pid: Pid, mut proc: Process, result: NodeId) {
        // Replace the pending redex with the result
        if let Some(redex) = proc.pending_redex.take() {
            // Overwrite Redex using Arena::overwrite
            // We clone the result node content to overwrite the redex.
            let result_node = proc.arena.inner.get_unchecked(result).clone();
            proc.arena.inner.overwrite(redex, result_node);
        }
        
        proc.status = Status::Runnable;
        self.registry.insert(pid, proc);
        self.schedule(pid);
    }
    
    /// Run the scheduler for one tick (round-robin)
    pub fn run_tick(&mut self, globals: &mut crate::context::GlobalContext) -> bool {
        self.tick += 1;
        
        // 1. Pick a process
        // Priority: High > Normal > Low
        let next = self.high_queue.pop_front()
            .or_else(|| self.normal_queue.pop_front())
            .or_else(|| self.low_queue.pop_front());
            
        if let Some(pid) = next {
            if let Some(mut proc) = self.registry.remove(&pid) {
                // 2. Run Process
                let budget = 1000;
                let result = proc.execute_slice(globals, budget);
                
                match result {
                    ExecutionResult::Yielded => {
                        proc.status = Status::Runnable;
                        self.registry.insert(pid, proc);
                        self.schedule(pid);
                    }
                    ExecutionResult::Terminated => {
                        proc.status = Status::Terminated;
                        self.registry.insert(pid, proc);
                        println!("Process {:?} terminated.", pid);
                    }
                    ExecutionResult::Blocked => {
                        proc.status = Status::Waiting(None);
                        self.registry.insert(pid, proc);
                        // Do not reschedule. It waits for message.
                    }
                    ExecutionResult::SysCall(syscall) => {
                        // Handle SysCall
                        self.handle_syscall(pid, proc, syscall, globals);
                    }
                }
                return true;
            }
        }
        return false; // Idle
    }
    
    pub fn run_until_empty(&mut self, globals: &mut crate::context::GlobalContext) {
        while self.run_tick(globals) {}
    }

    fn handle_syscall(&mut self, pid: Pid, mut proc: Process, syscall: SysCall, globals: &mut crate::context::GlobalContext) {
        match syscall {
            SysCall::Spawn(func) => {
                 let new_pid = Pid { node: self.node_id, id: self.next_pid, serial: 0 };
                 self.next_pid += 1;
                 
                 // Create new process with placeholder
                 let mut new_proc = Process::new(new_pid, NodeId(0), globals);
                 
                 // Deep copy function from Parent to Child
                 let copied_func = crate::arena::deep_copy(
                     &proc.arena.inner,
                     func,
                     &mut new_proc.arena.inner
                 );
                 
                 // Wrap in application (func . nil) to execute it
                 let nil = new_proc.make_nil();
                 let app = new_proc.arena.alloc(crate::arena::Node::Fork(copied_func, nil));
                 new_proc.program = app;
                 
                 self.registry.insert(new_pid, new_proc);
                 self.schedule(new_pid);
                 
                 // Return New PID to Parent
                 let pid_val = proc.arena.inner.alloc(crate::arena::Node::Leaf(OpaqueValue::Pid(new_pid)));
                 self.resume_process(pid, proc, pid_val);
            }
            SysCall::Send { target, message } => {
                let _success = if let Some(mut target_proc) = self.registry.remove(&target) {
                    let copied = crate::arena::deep_copy(
                        &proc.arena.inner,
                        message,
                        &mut target_proc.arena.inner
                    );
                    
                    let mut wake = false;
                    if let Status::Waiting(pat) = target_proc.status {
                        let matches = if let Some(pattern) = pat {
                            crate::arena::deep_equal(&target_proc.arena.inner, pattern, copied)
                        } else { true };
                        if matches { wake = true; }
                    }
                    
                    if wake {
                         // Wake up and deliver result directly
                         if let Some(redex) = target_proc.pending_redex.take() {
                              // Identify the result node in target arena
                              let result_node = target_proc.arena.inner.get_unchecked(copied).clone();
                              target_proc.arena.inner.overwrite(redex, result_node);
                         }
                         target_proc.status = Status::Runnable;
                         self.registry.insert(target, target_proc);
                         self.schedule(target);
                    } else {
                         // Enqueue in mailbox
                         target_proc.send(pid, copied);
                         // If already runnable, ensure it's in a queue (idempotent schedule check usually)
                         // But we removed it from registry.
                         if target_proc.status == Status::Runnable {
                             self.registry.insert(target, target_proc);
                             self.schedule(target);
                         } else {
                             self.registry.insert(target, target_proc);
                         }
                    }
                    true
                } else {
                    false
                };
                
                // Return Message to Sender
                self.resume_process(pid, proc, message); 
            }
            SysCall::Receive { pattern } => {
                let mut found = None;
                for (i, msg) in proc.mailbox.iter().enumerate() {
                    let matches = if let Some(pat) = pattern {
                        crate::arena::deep_equal(&proc.arena.inner, pat, msg.payload)
                    } else { true };
                    
                    if matches { found = Some(i); break; }
                }
                
                if let Some(i) = found {
                    let msg = proc.mailbox.remove(i).unwrap();
                    self.resume_process(pid, proc, msg.payload);
                } else {
                    proc.status = Status::Waiting(pattern);
                    self.registry.insert(pid, proc);
                }
            }
            SysCall::Sleep(ms) => {
                 // Blocking Sleep for now (Simulated)
                 std::thread::sleep(std::time::Duration::from_millis(ms));
                 let nil = proc.make_nil();
                 self.resume_process(pid, proc, nil);
            }
            SysCall::SelfPid => {
                 let pid_val = proc.arena.inner.alloc(crate::arena::Node::Leaf(OpaqueValue::Pid(pid)));
                 self.resume_process(pid, proc, pid_val);
            }
        }
    }
}
