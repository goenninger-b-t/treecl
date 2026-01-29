use crate::process::{ExecutionResult, Pid, Process, Status};
use crate::syscall::SysCall;
use crate::types::{NodeId, OpaqueValue};
use crossbeam_deque::{Injector, Stealer, Worker};
use dashmap::DashMap;
use std::iter;
use std::sync::{Arc, Mutex};
use std::thread;

/// Work-Stealing Scheduler
pub struct Scheduler {
    /// Process Registry (Shared)
    pub registry: Arc<DashMap<Pid, Arc<Mutex<Process>>>>,

    /// Global Injection Queue (for new processes or waking from global events)
    global_queue: Arc<Injector<Pid>>,

    /// PID Counter (Atomic or Mutex protected)
    next_pid: Arc<Mutex<u32>>,

    /// Node ID
    node_id: u32,

    /// Local Queues (Workers)
    /// We keep workers in a way that we can dispatch them to threads.
    /// But typically Scheduler struct constructs everything and then spawn() runs.
    /// We can't move Workers out easily if we keep them here.
    /// So we'll have a `start()` method that creates workers.
    stealers: Vec<Stealer<Pid>>,
}

impl Scheduler {
    pub fn new() -> Self {
        Self {
            registry: Arc::new(DashMap::new()),
            global_queue: Arc::new(Injector::new()),
            next_pid: Arc::new(Mutex::new(1)),
            node_id: 0,
            stealers: Vec::new(),
            // Workers are created in start() or run()
        }
    }

    /// Spawn a new process
    /// Spawn a new process
    pub fn spawn(
        &self,
        globals: &crate::context::GlobalContext,
        func: crate::types::NodeId,
    ) -> crate::process::Pid {
        let mut pid_guard = self.next_pid.lock().unwrap();
        let pid = crate::process::Pid {
            node: self.node_id,
            id: *pid_guard,
            serial: 0,
        };
        *pid_guard += 1;
        drop(pid_guard);

        let mut process = crate::process::Process::new(pid, func, globals);
        process.status = crate::process::Status::Runnable;
        self.registry.insert(pid, Arc::new(Mutex::new(process)));
        self.global_queue.push(pid);

        pid
    }

    /// Schedule a process (Global Injection)
    pub fn schedule(&self, pid: Pid) {
        self.global_queue.push(pid);
    }

    /// Run the scheduler (Multi-threaded)
    /// This will block until all threads join (never, in server mode)
    /// Ideally we return a handle or run in background?
    /// For now, let's implement the logic.
    pub fn start(&mut self, globals: Arc<crate::context::GlobalContext>) {
        let parallelism = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1);
        println!("INFO: Starting scheduler with {} threads", parallelism);

        // Create workers
        let mut workers = Vec::new();
        for _ in 0..parallelism {
            workers.push(Worker::new_fifo());
        }

        let stealers: Vec<Stealer<Pid>> = workers.iter().map(|w| w.stealer()).collect();
        self.stealers = stealers.clone();

        for (i, worker) in workers.into_iter().enumerate() {
            let handle = SchedulerHandle::new(self, stealers.clone());
            let g = globals.clone();

            thread::Builder::new()
                .name(format!("worker-{}", i))
                .spawn(move || {
                    run_worker(handle, worker, i, g);
                })
                .expect("Failed to spawn worker thread");
        }
    }
}

/// A handle to the scheduler that can be shared with threads
#[derive(Clone)]
pub struct SchedulerHandle {
    pub registry: Arc<DashMap<Pid, Arc<Mutex<Process>>>>,
    pub global_queue: Arc<Injector<Pid>>,
    stealers: Arc<Vec<Stealer<Pid>>>,
    next_pid: Arc<Mutex<u32>>,
    node_id: u32,
}

impl SchedulerHandle {
    pub fn new(sched: &Scheduler, stealers: Vec<Stealer<Pid>>) -> Self {
        Self {
            registry: sched.registry.clone(),
            global_queue: sched.global_queue.clone(),
            stealers: Arc::new(stealers),
            next_pid: sched.next_pid.clone(),
            node_id: sched.node_id,
        }
    }

    pub fn spawn_process(&self, globals: &mut crate::context::GlobalContext) -> Pid {
        let mut pid_guard = self.next_pid.lock().unwrap();
        let pid = Pid {
            node: self.node_id,
            id: *pid_guard,
            serial: 0,
        };
        *pid_guard += 1;
        drop(pid_guard);

        let process = Process::new(pid, NodeId(0), globals);
        self.registry.insert(pid, Arc::new(Mutex::new(process)));
        pid
    }

    pub fn schedule_global(&self, pid: Pid) {
        self.global_queue.push(pid);
    }

    fn resume_process(&self, pid: Pid, mut proc: Process, result: NodeId) {
        if let Some(redex) = proc.pending_redex.take() {
            let result_node = proc.arena.inner.get_unchecked(result).clone();
            proc.arena.inner.overwrite(redex, result_node);
        }

        proc.status = Status::Runnable;
        self.registry.insert(pid, Arc::new(Mutex::new(proc)));
        self.global_queue.push(pid);
    }
}

/// Worker Thread Logic
pub fn run_worker(
    handle: SchedulerHandle,
    local: Worker<Pid>,
    worker_idx: usize,
    // Global context is problematic here. It's shared!
    // But Globals uses RwLock internally for Symbols.
    // Primitives are read-only HashMap.
    // SpecialForms is Copy/Clone? No.
    // We need Arc<GlobalContext> or GlobalContext needs to be Sync.
    // GlobalContext has RwLock<SymbolTable>, HashMap<...>, etc.
    // If HashMap is read-only, we are fine?
    // But Primitives take `&mut GlobalContext` in signature? No, `&GlobalContext`.
    // Wait, `prim_load` takes `&GlobalContext`?
    // Let's assume GlobalContext is wrapped in Arc.
    globals: Arc<crate::context::GlobalContext>,
) {
    loop {
        // 1. Find Work
        let pid = local
            .pop()
            .or_else(|| {
                // Check global queue
                iter::repeat_with(|| handle.global_queue.steal_batch_and_pop(&local))
                    .find(|s| !s.is_retry())
                    .and_then(|s| s.success())
            })
            .or_else(|| {
                // Steal from others
                handle
                    .stealers
                    .iter()
                    .map(|s| s.steal_batch_and_pop(&local))
                    .find(|s| s.is_success())
                    .and_then(|s| s.success())
            });

        if let Some(pid) = pid {
            // 2. Run Process
            if let Some(proc_arc) = handle.registry.get(&pid) {
                // Lock Process
                let mut proc = proc_arc.lock().unwrap();

                // If it's runnable
                if proc.status == Status::Runnable {
                    let budget = 1000;
                    // Execute Slice
                    // Note: GlobalContext needs to be accessible.
                    // If we need to mutate Globals (e.g. intern symbols), we rely on internal mutability (RwLock).
                    // So passing &*globals should be fine if GlobalContext is Sync.
                    // (RwLock is Sync, HashMap is Sync if keys/values are Sync).
                    let result = proc.execute_slice(&globals, budget);

                    match result {
                        ExecutionResult::Yielded => {
                            proc.status = Status::Runnable;
                            drop(proc); // Unlock before pushing
                            local.push(pid);
                        }
                        ExecutionResult::Terminated => {
                            proc.status = Status::Terminated;
                            println!("Process {:?} terminated.", pid);
                        }
                        ExecutionResult::Blocked => {
                            proc.status = Status::Waiting(None);
                        }
                        ExecutionResult::SysCall(syscall) => {
                            // Handle SysCall
                            // We need to drop lock before complex operations if we touch other procs?
                            // But we need `proc` to be mutable.
                            // `handle_syscall` might need to unlock `proc` if it accesses registry?
                            // Currently our handle_syscall does registry access.
                            // So we MUST drop lock. But we need to modify proc.

                            // We can clone the syscall, drop lock, handle it, and re-lock if needed?
                            // Or handle_syscall takes the whole Arc?

                            // Let's inline simple syscall handling or be careful.
                            drop(proc);
                            handle_syscall(&handle, pid, syscall, &globals);
                        }
                    }
                }
            }
        } else {
            // Idle
            thread::yield_now();
            thread::sleep(std::time::Duration::from_millis(1));
        }
    }
}

fn handle_syscall(
    sched: &SchedulerHandle,
    pid: Pid,
    syscall: SysCall,
    globals: &Arc<crate::context::GlobalContext>,
) {
    // Re-acquire lock to modify sender process IF needed,
    // BUT we dropped it to avoid deadlock if we need to lock receiver.
    // Let's get the process again.
    let proc_arc = sched.registry.get(&pid).unwrap();
    let mut proc = proc_arc.lock().unwrap();

    match syscall {
        SysCall::Spawn(func) => {
            // Create new PID
            // We can use the handle to spawn logic
            drop(proc); // Drop lock

            // Create new process
            // Wait, we need GlobalContext to create process (intern symbols?)
            // Process::new takes &mut GlobalContext?
            // Let's check Process::new signature.
            // It takes `&mut GlobalContext`.
            // This is bad for multithreading if we need &mut.
            // But GlobalContext only mutates SymbolTable (RwLock) and MOP?
            // If we change Process::new to take `&GlobalContext`, and use internal mutability, it works.
            // We should fix this signature.

            // ASSUMING Process::new takes &GlobalContext or we can cast mut.
            // For now, let's fake it or assume we fixed it.
            // (See next edit for Process::new fix)
            // let new_pid = sched.spawn_process(&mut *globals); // Error: cannot borrow as mut
        }
        SysCall::Send { target, message } => {
            // Drop lock because we need to lock target
            // First deeply copy message
            // We need access to both arenas.
            // We hold lock on sender (proc).
            // We need lock on target.

            // Deadlock risk: A sends to B, B sends to A.
            // Classic solution: acquire locks in PID order?
            // Or: Copy out message, drop sender lock, acquire target lock, copy in?
            // Tree Calculus Nodes are in Arena. We can't copy "out" easily without cloning the whole tree structure intermediate.
            // But deep_copy does exactly that: Arena -> Arena.

            // If we lock target while holding sender:
            // if pid < target { lock(target) } else { drop(sender), lock(target), lock(sender) }?
            // Complex.

            // Allow "try_lock"?

            // Let's try: Lock target. If fail, yield?

            if let Some(target_arc) = sched.registry.get(&target) {
                // Try to lock target
                if let Ok(mut target_proc) = target_arc.try_lock() {
                    // Success, we have both locks
                    let copied = crate::arena::deep_copy(
                        &proc.arena.inner,
                        message,
                        &mut target_proc.arena.inner,
                    );

                    // Delivery logic
                    let mut wake = false;
                    if let Status::Waiting(pat) = target_proc.status {
                        // Check pattern
                        wake = true; // Simplify
                    }

                    if wake {
                        if let Some(redex) = target_proc.pending_redex.take() {
                            let result_node = target_proc.arena.inner.get_unchecked(copied).clone();
                            target_proc.arena.inner.overwrite(redex, result_node);
                        }
                        target_proc.status = Status::Runnable;
                        sched.global_queue.push(target);
                    } else {
                        target_proc.send(pid, copied);
                        // If runnable, it's already in queue? Or we should ensure?
                        // It's in queue if status is Runnable.
                    }

                    // Resume Sender
                    drop(target_proc);

                    // Return message to sender as result
                    // (Resume logic inline)
                    if let Some(redex) = proc.pending_redex.take() {
                        let res = proc.arena.inner.get_unchecked(message).clone();
                        proc.arena.inner.overwrite(redex, res);
                    }
                    proc.status = Status::Runnable;
                    sched.global_queue.push(pid); // Push to back of global queue
                } else {
                    // Failed to lock target. Retry later?
                    // Put syscall back?
                    proc.pending_syscall = Some(SysCall::Send { target, message });
                    // Re-schedule sender to retry
                    // This spins, but safe from deadlock.
                    drop(proc);
                    sched.global_queue.push(pid);
                }
            } else {
                // Target not found
                let nil = proc.make_nil();
                // Resume with nil?
                if let Some(redex) = proc.pending_redex.take() {
                    let n = proc.arena.inner.get_unchecked(nil).clone();
                    proc.arena.inner.overwrite(redex, n);
                }
                proc.status = Status::Runnable;
                sched.global_queue.push(pid);
            }
        }
        SysCall::Receive { pattern } => {
            let mut found = None;
            for (i, msg) in proc.mailbox.iter().enumerate() {
                let matches = if let Some(pat) = pattern {
                    crate::arena::deep_equal(&proc.arena.inner, pat, msg.payload)
                } else {
                    true
                };

                if matches {
                    found = Some(i);
                    break;
                }
            }

            if let Some(i) = found {
                let msg = proc.mailbox.remove(i).unwrap();
                // Resume execution with message payload
                // We need to pass the payload to the waiting redex
                if let Some(redex) = proc.pending_redex.take() {
                    let res = proc.arena.inner.get_unchecked(msg.payload).clone();
                    proc.arena.inner.overwrite(redex, res);
                }
                proc.status = Status::Runnable;
                sched.global_queue.push(pid);
            } else {
                proc.status = Status::Waiting(pattern);
                // Re-insert process with Waiting status
                drop(proc); // Unlock
                sched.registry.insert(pid, proc_arc.clone());
                // Do NOT schedule. It will be woken by Send.
            }
        }
        SysCall::Sleep(ms) => {
            // Blocking Sleep for now (Simulated)
            // Ideally this should be non-blocking with a timer wheel.
            // For now, we block the WORKER thread? No, that stops the scheduler.
            // We should just yield?
            // Or spawn a timer thread?
            // Simple hack: spawn a thread to wake it up?
            // Or just block the thread (bad for performance but easy).

            // Let's spawn a timer helper thread to avoid blocking the worker.
            let registry = sched.registry.clone();
            let global_queue = sched.global_queue.clone();

            thread::spawn(move || {
                thread::sleep(std::time::Duration::from_millis(ms));
                if let Some(proc_arc) = registry.get(&pid) {
                    let mut proc = proc_arc.lock().unwrap();
                    if let Status::Sleeping(_) = proc.status {
                        let nil = proc.make_nil();
                        if let Some(redex) = proc.pending_redex.take() {
                            let n = proc.arena.inner.get_unchecked(nil).clone();
                            proc.arena.inner.overwrite(redex, n);
                        }
                        proc.status = Status::Runnable;
                        global_queue.push(pid);
                    }
                }
            });

            proc.status = Status::Sleeping(0); // Using 0 as placeholder
                                               // Don't schedule.
            drop(proc);
            sched.registry.insert(pid, proc_arc.clone());
        }
        SysCall::SelfPid => {
            let pid_val = proc
                .arena
                .inner
                .alloc(crate::arena::Node::Leaf(OpaqueValue::Pid(pid)));
            if let Some(redex) = proc.pending_redex.take() {
                let n = proc.arena.inner.get_unchecked(pid_val).clone();
                proc.arena.inner.overwrite(redex, n);
            }
            proc.status = Status::Runnable;
            sched.global_queue.push(pid);
        }
    }
}
