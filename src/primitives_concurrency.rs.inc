
// ============================================================================
// Concurrency Primitives
// ============================================================================

fn prim_spawn(proc: &mut crate::process::Process, _ctx: &crate::context::GlobalContext, args: &[NodeId]) -> EvalResult {
    if args.is_empty() {
        return err_helper("SPAWN: Expected function argument");
    }
    // Syscall to spawn
    Err(ControlSignal::SysCall(SysCall::Spawn(args[0])))
}

fn prim_send(proc: &mut crate::process::Process, _ctx: &crate::context::GlobalContext, args: &[NodeId]) -> EvalResult {
    if args.len() != 2 {
        return err_helper("SEND: Expected (pid message)");
    }
    // Extract PID
    let pid = match proc.arena.inner.get_unchecked(args[0]) {
        Node::Leaf(OpaqueValue::Pid(pid)) => *pid,
        _ => return err_helper("SEND: Target must be a PID"),
    };
    
    Err(ControlSignal::SysCall(SysCall::Send { target: pid, message: args[1] }))
}

fn prim_receive(proc: &mut crate::process::Process, _ctx: &crate::context::GlobalContext, args: &[NodeId]) -> EvalResult {
    let pattern = args.first().copied();
    Err(ControlSignal::SysCall(SysCall::Receive { pattern }))
}

fn prim_self(proc: &mut crate::process::Process, _ctx: &crate::context::GlobalContext, _args: &[NodeId]) -> EvalResult {
    Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Pid(proc.pid))))
}

fn prim_sleep(proc: &mut crate::process::Process, _ctx: &crate::context::GlobalContext, args: &[NodeId]) -> EvalResult {
    if args.is_empty() {
        return err_helper("SLEEP: Expected ms argument");
    }
    let ms_val = extract_number(&proc.arena.inner, args[0]);
    let ms = match ms_val {
        NumVal::Int(n) => n as u64,
        _ => return err_helper("SLEEP: Invalid duration"),
    };
    Err(ControlSignal::SysCall(SysCall::Sleep(ms)))
}
