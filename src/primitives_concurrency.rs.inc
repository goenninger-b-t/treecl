
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
    let pid_val = extract_number(&proc.arena.inner, args[0]);
    let pid = match pid_val {
        NumVal::Int(n) => crate::process::Pid(n as u32),
        _ => return err_helper("SEND: Invalid PID"),
    };
    
    Err(ControlSignal::SysCall(SysCall::Send { target: pid, message: args[1] }))
}

fn prim_receive(proc: &mut crate::process::Process, _ctx: &crate::context::GlobalContext, _args: &[NodeId]) -> EvalResult {
    // TODO: Pattern matching support in args
    Err(ControlSignal::SysCall(SysCall::Receive { pattern: None }))
}

fn prim_self(proc: &mut crate::process::Process, _ctx: &crate::context::GlobalContext, _args: &[NodeId]) -> EvalResult {
    Ok(proc.arena.inner.alloc(Node::Leaf(OpaqueValue::Integer(proc.pid.0 as i64))))
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
