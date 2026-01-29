use crate::arena::Node;
use crate::context::GlobalContext;
use crate::eval::{ControlSignal, EvalResult};
use crate::process::Process;
use crate::symbol::{PackageId, SymbolId};
use crate::syscall::SysCall;
use crate::types::{NodeId, OpaqueValue};

fn err(msg: &str) -> EvalResult {
    Err(ControlSignal::Error(msg.to_string()))
}

// Primitives

fn mp_spawn(_proc: &mut Process, _globals: &GlobalContext, args: &[NodeId]) -> EvalResult {
    // (mp:spawn fn)
    if args.len() != 1 {
        return err("SPAWN requires exactly 1 argument (function)");
    }

    let func = args[0];
    Err(ControlSignal::SysCall(SysCall::Spawn(func)))
}

fn mp_send(proc: &mut Process, _globals: &GlobalContext, args: &[NodeId]) -> EvalResult {
    // (mp:send pid msg)
    if args.len() != 2 {
        return err("SEND requires exactly 2 arguments (pid message)");
    }

    let pid_node_id = args[0];
    let msg = args[1];

    // Check if first arg is PID
    if let Node::Leaf(OpaqueValue::Pid(pid)) = proc.arena.inner.get_unchecked(pid_node_id) {
        Err(ControlSignal::SysCall(SysCall::Send {
            target: *pid,
            message: msg,
        }))
    } else {
        err("SEND argument 1 must be a PID")
    }
}

fn mp_receive(_proc: &mut Process, _globals: &GlobalContext, args: &[NodeId]) -> EvalResult {
    // (mp:receive [pattern])
    let pattern = if args.is_empty() { None } else { Some(args[0]) };

    Err(ControlSignal::SysCall(SysCall::Receive { pattern }))
}

pub fn mp_self(process: &mut Process, _globals: &GlobalContext, args: &[NodeId]) -> EvalResult {
    // (mp:self)
    if !args.is_empty() {
        return err("SELF take no arguments");
    }
    Ok(process.make_pid(process.pid))
}

fn mp_sleep(proc: &mut Process, _globals: &GlobalContext, args: &[NodeId]) -> EvalResult {
    // (mp:sleep ms)
    if args.len() != 1 {
        return err("SLEEP requires 1 argument (ms)");
    }

    let ms_node = proc.arena.inner.get_unchecked(args[0]);
    if let Node::Leaf(OpaqueValue::Integer(ms)) = ms_node {
        if *ms < 0 {
            return err("SLEEP argument must be non-negative");
        }
        Err(ControlSignal::SysCall(SysCall::Sleep(*ms as u64)))
    } else {
        err("SLEEP argument must be an integer")
    }
}

pub fn register_mp_primitives(globals: &mut GlobalContext) {
    let mp = {
        let mut symbols = globals.symbols.write().unwrap();
        if let Some(id) = symbols.find_package("MP") {
            id
        } else {
            symbols.create_package("MP")
        }
    };

    globals.register_primitive("SPAWN", mp, mp_spawn);
    globals.register_primitive("PROCESS-SPAWN", mp, mp_spawn); // Alias
    globals.register_primitive("SEND", mp, mp_send);
    globals.register_primitive("RECEIVE", mp, mp_receive);
    globals.register_primitive("SELF", mp, mp_self);
    globals.register_primitive("SLEEP", mp, mp_sleep);
}
