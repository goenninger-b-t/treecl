use std::sync::{Arc, RwLock};
use treecl::context::GlobalContext;
use treecl::eval::{ControlSignal, Environment, Interpreter};
use treecl::process::{Pid, Process, Status};
use treecl::types::NodeId;

fn run_until_debugger_or_done(
    proc: &mut Process,
    globals: &GlobalContext,
) -> Result<NodeId, ControlSignal> {
    let mut interpreter = Interpreter::new(proc, globals);
    // Loop until Done or Debugger
    loop {
        match interpreter.step() {
            Ok(true) => continue,
            Ok(false) => return Ok(interpreter.process.program),
            Err(ControlSignal::Error(msg)) => {
                // Mimic execute_slice: invoke signal_error
                match interpreter.signal_error(&msg) {
                    Err(ControlSignal::Debugger(cond)) => {
                        interpreter.process.status = Status::Debugger(cond.clone());
                        return Err(ControlSignal::Debugger(cond));
                    }
                    Err(e) => return Err(e),
                    Ok(_) => panic!("signal_error returned Ok"),
                }
            }
            Err(e) => return Err(e),
        }
    }
}

#[test]
fn test_debugger_status_transition() {
    let mut globals = GlobalContext::new();
    treecl::primitives::register_primitives(&mut globals);

    let mut proc = Process::new(
        Pid {
            node: 0,
            id: 1,
            serial: 0,
        },
        NodeId(0),
        &globals,
    );

    let input = "(error \"Debug Me\")";
    let expr = treecl::reader::read_from_string(
        input,
        &mut proc.arena.inner,
        &mut *globals.symbols.write().unwrap(),
    )
    .unwrap();

    proc.program = expr;
    proc.status = Status::Runnable;
    proc.execution_mode = treecl::process::ExecutionMode::Eval;
    proc.current_env = Some(Environment::new());
    proc.continuation_stack
        .push(treecl::eval::Continuation::Done);

    let result = run_until_debugger_or_done(&mut proc, &globals);

    match result {
        Err(ControlSignal::Debugger(cond)) => {
            if let Status::Debugger(s_cond) = &proc.status {
                assert_eq!(cond, *s_cond);
                assert_eq!(cond.format_control.as_deref(), Some("Debug Me"));
            } else {
                panic!("Process status mismatch: {:?}", proc.status);
            }
        }
        _ => panic!("Expected Debugger signal, got {:?}", result),
    }
}

#[test]
fn test_restart_invocation() {
    let mut globals = GlobalContext::new();
    treecl::primitives::register_primitives(&mut globals);

    let mut proc = Process::new(
        Pid {
            node: 0,
            id: 1,
            serial: 0,
        },
        NodeId(0),
        &globals,
    );

    // Manually register a restart "CONTINUE"
    let restart_name = globals.symbols.write().unwrap().intern("CONTINUE");

    // Create a function for the restart: (lambda () 42)
    let lambda_sym = globals.symbols.write().unwrap().intern("LAMBDA");
    let params = proc.make_nil();
    let body_form = proc.make_integer(42);
    let nil = proc.make_nil();
    let body_list = proc
        .arena
        .inner
        .alloc(treecl::arena::Node::Fork(body_form, nil));

    let lambda_op = proc.arena.inner.alloc(treecl::arena::Node::Leaf(
        treecl::types::OpaqueValue::Symbol(lambda_sym.0),
    ));

    let lambda_expr = proc.make_list(&[lambda_op, params, body_list]);

    // Eval to get closure
    let func_input = "(function (lambda () 42))";
    let func_expr = treecl::reader::read_from_string(
        func_input,
        &mut proc.arena.inner,
        &mut *globals.symbols.write().unwrap(),
    )
    .unwrap();

    // Eval to get closure
    let mut interpreter = Interpreter::new(&mut proc, &globals);
    interpreter.process.program = func_expr;
    interpreter.process.execution_mode = treecl::process::ExecutionMode::Eval;
    interpreter.process.current_env = Some(Environment::new());
    interpreter
        .process
        .continuation_stack
        .push(treecl::eval::Continuation::Done);

    loop {
        match interpreter.step() {
            Ok(true) => continue,
            Ok(false) => break,
            Err(e) => panic!("Failed to compile restart function: {:?}", e),
        }
    }
    let restart_func = interpreter.process.program; // The closure

    // Push restart
    let restart = treecl::conditions::Restart {
        name: restart_name,
        function: restart_func,
        report: Some("Return 42".to_string()),
        interactive: None,
        test: None,
    };

    proc.conditions.push_restarts(vec![restart]);

    // Now raise error
    let input = "(error \"Foo\")";
    let expr = treecl::reader::read_from_string(
        input,
        &mut proc.arena.inner,
        &mut *globals.symbols.write().unwrap(),
    )
    .unwrap();

    proc.program = expr;
    proc.status = Status::Runnable;
    proc.execution_mode = treecl::process::ExecutionMode::Eval;
    proc.current_env = Some(Environment::new());
    proc.continuation_stack.clear();
    proc.continuation_stack
        .push(treecl::eval::Continuation::Done);

    let result = run_until_debugger_or_done(&mut proc, &globals);

    match result {
        Err(ControlSignal::Debugger(_)) => {
            // Check Restarts
            let restarts = proc.conditions.find_restarts();
            assert!(!restarts.is_empty(), "Should have restarts");

            let continue_rss = restarts.iter().find(|r| {
                let s_name = globals
                    .symbols
                    .read()
                    .unwrap()
                    .symbol_name(r.name)
                    .unwrap_or("")
                    .to_string();
                s_name.eq_ignore_ascii_case("CONTINUE")
            });

            assert!(continue_rss.is_some(), "Continue restart not found");
            let r = continue_rss.unwrap().clone();

            // Invoke restart
            let func = r.function;
            let args = proc.make_nil();
            let bare_call = proc
                .arena
                .inner
                .alloc(treecl::arena::Node::Fork(func, args));

            proc.program = bare_call;
            proc.status = Status::Runnable;
            proc.execution_mode = treecl::process::ExecutionMode::Eval;

            // Resume
            let resumed_result = run_until_debugger_or_done(&mut proc, &globals);

            match resumed_result {
                Ok(val_node) => {
                    // Should be 42
                    if let treecl::arena::Node::Leaf(treecl::types::OpaqueValue::Integer(i)) =
                        proc.arena.inner.get_unchecked(val_node)
                    {
                        assert_eq!(*i, 42);
                    } else {
                        use treecl::printer::print_to_string;
                        let s = print_to_string(
                            &proc.arena.inner,
                            &*globals.symbols.read().unwrap(),
                            val_node,
                        );
                        panic!("Expected 42, got {}", s);
                    }
                }
                Err(e) => panic!("Expected successful restart, got {:?}", e),
            }
        }
        _ => panic!("Expected Debugger for first run"),
    }
}
