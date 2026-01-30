// TreeCL REPL - Full Common Lisp REPL
//
// Uses Reader, Evaluator, and Printer for a complete read-eval-print loop.

use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use std::io;
use std::sync::Arc;
use treecl::context::GlobalContext;
use treecl::eval::{Environment, Interpreter};
use treecl::primitives::register_primitives;
use treecl::printer::print_to_string;
use treecl::process::Status;
use treecl::scheduler::Scheduler;
use treecl::symbol::PackageId;

const INIT_LISP: &str = include_str!("init.lisp");

fn main() -> io::Result<()> {
    println!("TreeCL v0.2.0 - DEBUG BUILD - ANSI Common Lisp on Tree Calculus");
    println!("Type (quit) or Ctrl-D to exit");
    println!();

    let mut globals = GlobalContext::new();
    // Register all built-in primitives
    register_primitives(&mut globals);
    // Register MP primitives
    treecl::mp::register_mp_primitives(&mut globals);

    // Intern REPL history variables
    let mut symbols_guard = globals.symbols.write().unwrap();
    let star_1 = symbols_guard.intern_in("*", PackageId(1));
    symbols_guard.export_symbol(star_1);
    let star_2 = symbols_guard.intern_in("**", PackageId(1));
    symbols_guard.export_symbol(star_2);
    let star_3 = symbols_guard.intern_in("***", PackageId(1));
    symbols_guard.export_symbol(star_3);
    let slash_1 = symbols_guard.intern_in("/", PackageId(1));
    symbols_guard.export_symbol(slash_1);
    let slash_2 = symbols_guard.intern_in("//", PackageId(1));
    symbols_guard.export_symbol(slash_2);
    let slash_3 = symbols_guard.intern_in("///", PackageId(1));
    symbols_guard.export_symbol(slash_3);
    drop(symbols_guard);

    // Wrap globals in Arc for sharing
    let globals = Arc::new(globals);

    let mut scheduler = Scheduler::new();

    // Create main process (REPL Worker)
    let repl_pid = scheduler.spawn(&globals, treecl::types::NodeId(0)); // spawn takes &GlobalContext, func

    // Bootstrap Standard Library
    if let Some(proc_ref) = scheduler.registry.get(&repl_pid) {
        let mut process = proc_ref.lock().unwrap();
        process.status = Status::Runnable;

        let mut interpreter = Interpreter::new(&mut process, &globals);
        let env = Environment::new();

        // Scope for reader
        let mut expressions = Vec::new();
        {
            let mut symbols_guard = globals.symbols.write().unwrap();
            let mut reader = treecl::reader::Reader::new(
                INIT_LISP,
                &mut interpreter.process.arena.inner,
                &mut *symbols_guard,
                &interpreter.process.readtable,
                Some(&mut interpreter.process.arrays),
            );

            loop {
                match reader.read() {
                    Ok(expr) => expressions.push(expr),
                    Err(treecl::reader::ReaderError::UnexpectedEof) => break,
                    Err(e) => {
                        eprintln!("Bootstrap Error (Parse): {}", e);
                        std::process::exit(1);
                    }
                }
            }
        }

        for expr in expressions {
            if let Err(e) = interpreter.eval(expr, &env) {
                eprintln!("Bootstrap Error (Eval): {:?}", e);
                std::process::exit(1);
            }
        }
    }

    // Check CLI args
    let args: Vec<String> = std::env::args().collect();
    if args.len() > 1 {
        // Run from file
        let filename = &args[1];
        let file_content = std::fs::read_to_string(filename)?;

        let mut expressions = Vec::new();

        // 1. Parse all expressions
        if let Some(proc_ref) = scheduler.registry.get(&repl_pid) {
            let mut process_guard = proc_ref.lock().unwrap();
            let process = &mut *process_guard;
            process.status = Status::Runnable;

            let mut symbols_guard = globals.symbols.write().unwrap();
            let mut reader = treecl::reader::Reader::new(
                &file_content,
                &mut process.arena.inner,
                &mut *symbols_guard,
                &process.readtable,
                Some(&mut process.arrays),
            );

            loop {
                match reader.read() {
                    Ok(expr) => expressions.push(expr),
                    Err(treecl::reader::ReaderError::UnexpectedEof) => break,
                    Err(e) => {
                        eprintln!("Read Error: {}", e);
                        std::process::exit(1);
                    }
                }
            }
        }

        // 2. Execute all expressions via Scheduler
        // Wrap in (PROGN ...) so they run sequentially in one process context
        if let Some(proc_ref) = scheduler.registry.get(&repl_pid) {
            let mut process_guard = proc_ref.lock().unwrap();
            let process = &mut *process_guard;

            // Construct PROGN
            if !expressions.is_empty() {
                let progn_sym = globals.special_forms.progn;
                let progn_val = treecl::types::OpaqueValue::Symbol(progn_sym.0);
                let progn_node = process
                    .arena
                    .inner
                    .alloc(treecl::arena::Node::Leaf(progn_val));

                let body_list = process.make_list(&expressions);
                let program = process
                    .arena
                    .inner
                    .alloc(treecl::arena::Node::Fork(progn_node, body_list));

                process.program = program;
                process.execution_mode = treecl::process::ExecutionMode::Eval;
                // Reset stack just in case
                process.continuation_stack.clear();
                process
                    .continuation_stack
                    .push(treecl::eval::Continuation::Done);
                process.current_env = Some(treecl::eval::Environment::new());
                process.status = Status::Runnable;
            }
        }

        // Start Scheduler (workers will pick up the process)
        scheduler.start(globals.clone());

        // Wait for completion
        loop {
            let mut finished = false;
            let mut exit_code = 0;

            if let Some(proc_ref) = scheduler.registry.get(&repl_pid) {
                let proc = proc_ref.lock().unwrap();
                if proc.status == Status::Terminated {
                    finished = true;
                    exit_code = 0;
                } else if let Status::Failed(msg) = &proc.status {
                    eprintln!("Execution Failed: {}", msg);
                    finished = true;
                    exit_code = 1;
                }
            }

            if finished {
                std::process::exit(exit_code);
            }

            // Sleep to avoid busy loop while waiting for workers
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }

    // Start Scheduler Threads
    scheduler.start(globals.clone());

    println!("REPL Process: {:?}", repl_pid);

    // Channels for REPL I/O
    let (input_tx, input_rx) = std::sync::mpsc::channel::<String>();
    let (prompt_tx, prompt_rx) = std::sync::mpsc::channel::<String>();

    // Input Thread
    std::thread::spawn(move || {
        let mut rl = DefaultEditor::new().expect("Failed to init readline");
        if rl.load_history("history.txt").is_err() {
            println!("No previous history.");
        }

        loop {
            // Wait for prompt request
            let prompt = match prompt_rx.recv() {
                Ok(p) => p,
                Err(_) => break, // Main thread likely died
            };

            match rl.readline(&prompt) {
                Ok(line) => {
                    let _ = rl.add_history_entry(line.as_str());
                    if input_tx.send(line).is_err() {
                        break;
                    }
                }
                Err(ReadlineError::Interrupted) => {
                    println!("CTRL-C");
                    if input_tx.send("".to_string()).is_err() {
                        break;
                    }
                }
                Err(ReadlineError::Eof) => {
                    println!("CTRL-D");
                    let _ = input_tx.send("(exit)".to_string());
                    break;
                }
                Err(err) => {
                    println!("Error: {:?}", err);
                    let _ = input_tx.send("(exit)".to_string());
                    break;
                }
            }
        }
        let _ = rl.save_history("history.txt");
    });

    let mut code_buffer = String::new();

    // REPL History values (NodeIds)
    let mut hist_1: Option<treecl::types::NodeId> = None;
    let mut hist_2: Option<treecl::types::NodeId> = None;

    // Initial prompt
    let _ = prompt_tx.send("CL-USER> ".to_string());
    let mut waiting_for_input = true;

    loop {
        // Non-blocking Input Check
        if let Ok(line) = input_rx.try_recv() {
            let trimmed_line = line.trim();

            if code_buffer.is_empty() && (trimmed_line == "(quit)" || trimmed_line == "(exit)") {
                println!("Goodbye!");
                break; // Exit Main Loop
            }

            if !line.trim().is_empty() {
                code_buffer.push_str(&line);
                code_buffer.push('\n');
            }

            if is_balanced(&code_buffer) {
                let trimmed = code_buffer.trim().to_string();
                if trimmed.is_empty() {
                    code_buffer.clear();
                    // Request next prompt
                    let _ = prompt_tx.send("CL-USER> ".to_string());
                } else {
                    // Evaluate!
                    if let Some(proc_ref) = scheduler.registry.get(&repl_pid) {
                        let mut process_guard = proc_ref.lock().unwrap();
                        let process = &mut *process_guard;

                        if process.status != Status::Terminated
                            && process.status != Status::Runnable
                        {
                            // If running, we might clash.
                            // But usually REPL waits.
                        }

                        process.status = Status::Runnable;

                        // Init history bindings if first run
                        if hist_1.is_none() {
                            let nil = process.make_nil();
                            hist_1 = Some(nil);
                            hist_2 = Some(nil);
                            process.set_value(star_1, nil);
                            process.set_value(star_2, nil);
                            process.set_value(star_3, nil);
                            process.set_value(slash_1, nil);
                            process.set_value(slash_2, nil);
                            process.set_value(slash_3, nil);
                        }

                        let input_source = code_buffer.clone();
                        code_buffer.clear(); // Clear buffer for next command

                        // Check for Debug Commands
                        let trimmed = input_source.trim();
                        if trimmed == ":bt" {
                            println!("Backtrace:");
                            for (i, frame) in process.continuation_stack.iter().rev().enumerate() {
                                println!("  {}: {:?}", i, frame);
                            }
                            let _ = prompt_tx.send("[DEBUG]> ".to_string());
                            waiting_for_input = true;
                        } else if trimmed == ":q" {
                            // Abort to top level
                            process.status = Status::Terminated; // Or just reset?
                            process.program = process.make_nil();
                            process.continuation_stack.clear();

                            // This will cause the polling loop to see 'Terminated' and reset to CL-USER
                            waiting_for_input = false;
                        } else if trimmed.starts_with(":r ") {
                            if let Ok(idx) = trimmed[3..].trim().parse::<usize>() {
                                let restarts = process.conditions.find_restarts();
                                if idx < restarts.len() {
                                    let r = restarts[idx].clone();
                                    // Invoke restart function
                                    // (func)
                                    let func = r.function;
                                    let args = process.make_nil(); // No args for simple restart invocation for now?
                                                                   // Actually usually restarts might take args if interactive, but here we assume thunks

                                    // Helper to make call: (func)
                                    let bare_call = process
                                        .arena
                                        .inner
                                        .alloc(treecl::arena::Node::Fork(func, args));
                                    process.program = bare_call;

                                    // If we are debugging, we want to return result to debugger?
                                    // Or if restart handles it, we exit debugger.
                                    // Let's assume restart handles it -> Exit debugger.
                                    // We do NOT push DebuggerRest.

                                    process.status = Status::Runnable;
                                    waiting_for_input = false;
                                    scheduler.schedule(repl_pid);
                                } else {
                                    println!("Invalid restart index");
                                    let _ = prompt_tx.send("[DEBUG]> ".to_string());
                                    waiting_for_input = true;
                                }
                            } else {
                                println!("Invalid restart format");
                                let _ = prompt_tx.send("[DEBUG]> ".to_string());
                                waiting_for_input = true;
                            }
                        } else {
                            match treecl::reader::read_from_string(
                                &input_source,
                                &mut process.arena.inner,
                                &mut *globals.symbols.write().unwrap(),
                            ) {
                                Ok(expr) => {
                                    // TCO Setup
                                    process.program = expr;
                                    process.execution_mode = treecl::process::ExecutionMode::Eval;

                                    // If in debugger, push DebuggerRest and preserve env
                                    if let Status::Debugger(cond) = &process.status {
                                        process.continuation_stack.push(
                                            treecl::eval::Continuation::DebuggerRest {
                                                condition: cond.clone(),
                                            },
                                        );
                                        // Do not reset env! Use the one from the crash site.
                                        if process.current_env.is_none() {
                                            process.current_env =
                                                Some(treecl::eval::Environment::new());
                                        }
                                    } else {
                                        // Normal REPL: Reset stack and env
                                        process.continuation_stack.clear();
                                        process
                                            .continuation_stack
                                            .push(treecl::eval::Continuation::Done);
                                        process.reduction_count = 0;
                                        process.current_env =
                                            Some(treecl::eval::Environment::new());
                                    }

                                    process.status = Status::Runnable;
                                    scheduler.schedule(repl_pid);
                                    waiting_for_input = false;
                                }
                                Err(e) => {
                                    eprintln!("Parse Error: {:?}", e);
                                    let _ = prompt_tx.send("CL-USER> ".to_string());
                                    waiting_for_input = true;
                                }
                            }
                        }
                    }
                }
            } else {
                // Incomplete
                let _ = prompt_tx.send(".....> ".to_string());
            }
        }

        // Post-Input Logic (Polling Execution)
        // Check REPL process status
        if !waiting_for_input {
            if let Some(proc_ref) = scheduler.registry.get(&repl_pid) {
                let mut finished = false;
                let mut result_node = None;
                let mut debugger_state = None;

                {
                    let mut proc = proc_ref.lock().unwrap();
                    match &proc.status {
                        Status::Terminated => {
                            finished = true;
                            result_node = Some(proc.program);
                        }
                        Status::Failed(msg) => {
                            eprintln!("Error: {}", msg);
                            finished = true;
                        }
                        Status::Debugger(cond) => {
                            // Captured condition
                            debugger_state = Some(cond.clone());
                        }
                        _ => {}
                    }
                }

                if let Some(cond) = debugger_state {
                    // We are in debugger.
                    // If we just arrived (waiting_for_input was false), print info
                    if !waiting_for_input {
                        println!("\n*** Debugger Entered ***");

                        let proc = proc_ref.lock().unwrap();
                        let type_name = proc
                            .conditions
                            .get_type_name(cond.condition_type)
                            .map(|s| s.as_str())
                            .unwrap_or("Condition");

                        println!("Processing {} in Process {}", type_name, proc.pid);

                        if let Some(fmt) = &cond.format_control {
                            let symbols = globals.symbols.read().unwrap();
                            let msg = treecl::printer::format(
                                &proc.arena.inner,
                                &*symbols,
                                fmt,
                                &cond.format_arguments,
                            );
                            println!("{}: {}", type_name, msg);
                        } else {
                            println!("{}: {:?}", type_name, cond);
                        }

                        println!("Restarts:");
                        let restarts = proc.conditions.find_restarts();
                        for (i, r) in restarts.iter().enumerate() {
                            let name = globals
                                .symbols
                                .read()
                                .unwrap()
                                .symbol_name(r.name)
                                .unwrap_or("?")
                                .to_string();
                            println!("  {}: [{}] {}", i, name, r.report.as_deref().unwrap_or(""));
                        }
                        println!("\nDebug commands: :bt (backtrace), :r N (restart N), :q (abort)");
                    } else {
                        // We returned from a debug-eval step
                        let proc = proc_ref.lock().unwrap();
                        let s = print_to_string(
                            &proc.arena.inner,
                            &*globals.symbols.read().unwrap(),
                            proc.program,
                        );
                        // Print result with "=> " to distinguish
                        println!("=> {}", s);
                    }

                    let _ = prompt_tx.send("[DEBUG]> ".to_string());
                    waiting_for_input = true;
                } else if finished {
                    if let Some(res) = result_node {
                        let proc_guard = proc_ref.lock().unwrap();
                        let s = print_to_string(
                            &proc_guard.arena.inner,
                            &*globals.symbols.read().unwrap(),
                            res,
                        );
                        println!("{}", s);

                        // Update History would go here
                    }

                    // Ready for next input
                    let _ = prompt_tx.send("CL-USER> ".to_string());
                    waiting_for_input = true;
                }
            }
        }

        // Sleep to prevent busy loop
        std::thread::sleep(std::time::Duration::from_millis(10));
    }

    Ok(())
}

fn is_balanced(s: &str) -> bool {
    let mut depth = 0;
    let mut in_string = false;
    let mut escape = false;
    let mut in_comment = false;

    for c in s.chars() {
        if in_comment {
            if c == '\n' {
                in_comment = false;
            }
            continue;
        }

        if escape {
            escape = false;
            continue;
        }

        match c {
            '\\' if in_string => escape = true,
            '"' => in_string = !in_string,
            ';' if !in_string => in_comment = true,
            '(' if !in_string => depth += 1,
            ')' if !in_string => depth -= 1,
            _ => {}
        }
    }

    depth <= 0
}
