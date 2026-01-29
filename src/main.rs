// TreeCL REPL - Full Common Lisp REPL
//
// Uses Reader, Evaluator, and Printer for a complete read-eval-print loop.

use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use std::io;
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

    // Intern REPL history variables
    let mut symbols_guard = globals.symbols.write().unwrap();
    let star_1 = symbols_guard.intern_in("*", PackageId(1));
    symbols_guard.export_symbol(star_1);
    let star_2 = symbols_guard.intern_in("**", PackageId(1));
    symbols_guard.export_symbol(star_2);
    let star_3 = symbols_guard.intern_in("***", PackageId(1));
    symbols_guard.export_symbol(star_3);
    drop(symbols_guard);

    let mut scheduler = Scheduler::new();

    // Create main process (REPL Worker)
    // We keep it in the scheduler mostly, but need to borrow it for parsing?
    // Actually, we can use a dedicated REPL process that stays in the registry.
    // Or we can assume PID 1 is the REPL.
    let repl_pid = scheduler.spawn(&mut globals);

    // Bootstrap Standard Library
    if let Some(mut process) = scheduler.registry.remove(&repl_pid) {
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

        scheduler.registry.insert(repl_pid, process);
    }

    // Check CLI args
    let args: Vec<String> = std::env::args().collect();
    if args.len() > 1 {
        // Run from file
        let filename = &args[1];
        let file_content = std::fs::read_to_string(filename)?;

        // Borrow REPL Process from Scheduler to Parse/Eval
        let mut expressions = Vec::new();

        // 1. Parse all expressions
        if let Some(mut process) = scheduler.registry.remove(&repl_pid) {
            process.status = Status::Runnable;

            let mut reader = treecl::reader::Reader::new(
                &file_content,
                &mut process.arena.inner,
                globals.symbols.get_mut().unwrap(),
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

            // Return process to registry
            scheduler.registry.insert(repl_pid, process);
        }

        // 2. Execute all expressions
        for expr in expressions {
            if let Some(mut process) = scheduler.registry.remove(&repl_pid) {
                process.status = Status::Runnable;

                let mut interpreter = Interpreter::new(&mut process, &globals);
                let env = Environment::new();

                if let Err(e) = interpreter.eval(expr, &env) {
                    eprintln!("Execution Error: {:?}", e);
                    scheduler.registry.insert(repl_pid, process);
                    std::process::exit(1);
                }

                // Return process
                scheduler.registry.insert(repl_pid, process);
            } else {
                eprintln!("Process lost!");
                std::process::exit(1);
            }
        }
        return Ok(());
    }

    println!("REPL Process: {:?}", repl_pid);

    let mut rl = DefaultEditor::new().map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
    if rl.load_history("history.txt").is_err() {
        println!("No previous history.");
    }

    let mut code_buffer = String::new();

    // REPL History values (NodeIds)
    // We init them to None and lazy-load NIL from process
    let mut hist_1: Option<treecl::types::NodeId> = None;
    let mut hist_2: Option<treecl::types::NodeId> = None;
    let mut hist_3: Option<treecl::types::NodeId> = None;

    loop {
        // Run background tasks (Scheduler tick)
        // We run a few ticks to let background processes progress
        for _ in 0..10 {
            scheduler.run_tick(&mut globals);
        }

        let prompt = if code_buffer.is_empty() {
            "CL-USER> "
        } else {
            ".....> "
        };

        let readline = rl.readline(prompt);
        match readline {
            Ok(line) => {
                let _ = rl.add_history_entry(line.as_str());

                let trimmed_line = line.trim();
                if code_buffer.is_empty() && (trimmed_line == "(quit)" || trimmed_line == "(exit)")
                {
                    println!("Goodbye!");
                    break;
                }

                if !line.trim().is_empty() {
                    code_buffer.push_str(&line);
                    code_buffer.push('\n');
                }

                if is_balanced(&code_buffer) {
                    let trimmed = code_buffer.trim().to_string();
                    if trimmed.is_empty() {
                        code_buffer.clear();
                        continue;
                    }

                    // Borrow REPL Process from Scheduler to Parse/Eval
                    if let Some(mut process) = scheduler.registry.remove(&repl_pid) {
                        // Ensure process is awake?
                        process.status = Status::Runnable;

                        // Init history bindings if first run
                        if hist_1.is_none() {
                            let nil = process.make_nil();
                            hist_1 = Some(nil);
                            hist_2 = Some(nil);
                            process.set_value(star_1, nil);
                            process.set_value(star_2, nil);
                            process.set_value(star_3, nil);
                        }

                        // Read
                        let read_result = treecl::reader::Reader::new(
                            &trimmed,
                            &mut process.arena.inner,
                            globals.symbols.get_mut().unwrap(),
                            &process.readtable,
                            Some(&mut process.arrays),
                        )
                        .read();

                        match read_result {
                            Ok(expr) => {
                                // Evaluate
                                let mut interpreter = Interpreter::new(&mut process, &globals);
                                let env = Environment::new();

                                match interpreter.eval(expr, &env) {
                                    Ok(val) => {
                                        // Print result
                                        let output = print_to_string(
                                            &process.arena.inner,
                                            &*globals.symbols.read().unwrap(),
                                            val,
                                        );
                                        println!("{}", output);

                                        // Update History (*, **, ***)
                                        hist_3 = hist_2;
                                        hist_2 = hist_1;
                                        hist_1 = Some(val);

                                        process.set_value(star_1, hist_1.unwrap());
                                        process.set_value(star_2, hist_2.unwrap());
                                        process.set_value(star_3, hist_3.unwrap());
                                    }
                                    Err(e) => {
                                        println!("Error: {:?}", e);
                                    }
                                }
                            }
                            Err(e) => {
                                println!("Read error: {}", e);
                            }
                        }
                        scheduler.registry.insert(repl_pid, process);
                    } else {
                        println!("REPL Process died!");
                        break;
                    }
                    code_buffer.clear();
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            }
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }

    let _ = rl.save_history("history.txt");
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
