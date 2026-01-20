// TreeCL REPL - Full Common Lisp REPL
//
// Uses Reader, Evaluator, and Printer for a complete read-eval-print loop.

use std::io::{self, Write};
use triage_rs::printer::print_to_string;
use triage_rs::primitives::register_primitives;
use triage_rs::context::GlobalContext;
use triage_rs::process::{Status};
use triage_rs::scheduler::Scheduler;

fn main() -> io::Result<()> {
    println!("TreeCL v0.2.0 - ANSI Common Lisp on Tree Calculus");
    println!("Type (quit) or Ctrl-D to exit");
    println!();
    
    let mut globals = GlobalContext::new();
    // Register all built-in primitives
    register_primitives(&mut globals);
    
    let mut scheduler = Scheduler::new();
    
    // Create main process (REPL Worker)
    // We keep it in the scheduler mostly, but need to borrow it for parsing?
    // Actually, we can use a dedicated REPL process that stays in the registry.
    // Or we can assume PID 1 is the REPL.
    let repl_pid = scheduler.spawn(&mut globals);
    println!("REPL Process: {:?}", repl_pid);
    
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    
    let mut code_buffer = String::new();
    
    loop {
        // Run background tasks (Scheduler tick)
        // We run a few ticks to let background processes progress
        for _ in 0..10 {
            scheduler.run_tick(&mut globals);
        }

        if code_buffer.is_empty() {
             print!("CL-USER> ");
        } else {
             print!(".....> ");
        }
        stdout.flush()?;
        
        let mut input = String::new();
        if stdin.read_line(&mut input)? == 0 {
            break; // EOF
        }
        
        let trimmed_line = input.trim();
        if code_buffer.is_empty() && (trimmed_line == "(quit)" || trimmed_line == "(exit)") {
            println!("Goodbye!");
            break;
        }
        
        if !input.trim().is_empty() {
            code_buffer.push_str(&input);
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

                 // Read
                 let read_result = triage_rs::reader::Reader::new(
                     &trimmed, 
                     &mut process.arena.inner, 
                     &mut globals.symbols, 
                     &process.readtable, 
                     Some(&mut process.arrays)
                 ).read();
                 
                 match read_result {
                    Ok(expr) => {
                        // Compile user input to Tree Calculus
                        let mut compiler = triage_rs::compiler::Compiler::new(&mut process, &globals);
                        match compiler.compile_expr(expr) {
                            Ok(program) => {
                                // Set program and run via Scheduler
                                process.program = program;
                                process.status = triage_rs::process::Status::Runnable;
                                
                                // Return process to scheduler to run it
                                scheduler.registry.insert(repl_pid, process);
                                scheduler.schedule(repl_pid);
                                
                                // Run until all tasks done (or blocked)
                                scheduler.run_until_empty(&mut globals);
                                
                                // Retrieve REPL process to print result
                                if let Some(mut proc) = scheduler.registry.remove(&repl_pid) {
                                    // Print result (program is now the normal form)
                                    // TODO: If proc failed/panicked? Status would be Terminated.
                                    // We assume generic success for now.
                                    let output = print_to_string(&proc.arena.inner, &globals.symbols, proc.program);
                                    println!("{}", output);
                                    process = proc; // Keep for next loop
                                } else {
                                    println!("REPL Process lost!");
                                    break;
                                }
                            }
                            Err(e) => {
                                println!("Compilation Error: {}", e);
                                // Return unmodified process
                                scheduler.registry.insert(repl_pid, process);
                            }
                        }
                    }
                     Err(e) => {
                        println!("Read error: {}", e);
                        scheduler.registry.insert(repl_pid, process);
                    }
                 }
                 
                 // Retrieve process for next iteration
                 if let Some(p) = scheduler.registry.remove(&repl_pid) {
                     process = p;
                 } else {
                     println!("REPL Process lost!");
                     break;
                 }
             } else {
                 println!("REPL Process died!");
                 break;
             }
             code_buffer.clear();
        }
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
             if c == '\n' { in_comment = false; }
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
