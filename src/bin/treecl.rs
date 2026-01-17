// TreeCL REPL - Full Common Lisp REPL
//
// Uses Reader, Evaluator, and Printer for a complete read-eval-print loop.

use std::io::{self, Write};
use triage_rs::printer::print_to_string;
use triage_rs::eval::{Interpreter, Environment};
use triage_rs::primitives::register_primitives;

fn main() -> io::Result<()> {
    println!("TreeCL v0.2.0 - ANSI Common Lisp on Tree Calculus");
    println!("Type (quit) or Ctrl-D to exit");
    println!();
    
    let mut interp = Interpreter::new();
    
    // Register all built-in primitives
    register_primitives(&mut interp);
    
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    
    let mut code_buffer = String::new();
    
    loop {
        if code_buffer.is_empty() {
             print!("CL-USER> ");
        } else {
             print!(".....> ");
        }
        stdout.flush()?;
        
        let mut input = String::new();
        if stdin.read_line(&mut input)? == 0 {
            // EOF
            if !code_buffer.is_empty() {
                 println!(); 
            } else {
                 println!("\nGoodbye!");
            }
            break;
        }
        
        // Handle input
        let trimmed_line = input.trim();
        
        // Check for quit only on empty buffer
        if code_buffer.is_empty() && (trimmed_line == "(quit)" || trimmed_line == "(exit)") {
            println!("Goodbye!");
            break;
        }
        
        if !input.trim().is_empty() {
            code_buffer.push_str(&input);
        }
        
        // Check balance
        if is_balanced(&code_buffer) {
             let trimmed = code_buffer.trim();
             if trimmed.is_empty() {
                 code_buffer.clear();
                 continue;
             }
             
             // Read
             match triage_rs::reader::Reader::new(trimmed, &mut interp.arena, &mut interp.symbols, &interp.readtable, Some(&mut interp.arrays)).read() {
                Ok(expr) => {
                    // Eval
                    let env = Environment::new();
                    match interp.eval(expr, &env) {
                        Ok(result) => {
                            // Print
                            let output = print_to_string(&interp.arena, &interp.symbols, result);
                            println!("{}", output);
                            
                            // Automatic GC check
                            interp.maybe_gc();
                        }
                        Err(signal) => {
                            println!("Control signal: {:?}", signal);
                        }
                    }
                }
                Err(e) => {
                    println!("Read error: {}", e);
                }
             }
             code_buffer.clear();
        }
        // Else: continue loop to read more lines
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
