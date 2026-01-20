use triage_rs::scheduler::Scheduler;
use triage_rs::process::{Status, ExecutionResult};
use triage_rs::arena::Node;
use triage_rs::types::OpaqueValue;
use triage_rs::context::GlobalContext;

fn main() {
    println!("TreeCL BeamVM Verification");
    println!("==========================");
    
    let mut globals = GlobalContext::new();
    let mut scheduler = Scheduler::new();
    
    // 1. Spawn Process
    let pid = scheduler.spawn(&mut globals);
    println!("[*] Spawned Process {:?}", pid);
    
    // 2. Setup Code (Identity Combinator I = ((nil nil) (nil nil))) applied to 42
    // We need to access the process mutably
    if let Some(proc) = scheduler.registry.get_mut(&pid) {
        let arena = &mut proc.arena.inner;
        
        // Create Nil (△)
        let nil = arena.alloc(Node::Leaf(OpaqueValue::Nil));
        
        // Create K = (△ △) = Fork(nil, nil)
        let k = arena.alloc(Node::Fork(nil, nil));
        
        // Create I = (K K) = Fork(k, k)
        let i = arena.alloc(Node::Fork(k, k));
        
        // Create Value 42
        let val = arena.alloc(Node::Leaf(OpaqueValue::Integer(42)));
        
        // Create Program: (I 42) = Fork(i, val)
        let program = arena.alloc(Node::Fork(i, val));
        
        proc.program = program;
        println!("[*] Loaded Program: (I 42)");
    }
    
    // 3. Schedule
    scheduler.schedule(pid);
    println!("[*] Scheduled Process {:?}", pid);
    
    // 4. Run
    println!("[*] Running Scheduler...");
    let mut ticks = 0;
    loop {
        let working = scheduler.run_tick(&mut globals);
        ticks += 1;
        
        if let Some(proc) = scheduler.registry.get(&pid) {
            if proc.status == Status::Terminated {
                println!("[+] Process Terminated in {} ticks ({} reductions)", ticks, proc.reduction_count);
                
                // Verify Result in Arena
                // Result is stored in proc.program
                let result_id = proc.program;
                let result_node = proc.arena.get(result_id).unwrap();
                println!("[+] Result Node: {:?}", result_node);
                
                if let Node::Leaf(OpaqueValue::Integer(42)) = result_node {
                    println!("[SUCCESS] Result is 42");
                } else {
                    println!("[FAILURE] Result is {:?}", result_node);
                    std::process::exit(1);
                }
                break;
            }
        }
        
        if !working {
            println!("[!] Scheduler Idle but process not terminated?");
            break;
        }
        
        if ticks > 100 {
            println!("[!] Timeout");
            break;
        }
    }
}
