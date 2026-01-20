use triage_rs::scheduler::Scheduler;
use triage_rs::process::{Status, ExecutionResult, Pid, Process};
use triage_rs::arena::Node; // Use standard Node
use triage_rs::types::{OpaqueValue, NodeId};
use triage_rs::context::GlobalContext;
use triage_rs::primitives::register_primitives;

fn main() {
    println!("Init...");
    let mut globals = GlobalContext::new();
    register_primitives(&mut globals);
    
    let mut scheduler = Scheduler::new();
    
    // 1. Spawn Process A and B
    let pid_a = scheduler.spawn(&mut globals);
    let pid_b = scheduler.spawn(&mut globals);
    println!("[*] Spawned Process A: {:?}, Process B: {:?}", pid_a, pid_b);
    
    // 2. Setup Message in Process A
    let msg_root = if let Some(proc_a) = scheduler.registry.get_mut(&pid_a) {
        let arena = &mut proc_a.arena.inner;
        
        // Create tree: (1 . 2)
        let v1 = arena.alloc(Node::Leaf(OpaqueValue::Integer(1)));
        let v2 = arena.alloc(Node::Leaf(OpaqueValue::Integer(2)));
        let cons = arena.alloc(Node::Fork(v1, v2));
        
        println!("[*] Created Message in A: {:?} -> (1 . 2)", cons);
        cons
    } else {
        panic!("Process A died");
    };
    
    // 3. Send Message A -> B using Scheduler
    println!("[*] Sending Message A -> B...");
    let success = scheduler.send_message(pid_a, pid_b, msg_root);
    
    if success {
        println!("[+] Send returned success");
    } else {
        println!("[-] Send failed");
        std::process::exit(1);
    }
    
    // 4. Verify Receiver B
    if let Some(proc_b) = scheduler.registry.get(&pid_b) {
        if let Some(msg) = proc_b.mailbox.front() {
            println!("[*] Process B has message from {:?}", msg.sender);
            assert_eq!(msg.sender, pid_a);
            
            let received_root = msg.payload;
            println!("[*] Received Root ID: {:?}", received_root);
            
            // Verify structural equality
            let arena_b = &proc_b.arena.inner;
            let node = arena_b.get(received_root).unwrap();
            
            println!("[*] Received Node Content: {:?}", node);
            
            match node {
                Node::Fork(l, r) => {
                    let v1 = arena_b.get(*l).unwrap();
                    let v2 = arena_b.get(*r).unwrap();
                    
                    match (v1, v2) {
                        (Node::Leaf(OpaqueValue::Integer(1)), Node::Leaf(OpaqueValue::Integer(2))) => {
                             println!("[SUCCESS] Deep Copy verified: (1 . 2)");
                        }
                        _ => {
                             println!("[FAILURE] Content mismatch: {:?} . {:?}", v1, v2);
                             std::process::exit(1);
                        }
                    }
                    
                    println!("[SUCCESS] Pointer dereference in Arena B successful.");
                }
                _ => {
                    println!("[FAILURE] Structure mismatch. Expected Fork.");
                     std::process::exit(1);
                }
            }
            
        } else {
            println!("[-] Process B mailbox empty (Failed)");
            std::process::exit(1);
        }
    }
}
