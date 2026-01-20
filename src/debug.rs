use crate::process::{Pid, StepMode};
use crate::types::NodeId;
use std::collections::HashMap;
use std::sync::mpsc::Sender;
use std::io::{BufRead, BufReader, Write};
use std::net::TcpStream;
use serde::{Deserialize, Serialize};

/// Commands sent from Debugger (Thread) to Scheduler (Main Loop)
#[derive(Debug)]
pub enum DebugCommand {
    Pause(Pid),
    Resume(Pid),
    StepInto(Pid),
    StepOver(Pid),
    StepOut(Pid),
    GetStack(Pid, Sender<Vec<NodeId>>),
    GetBindings(Pid, Sender<String>), // JSON string for now? Or structured data
}

/// Events/Updates sent from Scheduler to Debugger
#[derive(Debug)]
pub enum DebugEvent {
    Paused(Pid),
    Terminated(Pid),
    HitBreakpoint(Pid),
}

#[derive(Serialize, Deserialize, Debug)]
struct WireCommand {
    command: String,
    pid: Option<u32>, // Optional because some commands might not need it?
    node_id: Option<u32> // e.g. for distributed PID
}

#[derive(Serialize, Deserialize, Debug)]
enum WireResponse {
    Ok,
    Error(String),
    Stack(Vec<NodeId>),
    Bindings(String),
}

pub struct DebugServer {
    cmd_sender: Sender<DebugCommand>,
    port: u16,
}

impl DebugServer {
    pub fn new(cmd_sender: Sender<DebugCommand>, port: u16) -> Self {
        Self { cmd_sender, port }
    }

    pub fn start(&self) {
        let sender = self.cmd_sender.clone();
        let port = self.port;
        
        std::thread::spawn(move || {
            let listener = std::net::TcpListener::bind(format!("127.0.0.1:{}", port))
                .expect("Failed to bind debug port");
            println!("Debug Server listening on port {}", port);
            
            for stream in listener.incoming() {
                if let Ok(mut stream) = stream {
                    println!("Debugger connected");
                    // Simple text protocol for now
                    // TODO: Implement JSON protocol loop
                    Self::handle_client(stream, sender.clone());
                }
            }
        });
    }

    fn handle_client(mut stream: TcpStream, sender: Sender<DebugCommand>) {
        let mut reader = BufReader::new(stream.try_clone().expect("Clone stream failed"));
        let mut line = String::new();

        while reader.read_line(&mut line).unwrap_or(0) > 0 {
            if line.trim().is_empty() {
                line.clear();
                continue;
            }

            match serde_json::from_str::<WireCommand>(&line) {
                Ok(wire_cmd) => {
                    // Map WireCommand to internal DebugCommand
                    // Note: This is simplified. Real implementation needs more robust mapping.
                    // Also need to handle responses (requires separate channel or synced call).
                    
                    let pid = if let Some(id) = wire_cmd.pid {
                         Pid { node: 0, id, serial: 0 } // Assuming local node 0 for now
                    } else {
                         // Default generic pid? or Error?
                         Pid { node: 0, id: 0, serial: 0 }
                    };

                    let internal_cmd = match wire_cmd.command.as_str() {
                        "pause" => Some(DebugCommand::Pause(pid)),
                        "resume" => Some(DebugCommand::Resume(pid)),
                        "step_into" => Some(DebugCommand::StepInto(pid)),
                        "step_over" => Some(DebugCommand::StepOver(pid)),
                        "step_out" => Some(DebugCommand::StepOut(pid)),
                        "get_stack" => {
                             let (tx, rx) = std::sync::mpsc::channel();
                             sender.send(DebugCommand::GetStack(pid, tx)).unwrap();
                             if let Ok(stack) = rx.recv() {
                                 let resp = WireResponse::Stack(stack);
                                 let json = serde_json::to_string(&resp).unwrap();
                                 let _ = stream.write_all(json.as_bytes());
                                 let _ = stream.write_all(b"\n");
                             }
                             None // Already handled response
                        },
                         "get_bindings" => {
                             let (tx, rx) = std::sync::mpsc::channel();
                             sender.send(DebugCommand::GetBindings(pid, tx)).unwrap();
                             if let Ok(bindings) = rx.recv() {
                                 let resp = WireResponse::Bindings(bindings);
                                 let json = serde_json::to_string(&resp).unwrap();
                                 let _ = stream.write_all(json.as_bytes());
                                 let _ = stream.write_all(b"\n");
                             }
                             None
                        },
                        _ => None
                    };

                    if let Some(cmd) = internal_cmd {
                        let _ = sender.send(cmd);
                        // Send simple OK?
                        let _ = stream.write_all(b"{\"status\":\"ok\"}\n");
                    }
                }
                Err(e) => {
                    eprintln!("JSON Parse Error: {}", e);
                    let _ = stream.write_all(format!("{{\"error\":\"{}\"}}\n", e).as_bytes());
                }
            }
            line.clear();
        }
    }
}
