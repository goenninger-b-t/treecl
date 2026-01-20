use crate::process::Pid;
use crate::types::NodeId;

#[derive(Debug, Clone, PartialEq)]
pub enum SysCall {
    Spawn(NodeId),
    Send { target: Pid, message: NodeId },
    Receive { pattern: Option<NodeId> },
    Sleep(u64),
    SelfPid,
}
