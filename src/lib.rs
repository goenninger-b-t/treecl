// TreeCL: Embedded ANSI Common Lisp Runtime
// This module provides a minimal lib.rs that only exports TreeCL modules.
// Legacy triage-rs modules are disabled to avoid conflicts.

pub mod types;
pub mod arena;
pub mod search;
pub mod symbol;
pub mod eval;
pub mod reader;
pub mod printer;
pub mod primitives;
pub mod clos;
pub mod conditions;
pub mod arrays;
pub mod readtable;
pub mod streams;

// Legacy modules disabled - they use incompatible Node structure
// pub mod engine;
// pub mod parser;
pub mod compiler;
pub mod debug;
pub mod process;
pub mod scheduler;
pub mod context;
pub mod syscall;
