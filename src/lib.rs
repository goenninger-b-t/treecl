// TreeCL: Embedded ANSI Common Lisp Runtime
// This module provides a minimal lib.rs that only exports TreeCL modules.
// Legacy triage-rs modules are disabled to avoid conflicts.
extern crate num_bigint;
extern crate num_traits;

pub mod arena;
pub mod arrays;
pub mod clos;
pub mod counters;
pub mod conditions;
pub mod eval;
pub mod fastmap;
pub mod hashtables;
pub mod pattern;
pub mod primitives;
pub mod printer;
pub mod reader;
pub mod readtable;
pub mod search;
pub mod streams;
pub mod symbol;
pub mod types;
pub mod tree_calculus;

// Legacy modules disabled - they use incompatible Node structure
// pub mod engine;
// pub mod parser;
pub mod compiler;
pub mod context;
pub mod mp;
pub mod process;
pub mod scheduler;
pub mod syscall;
