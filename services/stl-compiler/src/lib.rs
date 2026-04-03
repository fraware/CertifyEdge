//! STL to Lean 4 Compiler
//!
//! Translates Signal Temporal Logic (STL) specifications into Lean 4 and SMT-LIB.

pub mod ast;
pub mod compiler;
pub mod config;
pub mod error;
pub mod lean4;
pub mod parser;
pub mod smt;

pub use compiler::{CompilationResult, CompilationStats, Compiler, ValidationResult};
pub use config::CompilerConfig;
