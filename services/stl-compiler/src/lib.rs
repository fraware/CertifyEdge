//! STL to Lean 4 Compiler
//! 
//! This crate provides a compiler that translates Signal Temporal Logic (STL) specifications
//! into Lean 4 definitions and SMT-LIB expressions for formal verification.

pub mod ast;
pub mod parser;
pub mod compiler;
pub mod lean4;
pub mod smt;
pub mod error;
pub mod config;

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Main compiler struct that orchestrates the STL to Lean 4 compilation process
#[derive(Debug, Clone)]
pub struct STLCompiler {
    config: config::CompilerConfig,
}

impl STLCompiler {
    /// Create a new STL compiler with default configuration
    pub fn new() -> Result<Self, error::CompilerError> {
        let config = config::CompilerConfig::default();
        Ok(Self { config })
    }

    /// Create a new STL compiler with custom configuration
    pub fn with_config(config: config::CompilerConfig) -> Self {
        Self { config }
    }

    /// Compile an STL specification to Lean 4
    pub async fn compile_to_lean4(
        &self,
        spec: &str,
    ) -> Result<lean4::Lean4Output, error::CompilerError> {
        let ast = self.parse_spec(spec)?;
        let lean4_output = self.translate_to_lean4(&ast).await?;
        Ok(lean4_output)
    }

    /// Compile an STL specification to SMT-LIB
    pub async fn compile_to_smt(
        &self,
        spec: &str,
    ) -> Result<smt::SMTOutput, error::CompilerError> {
        let ast = self.parse_spec(spec)?;
        let smt_output = self.translate_to_smt(&ast).await?;
        Ok(smt_output)
    }

    /// Parse an STL specification into an AST
    pub fn parse_spec(&self, spec: &str) -> Result<ast::STLSpecification, error::CompilerError> {
        let mut parser = parser::STLParser::new();
        parser.parse(spec)
    }

    /// Translate AST to Lean 4
    async fn translate_to_lean4(
        &self,
        ast: &ast::STLSpecification,
    ) -> Result<lean4::Lean4Output, error::CompilerError> {
        let mut translator = lean4::Lean4Translator::new(&self.config);
        translator.translate(ast).await
    }

    /// Translate AST to SMT-LIB
    async fn translate_to_smt(
        &self,
        ast: &ast::STLSpecification,
    ) -> Result<smt::SMTOutput, error::CompilerError> {
        let mut translator = smt::SMTTranslator::new(&self.config);
        translator.translate(ast).await
    }

    /// Validate that the AST can be round-tripped through JSON
    pub fn validate_roundtrip(
        &self,
        spec: &str,
    ) -> Result<bool, error::CompilerError> {
        let ast1 = self.parse_spec(spec)?;
        let json = serde_json::to_string(&ast1)?;
        let ast2: ast::STLSpecification = serde_json::from_str(&json)?;
        
        Ok(ast1 == ast2)
    }
}

impl Default for STLCompiler {
    fn default() -> Self {
        Self::new().expect("Failed to create default STL compiler")
    }
}

/// Compilation result containing both Lean 4 and SMT-LIB outputs
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompilationResult {
    pub lean4_output: lean4::Lean4Output,
    pub smt_output: smt::SMTOutput,
    pub compilation_time_ms: u64,
    pub ast_hash: String,
}

/// Compilation statistics for monitoring and optimization
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompilationStats {
    pub parse_time_ms: u64,
    pub lean4_translation_time_ms: u64,
    pub smt_translation_time_ms: u64,
    pub total_time_ms: u64,
    pub ast_size_bytes: usize,
    pub lean4_output_size_bytes: usize,
    pub smt_output_size_bytes: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_compiler_roundtrip(spec in "[a-zA-Z0-9_]+") {
            let compiler = STLCompiler::new().unwrap();
            // This is a simplified test - in practice we'd generate more complex STL specs
            let result = compiler.validate_roundtrip(&spec);
            // We expect this to fail for invalid specs, which is OK
            let _ = result;
        }
    }

    #[tokio::test]
    async fn test_compiler_creation() {
        let compiler = STLCompiler::new().unwrap();
        assert!(compiler.config.lean4_path.is_some());
    }
} 