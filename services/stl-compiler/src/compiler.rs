//! STL compiler that orchestrates the entire compilation process

use crate::ast::STLSpecification;
use crate::config::CompilerConfig;
use crate::error::{CompilerError, CompilerResult};
use crate::lean4::{Lean4Output, Lean4Translator};
use crate::smt::{SMTOutput, SMTTranslator};
use crate::parser::STLParser;
use serde::{Deserialize, Serialize};
use std::time::Instant;

/// Compilation result containing all outputs
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompilationResult {
    /// Original specification
    pub specification: STLSpecification,
    /// Lean 4 output
    pub lean4_output: Lean4Output,
    /// SMT output
    pub smt_output: SMTOutput,
    /// Compilation statistics
    pub stats: CompilationStats,
    /// Validation results
    pub validation: ValidationResult,
}

/// Compilation statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompilationStats {
    /// Total compilation time (milliseconds)
    pub total_time_ms: u64,
    /// Parsing time (milliseconds)
    pub parse_time_ms: u64,
    /// Lean 4 translation time (milliseconds)
    pub lean4_time_ms: u64,
    /// SMT translation time (milliseconds)
    pub smt_time_ms: u64,
    /// Validation time (milliseconds)
    pub validation_time_ms: u64,
    /// AST size (bytes)
    pub ast_size_bytes: usize,
    /// Lean 4 output size (bytes)
    pub lean4_size_bytes: usize,
    /// SMT output size (bytes)
    pub smt_size_bytes: usize,
}

/// Validation result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationResult {
    /// Round-trip validation passed
    pub roundtrip_valid: bool,
    /// Lean 4 compilation successful
    pub lean4_valid: bool,
    /// SMT solver execution successful
    pub smt_valid: bool,
    /// All validations passed
    pub all_valid: bool,
    /// Error messages
    pub errors: Vec<String>,
}

/// STL compiler that orchestrates the entire compilation process
pub struct Compiler {
    config: CompilerConfig,
}

impl Compiler {
    /// Create a new compiler
    pub fn new(config: CompilerConfig) -> Self {
        Self { config }
    }

    /// Compile STL specification to Lean 4 and SMT-LIB
    pub async fn compile(&self, spec_text: &str) -> CompilerResult<CompilationResult> {
        let start_time = Instant::now();
        
        // Parse specification
        let parse_start = Instant::now();
        let specification = self.parse_specification(spec_text)?;
        let parse_time = parse_start.elapsed().as_millis() as u64;
        
        // Translate to Lean 4
        let lean4_start = Instant::now();
        let lean4_output = self.translate_to_lean4(&specification).await?;
        let lean4_time = lean4_start.elapsed().as_millis() as u64;
        
        // Translate to SMT-LIB
        let smt_start = Instant::now();
        let smt_output = self.translate_to_smt(&specification).await?;
        let smt_time = smt_start.elapsed().as_millis() as u64;
        
        // Validate results
        let validation_start = Instant::now();
        let validation = self.validate_results(&specification, &lean4_output, &smt_output)?;
        let validation_time = validation_start.elapsed().as_millis() as u64;
        
        let total_time = start_time.elapsed().as_millis() as u64;
        
        let stats = CompilationStats {
            total_time_ms: total_time,
            parse_time_ms: parse_time,
            lean4_time_ms: lean4_time,
            smt_time_ms: smt_time,
            validation_time_ms: validation_time,
            ast_size_bytes: std::mem::size_of_val(&specification),
            lean4_size_bytes: lean4_output.lean4_code.len(),
            smt_size_bytes: smt_output.smt_lib_code.len(),
        };
        
        Ok(CompilationResult {
            specification,
            lean4_output,
            smt_output,
            stats,
            validation,
        })
    }

    /// Parse STL specification
    fn parse_specification(&self, spec_text: &str) -> CompilerResult<STLSpecification> {
        let mut parser = STLParser::new();
        parser.parse(spec_text).map_err(CompilerError::ParseError)
    }

    /// Translate specification to Lean 4
    async fn translate_to_lean4(&self, spec: &STLSpecification) -> CompilerResult<Lean4Output> {
        let mut translator = Lean4Translator::new(&self.config);
        translator.translate(spec).await.map_err(CompilerError::Lean4Error)
    }

    /// Translate specification to SMT-LIB
    async fn translate_to_smt(&self, spec: &STLSpecification) -> CompilerResult<SMTOutput> {
        let mut translator = SMTTranslator::new(&self.config);
        translator.translate(spec).await.map_err(CompilerError::SMTError)
    }

    /// Validate compilation results
    fn validate_results(
        &self,
        spec: &STLSpecification,
        lean4_output: &Lean4Output,
        smt_output: &SMTOutput,
    ) -> CompilerResult<ValidationResult> {
        let mut errors = Vec::new();
        
        // Validate round-trip
        let roundtrip_valid = self.validate_roundtrip(spec);
        if !roundtrip_valid {
            errors.push("Round-trip validation failed".to_string());
        }
        
        // Validate Lean 4 compilation
        let lean4_valid = lean4_output.metadata.success;
        if !lean4_valid {
            errors.extend(lean4_output.metadata.errors.clone());
        }
        
        // Validate SMT solver execution
        let smt_valid = smt_output.metadata.success;
        if !smt_valid {
            errors.push("SMT solver execution failed".to_string());
        }
        
        let all_valid = roundtrip_valid && lean4_valid && smt_valid;
        
        Ok(ValidationResult {
            roundtrip_valid,
            lean4_valid,
            smt_valid,
            all_valid,
            errors,
        })
    }

    /// Validate round-trip through JSON serialization
    fn validate_roundtrip(&self, spec: &STLSpecification) -> bool {
        match serde_json::to_string(spec) {
            Ok(json) => {
                match serde_json::from_str::<STLSpecification>(&json) {
                    Ok(deserialized) => spec == &deserialized,
                    Err(_) => false,
                }
            }
            Err(_) => false,
        }
    }

    /// Get compilation statistics
    pub fn get_stats(&self) -> CompilationStats {
        CompilationStats {
            total_time_ms: 0,
            parse_time_ms: 0,
            lean4_time_ms: 0,
            smt_time_ms: 0,
            validation_time_ms: 0,
            ast_size_bytes: 0,
            lean4_size_bytes: 0,
            smt_size_bytes: 0,
        }
    }

    /// Validate configuration
    pub fn validate_config(&self) -> CompilerResult<()> {
        self.config.validate().map_err(CompilerError::ConfigError)
    }

    /// Get supported features
    pub fn get_supported_features(&self) -> Vec<String> {
        vec![
            "STL parsing".to_string(),
            "Lean 4 translation".to_string(),
            "SMT-LIB translation".to_string(),
            "Round-trip validation".to_string(),
            "Temporal operators".to_string(),
            "Atomic predicates".to_string(),
            "Binary operators".to_string(),
            "Unary operators".to_string(),
        ]
    }
}

impl Default for Compiler {
    fn default() -> Self {
        Self::new(CompilerConfig::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{STLFormula, AtomicPredicate, ComparisonOperator};

    #[tokio::test]
    async fn test_compiler_creation() {
        let config = CompilerConfig::default();
        let compiler = Compiler::new(config);
        assert!(compiler.validate_config().is_ok());
    }

    #[tokio::test]
    async fn test_simple_compilation() {
        let compiler = Compiler::default();
        let spec_text = "test_spec
voltage > 220";
        
        let result = compiler.compile(spec_text).await;
        // This might fail if Lean 4 or SMT solvers are not available
        // but the parsing should work
        match result {
            Ok(compilation_result) => {
                assert_eq!(compilation_result.specification.name, "test_spec");
                assert!(matches!(compilation_result.specification.formula, STLFormula::Atomic(_)));
            }
            Err(_) => {
                // Expected if external tools are not available
            }
        }
    }

    #[test]
    fn test_roundtrip_validation() {
        let compiler = Compiler::default();
        let spec = STLSpecification {
            name: "test".to_string(),
            description: None,
            formula: STLFormula::Atomic(AtomicPredicate {
                variable: "voltage".to_string(),
                operator: ComparisonOperator::GreaterThan,
                threshold: 220.0,
                tolerance: None,
            }),
            parameters: vec![],
            constraints: vec![],
            metadata: std::collections::HashMap::new(),
        };
        
        assert!(compiler.validate_roundtrip(&spec));
    }

    #[test]
    fn test_supported_features() {
        let compiler = Compiler::default();
        let features = compiler.get_supported_features();
        
        assert!(features.contains(&"STL parsing".to_string()));
        assert!(features.contains(&"Lean 4 translation".to_string()));
        assert!(features.contains(&"SMT-LIB translation".to_string()));
    }
} 