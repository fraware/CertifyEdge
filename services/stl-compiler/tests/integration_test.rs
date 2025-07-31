//! Integration tests for STL compiler

use stl_compiler::{Compiler, CompilerConfig};
use std::path::PathBuf;
use tempfile::tempdir;

#[tokio::test]
async fn test_simple_compilation() {
    let compiler = Compiler::default();
    let spec_text = "test_spec
voltage > 220";
    
    let result = compiler.compile(spec_text).await;
    assert!(result.is_ok());
    
    if let Ok(compilation_result) = result {
        assert_eq!(compilation_result.specification.name, "test_spec");
        assert!(compilation_result.stats.total_time_ms > 0);
        assert!(compilation_result.stats.parse_time_ms > 0);
    }
}

#[tokio::test]
async fn test_binary_formula_compilation() {
    let compiler = Compiler::default();
    let spec_text = "binary_test
voltage > 220 && current < 100";
    
    let result = compiler.compile(spec_text).await;
    assert!(result.is_ok());
    
    if let Ok(compilation_result) = result {
        assert_eq!(compilation_result.specification.name, "binary_test");
        // Check that we have both voltage and current variables
        let variables = compilation_result.specification.formula.variables();
        assert!(variables.contains("voltage"));
        assert!(variables.contains("current"));
    }
}

#[tokio::test]
async fn test_temporal_formula_compilation() {
    let compiler = Compiler::default();
    let spec_text = "temporal_test
G[0,10] voltage > 220";
    
    let result = compiler.compile(spec_text).await;
    assert!(result.is_ok());
    
    if let Ok(compilation_result) = result {
        assert_eq!(compilation_result.specification.name, "temporal_test");
        assert!(compilation_result.specification.formula.temporal_depth() > 0);
    }
}

#[tokio::test]
async fn test_parameter_parsing() {
    let compiler = Compiler::default();
    let spec_text = "param_test
voltage > 220
param: max_voltage real 240.0 Maximum voltage threshold
param: safety_margin real 0.1 Safety margin factor";
    
    let result = compiler.compile(spec_text).await;
    assert!(result.is_ok());
    
    if let Ok(compilation_result) = result {
        assert_eq!(compilation_result.specification.name, "param_test");
        assert_eq!(compilation_result.specification.parameters.len(), 2);
        
        let param_names: Vec<_> = compilation_result.specification.parameters
            .iter()
            .map(|p| p.name.clone())
            .collect();
        assert!(param_names.contains(&"max_voltage".to_string()));
        assert!(param_names.contains(&"safety_margin".to_string()));
    }
}

#[tokio::test]
async fn test_constraint_parsing() {
    let compiler = Compiler::default();
    let spec_text = "constraint_test
voltage > 220
constraint: voltage_bounds bounds voltage <= 250.0
constraint: power_limit linear voltage * current <= 30000.0";
    
    let result = compiler.compile(spec_text).await;
    assert!(result.is_ok());
    
    if let Ok(compilation_result) = result {
        assert_eq!(compilation_result.specification.name, "constraint_test");
        assert_eq!(compilation_result.specification.constraints.len(), 2);
        
        let constraint_names: Vec<_> = compilation_result.specification.constraints
            .iter()
            .map(|c| c.name.clone())
            .collect();
        assert!(constraint_names.contains(&"voltage_bounds".to_string()));
        assert!(constraint_names.contains(&"power_limit".to_string()));
    }
}

#[tokio::test]
async fn test_metadata_parsing() {
    let compiler = Compiler::default();
    let spec_text = "meta_test
voltage > 220
meta: author CertifyEdge Team
meta: version 1.0.0
meta: category safety";
    
    let result = compiler.compile(spec_text).await;
    assert!(result.is_ok());
    
    if let Ok(compilation_result) = result {
        assert_eq!(compilation_result.specification.name, "meta_test");
        assert_eq!(compilation_result.specification.metadata.len(), 3);
        
        assert_eq!(compilation_result.specification.metadata.get("author"), Some(&"CertifyEdge Team".to_string()));
        assert_eq!(compilation_result.specification.metadata.get("version"), Some(&"1.0.0".to_string()));
        assert_eq!(compilation_result.specification.metadata.get("category"), Some(&"safety".to_string()));
    }
}

#[tokio::test]
async fn test_roundtrip_validation() {
    let compiler = Compiler::default();
    let spec_text = "roundtrip_test
voltage > 220 && current < 100";
    
    let result = compiler.compile(spec_text).await;
    assert!(result.is_ok());
    
    if let Ok(compilation_result) = result {
        assert!(compilation_result.validation.roundtrip_valid);
    }
}

#[tokio::test]
async fn test_compilation_statistics() {
    let compiler = Compiler::default();
    let spec_text = "stats_test
voltage > 220";
    
    let result = compiler.compile(spec_text).await;
    assert!(result.is_ok());
    
    if let Ok(compilation_result) = result {
        let stats = compilation_result.stats;
        assert!(stats.total_time_ms > 0);
        assert!(stats.parse_time_ms > 0);
        assert!(stats.ast_size_bytes > 0);
        assert!(stats.lean4_size_bytes > 0);
        assert!(stats.smt_size_bytes > 0);
    }
}

#[tokio::test]
async fn test_error_handling() {
    let compiler = Compiler::default();
    
    // Test empty specification
    let result = compiler.compile("").await;
    assert!(result.is_err());
    
    // Test invalid formula
    let result = compiler.compile("test_spec\ninvalid_formula").await;
    assert!(result.is_err());
}

#[tokio::test]
async fn test_file_compilation() {
    let temp_dir = tempdir().unwrap();
    let spec_file = temp_dir.path().join("test.stl");
    std::fs::write(&spec_file, "file_test\nvoltage > 220").unwrap();
    
    let compiler = Compiler::default();
    let spec_text = std::fs::read_to_string(&spec_file).unwrap();
    
    let result = compiler.compile(&spec_text).await;
    assert!(result.is_ok());
    
    if let Ok(compilation_result) = result {
        assert_eq!(compilation_result.specification.name, "file_test");
    }
}

#[tokio::test]
async fn test_complex_specification() {
    let compiler = Compiler::default();
    let spec_text = "complex_spec
// Complex specification with multiple operators
G[0,10] voltage > 220 && F[0,5] current < 100
param: voltage_threshold real 220.0 Voltage safety threshold
param: current_threshold real 100.0 Current safety threshold
constraint: voltage_bounds bounds voltage <= 250.0
constraint: current_bounds bounds current <= 120.0
meta: author CertifyEdge Team
meta: version 1.0.0
meta: category complex_safety";
    
    let result = compiler.compile(spec_text).await;
    assert!(result.is_ok());
    
    if let Ok(compilation_result) = result {
        assert_eq!(compilation_result.specification.name, "complex_spec");
        assert!(compilation_result.specification.description.is_some());
        assert_eq!(compilation_result.specification.parameters.len(), 2);
        assert_eq!(compilation_result.specification.constraints.len(), 2);
        assert_eq!(compilation_result.specification.metadata.len(), 3);
        assert!(compilation_result.specification.formula.temporal_depth() > 0);
    }
} 