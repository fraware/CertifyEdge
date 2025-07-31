use std::collections::HashMap;
use std::time::SystemTime;

use certifedge::stl_compiler::{
    ast::{STLFormula, AtomicPredicate, ComparisonOperator, LogicalOperator, TemporalOperator},
    compiler::STLCompiler,
    config::STLCompilerConfig,
    error::STLCompilerError,
    parser::STLParser,
};

#[tokio::test]
async fn test_stl_parser_basic_formulas() {
    let parser = STLParser::new();
    
    // Test basic atomic predicates
    let formula = "voltage > 120.0";
    let result = parser.parse(formula).await;
    assert!(result.is_ok());
    
    let parsed = result.unwrap();
    assert!(matches!(parsed, STLFormula::Atomic(_)));
    
    // Test logical operators
    let formula = "voltage > 120.0 AND current < 50.0";
    let result = parser.parse(formula).await;
    assert!(result.is_ok());
    
    // Test temporal operators
    let formula = "G(voltage > 120.0)";
    let result = parser.parse(formula).await;
    assert!(result.is_ok());
    
    let parsed = result.unwrap();
    assert!(matches!(parsed, STLFormula::Always(_)));
}

#[tokio::test]
async fn test_stl_parser_complex_formulas() {
    let parser = STLParser::new();
    
    // Test complex nested formulas
    let formula = "G((voltage > 120.0 AND voltage < 130.0) OR F(current < 50.0))";
    let result = parser.parse(formula).await;
    assert!(result.is_ok());
    
    // Test with multiple temporal operators
    let formula = "G(F(voltage > 120.0))";
    let result = parser.parse(formula).await;
    assert!(result.is_ok());
}

#[tokio::test]
async fn test_stl_parser_error_handling() {
    let parser = STLParser::new();
    
    // Test invalid syntax
    let formula = "voltage > > 120.0";
    let result = parser.parse(formula).await;
    assert!(result.is_err());
    
    // Test missing operand
    let formula = "voltage >";
    let result = parser.parse(formula).await;
    assert!(result.is_err());
    
    // Test invalid operator
    let formula = "voltage INVALID 120.0";
    let result = parser.parse(formula).await;
    assert!(result.is_err());
}

#[tokio::test]
async fn test_stl_compiler_basic_compilation() {
    let config = STLCompilerConfig::default();
    let compiler = STLCompiler::new(config);
    
    // Test basic formula compilation
    let formula = STLFormula::Atomic(AtomicPredicate {
        variable: "voltage".to_string(),
        operator: ComparisonOperator::GreaterThan,
        threshold: 120.0,
    });
    
    let result = compiler.compile_to_lean(&formula).await;
    assert!(result.is_ok());
    
    let lean_code = result.unwrap();
    assert!(lean_code.contains("voltage"));
    assert!(lean_code.contains("120.0"));
}

#[tokio::test]
async fn test_stl_compiler_temporal_operators() {
    let config = STLCompilerConfig::default();
    let compiler = STLCompiler::new(config);
    
    // Test Always operator
    let formula = STLFormula::Always(Box::new(STLFormula::Atomic(AtomicPredicate {
        variable: "voltage".to_string(),
        operator: ComparisonOperator::GreaterThan,
        threshold: 120.0,
    })));
    
    let result = compiler.compile_to_lean(&formula).await;
    assert!(result.is_ok());
    
    let lean_code = result.unwrap();
    assert!(lean_code.contains("∀"));
    
    // Test Eventually operator
    let formula = STLFormula::Eventually(Box::new(STLFormula::Atomic(AtomicPredicate {
        variable: "current".to_string(),
        operator: ComparisonOperator::LessThan,
        threshold: 50.0,
    })));
    
    let result = compiler.compile_to_lean(&formula).await;
    assert!(result.is_ok());
    
    let lean_code = result.unwrap();
    assert!(lean_code.contains("∃"));
}

#[tokio::test]
async fn test_stl_compiler_logical_operators() {
    let config = STLCompilerConfig::default();
    let compiler = STLCompiler::new(config);
    
    // Test AND operator
    let formula = STLFormula::Logical(
        LogicalOperator::And,
        Box::new(STLFormula::Atomic(AtomicPredicate {
            variable: "voltage".to_string(),
            operator: ComparisonOperator::GreaterThan,
            threshold: 120.0,
        })),
        Box::new(STLFormula::Atomic(AtomicPredicate {
            variable: "current".to_string(),
            operator: ComparisonOperator::LessThan,
            threshold: 50.0,
        })),
    );
    
    let result = compiler.compile_to_lean(&formula).await;
    assert!(result.is_ok());
    
    let lean_code = result.unwrap();
    assert!(lean_code.contains("∧"));
}

#[tokio::test]
async fn test_stl_compiler_complex_nested_formulas() {
    let config = STLCompilerConfig::default();
    let compiler = STLCompiler::new(config);
    
    // Test complex nested formula
    let inner_formula = STLFormula::Logical(
        LogicalOperator::And,
        Box::new(STLFormula::Atomic(AtomicPredicate {
            variable: "voltage".to_string(),
            operator: ComparisonOperator::GreaterThan,
            threshold: 120.0,
        })),
        Box::new(STLFormula::Atomic(AtomicPredicate {
            variable: "voltage".to_string(),
            operator: ComparisonOperator::LessThan,
            threshold: 130.0,
        })),
    );
    
    let formula = STLFormula::Always(Box::new(inner_formula));
    
    let result = compiler.compile_to_lean(&formula).await;
    assert!(result.is_ok());
    
    let lean_code = result.unwrap();
    assert!(lean_code.contains("∀"));
    assert!(lean_code.contains("∧"));
}

#[tokio::test]
async fn test_stl_compiler_error_handling() {
    let config = STLCompilerConfig::default();
    let compiler = STLCompiler::new(config);
    
    // Test compilation with invalid formula
    let formula = STLFormula::Atomic(AtomicPredicate {
        variable: "".to_string(), // Invalid empty variable
        operator: ComparisonOperator::GreaterThan,
        threshold: 120.0,
    });
    
    let result = compiler.compile_to_lean(&formula).await;
    assert!(result.is_err());
}

#[tokio::test]
async fn test_stl_compiler_smt_generation() {
    let config = STLCompilerConfig::default();
    let compiler = STLCompiler::new(config);
    
    let formula = STLFormula::Atomic(AtomicPredicate {
        variable: "voltage".to_string(),
        operator: ComparisonOperator::GreaterThan,
        threshold: 120.0,
    });
    
    let result = compiler.compile_to_smt(&formula).await;
    assert!(result.is_ok());
    
    let smt_code = result.unwrap();
    assert!(smt_code.contains("declare-fun"));
    assert!(smt_code.contains("assert"));
}

#[tokio::test]
async fn test_stl_compiler_configuration() {
    let mut config = STLCompilerConfig::default();
    config.enable_optimization = true;
    config.max_formula_depth = 100;
    config.enable_debug_output = true;
    
    let compiler = STLCompiler::new(config);
    
    let formula = STLFormula::Atomic(AtomicPredicate {
        variable: "voltage".to_string(),
        operator: ComparisonOperator::GreaterThan,
        threshold: 120.0,
    });
    
    let result = compiler.compile_to_lean(&formula).await;
    assert!(result.is_ok());
}

#[tokio::test]
async fn test_stl_compiler_performance() {
    let config = STLCompilerConfig::default();
    let compiler = STLCompiler::new(config);
    
    // Test compilation performance
    let start_time = SystemTime::now();
    
    let formula = STLFormula::Always(Box::new(STLFormula::Eventually(Box::new(
        STLFormula::Atomic(AtomicPredicate {
            variable: "voltage".to_string(),
            operator: ComparisonOperator::GreaterThan,
            threshold: 120.0,
        })
    ))));
    
    let result = compiler.compile_to_lean(&formula).await;
    assert!(result.is_ok());
    
    let end_time = SystemTime::now();
    let duration = end_time.duration_since(start_time).unwrap();
    
    // Compilation should complete within 1 second
    assert!(duration.as_millis() < 1000);
}

#[tokio::test]
async fn test_stl_compiler_metadata() {
    let config = STLCompilerConfig::default();
    let compiler = STLCompiler::new(config);
    
    let mut metadata = HashMap::new();
    metadata.insert("author".to_string(), "test@example.com".to_string());
    metadata.insert("version".to_string(), "1.0.0".to_string());
    
    let formula = STLFormula::Atomic(AtomicPredicate {
        variable: "voltage".to_string(),
        operator: ComparisonOperator::GreaterThan,
        threshold: 120.0,
    });
    
    let result = compiler.compile_with_metadata(&formula, &metadata).await;
    assert!(result.is_ok());
    
    let (lean_code, compiled_metadata) = result.unwrap();
    assert!(lean_code.contains("voltage"));
    assert_eq!(compiled_metadata.get("author"), Some(&"test@example.com".to_string()));
}

#[tokio::test]
async fn test_stl_compiler_validation() {
    let config = STLCompilerConfig::default();
    let compiler = STLCompiler::new(config);
    
    // Test valid formula
    let formula = STLFormula::Atomic(AtomicPredicate {
        variable: "voltage".to_string(),
        operator: ComparisonOperator::GreaterThan,
        threshold: 120.0,
    });
    
    let result = compiler.validate_formula(&formula).await;
    assert!(result.is_ok());
    
    // Test invalid formula (empty variable)
    let invalid_formula = STLFormula::Atomic(AtomicPredicate {
        variable: "".to_string(),
        operator: ComparisonOperator::GreaterThan,
        threshold: 120.0,
    });
    
    let result = compiler.validate_formula(&invalid_formula).await;
    assert!(result.is_err());
}

#[tokio::test]
async fn test_stl_compiler_error_recovery() {
    let config = STLCompilerConfig::default();
    let compiler = STLCompiler::new(config);
    
    // Test that compiler can recover from errors
    let invalid_formula = STLFormula::Atomic(AtomicPredicate {
        variable: "".to_string(),
        operator: ComparisonOperator::GreaterThan,
        threshold: 120.0,
    });
    
    let result = compiler.compile_to_lean(&invalid_formula).await;
    assert!(result.is_err());
    
    // Test that valid formula still works after error
    let valid_formula = STLFormula::Atomic(AtomicPredicate {
        variable: "voltage".to_string(),
        operator: ComparisonOperator::GreaterThan,
        threshold: 120.0,
    });
    
    let result = compiler.compile_to_lean(&valid_formula).await;
    assert!(result.is_ok());
} 