use std::collections::HashMap;
use std::time::{Duration, SystemTime};

use certifedge::smt_verifier::{
    config::SMTVerifierConfig,
    error::SMTVerifierError,
    solver::{SolverType, SolverConfig},
    verifier::SMTVerifier,
    sandbox::SandboxConfig,
    metrics::VerificationMetrics,
};

#[tokio::test]
async fn test_smt_verifier_creation() {
    let config = SMTVerifierConfig::default();
    let verifier = SMTVerifier::new(config);
    assert!(verifier.is_ok());
}

#[tokio::test]
async fn test_smt_verifier_basic_verification() {
    let config = SMTVerifierConfig::default();
    let verifier = SMTVerifier::new(config).unwrap();
    
    // Test basic SMT formula
    let smt_formula = r#"
        (declare-fun x () Real)
        (declare-fun y () Real)
        (assert (> x 0))
        (assert (< y 10))
        (assert (= (+ x y) 5))
        (check-sat)
    "#;
    
    let result = verifier.verify_formula(smt_formula).await;
    assert!(result.is_ok());
    
    let verification_result = result.unwrap();
    assert!(verification_result.is_satisfiable);
    assert!(verification_result.solving_time_ms > 0);
}

#[tokio::test]
async fn test_smt_verifier_unsatisfiable_formula() {
    let config = SMTVerifierConfig::default();
    let verifier = SMTVerifier::new(config).unwrap();
    
    // Test unsatisfiable formula
    let smt_formula = r#"
        (declare-fun x () Real)
        (assert (> x 10))
        (assert (< x 0))
        (check-sat)
    "#;
    
    let result = verifier.verify_formula(smt_formula).await;
    assert!(result.is_ok());
    
    let verification_result = result.unwrap();
    assert!(!verification_result.is_satisfiable);
}

#[tokio::test]
async fn test_smt_verifier_multiple_solvers() {
    let mut config = SMTVerifierConfig::default();
    config.solvers = vec![
        SolverConfig {
            solver_type: SolverType::Z3,
            timeout_seconds: 30,
            memory_limit_mb: 1024,
        },
        SolverConfig {
            solver_type: SolverType::CVC5,
            timeout_seconds: 30,
            memory_limit_mb: 1024,
        },
    ];
    
    let verifier = SMTVerifier::new(config).unwrap();
    
    let smt_formula = r#"
        (declare-fun x () Real)
        (assert (> x 0))
        (check-sat)
    "#;
    
    let result = verifier.verify_with_multiple_solvers(smt_formula).await;
    assert!(result.is_ok());
    
    let results = result.unwrap();
    assert_eq!(results.len(), 2);
    
    // All solvers should agree on satisfiability
    let first_result = &results[0];
    for result in &results[1..] {
        assert_eq!(first_result.is_satisfiable, result.is_satisfiable);
    }
}

#[tokio::test]
async fn test_smt_verifier_timeout_handling() {
    let mut config = SMTVerifierConfig::default();
    config.solvers = vec![SolverConfig {
        solver_type: SolverType::Z3,
        timeout_seconds: 1, // Very short timeout
        memory_limit_mb: 1024,
    }];
    
    let verifier = SMTVerifier::new(config).unwrap();
    
    // Create a complex formula that might timeout
    let smt_formula = r#"
        (declare-fun x () Real)
        (declare-fun y () Real)
        (declare-fun z () Real)
        (assert (> x 0))
        (assert (> y 0))
        (assert (> z 0))
        (assert (= (+ x y z) 100))
        (assert (= (* x y z) 1000))
        (check-sat)
    "#;
    
    let result = verifier.verify_formula(smt_formula).await;
    // Should either succeed or timeout gracefully
    assert!(result.is_ok() || matches!(result.unwrap_err(), SMTVerifierError::Timeout(_)));
}

#[tokio::test]
async fn test_smt_verifier_memory_limits() {
    let mut config = SMTVerifierConfig::default();
    config.solvers = vec![SolverConfig {
        solver_type: SolverType::Z3,
        timeout_seconds: 30,
        memory_limit_mb: 1, // Very low memory limit
    }];
    
    let verifier = SMTVerifier::new(config).unwrap();
    
    let smt_formula = r#"
        (declare-fun x () Real)
        (assert (> x 0))
        (check-sat)
    "#;
    
    let result = verifier.verify_formula(smt_formula).await;
    // Should either succeed or fail gracefully due to memory limits
    assert!(result.is_ok() || matches!(result.unwrap_err(), SMTVerifierError::MemoryLimitExceeded(_)));
}

#[tokio::test]
async fn test_smt_verifier_sandbox_isolation() {
    let mut config = SMTVerifierConfig::default();
    config.sandbox = SandboxConfig {
        enabled: true,
        timeout_seconds: 10,
        memory_limit_mb: 512,
        network_access: false,
        file_access: false,
    };
    
    let verifier = SMTVerifier::new(config).unwrap();
    
    let smt_formula = r#"
        (declare-fun x () Real)
        (assert (> x 0))
        (check-sat)
    "#;
    
    let result = verifier.verify_formula(smt_formula).await;
    assert!(result.is_ok());
}

#[tokio::test]
async fn test_smt_verifier_error_handling() {
    let config = SMTVerifierConfig::default();
    let verifier = SMTVerifier::new(config).unwrap();
    
    // Test invalid SMT syntax
    let invalid_formula = r#"
        (declare-fun x () Real)
        (assert (> x 0))
        (invalid-command)
        (check-sat)
    "#;
    
    let result = verifier.verify_formula(invalid_formula).await;
    assert!(result.is_err());
}

#[tokio::test]
async fn test_smt_verifier_metrics_collection() {
    let config = SMTVerifierConfig::default();
    let verifier = SMTVerifier::new(config).unwrap();
    
    let smt_formula = r#"
        (declare-fun x () Real)
        (assert (> x 0))
        (check-sat)
    "#;
    
    let result = verifier.verify_formula(smt_formula).await;
    assert!(result.is_ok());
    
    let metrics = verifier.get_metrics().await;
    assert!(metrics.is_ok());
    
    let metrics = metrics.unwrap();
    assert!(metrics.total_verifications > 0);
    assert!(metrics.average_solving_time_ms > 0.0);
}

#[tokio::test]
async fn test_smt_verifier_performance_benchmark() {
    let config = SMTVerifierConfig::default();
    let verifier = SMTVerifier::new(config).unwrap();
    
    let start_time = SystemTime::now();
    
    let smt_formula = r#"
        (declare-fun x () Real)
        (declare-fun y () Real)
        (assert (> x 0))
        (assert (> y 0))
        (assert (= (+ x y) 10))
        (check-sat)
    "#;
    
    let result = verifier.verify_formula(smt_formula).await;
    assert!(result.is_ok());
    
    let end_time = SystemTime::now();
    let duration = end_time.duration_since(start_time).unwrap();
    
    // Verification should complete within 5 seconds
    assert!(duration.as_secs() < 5);
}

#[tokio::test]
async fn test_smt_verifier_concurrent_verifications() {
    let config = SMTVerifierConfig::default();
    let verifier = SMTVerifier::new(config).unwrap();
    
    let smt_formula = r#"
        (declare-fun x () Real)
        (assert (> x 0))
        (check-sat)
    "#;
    
    // Run multiple verifications concurrently
    let handles: Vec<_> = (0..10)
        .map(|_| {
            let verifier_clone = verifier.clone();
            let formula = smt_formula.to_string();
            tokio::spawn(async move {
                verifier_clone.verify_formula(&formula).await
            })
        })
        .collect();
    
    let results = futures::future::join_all(handles).await;
    
    for result in results {
        assert!(result.is_ok());
        let verification_result = result.unwrap();
        assert!(verification_result.is_ok());
    }
}

#[tokio::test]
async fn test_smt_verifier_formula_validation() {
    let config = SMTVerifierConfig::default();
    let verifier = SMTVerifier::new(config).unwrap();
    
    // Test valid formula
    let valid_formula = r#"
        (declare-fun x () Real)
        (assert (> x 0))
        (check-sat)
    "#;
    
    let result = verifier.validate_formula(valid_formula).await;
    assert!(result.is_ok());
    
    // Test invalid formula
    let invalid_formula = r#"
        (declare-fun x () Real)
        (assert (> x 0))
        (invalid-command)
    "#;
    
    let result = verifier.validate_formula(invalid_formula).await;
    assert!(result.is_err());
}

#[tokio::test]
async fn test_smt_verifier_solver_health_check() {
    let config = SMTVerifierConfig::default();
    let verifier = SMTVerifier::new(config).unwrap();
    
    let health_status = verifier.check_solver_health().await;
    assert!(health_status.is_ok());
    
    let health_status = health_status.unwrap();
    assert!(health_status.all_solvers_healthy);
    assert!(!health_status.solver_statuses.is_empty());
}

#[tokio::test]
async fn test_smt_verifier_configuration_validation() {
    // Test valid configuration
    let config = SMTVerifierConfig::default();
    let result = SMTVerifier::new(config);
    assert!(result.is_ok());
    
    // Test invalid configuration (empty solver list)
    let mut invalid_config = SMTVerifierConfig::default();
    invalid_config.solvers = vec![];
    let result = SMTVerifier::new(invalid_config);
    assert!(result.is_err());
}

#[tokio::test]
async fn test_smt_verifier_error_recovery() {
    let config = SMTVerifierConfig::default();
    let verifier = SMTVerifier::new(config).unwrap();
    
    // Test with invalid formula first
    let invalid_formula = r#"
        (declare-fun x () Real)
        (assert (> x 0))
        (invalid-command)
        (check-sat)
    "#;
    
    let result = verifier.verify_formula(invalid_formula).await;
    assert!(result.is_err());
    
    // Test that valid formula still works after error
    let valid_formula = r#"
        (declare-fun x () Real)
        (assert (> x 0))
        (check-sat)
    "#;
    
    let result = verifier.verify_formula(valid_formula).await;
    assert!(result.is_ok());
}

#[tokio::test]
async fn test_smt_verifier_metadata_handling() {
    let config = SMTVerifierConfig::default();
    let verifier = SMTVerifier::new(config).unwrap();
    
    let mut metadata = HashMap::new();
    metadata.insert("formula_id".to_string(), "test_001".to_string());
    metadata.insert("author".to_string(), "test@example.com".to_string());
    
    let smt_formula = r#"
        (declare-fun x () Real)
        (assert (> x 0))
        (check-sat)
    "#;
    
    let result = verifier.verify_with_metadata(smt_formula, &metadata).await;
    assert!(result.is_ok());
    
    let verification_result = result.unwrap();
    assert_eq!(verification_result.metadata.get("formula_id"), Some(&"test_001".to_string()));
    assert_eq!(verification_result.metadata.get("author"), Some(&"test@example.com".to_string()));
} 