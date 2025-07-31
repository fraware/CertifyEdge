use std::collections::HashMap;
use std::time::SystemTime;

use certifedge::{
    stl_compiler::{STLCompiler, STLCompilerConfig},
    smt_verifier::{SMTVerifier, SMTVerifierConfig},
    certificate::{CertificateService, CertificateConfig},
    auditor_api::{AuditorAPI, AuditorConfig},
    gpu_farm::{GPUFarm, GPUFarmConfig},
    grid_in_loop::{GridInLoopTester, GridInLoopConfig},
};

#[tokio::test]
async fn test_complete_stl_to_certificate_pipeline() {
    // Initialize all services
    let stl_config = STLCompilerConfig::default();
    let stl_compiler = STLCompiler::new(stl_config);
    
    let smt_config = SMTVerifierConfig::default();
    let smt_verifier = SMTVerifier::new(smt_config).unwrap();
    
    let cert_config = CertificateConfig::default();
    let cert_service = CertificateService::new(cert_config).unwrap();
    
    let auditor_config = AuditorConfig::default();
    let auditor_api = AuditorAPI::new(auditor_config).unwrap();
    
    // Test STL specification
    let stl_spec = r#"
        specification voltage_safety {
            description: "Ensure voltage stays within safe limits";
            formula: "G(voltage > 110.0 AND voltage < 130.0)";
            author: "grid_operator@example.com";
            version: "1.0.0";
        }
    "#;
    
    // Step 1: Parse and compile STL to Lean
    let lean_code = stl_compiler.compile_stl_to_lean(stl_spec).await;
    assert!(lean_code.is_ok());
    
    let lean_code = lean_code.unwrap();
    assert!(lean_code.contains("voltage"));
    assert!(lean_code.contains("110.0"));
    assert!(lean_code.contains("130.0"));
    
    // Step 2: Generate SMT formula from Lean
    let smt_formula = stl_compiler.compile_lean_to_smt(&lean_code).await;
    assert!(smt_formula.is_ok());
    
    let smt_formula = smt_formula.unwrap();
    assert!(smt_formula.contains("declare-fun"));
    assert!(smt_formula.contains("assert"));
    
    // Step 3: Verify with SMT solver
    let verification_result = smt_verifier.verify_formula(&smt_formula).await;
    assert!(verification_result.is_ok());
    
    let verification_result = verification_result.unwrap();
    assert!(verification_result.is_satisfiable);
    
    // Step 4: Generate certificate
    let model_hash = "abc123def456".to_string();
    let certificate = cert_service.create_certificate(
        stl_spec,
        &lean_code,
        &smt_formula,
        &verification_result,
        &model_hash,
    ).await;
    
    assert!(certificate.is_ok());
    
    let certificate = certificate.unwrap();
    assert!(!certificate.certificate_id.is_empty());
    assert!(certificate.is_signed());
    
    // Step 5: Store and retrieve certificate
    let stored_cert = auditor_api.store_certificate(&certificate).await;
    assert!(stored_cert.is_ok());
    
    let retrieved_cert = auditor_api.get_certificate(&certificate.certificate_id).await;
    assert!(retrieved_cert.is_ok());
    
    let retrieved_cert = retrieved_cert.unwrap();
    assert_eq!(retrieved_cert.certificate_id, certificate.certificate_id);
}

#[tokio::test]
async fn test_gpu_farm_integration() {
    let gpu_config = GPUFarmConfig::default();
    let mut gpu_farm = GPUFarm::new(gpu_config).unwrap();
    
    // Test job submission
    let job_request = ProofJobRequest {
        lean_spec: "test specification".to_string(),
        proof_goal: "test goal".to_string(),
        timeout_seconds: 300,
        gpu_requirements: GPURequirements {
            gpu_type: "a10".to_string(),
            gpu_count: 1,
            memory_per_gpu_gb: 8,
        },
        memory_requirements_mb: 4096,
        cpu_requirements: 2.0,
        priority: JobPriority::Normal,
        user_id: "test_user".to_string(),
        project_id: "test_project".to_string(),
    };
    
    let job_response = gpu_farm.submit_proof_job(job_request).await;
    assert!(job_response.is_ok());
    
    let job_response = job_response.unwrap();
    assert!(!job_response.job_id.is_empty());
    
    // Test job status monitoring
    let status = gpu_farm.get_job_status(&job_response.job_id).await;
    assert!(status.is_ok());
    
    let status = status.unwrap();
    assert!(matches!(status, JobStatus::Submitted | JobStatus::Queued | JobStatus::Running));
}

#[tokio::test]
async fn test_grid_in_loop_integration() {
    let grid_config = GridInLoopConfig::default();
    let mut grid_tester = GridInLoopTester::new(grid_config).unwrap();
    
    // Test grid simulation
    let test_request = GridInLoopTestRequest {
        simulator_type: SimulatorType::GridLABD,
        feeder_model_path: "tests/fixtures/ieee_13_bus.glm".to_string(),
        load_config: LoadConfig {
            load_types: vec![LoadType::Residential, LoadType::Commercial],
            time_series_length: Duration::from_secs(3600),
            stochastic_parameters: StochasticParameters {
                mean_load: 1000.0,
                standard_deviation: 200.0,
                skewness: 0.5,
                kurtosis: 3.0,
                seasonality: SeasonalityConfig::default(),
            },
            correlation_matrix: None,
        },
        agent_config: AgentConfig {
            model_path: "tests/fixtures/test_model.onnx".to_string(),
            model_type: ModelType::ONNX,
            inference_config: InferenceConfig::default(),
            safety_constraints: vec![SafetyConstraint {
                name: "voltage_limit".to_string(),
                constraint_type: ConstraintType::VoltageLimit,
                parameters: HashMap::new(),
            }],
        },
        stl_specs: vec![STLSpecification {
            name: "voltage_safety".to_string(),
            description: "Voltage safety constraint".to_string(),
            formula: "G(voltage > 110.0 AND voltage < 130.0)".to_string(),
            author: "test@example.com".to_string(),
            version: "1.0.0".to_string(),
        }],
        num_monte_carlo_runs: 10,
        max_violations_before_termination: 5,
    };
    
    let test_result = grid_tester.run_test(test_request).await;
    assert!(test_result.is_ok());
    
    let test_result = test_result.unwrap();
    assert!(test_result.total_runs > 0);
    assert!(test_result.successful_runs > 0);
    assert!(test_result.test_duration_seconds > 0);
}

#[tokio::test]
async fn test_certificate_lifecycle() {
    let cert_config = CertificateConfig::default();
    let cert_service = CertificateService::new(cert_config).unwrap();
    
    let auditor_config = AuditorConfig::default();
    let auditor_api = AuditorAPI::new(auditor_config).unwrap();
    
    // Create certificate
    let certificate = cert_service.create_test_certificate().await;
    assert!(certificate.is_ok());
    
    let certificate = certificate.unwrap();
    let cert_id = certificate.certificate_id.clone();
    
    // Store certificate
    let stored = auditor_api.store_certificate(&certificate).await;
    assert!(stored.is_ok());
    
    // Retrieve certificate
    let retrieved = auditor_api.get_certificate(&cert_id).await;
    assert!(retrieved.is_ok());
    
    let retrieved = retrieved.unwrap();
    assert_eq!(retrieved.certificate_id, cert_id);
    
    // Verify certificate
    let verification = cert_service.verify_certificate(&retrieved).await;
    assert!(verification.is_ok());
    
    let verification = verification.unwrap();
    assert!(verification.valid);
    
    // Revoke certificate
    let revocation = auditor_api.revoke_certificate(&cert_id, "Test revocation").await;
    assert!(revocation.is_ok());
    
    // Verify revocation
    let revoked = auditor_api.get_certificate(&cert_id).await;
    assert!(revoked.is_ok());
    
    let revoked = revoked.unwrap();
    assert!(revoked.is_revoked());
}

#[tokio::test]
async fn test_audit_trail_integration() {
    let auditor_config = AuditorConfig::default();
    let auditor_api = AuditorAPI::new(auditor_config).unwrap();
    
    // Test audit trail creation
    let audit_event = AuditEvent {
        event_id: "test_event_001".to_string(),
        timestamp: SystemTime::now(),
        user_id: "test_user".to_string(),
        action: "certificate_created".to_string(),
        resource_id: "test_cert_001".to_string(),
        details: HashMap::new(),
    };
    
    let stored = auditor_api.store_audit_event(&audit_event).await;
    assert!(stored.is_ok());
    
    // Test audit trail retrieval
    let events = auditor_api.get_audit_events(&audit_event.resource_id).await;
    assert!(events.is_ok());
    
    let events = events.unwrap();
    assert!(!events.is_empty());
    assert_eq!(events[0].event_id, audit_event.event_id);
}

#[tokio::test]
async fn test_error_handling_and_recovery() {
    let stl_config = STLCompilerConfig::default();
    let stl_compiler = STLCompiler::new(stl_config);
    
    let smt_config = SMTVerifierConfig::default();
    let smt_verifier = SMTVerifier::new(smt_config).unwrap();
    
    // Test with invalid STL specification
    let invalid_stl = r#"
        specification invalid_spec {
            formula: "INVALID_SYNTAX";
        }
    "#;
    
    let result = stl_compiler.compile_stl_to_lean(invalid_stl).await;
    assert!(result.is_err());
    
    // Test that valid specification still works after error
    let valid_stl = r#"
        specification voltage_safety {
            formula: "G(voltage > 110.0)";
        }
    "#;
    
    let result = stl_compiler.compile_stl_to_lean(valid_stl).await;
    assert!(result.is_ok());
    
    // Test SMT verification with invalid formula
    let invalid_smt = r#"
        (declare-fun x () Real)
        (invalid-command)
        (check-sat)
    "#;
    
    let result = smt_verifier.verify_formula(invalid_smt).await;
    assert!(result.is_err());
    
    // Test that valid SMT formula still works after error
    let valid_smt = r#"
        (declare-fun x () Real)
        (assert (> x 0))
        (check-sat)
    "#;
    
    let result = smt_verifier.verify_formula(valid_smt).await;
    assert!(result.is_ok());
}

#[tokio::test]
async fn test_performance_under_load() {
    let stl_config = STLCompilerConfig::default();
    let stl_compiler = STLCompiler::new(stl_config);
    
    let smt_config = SMTVerifierConfig::default();
    let smt_verifier = SMTVerifier::new(smt_config).unwrap();
    
    // Test concurrent processing
    let test_specs = vec![
        r#"specification spec1 { formula: "G(voltage > 110.0)"; }"#,
        r#"specification spec2 { formula: "F(current < 50.0)"; }"#,
        r#"specification spec3 { formula: "G(voltage > 110.0 AND voltage < 130.0)"; }"#,
    ];
    
    let start_time = SystemTime::now();
    
    let handles: Vec<_> = test_specs
        .into_iter()
        .map(|spec| {
            let compiler = stl_compiler.clone();
            let verifier = smt_verifier.clone();
            tokio::spawn(async move {
                let lean_code = compiler.compile_stl_to_lean(spec).await?;
                let smt_formula = compiler.compile_lean_to_smt(&lean_code).await?;
                let verification = verifier.verify_formula(&smt_formula).await?;
                Ok::<_, Box<dyn std::error::Error>>(verification)
            })
        })
        .collect();
    
    let results = futures::future::join_all(handles).await;
    
    let end_time = SystemTime::now();
    let duration = end_time.duration_since(start_time).unwrap();
    
    // All concurrent operations should complete successfully
    for result in results {
        assert!(result.is_ok());
        let verification = result.unwrap();
        assert!(verification.is_ok());
    }
    
    // Total processing time should be reasonable
    assert!(duration.as_secs() < 30);
}

#[tokio::test]
async fn test_security_and_compliance() {
    let auditor_config = AuditorConfig::default();
    let auditor_api = AuditorAPI::new(auditor_config).unwrap();
    
    // Test authentication
    let auth_result = auditor_api.authenticate_user("test_user", "test_password").await;
    assert!(auth_result.is_ok());
    
    let token = auth_result.unwrap();
    assert!(!token.is_empty());
    
    // Test authorization
    let authz_result = auditor_api.authorize_action(&token, "read_certificate", "cert_001").await;
    assert!(authz_result.is_ok());
    
    // Test audit logging
    let audit_result = auditor_api.log_audit_event("test_user", "read_certificate", "cert_001").await;
    assert!(audit_result.is_ok());
    
    // Test data encryption
    let cert_data = "sensitive certificate data".to_string();
    let encrypted = auditor_api.encrypt_data(&cert_data).await;
    assert!(encrypted.is_ok());
    
    let encrypted = encrypted.unwrap();
    assert_ne!(encrypted, cert_data);
    
    let decrypted = auditor_api.decrypt_data(&encrypted).await;
    assert!(decrypted.is_ok());
    
    let decrypted = decrypted.unwrap();
    assert_eq!(decrypted, cert_data);
}

#[tokio::test]
async fn test_monitoring_and_metrics() {
    let auditor_config = AuditorConfig::default();
    let auditor_api = AuditorAPI::new(auditor_config).unwrap();
    
    // Test metrics collection
    let metrics = auditor_api.get_metrics().await;
    assert!(metrics.is_ok());
    
    let metrics = metrics.unwrap();
    assert!(metrics.total_certificates >= 0);
    assert!(metrics.total_queries >= 0);
    assert!(metrics.uptime_seconds > 0);
    
    // Test health check
    let health = auditor_api.health_check().await;
    assert!(health.is_ok());
    
    let health = health.unwrap();
    assert_eq!(health.status, "healthy");
    
    // Test performance metrics
    let perf_metrics = auditor_api.get_performance_metrics().await;
    assert!(perf_metrics.is_ok());
    
    let perf_metrics = perf_metrics.unwrap();
    assert!(perf_metrics.average_response_time_ms >= 0);
    assert!(perf_metrics.requests_per_second >= 0.0);
} 