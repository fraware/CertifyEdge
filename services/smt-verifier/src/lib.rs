//! CertifyEdge SMT Verification Microservice
//! 
//! This crate provides a high-performance SMT verification service that accepts
//! gRPC streams of SMT-LIB jobs, fans out to Z3 4.13 and CVC5 1.2 in sandboxed
//! Wasm runtimes, and collects UNSAT cores for auditor replay.

pub mod verifier;
pub mod solver;
pub mod sandbox;
pub mod metrics;
pub mod error;
pub mod config;
pub mod proto;

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{Duration, SystemTime};
use uuid::Uuid;

use crate::error::VerifierError;
use crate::verifier::VerificationResult;
use crate::solver::SolverType;

/// Main SMT verifier service
#[derive(Debug, Clone)]
pub struct SMTVerifier {
    config: config::VerifierConfig,
    solvers: HashMap<SolverType, solver::Solver>,
    sandbox: sandbox::WasmSandbox,
    metrics: metrics::VerifierMetrics,
}

impl SMTVerifier {
    /// Create a new SMT verifier with default configuration
    pub fn new() -> Result<Self, VerifierError> {
        let config = config::VerifierConfig::default();
        let solvers = Self::initialize_solvers(&config)?;
        let sandbox = sandbox::WasmSandbox::new(&config)?;
        let metrics = metrics::VerifierMetrics::new();
        
        Ok(Self {
            config,
            solvers,
            sandbox,
            metrics,
        })
    }

    /// Create a new SMT verifier with custom configuration
    pub fn with_config(config: config::VerifierConfig) -> Result<Self, VerifierError> {
        let solvers = Self::initialize_solvers(&config)?;
        let sandbox = sandbox::WasmSandbox::new(&config)?;
        let metrics = metrics::VerifierMetrics::new();
        
        Ok(Self {
            config,
            solvers,
            sandbox,
            metrics,
        })
    }

    /// Initialize SMT solvers
    fn initialize_solvers(config: &config::VerifierConfig) -> Result<HashMap<SolverType, solver::Solver>, VerifierError> {
        let mut solvers = HashMap::new();
        
        if config.enable_z3 {
            let z3_solver = solver::Solver::new(SolverType::Z3, &config.z3_config)?;
            solvers.insert(SolverType::Z3, z3_solver);
        }
        
        if config.enable_cvc5 {
            let cvc5_solver = solver::Solver::new(SolverType::CVC5, &config.cvc5_config)?;
            solvers.insert(SolverType::CVC5, cvc5_solver);
        }
        
        if solvers.is_empty() {
            return Err(VerifierError::NoSolversAvailable);
        }
        
        Ok(solvers)
    }

    /// Verify an SMT-LIB script
    pub async fn verify_script(
        &mut self,
        script: &str,
        solver_preferences: Option<Vec<SolverType>>,
    ) -> Result<VerificationResult, VerifierError> {
        let start_time = SystemTime::now();
        let verification_id = Uuid::new_v4().to_string();
        
        // Parse and validate SMT-LIB script
        let parsed_script = self.parse_smt_script(script)?;
        
        // Determine which solvers to use
        let solvers_to_use = solver_preferences.unwrap_or_else(|| {
            self.solvers.keys().cloned().collect()
        });
        
        // Execute verification with multiple solvers
        let mut results = Vec::new();
        for solver_type in solvers_to_use {
            if let Some(solver) = self.solvers.get(&solver_type) {
                let result = self.execute_verification(solver, &parsed_script, &verification_id).await?;
                results.push(result);
            }
        }
        
        // Aggregate results
        let aggregated_result = self.aggregate_results(results, &verification_id)?;
        
        // Update metrics
        let verification_time = start_time.elapsed()?;
        self.metrics.record_verification(aggregated_result.success, verification_time);
        
        Ok(aggregated_result)
    }

    /// Execute verification with a specific solver
    async fn execute_verification(
        &self,
        solver: &solver::Solver,
        script: &str,
        verification_id: &str,
    ) -> Result<VerificationResult, VerifierError> {
        let start_time = SystemTime::now();
        
        // Execute in sandbox
        let sandbox_result = self.sandbox.execute_solver(solver, script).await?;
        
        let execution_time = start_time.elapsed()?;
        
        Ok(VerificationResult {
            verification_id: verification_id.to_string(),
            solver_type: solver.solver_type(),
            success: sandbox_result.success,
            result: sandbox_result.result,
            execution_time_ms: execution_time.as_millis() as u64,
            memory_usage_mb: sandbox_result.memory_usage_mb,
            unsat_core: sandbox_result.unsat_core,
            model: sandbox_result.model,
            errors: sandbox_result.errors,
            metadata: HashMap::new(),
        })
    }

    /// Parse and validate SMT-LIB script
    fn parse_smt_script(&self, script: &str) -> Result<String, VerifierError> {
        // Basic validation - in practice this would be more comprehensive
        if script.trim().is_empty() {
            return Err(VerifierError::InvalidScript("Empty script".to_string()));
        }
        
        if !script.contains("(set-logic") {
            return Err(VerifierError::InvalidScript("Missing set-logic".to_string()));
        }
        
        Ok(script.to_string())
    }

    /// Aggregate results from multiple solvers
    fn aggregate_results(
        &self,
        results: Vec<VerificationResult>,
        verification_id: &str,
    ) -> Result<VerificationResult, VerifierError> {
        if results.is_empty() {
            return Err(VerifierError::NoResultsAvailable);
        }
        
        // If all results agree, use the first one
        let first_result = &results[0];
        let all_same = results.iter().all(|r| r.result == first_result.result);
        
        if all_same {
            Ok(first_result.clone())
        } else {
            // Results differ - this is a critical alert
            Err(VerifierError::SolverDisagreement {
                verification_id: verification_id.to_string(),
                results: results,
            })
        }
    }

    /// Get verification statistics
    pub fn get_stats(&self) -> metrics::VerifierStats {
        self.metrics.get_stats()
    }

    /// Get available solvers
    pub fn get_available_solvers(&self) -> Vec<SolverType> {
        self.solvers.keys().cloned().collect()
    }

    /// Check solver health
    pub async fn check_solver_health(&self, solver_type: SolverType) -> Result<bool, VerifierError> {
        if let Some(solver) = self.solvers.get(&solver_type) {
            solver.check_health().await
        } else {
            Ok(false)
        }
    }

    /// Validate verifier configuration
    pub fn validate_config(&self) -> Result<(), VerifierError> {
        self.config.validate()
    }
}

impl Default for SMTVerifier {
    fn default() -> Self {
        Self::new().expect("Failed to create default SMT verifier")
    }
}

/// Verification request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationRequest {
    pub request_id: String,
    pub script: String,
    pub solver_preferences: Option<Vec<SolverType>>,
    pub timeout_ms: Option<u64>,
    pub max_memory_mb: Option<u64>,
}

/// Verification response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationResponse {
    pub request_id: String,
    pub result: VerificationResult,
    pub timestamp: SystemTime,
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_verifier_creation(solver_count in 1..5usize) {
            let verifier = SMTVerifier::new();
            assert!(verifier.is_ok());
        }
    }

    #[tokio::test]
    async fn test_verifier_stats() {
        let verifier = SMTVerifier::new().unwrap();
        let stats = verifier.get_stats();
        assert!(stats.total_verifications >= 0);
    }

    #[tokio::test]
    async fn test_solver_health() {
        let verifier = SMTVerifier::new().unwrap();
        let solvers = verifier.get_available_solvers();
        
        for solver_type in solvers {
            let health = verifier.check_solver_health(solver_type).await;
            assert!(health.is_ok());
        }
    }
} 