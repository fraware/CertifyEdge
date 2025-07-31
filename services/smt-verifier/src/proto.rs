//! Protocol buffer definitions for SMT verification service
//! 
//! This module contains the gRPC service definitions and message types
//! for the SMT verification service.

// This would contain the generated protobuf code
// For now, we'll create placeholder structures

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use crate::verifier::{SMTResult, VerificationResult};
use crate::solver::SolverType;

/// gRPC verification request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationRequest {
    pub request_id: String,
    pub script: String,
    pub solver_preferences: Vec<String>,
    pub timeout_ms: Option<u64>,
    pub max_memory_mb: Option<u64>,
}

/// gRPC verification response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationResponse {
    pub request_id: String,
    pub result: VerificationResult,
    pub timestamp: String,
}

/// gRPC health check request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthCheckRequest {
    pub service: String,
}

/// gRPC health check response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthCheckResponse {
    pub status: HealthStatus,
    pub details: HashMap<String, String>,
}

/// Health status enum
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum HealthStatus {
    Unknown,
    Serving,
    NotServing,
    ServiceUnknown,
}

/// gRPC metrics request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricsRequest {
    pub format: MetricsFormat,
}

/// Metrics format enum
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MetricsFormat {
    Prometheus,
    Json,
    Text,
}

/// gRPC metrics response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricsResponse {
    pub metrics: String,
    pub format: MetricsFormat,
}

/// gRPC solver status request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SolverStatusRequest {
    pub solver_type: String,
}

/// gRPC solver status response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SolverStatusResponse {
    pub solver_type: String,
    pub healthy: bool,
    pub version: String,
    pub uptime_seconds: u64,
    pub total_executions: u64,
    pub successful_executions: u64,
    pub failed_executions: u64,
}

/// gRPC service statistics request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceStatsRequest {
    pub include_solver_stats: bool,
}

/// gRPC service statistics response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceStatsResponse {
    pub total_verifications: u64,
    pub successful_verifications: u64,
    pub failed_verifications: u64,
    pub sat_count: u64,
    pub unsat_count: u64,
    pub unknown_count: u64,
    pub error_count: u64,
    pub average_execution_time_ms: u64,
    pub average_memory_usage_mb: u64,
    pub solver_stats: HashMap<String, SolverStats>,
}

/// Solver statistics for gRPC
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SolverStats {
    pub solver_type: String,
    pub total_executions: u64,
    pub successful_executions: u64,
    pub failed_executions: u64,
    pub sat_count: u64,
    pub unsat_count: u64,
    pub unknown_count: u64,
    pub error_count: u64,
    pub average_execution_time_ms: u64,
    pub average_memory_usage_mb: u64,
    pub last_used: Option<String>,
}

/// Convert VerificationResult to gRPC response
impl From<VerificationResult> for VerificationResponse {
    fn from(result: VerificationResult) -> Self {
        Self {
            request_id: result.verification_id,
            result,
            timestamp: chrono::Utc::now().to_rfc3339(),
        }
    }
}

/// Convert SMTResult to string
impl From<SMTResult> for String {
    fn from(result: SMTResult) -> Self {
        result.as_str().to_string()
    }
}

/// Convert SolverType to string
impl From<SolverType> for String {
    fn from(solver_type: SolverType) -> Self {
        solver_type.as_str().to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verification_request() {
        let request = VerificationRequest {
            request_id: "test-123".to_string(),
            script: "(set-logic QF_LIA)\n(assert (> x 0))\n(check-sat)".to_string(),
            solver_preferences: vec!["z3".to_string(), "cvc5".to_string()],
            timeout_ms: Some(5000),
            max_memory_mb: Some(512),
        };
        
        assert_eq!(request.request_id, "test-123");
        assert!(request.script.contains("set-logic"));
        assert_eq!(request.solver_preferences.len(), 2);
    }

    #[test]
    fn test_health_check_response() {
        let response = HealthCheckResponse {
            status: HealthStatus::Serving,
            details: HashMap::new(),
        };
        
        match response.status {
            HealthStatus::Serving => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_smt_result_conversion() {
        let result = SMTResult::Sat;
        let result_str: String = result.into();
        assert_eq!(result_str, "sat");
    }

    #[test]
    fn test_solver_type_conversion() {
        let solver_type = SolverType::Z3;
        let solver_str: String = solver_type.into();
        assert_eq!(solver_str, "z3");
    }
} 