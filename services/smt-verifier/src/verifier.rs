//! Verification result types and processing
//! 
//! This module defines the verification result types and processing logic
//! for the SMT verification service.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::SystemTime;

use crate::solver::SolverType;

/// Result of an SMT verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationResult {
    pub verification_id: String,
    pub solver_type: SolverType,
    pub success: bool,
    pub result: SMTResult,
    pub execution_time_ms: u64,
    pub memory_usage_mb: u64,
    pub unsat_core: Option<Vec<String>>,
    pub model: Option<String>,
    pub errors: Vec<String>,
    pub metadata: HashMap<String, String>,
}

/// SMT solver result
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum SMTResult {
    Sat,
    Unsat,
    Unknown,
    Error,
}

impl SMTResult {
    /// Check if the result indicates satisfiability
    pub fn is_sat(&self) -> bool {
        matches!(self, SMTResult::Sat)
    }

    /// Check if the result indicates unsatisfiability
    pub fn is_unsat(&self) -> bool {
        matches!(self, SMTResult::Unsat)
    }

    /// Check if the result is unknown
    pub fn is_unknown(&self) -> bool {
        matches!(self, SMTResult::Unknown)
    }

    /// Check if the result indicates an error
    pub fn is_error(&self) -> bool {
        matches!(self, SMTResult::Error)
    }

    /// Get the result as a string
    pub fn as_str(&self) -> &'static str {
        match self {
            SMTResult::Sat => "sat",
            SMTResult::Unsat => "unsat",
            SMTResult::Unknown => "unknown",
            SMTResult::Error => "error",
        }
    }

    /// Parse result from string
    pub fn from_str(s: &str) -> Option<Self> {
        match s.trim().to_lowercase().as_str() {
            "sat" => Some(SMTResult::Sat),
            "unsat" => Some(SMTResult::Unsat),
            "unknown" => Some(SMTResult::Unknown),
            "error" => Some(SMTResult::Error),
            _ => None,
        }
    }
}

/// Verification statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationStats {
    pub total_verifications: u64,
    pub successful_verifications: u64,
    pub failed_verifications: u64,
    pub sat_count: u64,
    pub unsat_count: u64,
    pub unknown_count: u64,
    pub error_count: u64,
    pub average_execution_time_ms: u64,
    pub average_memory_usage_mb: u64,
    pub solver_stats: HashMap<SolverType, SolverStats>,
}

/// Solver-specific statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SolverStats {
    pub solver_type: SolverType,
    pub total_verifications: u64,
    pub successful_verifications: u64,
    pub failed_verifications: u64,
    pub sat_count: u64,
    pub unsat_count: u64,
    pub unknown_count: u64,
    pub error_count: u64,
    pub average_execution_time_ms: u64,
    pub average_memory_usage_mb: u64,
    pub last_used: Option<SystemTime>,
}

impl SolverStats {
    /// Create new solver statistics
    pub fn new(solver_type: SolverType) -> Self {
        Self {
            solver_type,
            total_verifications: 0,
            successful_verifications: 0,
            failed_verifications: 0,
            sat_count: 0,
            unsat_count: 0,
            unknown_count: 0,
            error_count: 0,
            average_execution_time_ms: 0,
            average_memory_usage_mb: 0,
            last_used: None,
        }
    }

    /// Update statistics with a verification result
    pub fn update(&mut self, result: &VerificationResult) {
        self.total_verifications += 1;
        self.last_used = Some(SystemTime::now());

        if result.success {
            self.successful_verifications += 1;
        } else {
            self.failed_verifications += 1;
        }

        // Update result counts
        match result.result {
            SMTResult::Sat => self.sat_count += 1,
            SMTResult::Unsat => self.unsat_count += 1,
            SMTResult::Unknown => self.unknown_count += 1,
            SMTResult::Error => self.error_count += 1,
        }

        // Update averages
        self.average_execution_time_ms = 
            (self.average_execution_time_ms * (self.total_verifications - 1) + result.execution_time_ms) 
            / self.total_verifications;
        
        self.average_memory_usage_mb = 
            (self.average_memory_usage_mb * (self.total_verifications - 1) + result.memory_usage_mb) 
            / self.total_verifications;
    }

    /// Get success rate
    pub fn success_rate(&self) -> f64 {
        if self.total_verifications == 0 {
            0.0
        } else {
            self.successful_verifications as f64 / self.total_verifications as f64
        }
    }

    /// Get result distribution
    pub fn result_distribution(&self) -> HashMap<SMTResult, f64> {
        let mut distribution = HashMap::new();
        let total = self.total_verifications as f64;
        
        if total > 0.0 {
            distribution.insert(SMTResult::Sat, self.sat_count as f64 / total);
            distribution.insert(SMTResult::Unsat, self.unsat_count as f64 / total);
            distribution.insert(SMTResult::Unknown, self.unknown_count as f64 / total);
            distribution.insert(SMTResult::Error, self.error_count as f64 / total);
        }
        
        distribution
    }
}

/// Verification result processor
pub struct ResultProcessor;

impl ResultProcessor {
    /// Process verification results and detect anomalies
    pub fn process_results(results: &[VerificationResult]) -> ProcessingResult {
        if results.is_empty() {
            return ProcessingResult {
                consensus: None,
                anomalies: vec![],
                confidence: 0.0,
            };
        }

        // Check for consensus
        let first_result = &results[0];
        let consensus = if results.iter().all(|r| r.result == first_result.result) {
            Some(first_result.result.clone())
        } else {
            None
        };

        // Detect anomalies
        let mut anomalies = Vec::new();
        
        // Check for execution time anomalies
        let avg_time: u64 = results.iter().map(|r| r.execution_time_ms).sum::<u64>() / results.len() as u64;
        for result in results {
            if result.execution_time_ms > avg_time * 3 {
                anomalies.push(Anomaly::ExecutionTimeOutlier {
                    solver: result.solver_type.clone(),
                    time_ms: result.execution_time_ms,
                    expected_ms: avg_time,
                });
            }
        }

        // Check for memory usage anomalies
        let avg_memory: u64 = results.iter().map(|r| r.memory_usage_mb).sum::<u64>() / results.len() as u64;
        for result in results {
            if result.memory_usage_mb > avg_memory * 2 {
                anomalies.push(Anomaly::MemoryUsageOutlier {
                    solver: result.solver_type.clone(),
                    memory_mb: result.memory_usage_mb,
                    expected_mb: avg_memory,
                });
            }
        }

        // Check for result disagreements
        if consensus.is_none() {
            anomalies.push(Anomaly::SolverDisagreement {
                results: results.iter().map(|r| r.result.clone()).collect(),
            });
        }

        // Calculate confidence
        let confidence = if consensus.is_some() && anomalies.is_empty() {
            1.0
        } else if consensus.is_some() {
            0.8
        } else {
            0.0
        };

        ProcessingResult {
            consensus,
            anomalies,
            confidence,
        }
    }

    /// Validate verification result
    pub fn validate_result(result: &VerificationResult) -> Result<(), ValidationError> {
        if result.verification_id.is_empty() {
            return Err(ValidationError::InvalidVerificationId);
        }

        if result.execution_time_ms == 0 && result.success {
            return Err(ValidationError::InvalidExecutionTime);
        }

        if result.memory_usage_mb == 0 && result.success {
            return Err(ValidationError::InvalidMemoryUsage);
        }

        if result.result == SMTResult::Error && result.errors.is_empty() {
            return Err(ValidationError::MissingErrorDetails);
        }

        Ok(())
    }
}

/// Result of processing verification results
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProcessingResult {
    pub consensus: Option<SMTResult>,
    pub anomalies: Vec<Anomaly>,
    pub confidence: f64,
}

/// Types of anomalies that can be detected
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Anomaly {
    ExecutionTimeOutlier {
        solver: SolverType,
        time_ms: u64,
        expected_ms: u64,
    },
    MemoryUsageOutlier {
        solver: SolverType,
        memory_mb: u64,
        expected_mb: u64,
    },
    SolverDisagreement {
        results: Vec<SMTResult>,
    },
    UnexpectedResult {
        solver: SolverType,
        result: SMTResult,
        expected: SMTResult,
    },
}

/// Validation error
#[derive(Debug, thiserror::Error)]
pub enum ValidationError {
    #[error("Invalid verification ID")]
    InvalidVerificationId,
    
    #[error("Invalid execution time")]
    InvalidExecutionTime,
    
    #[error("Invalid memory usage")]
    InvalidMemoryUsage,
    
    #[error("Missing error details")]
    MissingErrorDetails,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_smt_result_parsing() {
        assert_eq!(SMTResult::from_str("sat"), Some(SMTResult::Sat));
        assert_eq!(SMTResult::from_str("unsat"), Some(SMTResult::Unsat));
        assert_eq!(SMTResult::from_str("unknown"), Some(SMTResult::Unknown));
        assert_eq!(SMTResult::from_str("error"), Some(SMTResult::Error));
        assert_eq!(SMTResult::from_str("invalid"), None);
    }

    #[test]
    fn test_solver_stats() {
        let mut stats = SolverStats::new(SolverType::Z3);
        
        let result = VerificationResult {
            verification_id: "test".to_string(),
            solver_type: SolverType::Z3,
            success: true,
            result: SMTResult::Sat,
            execution_time_ms: 100,
            memory_usage_mb: 50,
            unsat_core: None,
            model: None,
            errors: vec![],
            metadata: HashMap::new(),
        };
        
        stats.update(&result);
        assert_eq!(stats.total_verifications, 1);
        assert_eq!(stats.successful_verifications, 1);
        assert_eq!(stats.sat_count, 1);
        assert_eq!(stats.success_rate(), 1.0);
    }

    #[test]
    fn test_result_processing() {
        let results = vec![
            VerificationResult {
                verification_id: "test1".to_string(),
                solver_type: SolverType::Z3,
                success: true,
                result: SMTResult::Sat,
                execution_time_ms: 100,
                memory_usage_mb: 50,
                unsat_core: None,
                model: None,
                errors: vec![],
                metadata: HashMap::new(),
            },
            VerificationResult {
                verification_id: "test2".to_string(),
                solver_type: SolverType::CVC5,
                success: true,
                result: SMTResult::Sat,
                execution_time_ms: 120,
                memory_usage_mb: 60,
                unsat_core: None,
                model: None,
                errors: vec![],
                metadata: HashMap::new(),
            },
        ];
        
        let processing = ResultProcessor::process_results(&results);
        assert_eq!(processing.consensus, Some(SMTResult::Sat));
        assert_eq!(processing.confidence, 1.0);
        assert!(processing.anomalies.is_empty());
    }
} 