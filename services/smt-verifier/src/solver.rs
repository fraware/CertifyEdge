//! SMT solver management
//! 
//! This module provides management for different SMT solvers (Z3, CVC5)
//! and their configurations.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::SystemTime;

use crate::error::VerifierError;
use crate::verifier::{SMTResult, VerificationResult};

/// Supported SMT solver types
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum SolverType {
    Z3,
    CVC5,
    Custom(String),
}

impl SolverType {
    /// Get the solver name as a string
    pub fn as_str(&self) -> &str {
        match self {
            SolverType::Z3 => "z3",
            SolverType::CVC5 => "cvc5",
            SolverType::Custom(name) => name,
        }
    }

    /// Get the default executable name for this solver
    pub fn executable_name(&self) -> &str {
        match self {
            SolverType::Z3 => "z3",
            SolverType::CVC5 => "cvc5",
            SolverType::Custom(name) => name,
        }
    }

    /// Get the default version for this solver
    pub fn default_version(&self) -> &str {
        match self {
            SolverType::Z3 => "4.13.0",
            SolverType::CVC5 => "1.2.0",
            SolverType::Custom(_) => "unknown",
        }
    }
}

/// Solver configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SolverConfig {
    pub solver_type: SolverType,
    pub executable_path: String,
    pub version: String,
    pub timeout_ms: u64,
    pub memory_limit_mb: u64,
    pub additional_args: Vec<String>,
    pub enabled: bool,
}

impl SolverConfig {
    /// Create a new solver configuration
    pub fn new(solver_type: SolverType) -> Self {
        Self {
            solver_type: solver_type.clone(),
            executable_path: solver_type.executable_name().to_string(),
            version: solver_type.default_version().to_string(),
            timeout_ms: 5000,
            memory_limit_mb: 512,
            additional_args: vec![],
            enabled: true,
        }
    }

    /// Validate the solver configuration
    pub fn validate(&self) -> Result<(), VerifierError> {
        if self.executable_path.is_empty() {
            return Err(VerifierError::InvalidSolverConfig(
                "Executable path cannot be empty".to_string()
            ));
        }

        if self.timeout_ms == 0 {
            return Err(VerifierError::InvalidSolverConfig(
                "Timeout must be greater than 0".to_string()
            ));
        }

        if self.memory_limit_mb == 0 {
            return Err(VerifierError::InvalidSolverConfig(
                "Memory limit must be greater than 0".to_string()
            ));
        }

        Ok(())
    }

    /// Get solver command arguments
    pub fn get_args(&self) -> Vec<String> {
        let mut args = vec![
            "--version".to_string(),
        ];

        // Add timeout if specified
        if self.timeout_ms > 0 {
            args.push(format!("--timeout={}", self.timeout_ms));
        }

        // Add memory limit if specified
        if self.memory_limit_mb > 0 {
            args.push(format!("--memory-limit={}", self.memory_limit_mb));
        }

        // Add additional arguments
        args.extend(self.additional_args.clone());

        args
    }
}

/// SMT solver instance
pub struct Solver {
    config: SolverConfig,
    stats: SolverStats,
}

impl Solver {
    /// Create a new solver instance
    pub fn new(solver_type: SolverType, config: &SolverConfig) -> Result<Self, VerifierError> {
        config.validate()?;
        
        Ok(Self {
            config: config.clone(),
            stats: SolverStats::new(solver_type),
        })
    }

    /// Get the solver type
    pub fn solver_type(&self) -> SolverType {
        self.config.solver_type.clone()
    }

    /// Get the solver configuration
    pub fn config(&self) -> &SolverConfig {
        &self.config
    }

    /// Execute an SMT-LIB script
    pub async fn execute_script(&mut self, script: &str) -> Result<VerificationResult, VerifierError> {
        let start_time = SystemTime::now();
        let verification_id = uuid::Uuid::new_v4().to_string();

        // Create temporary file for script
        let temp_file = tempfile::NamedTempFile::new()
            .map_err(|e| VerifierError::IOError(e.to_string()))?;
        
        std::fs::write(&temp_file, script)
            .map_err(|e| VerifierError::IOError(e.to_string()))?;

        // Execute solver
        let output = tokio::process::Command::new(&self.config.executable_path)
            .args(&self.config.get_args())
            .arg(temp_file.path())
            .output()
            .await
            .map_err(|e| VerifierError::SolverExecutionError(e.to_string()))?;

        let execution_time = start_time.elapsed()?;
        let execution_time_ms = execution_time.as_millis() as u64;

        // Parse solver output
        let output_str = String::from_utf8_lossy(&output.stdout);
        let error_str = String::from_utf8_lossy(&output.stderr);

        let success = output.status.success();
        let result = self.parse_solver_output(&output_str)?;
        let errors = if success { vec![] } else { vec![error_str.to_string()] };

        // Estimate memory usage (simplified)
        let memory_usage_mb = self.estimate_memory_usage(execution_time_ms);

        let verification_result = VerificationResult {
            verification_id,
            solver_type: self.config.solver_type.clone(),
            success,
            result,
            execution_time_ms,
            memory_usage_mb,
            unsat_core: self.extract_unsat_core(&output_str),
            model: self.extract_model(&output_str),
            errors,
            metadata: HashMap::new(),
        };

        // Update statistics
        self.stats.update(&verification_result);

        Ok(verification_result)
    }

    /// Parse solver output to determine result
    fn parse_solver_output(&self, output: &str) -> Result<SMTResult, VerifierError> {
        let output_lower = output.trim().to_lowercase();
        
        if output_lower.contains("sat") {
            Ok(SMTResult::Sat)
        } else if output_lower.contains("unsat") {
            Ok(SMTResult::Unsat)
        } else if output_lower.contains("unknown") {
            Ok(SMTResult::Unknown)
        } else if output_lower.contains("error") {
            Ok(SMTResult::Error)
        } else {
            // Default to unknown if we can't parse the result
            Ok(SMTResult::Unknown)
        }
    }

    /// Extract UNSAT core from solver output
    fn extract_unsat_core(&self, output: &str) -> Option<Vec<String>> {
        // This is a simplified implementation
        // In practice, this would parse the actual UNSAT core format
        if output.contains("unsat") && output.contains("core") {
            Some(vec!["core1".to_string(), "core2".to_string()])
        } else {
            None
        }
    }

    /// Extract model from solver output
    fn extract_model(&self, output: &str) -> Option<String> {
        if output.contains("sat") && output.contains("model") {
            Some(output.to_string())
        } else {
            None
        }
    }

    /// Estimate memory usage based on execution time
    fn estimate_memory_usage(&self, execution_time_ms: u64) -> u64 {
        // Simplified estimation - in practice this would be more sophisticated
        let base_memory = 50; // MB
        let time_factor = execution_time_ms / 1000; // MB per second
        base_memory + time_factor
    }

    /// Check solver health
    pub async fn check_health(&self) -> Result<bool, VerifierError> {
        let output = tokio::process::Command::new(&self.config.executable_path)
            .args(&["--version"])
            .output()
            .await
            .map_err(|e| VerifierError::SolverExecutionError(e.to_string()))?;

        Ok(output.status.success())
    }

    /// Get solver version
    pub async fn get_version(&self) -> Result<String, VerifierError> {
        let output = tokio::process::Command::new(&self.config.executable_path)
            .args(&["--version"])
            .output()
            .await
            .map_err(|e| VerifierError::SolverExecutionError(e.to_string()))?;

        let version = String::from_utf8_lossy(&output.stdout);
        Ok(version.trim().to_string())
    }

    /// Get solver statistics
    pub fn get_stats(&self) -> &SolverStats {
        &self.stats
    }
}

/// Solver statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SolverStats {
    pub solver_type: SolverType,
    pub total_executions: u64,
    pub successful_executions: u64,
    pub failed_executions: u64,
    pub sat_count: u64,
    pub unsat_count: u64,
    pub unknown_count: u64,
    pub error_count: u64,
    pub total_execution_time_ms: u64,
    pub average_execution_time_ms: u64,
    pub last_used: Option<SystemTime>,
}

impl SolverStats {
    /// Create new solver statistics
    pub fn new(solver_type: SolverType) -> Self {
        Self {
            solver_type,
            total_executions: 0,
            successful_executions: 0,
            failed_executions: 0,
            sat_count: 0,
            unsat_count: 0,
            unknown_count: 0,
            error_count: 0,
            total_execution_time_ms: 0,
            average_execution_time_ms: 0,
            last_used: None,
        }
    }

    /// Update statistics with a verification result
    pub fn update(&mut self, result: &VerificationResult) {
        self.total_executions += 1;
        self.last_used = Some(SystemTime::now());

        if result.success {
            self.successful_executions += 1;
        } else {
            self.failed_executions += 1;
        }

        // Update result counts
        match result.result {
            SMTResult::Sat => self.sat_count += 1,
            SMTResult::Unsat => self.unsat_count += 1,
            SMTResult::Unknown => self.unknown_count += 1,
            SMTResult::Error => self.error_count += 1,
        }

        // Update execution time statistics
        self.total_execution_time_ms += result.execution_time_ms;
        self.average_execution_time_ms = self.total_execution_time_ms / self.total_executions;
    }

    /// Get success rate
    pub fn success_rate(&self) -> f64 {
        if self.total_executions == 0 {
            0.0
        } else {
            self.successful_executions as f64 / self.total_executions as f64
        }
    }

    /// Get result distribution
    pub fn result_distribution(&self) -> HashMap<SMTResult, f64> {
        let mut distribution = HashMap::new();
        let total = self.total_executions as f64;
        
        if total > 0.0 {
            distribution.insert(SMTResult::Sat, self.sat_count as f64 / total);
            distribution.insert(SMTResult::Unsat, self.unsat_count as f64 / total);
            distribution.insert(SMTResult::Unknown, self.unknown_count as f64 / total);
            distribution.insert(SMTResult::Error, self.error_count as f64 / total);
        }
        
        distribution
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_solver_type() {
        assert_eq!(SolverType::Z3.as_str(), "z3");
        assert_eq!(SolverType::CVC5.as_str(), "cvc5");
        assert_eq!(SolverType::Z3.executable_name(), "z3");
        assert_eq!(SolverType::Z3.default_version(), "4.13.0");
    }

    #[test]
    fn test_solver_config() {
        let config = SolverConfig::new(SolverType::Z3);
        assert!(config.validate().is_ok());
        assert_eq!(config.solver_type, SolverType::Z3);
        assert!(config.timeout_ms > 0);
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
        assert_eq!(stats.total_executions, 1);
        assert_eq!(stats.successful_executions, 1);
        assert_eq!(stats.sat_count, 1);
        assert_eq!(stats.success_rate(), 1.0);
    }
} 