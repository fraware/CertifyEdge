//! Lean 4 tactics for STL formula proving
//! 
//! This module provides tactics specifically tuned for Signal Temporal Logic
//! formulas, including simp, linarith, aesop, and custom tactics.

use serde::{Deserialize, Serialize};
use std::time::SystemTime;

/// Result of applying a Lean 4 tactic
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TacticResult {
    pub success: bool,
    pub tactic_used: String,
    pub execution_time_ms: u64,
    pub output: String,
    pub errors: Vec<String>,
}

/// Available Lean 4 tactics for STL proving
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Tactic {
    Simp,
    Linarith,
    Aesop,
    Omega,
    Ring,
    NormNum,
    Custom(String),
}

impl Tactic {
    /// Get the tactic name as a string
    pub fn as_str(&self) -> &str {
        match self {
            Tactic::Simp => "simp",
            Tactic::Linarith => "linarith",
            Tactic::Aesop => "aesop",
            Tactic::Omega => "omega",
            Tactic::Ring => "ring",
            Tactic::NormNum => "norm_num",
            Tactic::Custom(name) => name,
        }
    }

    /// Check if this tactic is suitable for the given formula type
    pub fn is_suitable_for(&self, formula_type: &str) -> bool {
        match self {
            Tactic::Simp => true, // Always suitable
            Tactic::Linarith => formula_type.contains("linear"),
            Tactic::Aesop => formula_type.contains("automation"),
            Tactic::Omega => formula_type.contains("integer"),
            Tactic::Ring => formula_type.contains("algebraic"),
            Tactic::NormNum => formula_type.contains("numeric"),
            Tactic::Custom(_) => true,
        }
    }

    /// Get the timeout for this tactic (in milliseconds)
    pub fn timeout_ms(&self) -> u64 {
        match self {
            Tactic::Simp => 1000,
            Tactic::Linarith => 2000,
            Tactic::Aesop => 5000,
            Tactic::Omega => 3000,
            Tactic::Ring => 1500,
            Tactic::NormNum => 500,
            Tactic::Custom(_) => 1000,
        }
    }
}

/// Tactic execution context
#[derive(Debug, Clone)]
pub struct TacticContext {
    pub formula: String,
    pub assumptions: Vec<String>,
    pub goal: String,
    pub timeout_ms: u64,
    pub max_memory_mb: u64,
}

impl TacticContext {
    /// Create a new tactic context
    pub fn new(formula: String, goal: String) -> Self {
        Self {
            formula,
            assumptions: vec![],
            goal,
            timeout_ms: 5000,
            max_memory_mb: 512,
        }
    }

    /// Add an assumption to the context
    pub fn with_assumption(mut self, assumption: String) -> Self {
        self.assumptions.push(assumption);
        self
    }

    /// Set the timeout for tactic execution
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }

    /// Set the memory limit for tactic execution
    pub fn with_memory_limit(mut self, max_memory_mb: u64) -> Self {
        self.max_memory_mb = max_memory_mb;
        self
    }

    /// Generate Lean 4 code for this context
    pub fn to_lean_code(&self) -> String {
        let mut code = String::new();
        
        // Add imports
        code.push_str("import Mathlib.Data.Real.Basic\n");
        code.push_str("import Mathlib.Tactic\n");
        code.push_str("import Mathlib.Tactic.Linarith\n");
        code.push_str("import Mathlib.Tactic.Aesop\n");
        code.push_str("import Mathlib.Tactic.Omega\n");
        code.push_str("import Mathlib.Tactic.Ring\n");
        code.push_str("import Mathlib.Tactic.NormNum\n\n");
        
        // Add assumptions
        for assumption in &self.assumptions {
            code.push_str(&format!("variable {}\n", assumption));
        }
        
        // Add the main formula
        code.push_str(&format!("theorem stl_formula : {}\n", self.formula));
        
        // Add the goal
        code.push_str(&format!("  := {}\n", self.goal));
        
        code
    }
}

/// Tactic execution statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TacticStats {
    pub tactic_name: String,
    pub success_count: u64,
    pub failure_count: u64,
    pub total_execution_time_ms: u64,
    pub average_execution_time_ms: u64,
    pub last_used: Option<SystemTime>,
}

impl TacticStats {
    /// Create new tactic statistics
    pub fn new(tactic_name: String) -> Self {
        Self {
            tactic_name,
            success_count: 0,
            failure_count: 0,
            total_execution_time_ms: 0,
            average_execution_time_ms: 0,
            last_used: None,
        }
    }

    /// Update statistics with a new result
    pub fn update(&mut self, result: &TacticResult) {
        if result.success {
            self.success_count += 1;
        } else {
            self.failure_count += 1;
        }
        
        self.total_execution_time_ms += result.execution_time_ms;
        self.average_execution_time_ms = self.total_execution_time_ms / 
            (self.success_count + self.failure_count);
        self.last_used = Some(SystemTime::now());
    }

    /// Get the success rate for this tactic
    pub fn success_rate(&self) -> f64 {
        let total = self.success_count + self.failure_count;
        if total == 0 {
            0.0
        } else {
            self.success_count as f64 / total as f64
        }
    }
}

/// Tactic execution error
#[derive(Debug, thiserror::Error)]
pub enum TacticError {
    #[error("Tactic execution timeout after {timeout_ms}ms")]
    Timeout { timeout_ms: u64 },
    
    #[error("Tactic execution failed: {message}")]
    ExecutionFailed { message: String },
    
    #[error("Invalid tactic: {tactic}")]
    InvalidTactic { tactic: String },
    
    #[error("Memory limit exceeded: {memory_mb}MB")]
    MemoryLimitExceeded { memory_mb: u64 },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tactic_as_str() {
        assert_eq!(Tactic::Simp.as_str(), "simp");
        assert_eq!(Tactic::Linarith.as_str(), "linarith");
        assert_eq!(Tactic::Aesop.as_str(), "aesop");
    }

    #[test]
    fn test_tactic_timeout() {
        assert_eq!(Tactic::Simp.timeout_ms(), 1000);
        assert_eq!(Tactic::Aesop.timeout_ms(), 5000);
    }

    #[test]
    fn test_tactic_context() {
        let context = TacticContext::new(
            "∀ t, voltage t > 0".to_string(),
            "simp".to_string(),
        );
        
        let lean_code = context.to_lean_code();
        assert!(lean_code.contains("import Mathlib"));
        assert!(lean_code.contains("theorem stl_formula"));
    }

    #[test]
    fn test_tactic_stats() {
        let mut stats = TacticStats::new("simp".to_string());
        
        let result = TacticResult {
            success: true,
            tactic_used: "simp".to_string(),
            execution_time_ms: 100,
            output: "success".to_string(),
            errors: vec![],
        };
        
        stats.update(&result);
        assert_eq!(stats.success_count, 1);
        assert_eq!(stats.failure_count, 0);
        assert_eq!(stats.success_rate(), 1.0);
    }
} 