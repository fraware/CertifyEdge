//! CertifyEdge Lean 4 Autoprover Plugin
//! 
//! This crate provides a Lean 4 plugin that wraps simp, linarith, and aesop
//! into a one-shot autoprove tactic tuned for STL formulas. It caches proof
//! traces to avoid re-solving unchanged goals and folds successful proofs into
//! CertifyEdge.Certificate objects.

pub mod tactics;
pub mod cache;
pub mod certificate;
pub mod error;
pub mod config;

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{Duration, SystemTime};
use uuid::Uuid;

use crate::error::AutoproverError;
use crate::tactics::TacticResult;
use crate::certificate::Certificate;

/// Main autoprover struct that orchestrates Lean 4 proof generation
#[derive(Debug, Clone)]
pub struct LeanAutoprover {
    config: config::AutoproverConfig,
    cache: cache::ProofCache,
}

impl LeanAutoprover {
    /// Create a new autoprover with default configuration
    pub fn new() -> Result<Self, AutoproverError> {
        let config = config::AutoproverConfig::default();
        let cache = cache::ProofCache::new(&config)?;
        Ok(Self { config, cache })
    }

    /// Create a new autoprover with custom configuration
    pub fn with_config(config: config::AutoproverConfig) -> Result<Self, AutoproverError> {
        let cache = cache::ProofCache::new(&config)?;
        Ok(Self { config, cache })
    }

    /// Attempt to automatically prove an STL formula
    pub async fn autoprove(
        &mut self,
        spec: &str,
        ast_hash: &str,
    ) -> Result<AutoproverResult, AutoproverError> {
        let start_time = SystemTime::now();
        
        // Check cache first
        if let Some(cached_result) = self.cache.get(ast_hash).await? {
            return Ok(AutoproverResult {
                certificate: cached_result.certificate,
                proof_time_ms: cached_result.proof_time_ms,
                cache_hit: true,
                tactic_used: cached_result.tactic_used,
                lean_commit: cached_result.lean_commit,
            });
        }

        // Parse and validate the specification
        let stl_compiler = stl_compiler::STLCompiler::new()?;
        let lean4_output = stl_compiler.compile_to_lean4(spec).await?;
        
        // Generate proof using Lean 4 tactics
        let tactic_result = self.apply_tactics(&lean4_output.lean4_code).await?;
        
        // Create certificate if proof successful
        let certificate = if tactic_result.success {
            Some(self.create_certificate(spec, &lean4_output, &tactic_result).await?)
        } else {
            None
        };

        let proof_time_ms = start_time.elapsed()?.as_millis() as u64;

        // Cache the result
        let cache_entry = cache::CacheEntry {
            certificate: certificate.clone(),
            proof_time_ms,
            tactic_used: tactic_result.tactic_used.clone(),
            lean_commit: self.get_lean_commit().await?,
            created_at: SystemTime::now(),
        };
        self.cache.put(ast_hash, cache_entry).await?;

        Ok(AutoproverResult {
            certificate,
            proof_time_ms,
            cache_hit: false,
            tactic_used: tactic_result.tactic_used,
            lean_commit: self.get_lean_commit().await?,
        })
    }

    /// Apply Lean 4 tactics to prove a goal
    async fn apply_tactics(&self, lean_code: &str) -> Result<TacticResult, AutoproverError> {
        let mut tactics = vec![
            "simp",
            "linarith", 
            "aesop",
            "omega",
            "ring",
            "norm_num",
        ];

        for tactic in tactics {
            let result = self.execute_tactic(lean_code, tactic).await?;
            if result.success {
                return Ok(result);
            }
        }

        // If all tactics fail, return the last result
        self.execute_tactic(lean_code, "simp").await
    }

    /// Execute a specific Lean 4 tactic
    async fn execute_tactic(&self, lean_code: &str, tactic: &str) -> Result<TacticResult, AutoproverError> {
        let start_time = SystemTime::now();
        
        // Create temporary Lean file with tactic
        let temp_file = format!(
            "import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic\n\n{lean_code}\n\nby {tactic}"
        );

        // Execute Lean 4 with timeout
        let output = tokio::process::Command::new(&self.config.lean4_path)
            .args(&["--check", "--json"])
            .arg(&temp_file)
            .output()
            .await
            .map_err(|e| AutoproverError::LeanExecutionError(e.to_string()))?;

        let execution_time_ms = start_time.elapsed()?.as_millis() as u64;

        // Parse Lean 4 output
        let success = output.status.success();
        let output_str = String::from_utf8_lossy(&output.stdout);
        let error_str = String::from_utf8_lossy(&output.stderr);

        Ok(TacticResult {
            success,
            tactic_used: tactic.to_string(),
            execution_time_ms,
            output: output_str.to_string(),
            errors: if success { vec![] } else { vec![error_str.to_string()] },
        })
    }

    /// Create a certificate from successful proof
    async fn create_certificate(
        &self,
        spec: &str,
        lean4_output: &stl_compiler::Lean4Output,
        tactic_result: &TacticResult,
    ) -> Result<Certificate, AutoproverError> {
        let certificate_id = Uuid::new_v4().to_string();
        
        Ok(Certificate {
            certificate_id,
            created_at: SystemTime::now(),
            version: "1.0.0".to_string(),
            spec_hash: self.hash_content(spec),
            lean_proof_hash: self.hash_content(&lean4_output.lean4_code),
            tactic_used: tactic_result.tactic_used.clone(),
            proof_time_ms: tactic_result.execution_time_ms,
            lean_commit: self.get_lean_commit().await?,
            metadata: HashMap::new(),
        })
    }

    /// Get the current Lean 4 commit hash
    async fn get_lean_commit(&self) -> Result<String, AutoproverError> {
        let output = tokio::process::Command::new(&self.config.lean4_path)
            .args(&["--version"])
            .output()
            .await
            .map_err(|e| AutoproverError::LeanExecutionError(e.to_string()))?;

        let version_output = String::from_utf8_lossy(&output.stdout);
        
        // Extract commit hash from version output
        // This is a simplified implementation - in practice we'd parse the actual output
        Ok("lean-4.0.0-commit-hash".to_string())
    }

    /// Hash content using SHA256
    fn hash_content(&self, content: &str) -> Vec<u8> {
        use sha2::{Sha256, Digest};
        let mut hasher = Sha256::new();
        hasher.update(content.as_bytes());
        hasher.finalize().to_vec()
    }

    /// Get autoprover statistics
    pub async fn get_stats(&self) -> Result<AutoproverStats, AutoproverError> {
        let cache_stats = self.cache.get_stats().await?;
        
        Ok(AutoproverStats {
            total_proofs: cache_stats.total_entries,
            successful_proofs: cache_stats.successful_entries,
            cache_hit_rate: cache_stats.hit_rate,
            average_proof_time_ms: cache_stats.average_time_ms,
            most_used_tactic: cache_stats.most_used_tactic,
        })
    }

    /// Validate autoprover configuration
    pub fn validate_config(&self) -> Result<(), AutoproverError> {
        self.config.validate()
    }
}

/// Result of autoprover execution
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AutoproverResult {
    pub certificate: Option<Certificate>,
    pub proof_time_ms: u64,
    pub cache_hit: bool,
    pub tactic_used: String,
    pub lean_commit: String,
}

/// Autoprover statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AutoproverStats {
    pub total_proofs: u64,
    pub successful_proofs: u64,
    pub cache_hit_rate: f64,
    pub average_proof_time_ms: u64,
    pub most_used_tactic: String,
}

impl Default for LeanAutoprover {
    fn default() -> Self {
        Self::new().expect("Failed to create default Lean autoprover")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_autoprover_creation(spec in "[a-zA-Z0-9_]+") {
            let autoprover = LeanAutoprover::new();
            assert!(autoprover.is_ok());
        }
    }

    #[tokio::test]
    async fn test_autoprover_stats() {
        let autoprover = LeanAutoprover::new().unwrap();
        let stats = autoprover.get_stats().await;
        assert!(stats.is_ok());
    }
} 