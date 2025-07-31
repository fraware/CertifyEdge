//! Configuration for Lean 4 autoprover
//! 
//! This module handles configuration management for the autoprover.

use serde::{Deserialize, Serialize};
use std::path::PathBuf;

/// Configuration for the Lean 4 autoprover
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AutoproverConfig {
    /// Path to Lean 4 executable
    pub lean4_path: String,
    
    /// Path to Lean 4 library
    pub lean4_library_path: String,
    
    /// Cache database URL
    pub cache_database_url: String,
    
    /// Cache TTL in seconds
    pub cache_ttl_seconds: u64,
    
    /// Maximum proof time in milliseconds
    pub max_proof_time_ms: u64,
    
    /// Maximum memory usage in MB
    pub max_memory_mb: u64,
    
    /// Enable caching
    pub enable_cache: bool,
    
    /// Enable parallel execution
    pub enable_parallel: bool,
    
    /// Number of parallel threads
    pub num_threads: usize,
    
    /// Enable verbose logging
    pub verbose: bool,
    
    /// Enable debug mode
    pub debug: bool,
    
    /// Output directory for certificates
    pub output_dir: PathBuf,
    
    /// Enable certificate signing
    pub enable_signing: bool,
    
    /// Certificate signing key path
    pub signing_key_path: Option<PathBuf>,
}

impl Default for AutoproverConfig {
    fn default() -> Self {
        Self {
            lean4_path: "lean".to_string(),
            lean4_library_path: "/usr/local/lib/lean".to_string(),
            cache_database_url: "sqlite:cache.db".to_string(),
            cache_ttl_seconds: 86400, // 24 hours
            max_proof_time_ms: 5000,  // 5 seconds
            max_memory_mb: 512,
            enable_cache: true,
            enable_parallel: true,
            num_threads: num_cpus::get(),
            verbose: false,
            debug: false,
            output_dir: PathBuf::from("output"),
            enable_signing: false,
            signing_key_path: None,
        }
    }
}

impl AutoproverConfig {
    /// Create configuration from file
    pub fn from_file(path: &PathBuf) -> Result<Self, crate::error::AutoproverError> {
        let content = std::fs::read_to_string(path)
            .map_err(|e| crate::error::AutoproverError::ConfigError(e.to_string()))?;
        
        toml::from_str(&content)
            .map_err(|e| crate::error::AutoproverError::ConfigError(e.to_string()))
    }

    /// Save configuration to file
    pub fn save_to_file(&self, path: &PathBuf) -> Result<(), crate::error::AutoproverError> {
        let content = toml::to_string_pretty(self)
            .map_err(|e| crate::error::AutoproverError::ConfigError(e.to_string()))?;
        
        std::fs::write(path, content)
            .map_err(|e| crate::error::AutoproverError::ConfigError(e.to_string()))
    }

    /// Validate configuration
    pub fn validate(&self) -> Result<(), crate::error::AutoproverError> {
        // Check if Lean 4 executable exists
        if !std::path::Path::new(&self.lean4_path).exists() {
            return Err(crate::error::AutoproverError::ConfigError(
                format!("Lean 4 executable not found at: {}", self.lean4_path)
            ));
        }

        // Check if Lean 4 library path exists
        if !std::path::Path::new(&self.lean4_library_path).exists() {
            return Err(crate::error::AutoproverError::ConfigError(
                format!("Lean 4 library not found at: {}", self.lean4_library_path)
            ));
        }

        // Validate cache database URL
        if !self.cache_database_url.starts_with("sqlite:") {
            return Err(crate::error::AutoproverError::ConfigError(
                "Cache database URL must start with 'sqlite:'".to_string()
            ));
        }

        // Validate timeouts
        if self.max_proof_time_ms == 0 {
            return Err(crate::error::AutoproverError::ConfigError(
                "Max proof time must be greater than 0".to_string()
            ));
        }

        // Validate memory limits
        if self.max_memory_mb == 0 {
            return Err(crate::error::AutoproverError::ConfigError(
                "Max memory must be greater than 0".to_string()
            ));
        }

        // Validate thread count
        if self.num_threads == 0 {
            return Err(crate::error::AutoproverError::ConfigError(
                "Number of threads must be greater than 0".to_string()
            ));
        }

        // Create output directory if it doesn't exist
        if !self.output_dir.exists() {
            std::fs::create_dir_all(&self.output_dir)
                .map_err(|e| crate::error::AutoproverError::ConfigError(e.to_string()))?;
        }

        Ok(())
    }

    /// Get Lean 4 version
    pub fn get_lean_version(&self) -> Result<String, crate::error::AutoproverError> {
        let output = std::process::Command::new(&self.lean4_path)
            .args(&["--version"])
            .output()
            .map_err(|e| crate::error::AutoproverError::ConfigError(e.to_string()))?;

        let version = String::from_utf8_lossy(&output.stdout);
        Ok(version.trim().to_string())
    }

    /// Check if Lean 4 is available
    pub fn is_lean_available(&self) -> bool {
        std::process::Command::new(&self.lean4_path)
            .args(&["--version"])
            .output()
            .is_ok()
    }

    /// Get configuration as environment variables
    pub fn as_env_vars(&self) -> Vec<(String, String)> {
        vec![
            ("LEAN4_PATH".to_string(), self.lean4_path.clone()),
            ("LEAN4_LIBRARY_PATH".to_string(), self.lean4_library_path.clone()),
            ("CACHE_DATABASE_URL".to_string(), self.cache_database_url.clone()),
            ("CACHE_TTL_SECONDS".to_string(), self.cache_ttl_seconds.to_string()),
            ("MAX_PROOF_TIME_MS".to_string(), self.max_proof_time_ms.to_string()),
            ("MAX_MEMORY_MB".to_string(), self.max_memory_mb.to_string()),
            ("ENABLE_CACHE".to_string(), self.enable_cache.to_string()),
            ("ENABLE_PARALLEL".to_string(), self.enable_parallel.to_string()),
            ("NUM_THREADS".to_string(), self.num_threads.to_string()),
            ("VERBOSE".to_string(), self.verbose.to_string()),
            ("DEBUG".to_string(), self.debug.to_string()),
            ("OUTPUT_DIR".to_string(), self.output_dir.to_string_lossy().to_string()),
            ("ENABLE_SIGNING".to_string(), self.enable_signing.to_string()),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = AutoproverConfig::default();
        assert!(!config.lean4_path.is_empty());
        assert!(config.max_proof_time_ms > 0);
        assert!(config.max_memory_mb > 0);
        assert!(config.num_threads > 0);
    }

    #[test]
    fn test_config_validation() {
        let mut config = AutoproverConfig::default();
        config.lean4_path = "/nonexistent/lean".to_string();
        
        let result = config.validate();
        assert!(result.is_err());
    }

    #[test]
    fn test_config_env_vars() {
        let config = AutoproverConfig::default();
        let env_vars = config.as_env_vars();
        
        assert!(!env_vars.is_empty());
        assert!(env_vars.iter().any(|(k, _)| k == "LEAN4_PATH"));
    }
} 