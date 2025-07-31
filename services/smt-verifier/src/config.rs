//! Configuration for SMT verification service
//! 
//! This module handles configuration management for the SMT verifier.

use serde::{Deserialize, Serialize};
use std::path::PathBuf;

use crate::solver::{SolverType, SolverConfig};

/// Configuration for the SMT verifier
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifierConfig {
    /// Enable Z3 solver
    pub enable_z3: bool,
    
    /// Enable CVC5 solver
    pub enable_cvc5: bool,
    
    /// Z3 configuration
    pub z3_config: SolverConfig,
    
    /// CVC5 configuration
    pub cvc5_config: SolverConfig,
    
    /// Sandbox configuration
    pub sandbox: SandboxConfig,
    
    /// Metrics configuration
    pub metrics: MetricsConfig,
    
    /// Server configuration
    pub server: ServerConfig,
    
    /// Enable differential testing
    pub enable_differential_testing: bool,
    
    /// Enable sandboxing
    pub enable_sandboxing: bool,
    
    /// Enable metrics collection
    pub enable_metrics: bool,
    
    /// Enable health checks
    pub enable_health_checks: bool,
    
    /// Output directory for results
    pub output_dir: PathBuf,
    
    /// Log level
    pub log_level: String,
}

/// Sandbox configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SandboxConfig {
    /// Enable WebAssembly sandboxing
    pub enable_wasm: bool,
    
    /// Wasmtime configuration
    pub wasmtime: WasmtimeConfig,
    
    /// Memory limit for sandbox (MB)
    pub memory_limit_mb: u64,
    
    /// Timeout for sandbox execution (ms)
    pub timeout_ms: u64,
    
    /// Enable resource limits
    pub enable_resource_limits: bool,
    
    /// Enable network isolation
    pub enable_network_isolation: bool,
    
    /// Enable filesystem isolation
    pub enable_fs_isolation: bool,
}

/// Wasmtime configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WasmtimeConfig {
    /// Wasmtime engine configuration
    pub engine_config: String,
    
    /// Enable WASI
    pub enable_wasi: bool,
    
    /// Enable WASI preview1
    pub enable_wasi_preview1: bool,
    
    /// Enable WASI preview2
    pub enable_wasi_preview2: bool,
    
    /// WASI environment variables
    pub wasi_env_vars: Vec<(String, String)>,
    
    /// WASI preopen directories
    pub wasi_preopen_dirs: Vec<(String, String)>,
}

/// Metrics configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricsConfig {
    /// Enable Prometheus metrics
    pub enable_prometheus: bool,
    
    /// Prometheus endpoint
    pub prometheus_endpoint: String,
    
    /// Enable OpenTelemetry
    pub enable_opentelemetry: bool,
    
    /// OpenTelemetry endpoint
    pub opentelemetry_endpoint: String,
    
    /// Metrics collection interval (seconds)
    pub collection_interval_seconds: u64,
    
    /// Enable custom metrics
    pub enable_custom_metrics: bool,
}

/// Server configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerConfig {
    /// gRPC server host
    pub host: String,
    
    /// gRPC server port
    pub port: u16,
    
    /// Enable TLS
    pub enable_tls: bool,
    
    /// TLS certificate path
    pub tls_cert_path: Option<PathBuf>,
    
    /// TLS key path
    pub tls_key_path: Option<PathBuf>,
    
    /// Maximum concurrent connections
    pub max_concurrent_connections: u32,
    
    /// Request timeout (seconds)
    pub request_timeout_seconds: u64,
    
    /// Enable health check endpoint
    pub enable_health_check: bool,
    
    /// Enable metrics endpoint
    pub enable_metrics_endpoint: bool,
}

impl Default for VerifierConfig {
    fn default() -> Self {
        Self {
            enable_z3: true,
            enable_cvc5: true,
            z3_config: SolverConfig::new(SolverType::Z3),
            cvc5_config: SolverConfig::new(SolverType::CVC5),
            sandbox: SandboxConfig::default(),
            metrics: MetricsConfig::default(),
            server: ServerConfig::default(),
            enable_differential_testing: true,
            enable_sandboxing: true,
            enable_metrics: true,
            enable_health_checks: true,
            output_dir: PathBuf::from("output"),
            log_level: "info".to_string(),
        }
    }
}

impl Default for SandboxConfig {
    fn default() -> Self {
        Self {
            enable_wasm: true,
            wasmtime: WasmtimeConfig::default(),
            memory_limit_mb: 512,
            timeout_ms: 10000,
            enable_resource_limits: true,
            enable_network_isolation: true,
            enable_fs_isolation: true,
        }
    }
}

impl Default for WasmtimeConfig {
    fn default() -> Self {
        Self {
            engine_config: "default".to_string(),
            enable_wasi: true,
            enable_wasi_preview1: true,
            enable_wasi_preview2: false,
            wasi_env_vars: vec![],
            wasi_preopen_dirs: vec![],
        }
    }
}

impl Default for MetricsConfig {
    fn default() -> Self {
        Self {
            enable_prometheus: true,
            prometheus_endpoint: "0.0.0.0:9090".to_string(),
            enable_opentelemetry: true,
            opentelemetry_endpoint: "http://localhost:4317".to_string(),
            collection_interval_seconds: 60,
            enable_custom_metrics: true,
        }
    }
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            host: "0.0.0.0".to_string(),
            port: 8080,
            enable_tls: false,
            tls_cert_path: None,
            tls_key_path: None,
            max_concurrent_connections: 1000,
            request_timeout_seconds: 30,
            enable_health_check: true,
            enable_metrics_endpoint: true,
        }
    }
}

impl VerifierConfig {
    /// Create configuration from file
    pub fn from_file(path: &PathBuf) -> Result<Self, crate::error::VerifierError> {
        let content = std::fs::read_to_string(path)
            .map_err(|e| crate::error::VerifierError::ConfigError(e.to_string()))?;
        
        toml::from_str(&content)
            .map_err(|e| crate::error::VerifierError::ConfigError(e.to_string()))
    }

    /// Save configuration to file
    pub fn save_to_file(&self, path: &PathBuf) -> Result<(), crate::error::VerifierError> {
        let content = toml::to_string_pretty(self)
            .map_err(|e| crate::error::VerifierError::ConfigError(e.to_string()))?;
        
        std::fs::write(path, content)
            .map_err(|e| crate::error::VerifierError::ConfigError(e.to_string()))
    }

    /// Validate configuration
    pub fn validate(&self) -> Result<(), crate::error::VerifierError> {
        // Validate that at least one solver is enabled
        if !self.enable_z3 && !self.enable_cvc5 {
            return Err(crate::error::VerifierError::ConfigError(
                "At least one solver must be enabled".to_string()
            ));
        }

        // Validate Z3 configuration if enabled
        if self.enable_z3 {
            self.z3_config.validate()?;
        }

        // Validate CVC5 configuration if enabled
        if self.enable_cvc5 {
            self.cvc5_config.validate()?;
        }

        // Validate sandbox configuration
        self.sandbox.validate()?;

        // Validate metrics configuration
        self.metrics.validate()?;

        // Validate server configuration
        self.server.validate()?;

        // Create output directory if it doesn't exist
        if !self.output_dir.exists() {
            std::fs::create_dir_all(&self.output_dir)
                .map_err(|e| crate::error::VerifierError::ConfigError(e.to_string()))?;
        }

        Ok(())
    }

    /// Get enabled solvers
    pub fn get_enabled_solvers(&self) -> Vec<SolverType> {
        let mut solvers = Vec::new();
        
        if self.enable_z3 {
            solvers.push(SolverType::Z3);
        }
        
        if self.enable_cvc5 {
            solvers.push(SolverType::CVC5);
        }
        
        solvers
    }

    /// Get configuration as environment variables
    pub fn as_env_vars(&self) -> Vec<(String, String)> {
        vec![
            ("ENABLE_Z3".to_string(), self.enable_z3.to_string()),
            ("ENABLE_CVC5".to_string(), self.enable_cvc5.to_string()),
            ("ENABLE_DIFFERENTIAL_TESTING".to_string(), self.enable_differential_testing.to_string()),
            ("ENABLE_SANDBOXING".to_string(), self.enable_sandboxing.to_string()),
            ("ENABLE_METRICS".to_string(), self.enable_metrics.to_string()),
            ("ENABLE_HEALTH_CHECKS".to_string(), self.enable_health_checks.to_string()),
            ("LOG_LEVEL".to_string(), self.log_level.clone()),
            ("OUTPUT_DIR".to_string(), self.output_dir.to_string_lossy().to_string()),
        ]
    }
}

impl SandboxConfig {
    /// Validate sandbox configuration
    pub fn validate(&self) -> Result<(), crate::error::VerifierError> {
        if self.memory_limit_mb == 0 {
            return Err(crate::error::VerifierError::ConfigError(
                "Memory limit must be greater than 0".to_string()
            ));
        }

        if self.timeout_ms == 0 {
            return Err(crate::error::VerifierError::ConfigError(
                "Timeout must be greater than 0".to_string()
            ));
        }

        self.wasmtime.validate()?;

        Ok(())
    }
}

impl WasmtimeConfig {
    /// Validate Wasmtime configuration
    pub fn validate(&self) -> Result<(), crate::error::VerifierError> {
        if self.engine_config.is_empty() {
            return Err(crate::error::VerifierError::ConfigError(
                "Engine config cannot be empty".to_string()
            ));
        }

        Ok(())
    }
}

impl MetricsConfig {
    /// Validate metrics configuration
    pub fn validate(&self) -> Result<(), crate::error::VerifierError> {
        if self.collection_interval_seconds == 0 {
            return Err(crate::error::VerifierError::ConfigError(
                "Collection interval must be greater than 0".to_string()
            ));
        }

        Ok(())
    }
}

impl ServerConfig {
    /// Validate server configuration
    pub fn validate(&self) -> Result<(), crate::error::VerifierError> {
        if self.host.is_empty() {
            return Err(crate::error::VerifierError::ConfigError(
                "Host cannot be empty".to_string()
            ));
        }

        if self.port == 0 {
            return Err(crate::error::VerifierError::ConfigError(
                "Port must be greater than 0".to_string()
            ));
        }

        if self.max_concurrent_connections == 0 {
            return Err(crate::error::VerifierError::ConfigError(
                "Max concurrent connections must be greater than 0".to_string()
            ));
        }

        if self.request_timeout_seconds == 0 {
            return Err(crate::error::VerifierError::ConfigError(
                "Request timeout must be greater than 0".to_string()
            ));
        }

        // Validate TLS configuration if enabled
        if self.enable_tls {
            if self.tls_cert_path.is_none() {
                return Err(crate::error::VerifierError::ConfigError(
                    "TLS certificate path is required when TLS is enabled".to_string()
                ));
            }

            if self.tls_key_path.is_none() {
                return Err(crate::error::VerifierError::ConfigError(
                    "TLS key path is required when TLS is enabled".to_string()
                ));
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = VerifierConfig::default();
        assert!(config.enable_z3);
        assert!(config.enable_cvc5);
        assert!(config.enable_differential_testing);
        assert!(config.enable_sandboxing);
        assert!(config.enable_metrics);
    }

    #[test]
    fn test_config_validation() {
        let mut config = VerifierConfig::default();
        config.enable_z3 = false;
        config.enable_cvc5 = false;
        
        let result = config.validate();
        assert!(result.is_err());
    }

    #[test]
    fn test_enabled_solvers() {
        let config = VerifierConfig::default();
        let solvers = config.get_enabled_solvers();
        assert_eq!(solvers.len(), 2);
        assert!(solvers.contains(&SolverType::Z3));
        assert!(solvers.contains(&SolverType::CVC5));
    }

    #[test]
    fn test_config_env_vars() {
        let config = VerifierConfig::default();
        let env_vars = config.as_env_vars();
        
        assert!(!env_vars.is_empty());
        assert!(env_vars.iter().any(|(k, _)| k == "ENABLE_Z3"));
        assert!(env_vars.iter().any(|(k, _)| k == "ENABLE_CVC5"));
    }
} 