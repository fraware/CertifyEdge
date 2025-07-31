//! Configuration for the CertifyEdge Auditor API

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::SystemTime;

use crate::error::AuditorError;
use crate::auth::AuthConfig;

/// Main configuration for the auditor API
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditorConfig {
    /// Server configuration
    pub server: ServerConfig,
    
    /// Authentication configuration
    pub auth: AuthConfig,
    
    /// Storage configuration
    pub storage: StorageConfig,
    
    /// OPA configuration
    pub opa: OpaConfig,
    
    /// Performance configuration
    pub performance: PerformanceConfig,
    
    /// Security configuration
    pub security: SecurityConfig,
    
    /// Monitoring configuration
    pub monitoring: MonitoringConfig,
    
    /// Rate limiting configuration
    pub rate_limiting: RateLimitingConfig,
    
    /// Cache configuration
    pub cache: CacheConfig,
    
    /// API configuration
    pub api: ApiConfig,
}

impl Default for AuditorConfig {
    fn default() -> Self {
        Self {
            server: ServerConfig::default(),
            auth: AuthConfig::default(),
            storage: StorageConfig::default(),
            opa: OpaConfig::default(),
            performance: PerformanceConfig::default(),
            security: SecurityConfig::default(),
            monitoring: MonitoringConfig::default(),
            rate_limiting: RateLimitingConfig::default(),
            cache: CacheConfig::default(),
            api: ApiConfig::default(),
        }
    }
}

impl AuditorConfig {
    /// Load configuration from file
    pub fn from_file(path: &std::path::Path) -> Result<Self, AuditorError> {
        let content = std::fs::read_to_string(path)
            .map_err(|e| AuditorError::ConfigError(format!("Failed to read config file: {}", e)))?;
        
        serde_json::from_str(&content)
            .map_err(|e| AuditorError::ConfigError(format!("Failed to parse config: {}", e)))
    }
    
    /// Save configuration to file
    pub fn save_to_file(&self, path: &std::path::Path) -> Result<(), AuditorError> {
        let content = serde_json::to_string_pretty(self)
            .map_err(|e| AuditorError::ConfigError(format!("Failed to serialize config: {}", e)))?;
        
        std::fs::write(path, content)
            .map_err(|e| AuditorError::ConfigError(format!("Failed to write config file: {}", e)))
    }
    
    /// Validate configuration
    pub fn validate(&self) -> Result<(), AuditorError> {
        self.server.validate()?;
        self.storage.validate()?;
        self.opa.validate()?;
        self.performance.validate()?;
        self.security.validate()?;
        self.monitoring.validate()?;
        self.rate_limiting.validate()?;
        self.cache.validate()?;
        self.api.validate()?;
        
        Ok(())
    }
    
    /// Get configuration as environment variables
    pub fn as_env_vars(&self) -> HashMap<String, String> {
        let mut vars = HashMap::new();
        
        // Server config
        vars.insert("AUDITOR_HOST".to_string(), self.server.host.clone());
        vars.insert("AUDITOR_PORT".to_string(), self.server.port.to_string());
        vars.insert("AUDITOR_WORKERS".to_string(), self.server.workers.to_string());
        
        // Auth config
        vars.insert("JWT_SECRET".to_string(), self.auth.jwt_secret.clone());
        vars.insert("JWT_ISSUER".to_string(), self.auth.jwt_issuer.clone());
        vars.insert("JWT_AUDIENCE".to_string(), self.auth.jwt_audience.clone());
        vars.insert("TOKEN_EXPIRY_SECONDS".to_string(), self.auth.token_expiry_seconds.to_string());
        
        // Storage config
        vars.insert("DATABASE_URL".to_string(), self.storage.database_url.clone());
        vars.insert("REDIS_URL".to_string(), self.storage.redis_url.clone());
        
        // OPA config
        vars.insert("OPA_ENDPOINT".to_string(), self.opa.endpoint.clone());
        vars.insert("OPA_TIMEOUT_SECONDS".to_string(), self.opa.timeout_seconds.to_string());
        
        vars
    }
}

/// Server configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerConfig {
    /// Server host
    pub host: String,
    
    /// Server port
    pub port: u16,
    
    /// Number of worker threads
    pub workers: usize,
    
    /// Request timeout (seconds)
    pub request_timeout_seconds: u64,
    
    /// Enable TLS
    pub enable_tls: bool,
    
    /// TLS certificate path
    pub tls_cert_path: Option<String>,
    
    /// TLS key path
    pub tls_key_path: Option<String>,
    
    /// Maximum request size (bytes)
    pub max_request_size: usize,
    
    /// Enable compression
    pub enable_compression: bool,
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            host: "127.0.0.1".to_string(),
            port: 8080,
            workers: num_cpus::get(),
            request_timeout_seconds: 30,
            enable_tls: false,
            tls_cert_path: None,
            tls_key_path: None,
            max_request_size: 10 * 1024 * 1024, // 10MB
            enable_compression: true,
        }
    }
}

impl ServerConfig {
    pub fn validate(&self) -> Result<(), AuditorError> {
        if self.port == 0 {
            return Err(AuditorError::ConfigError("Port cannot be 0".to_string()));
        }
        
        if self.workers == 0 {
            return Err(AuditorError::ConfigError("Workers cannot be 0".to_string()));
        }
        
        if self.enable_tls {
            if self.tls_cert_path.is_none() || self.tls_key_path.is_none() {
                return Err(AuditorError::ConfigError("TLS enabled but certificate/key paths not provided".to_string()));
            }
        }
        
        Ok(())
    }
}

/// Storage configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StorageConfig {
    /// Database URL
    pub database_url: String,
    
    /// Redis URL
    pub redis_url: String,
    
    /// Database connection pool size
    pub connection_pool_size: u32,
    
    /// Database connection timeout (seconds)
    pub connection_timeout_seconds: u64,
    
    /// Query timeout (seconds)
    pub query_timeout_seconds: u64,
    
    /// Enable connection pooling
    pub enable_connection_pooling: bool,
    
    /// Enable query logging
    pub enable_query_logging: bool,
    
    /// Enable slow query logging
    pub enable_slow_query_logging: bool,
    
    /// Slow query threshold (milliseconds)
    pub slow_query_threshold_ms: u64,
}

impl Default for StorageConfig {
    fn default() -> Self {
        Self {
            database_url: "postgresql://localhost/certifyedge".to_string(),
            redis_url: "redis://localhost:6379".to_string(),
            connection_pool_size: 10,
            connection_timeout_seconds: 30,
            query_timeout_seconds: 60,
            enable_connection_pooling: true,
            enable_query_logging: false,
            enable_slow_query_logging: true,
            slow_query_threshold_ms: 1000,
        }
    }
}

impl StorageConfig {
    pub fn validate(&self) -> Result<(), AuditorError> {
        if self.database_url.is_empty() {
            return Err(AuditorError::ConfigError("Database URL cannot be empty".to_string()));
        }
        
        if self.redis_url.is_empty() {
            return Err(AuditorError::ConfigError("Redis URL cannot be empty".to_string()));
        }
        
        if self.connection_pool_size == 0 {
            return Err(AuditorError::ConfigError("Connection pool size cannot be 0".to_string()));
        }
        
        Ok(())
    }
}

/// OPA configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OpaConfig {
    /// OPA endpoint
    pub endpoint: String,
    
    /// OPA timeout (seconds)
    pub timeout_seconds: u64,
    
    /// Enable OPA caching
    pub enable_caching: bool,
    
    /// OPA cache TTL (seconds)
    pub cache_ttl_seconds: u64,
    
    /// Enable OPA health checks
    pub enable_health_checks: bool,
    
    /// OPA health check interval (seconds)
    pub health_check_interval_seconds: u64,
}

impl Default for OpaConfig {
    fn default() -> Self {
        Self {
            endpoint: "http://localhost:8181".to_string(),
            timeout_seconds: 5,
            enable_caching: true,
            cache_ttl_seconds: 300,
            enable_health_checks: true,
            health_check_interval_seconds: 30,
        }
    }
}

impl OpaConfig {
    pub fn validate(&self) -> Result<(), AuditorError> {
        if self.endpoint.is_empty() {
            return Err(AuditorError::ConfigError("OPA endpoint cannot be empty".to_string()));
        }
        
        if self.timeout_seconds == 0 {
            return Err(AuditorError::ConfigError("OPA timeout cannot be 0".to_string()));
        }
        
        Ok(())
    }
}

/// Performance configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceConfig {
    /// Enable response caching
    pub enable_response_caching: bool,
    
    /// Response cache TTL (seconds)
    pub response_cache_ttl_seconds: u64,
    
    /// Enable request compression
    pub enable_request_compression: bool,
    
    /// Enable response compression
    pub enable_response_compression: bool,
    
    /// Maximum concurrent requests
    pub max_concurrent_requests: usize,
    
    /// Request queue size
    pub request_queue_size: usize,
    
    /// Enable connection pooling
    pub enable_connection_pooling: bool,
    
    /// Connection pool size
    pub connection_pool_size: usize,
}

impl Default for PerformanceConfig {
    fn default() -> Self {
        Self {
            enable_response_caching: true,
            response_cache_ttl_seconds: 300,
            enable_request_compression: true,
            enable_response_compression: true,
            max_concurrent_requests: 1000,
            request_queue_size: 10000,
            enable_connection_pooling: true,
            connection_pool_size: 100,
        }
    }
}

impl PerformanceConfig {
    pub fn validate(&self) -> Result<(), AuditorError> {
        if self.max_concurrent_requests == 0 {
            return Err(AuditorError::ConfigError("Max concurrent requests cannot be 0".to_string()));
        }
        
        if self.request_queue_size == 0 {
            return Err(AuditorError::ConfigError("Request queue size cannot be 0".to_string()));
        }
        
        if self.connection_pool_size == 0 {
            return Err(AuditorError::ConfigError("Connection pool size cannot be 0".to_string()));
        }
        
        Ok(())
    }
}

/// Security configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityConfig {
    /// Enable CORS
    pub enable_cors: bool,
    
    /// CORS allowed origins
    pub cors_allowed_origins: Vec<String>,
    
    /// Enable rate limiting
    pub enable_rate_limiting: bool,
    
    /// Rate limit requests per minute
    pub rate_limit_requests_per_minute: u32,
    
    /// Enable request validation
    pub enable_request_validation: bool,
    
    /// Enable response validation
    pub enable_response_validation: bool,
    
    /// Enable security headers
    pub enable_security_headers: bool,
    
    /// Allowed HTTP methods
    pub allowed_http_methods: Vec<String>,
}

impl Default for SecurityConfig {
    fn default() -> Self {
        Self {
            enable_cors: true,
            cors_allowed_origins: vec!["http://localhost:3000".to_string()],
            enable_rate_limiting: true,
            rate_limit_requests_per_minute: 1000,
            enable_request_validation: true,
            enable_response_validation: true,
            enable_security_headers: true,
            allowed_http_methods: vec![
                "GET".to_string(),
                "POST".to_string(),
                "OPTIONS".to_string(),
            ],
        }
    }
}

impl SecurityConfig {
    pub fn validate(&self) -> Result<(), AuditorError> {
        if self.rate_limit_requests_per_minute == 0 {
            return Err(AuditorError::ConfigError("Rate limit cannot be 0".to_string()));
        }
        
        Ok(())
    }
}

/// Monitoring configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MonitoringConfig {
    /// Enable metrics collection
    pub enable_metrics: bool,
    
    /// Metrics endpoint
    pub metrics_endpoint: String,
    
    /// Enable health checks
    pub enable_health_checks: bool,
    
    /// Health check interval (seconds)
    pub health_check_interval_seconds: u64,
    
    /// Enable request logging
    pub enable_request_logging: bool,
    
    /// Enable error logging
    pub enable_error_logging: bool,
    
    /// Log level
    pub log_level: String,
    
    /// Enable structured logging
    pub enable_structured_logging: bool,
}

impl Default for MonitoringConfig {
    fn default() -> Self {
        Self {
            enable_metrics: true,
            metrics_endpoint: "/metrics".to_string(),
            enable_health_checks: true,
            health_check_interval_seconds: 30,
            enable_request_logging: true,
            enable_error_logging: true,
            log_level: "info".to_string(),
            enable_structured_logging: true,
        }
    }
}

impl MonitoringConfig {
    pub fn validate(&self) -> Result<(), AuditorError> {
        if self.health_check_interval_seconds == 0 {
            return Err(AuditorError::ConfigError("Health check interval cannot be 0".to_string()));
        }
        
        Ok(())
    }
}

/// Rate limiting configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RateLimitingConfig {
    /// Enable rate limiting
    pub enabled: bool,
    
    /// Requests per minute
    pub requests_per_minute: u32,
    
    /// Burst size
    pub burst_size: u32,
    
    /// Rate limit window (seconds)
    pub window_seconds: u64,
    
    /// Enable per-user rate limiting
    pub enable_per_user_limiting: bool,
    
    /// Enable per-IP rate limiting
    pub enable_per_ip_limiting: bool,
}

impl Default for RateLimitingConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            requests_per_minute: 1000,
            burst_size: 100,
            window_seconds: 60,
            enable_per_user_limiting: true,
            enable_per_ip_limiting: true,
        }
    }
}

impl RateLimitingConfig {
    pub fn validate(&self) -> Result<(), AuditorError> {
        if self.enabled {
            if self.requests_per_minute == 0 {
                return Err(AuditorError::ConfigError("Requests per minute cannot be 0".to_string()));
            }
            
            if self.burst_size == 0 {
                return Err(AuditorError::ConfigError("Burst size cannot be 0".to_string()));
            }
            
            if self.window_seconds == 0 {
                return Err(AuditorError::ConfigError("Window seconds cannot be 0".to_string()));
            }
        }
        
        Ok(())
    }
}

/// Cache configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheConfig {
    /// Enable caching
    pub enabled: bool,
    
    /// Cache TTL (seconds)
    pub ttl_seconds: u64,
    
    /// Maximum cache size (entries)
    pub max_size: usize,
    
    /// Enable cache compression
    pub enable_compression: bool,
    
    /// Cache eviction policy
    pub eviction_policy: String,
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            ttl_seconds: 300,
            max_size: 10000,
            enable_compression: true,
            eviction_policy: "lru".to_string(),
        }
    }
}

impl CacheConfig {
    pub fn validate(&self) -> Result<(), AuditorError> {
        if self.enabled {
            if self.max_size == 0 {
                return Err(AuditorError::ConfigError("Cache max size cannot be 0".to_string()));
            }
        }
        
        Ok(())
    }
}

/// API configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApiConfig {
    /// API version
    pub version: String,
    
    /// API base path
    pub base_path: String,
    
    /// Enable API documentation
    pub enable_documentation: bool,
    
    /// Documentation path
    pub documentation_path: String,
    
    /// Enable API versioning
    pub enable_versioning: bool,
    
    /// Default page size
    pub default_page_size: usize,
    
    /// Maximum page size
    pub max_page_size: usize,
    
    /// Enable pagination
    pub enable_pagination: bool,
}

impl Default for ApiConfig {
    fn default() -> Self {
        Self {
            version: "v1".to_string(),
            base_path: "/api".to_string(),
            enable_documentation: true,
            documentation_path: "/docs".to_string(),
            enable_versioning: true,
            default_page_size: 20,
            max_page_size: 100,
            enable_pagination: true,
        }
    }
}

impl ApiConfig {
    pub fn validate(&self) -> Result<(), AuditorError> {
        if self.default_page_size == 0 {
            return Err(AuditorError::ConfigError("Default page size cannot be 0".to_string()));
        }
        
        if self.max_page_size == 0 {
            return Err(AuditorError::ConfigError("Max page size cannot be 0".to_string()));
        }
        
        if self.default_page_size > self.max_page_size {
            return Err(AuditorError::ConfigError("Default page size cannot be greater than max page size".to_string()));
        }
        
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_config_creation() {
        let config = AuditorConfig::default();
        assert!(config.validate().is_ok());
    }

    #[test]
    fn test_config_env_vars() {
        let config = AuditorConfig::default();
        let env_vars = config.as_env_vars();
        
        assert!(env_vars.contains_key("AUDITOR_HOST"));
        assert!(env_vars.contains_key("AUDITOR_PORT"));
        assert!(env_vars.contains_key("JWT_SECRET"));
        assert!(env_vars.contains_key("DATABASE_URL"));
    }

    #[test]
    fn test_server_config_validation() {
        let mut config = ServerConfig::default();
        assert!(config.validate().is_ok());
        
        config.port = 0;
        assert!(config.validate().is_err());
    }

    #[test]
    fn test_storage_config_validation() {
        let mut config = StorageConfig::default();
        assert!(config.validate().is_ok());
        
        config.database_url = "".to_string();
        assert!(config.validate().is_err());
    }
} 