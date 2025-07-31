//! Configuration for certificate service
//! 
//! This module handles configuration management for the certificate service.

use serde::{Deserialize, Serialize};
use std::path::PathBuf;

/// Configuration for the certificate service
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertificateConfig {
    /// Enable Ed25519 signing
    pub enable_ed25519: bool,
    
    /// Enable Sigstore signing
    pub enable_sigstore: bool,
    
    /// Ed25519 private key path
    pub ed25519_private_key_path: Option<PathBuf>,
    
    /// Ed25519 public key path
    pub ed25519_public_key_path: Option<PathBuf>,
    
    /// Sigstore configuration
    pub sigstore: SigstoreConfig,
    
    /// Certificate validity period (seconds)
    pub validity_period_seconds: u64,
    
    /// Maximum certificate size (bytes)
    pub max_certificate_size_bytes: u64,
    
    /// Enable certificate compression
    pub enable_compression: bool,
    
    /// Output directory for certificates
    pub output_dir: PathBuf,
    
    /// Log level
    pub log_level: String,
}

/// Sigstore configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SigstoreConfig {
    /// Enable Sigstore integration
    pub enabled: bool,
    
    /// Fulcio endpoint
    pub fulcio_endpoint: String,
    
    /// Rekor endpoint
    pub rekor_endpoint: String,
    
    /// OIDC issuer
    pub oidc_issuer: String,
    
    /// OIDC client ID
    pub oidc_client_id: String,
    
    /// OIDC client secret
    pub oidc_client_secret: Option<String>,
    
    /// Certificate chain path
    pub certificate_chain_path: Option<PathBuf>,
    
    /// Private key path
    pub private_key_path: Option<PathBuf>,
}

impl Default for CertificateConfig {
    fn default() -> Self {
        Self {
            enable_ed25519: true,
            enable_sigstore: true,
            ed25519_private_key_path: None,
            ed25519_public_key_path: None,
            sigstore: SigstoreConfig::default(),
            validity_period_seconds: 31536000, // 1 year
            max_certificate_size_bytes: 1024 * 1024, // 1MB
            enable_compression: false,
            output_dir: PathBuf::from("certificates"),
            log_level: "info".to_string(),
        }
    }
}

impl Default for SigstoreConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            fulcio_endpoint: "https://fulcio.sigstore.dev".to_string(),
            rekor_endpoint: "https://rekor.sigstore.dev".to_string(),
            oidc_issuer: "https://oauth2.sigstore.dev/auth".to_string(),
            oidc_client_id: "sigstore".to_string(),
            oidc_client_secret: None,
            certificate_chain_path: None,
            private_key_path: None,
        }
    }
}

impl CertificateConfig {
    /// Create configuration from file
    pub fn from_file(path: &PathBuf) -> Result<Self, crate::error::CertificateError> {
        let content = std::fs::read_to_string(path)
            .map_err(|e| crate::error::CertificateError::ConfigError(e.to_string()))?;
        
        toml::from_str(&content)
            .map_err(|e| crate::error::CertificateError::ConfigError(e.to_string()))
    }

    /// Save configuration to file
    pub fn save_to_file(&self, path: &PathBuf) -> Result<(), crate::error::CertificateError> {
        let content = toml::to_string_pretty(self)
            .map_err(|e| crate::error::CertificateError::ConfigError(e.to_string()))?;
        
        std::fs::write(path, content)
            .map_err(|e| crate::error::CertificateError::ConfigError(e.to_string()))
    }

    /// Validate configuration
    pub fn validate(&self) -> Result<(), crate::error::CertificateError> {
        // Check validity period
        if self.validity_period_seconds == 0 {
            return Err(crate::error::CertificateError::ConfigError(
                "Validity period must be greater than 0".to_string()
            ));
        }

        // Check maximum certificate size
        if self.max_certificate_size_bytes == 0 {
            return Err(crate::error::CertificateError::ConfigError(
                "Maximum certificate size must be greater than 0".to_string()
            ));
        }

        // Validate Ed25519 configuration
        if self.enable_ed25519 {
            if self.ed25519_private_key_path.is_none() {
                return Err(crate::error::CertificateError::ConfigError(
                    "Ed25519 private key path is required when Ed25519 signing is enabled".to_string()
                ));
            }
        }

        // Validate Sigstore configuration
        self.sigstore.validate()?;

        // Create output directory if it doesn't exist
        if !self.output_dir.exists() {
            std::fs::create_dir_all(&self.output_dir)
                .map_err(|e| crate::error::CertificateError::ConfigError(e.to_string()))?;
        }

        Ok(())
    }

    /// Get configuration as environment variables
    pub fn as_env_vars(&self) -> Vec<(String, String)> {
        vec![
            ("ENABLE_ED25519".to_string(), self.enable_ed25519.to_string()),
            ("ENABLE_SIGSTORE".to_string(), self.enable_sigstore.to_string()),
            ("VALIDITY_PERIOD_SECONDS".to_string(), self.validity_period_seconds.to_string()),
            ("MAX_CERTIFICATE_SIZE_BYTES".to_string(), self.max_certificate_size_bytes.to_string()),
            ("ENABLE_COMPRESSION".to_string(), self.enable_compression.to_string()),
            ("LOG_LEVEL".to_string(), self.log_level.clone()),
            ("OUTPUT_DIR".to_string(), self.output_dir.to_string_lossy().to_string()),
        ]
    }

    /// Check if signing is enabled
    pub fn is_signing_enabled(&self) -> bool {
        self.enable_ed25519 || self.enable_sigstore
    }

    /// Get signing methods
    pub fn get_signing_methods(&self) -> Vec<String> {
        let mut methods = Vec::new();
        
        if self.enable_ed25519 {
            methods.push("ed25519".to_string());
        }
        
        if self.enable_sigstore {
            methods.push("sigstore".to_string());
        }
        
        methods
    }
}

impl SigstoreConfig {
    /// Validate Sigstore configuration
    pub fn validate(&self) -> Result<(), crate::error::CertificateError> {
        if !self.enabled {
            return Ok(());
        }

        // Check endpoints
        if self.fulcio_endpoint.is_empty() {
            return Err(crate::error::CertificateError::ConfigError(
                "Fulcio endpoint cannot be empty".to_string()
            ));
        }

        if self.rekor_endpoint.is_empty() {
            return Err(crate::error::CertificateError::ConfigError(
                "Rekor endpoint cannot be empty".to_string()
            ));
        }

        // Check OIDC configuration
        if self.oidc_issuer.is_empty() {
            return Err(crate::error::CertificateError::ConfigError(
                "OIDC issuer cannot be empty".to_string()
            ));
        }

        if self.oidc_client_id.is_empty() {
            return Err(crate::error::CertificateError::ConfigError(
                "OIDC client ID cannot be empty".to_string()
            ));
        }

        Ok(())
    }

    /// Get Sigstore endpoints
    pub fn get_endpoints(&self) -> Vec<String> {
        vec![
            self.fulcio_endpoint.clone(),
            self.rekor_endpoint.clone(),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = CertificateConfig::default();
        assert!(config.enable_ed25519);
        assert!(config.enable_sigstore);
        assert!(config.validity_period_seconds > 0);
        assert!(config.max_certificate_size_bytes > 0);
    }

    #[test]
    fn test_config_validation() {
        let mut config = CertificateConfig::default();
        config.validity_period_seconds = 0;
        
        let result = config.validate();
        assert!(result.is_err());
    }

    #[test]
    fn test_signing_methods() {
        let config = CertificateConfig::default();
        let methods = config.get_signing_methods();
        
        assert_eq!(methods.len(), 2);
        assert!(methods.contains(&"ed25519".to_string()));
        assert!(methods.contains(&"sigstore".to_string()));
    }

    #[test]
    fn test_sigstore_config() {
        let config = SigstoreConfig::default();
        assert!(config.enabled);
        assert!(!config.fulcio_endpoint.is_empty());
        assert!(!config.rekor_endpoint.is_empty());
    }

    #[test]
    fn test_config_env_vars() {
        let config = CertificateConfig::default();
        let env_vars = config.as_env_vars();
        
        assert!(!env_vars.is_empty());
        assert!(env_vars.iter().any(|(k, _)| k == "ENABLE_ED25519"));
        assert!(env_vars.iter().any(|(k, _)| k == "ENABLE_SIGSTORE"));
    }
} 