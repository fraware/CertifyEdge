//! CertifyEdge Certificate Service
//! 
//! This crate provides cryptographic certificate format with Ed25519 signatures
//! and Sigstore integration for tamper-proof verification of AI models.

pub mod format;
pub mod signing;
pub mod verification;
pub mod sigstore;
pub mod error;
pub mod config;

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::SystemTime;
use uuid::Uuid;

use crate::error::CertificateError;
use crate::format::CertificateFormat;
use crate::signing::CertificateSigner;
use crate::verification::CertificateVerifier;

/// Main certificate service
#[derive(Debug, Clone)]
pub struct CertificateService {
    config: config::CertificateConfig,
    signer: CertificateSigner,
    verifier: CertificateVerifier,
}

impl CertificateService {
    /// Create a new certificate service with default configuration
    pub fn new() -> Result<Self, CertificateError> {
        let config = config::CertificateConfig::default();
        let signer = CertificateSigner::new(&config)?;
        let verifier = CertificateVerifier::new(&config)?;
        
        Ok(Self {
            config,
            signer,
            verifier,
        })
    }

    /// Create a new certificate service with custom configuration
    pub fn with_config(config: config::CertificateConfig) -> Result<Self, CertificateError> {
        let signer = CertificateSigner::new(&config)?;
        let verifier = CertificateVerifier::new(&config)?;
        
        Ok(Self {
            config,
            signer,
            verifier,
        })
    }

    /// Create a new certificate
    pub async fn create_certificate(
        &self,
        spec_hash: Vec<u8>,
        lean_proof_hash: Vec<u8>,
        smt_proof_hashes: Vec<Vec<u8>>,
        model_hash: Vec<u8>,
        solver_version: String,
        lean_version: String,
        sbom_components: Vec<String>,
    ) -> Result<CertificateFormat, CertificateError> {
        let certificate_id = Uuid::new_v4().to_string();
        let created_at = SystemTime::now();
        
        let mut certificate = CertificateFormat {
            certificate_id,
            created_at,
            version: "1.0.0".to_string(),
            spec_hash,
            lean_proof_hash,
            smt_proof_hashes,
            model_hash,
            solver_version,
            lean_version,
            sbom_components,
            ed25519_signature: None,
            sigstore_signature: None,
            git_commit: self.get_git_commit().await?,
            build_id: self.get_build_id().await?,
            pipeline_run_id: self.get_pipeline_run_id().await?,
            metadata: HashMap::new(),
        };

        // Sign the certificate
        certificate = self.signer.sign_certificate(certificate).await?;

        Ok(certificate)
    }

    /// Verify a certificate
    pub async fn verify_certificate(
        &self,
        certificate: &CertificateFormat,
    ) -> Result<VerificationResult, CertificateError> {
        self.verifier.verify_certificate(certificate).await
    }

    /// Verify a certificate from file
    pub async fn verify_certificate_file(
        &self,
        file_path: &str,
    ) -> Result<VerificationResult, CertificateError> {
        let certificate = self.load_certificate_from_file(file_path).await?;
        self.verify_certificate(&certificate).await
    }

    /// Load certificate from file
    pub async fn load_certificate_from_file(
        &self,
        file_path: &str,
    ) -> Result<CertificateFormat, CertificateError> {
        let content = tokio::fs::read_to_string(file_path).await
            .map_err(|e| CertificateError::IOError(e.to_string()))?;
        
        serde_json::from_str(&content)
            .map_err(|e| CertificateError::DeserializationError(e.to_string()))
    }

    /// Save certificate to file
    pub async fn save_certificate_to_file(
        &self,
        certificate: &CertificateFormat,
        file_path: &str,
    ) -> Result<(), CertificateError> {
        let content = serde_json::to_string_pretty(certificate)
            .map_err(|e| CertificateError::SerializationError(e.to_string()))?;
        
        tokio::fs::write(file_path, content).await
            .map_err(|e| CertificateError::IOError(e.to_string()))
    }

    /// Get certificate fingerprint
    pub fn get_certificate_fingerprint(
        &self,
        certificate: &CertificateFormat,
    ) -> Result<String, CertificateError> {
        certificate.fingerprint()
    }

    /// Validate certificate format
    pub fn validate_certificate_format(
        &self,
        certificate: &CertificateFormat,
    ) -> Result<(), CertificateError> {
        certificate.validate()
    }

    /// Get service configuration
    pub fn get_config(&self) -> &config::CertificateConfig {
        &self.config
    }

    /// Get Git commit hash
    async fn get_git_commit(&self) -> Result<String, CertificateError> {
        // In practice, this would read from environment or Git
        Ok("git-commit-hash".to_string())
    }

    /// Get build ID
    async fn get_build_id(&self) -> Result<String, CertificateError> {
        // In practice, this would read from environment
        Ok("build-id".to_string())
    }

    /// Get pipeline run ID
    async fn get_pipeline_run_id(&self) -> Result<String, CertificateError> {
        // In practice, this would read from environment
        Ok("pipeline-run-id".to_string())
    }
}

impl Default for CertificateService {
    fn default() -> Self {
        Self::new().expect("Failed to create default certificate service")
    }
}

/// Verification result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationResult {
    pub valid: bool,
    pub certificate_id: String,
    pub verification_time: SystemTime,
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
    pub metadata: HashMap<String, String>,
}

impl VerificationResult {
    /// Create a successful verification result
    pub fn success(certificate_id: String) -> Self {
        Self {
            valid: true,
            certificate_id,
            verification_time: SystemTime::now(),
            errors: vec![],
            warnings: vec![],
            metadata: HashMap::new(),
        }
    }

    /// Create a failed verification result
    pub fn failure(certificate_id: String, errors: Vec<String>) -> Self {
        Self {
            valid: false,
            certificate_id,
            verification_time: SystemTime::now(),
            errors,
            warnings: vec![],
            metadata: HashMap::new(),
        }
    }

    /// Add an error
    pub fn add_error(&mut self, error: String) {
        self.errors.push(error);
        self.valid = false;
    }

    /// Add a warning
    pub fn add_warning(&mut self, warning: String) {
        self.warnings.push(warning);
    }

    /// Add metadata
    pub fn add_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_certificate_service_creation() {
        let service = CertificateService::new();
        assert!(service.is_ok());
    }

    #[tokio::test]
    async fn test_certificate_creation() {
        let service = CertificateService::new().unwrap();
        
        let certificate = service.create_certificate(
            vec![1, 2, 3, 4],
            vec![5, 6, 7, 8],
            vec![vec![9, 10, 11, 12]],
            vec![13, 14, 15, 16],
            "z3-4.13.0".to_string(),
            "lean-4.0.0".to_string(),
            vec!["component1".to_string(), "component2".to_string()],
        ).await.unwrap();
        
        assert!(!certificate.certificate_id.is_empty());
        assert_eq!(certificate.version, "1.0.0");
        assert_eq!(certificate.solver_version, "z3-4.13.0");
    }

    #[tokio::test]
    async fn test_certificate_validation() {
        let service = CertificateService::new().unwrap();
        
        let certificate = service.create_certificate(
            vec![1, 2, 3, 4],
            vec![5, 6, 7, 8],
            vec![vec![9, 10, 11, 12]],
            vec![13, 14, 15, 16],
            "z3-4.13.0".to_string(),
            "lean-4.0.0".to_string(),
            vec!["component1".to_string()],
        ).await.unwrap();
        
        let result = service.validate_certificate_format(&certificate);
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_verification_result() {
        let mut result = VerificationResult::success("test-cert".to_string());
        assert!(result.valid);
        
        result.add_error("Test error".to_string());
        assert!(!result.valid);
        assert_eq!(result.errors.len(), 1);
        
        result.add_warning("Test warning".to_string());
        assert_eq!(result.warnings.len(), 1);
    }
} 