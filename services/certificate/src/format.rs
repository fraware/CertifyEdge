//! Certificate format definitions
//! 
//! This module defines the certificate format structure and validation logic.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::SystemTime;

use crate::error::CertificateError;

/// Certificate format structure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertificateFormat {
    pub certificate_id: String,
    pub created_at: SystemTime,
    pub version: String,
    pub spec_hash: Vec<u8>,
    pub lean_proof_hash: Vec<u8>,
    pub smt_proof_hashes: Vec<Vec<u8>>,
    pub model_hash: Vec<u8>,
    pub solver_version: String,
    pub lean_version: String,
    pub sbom_components: Vec<String>,
    pub ed25519_signature: Option<Vec<u8>>,
    pub sigstore_signature: Option<Vec<u8>>,
    pub git_commit: String,
    pub build_id: String,
    pub pipeline_run_id: String,
    pub metadata: HashMap<String, String>,
}

impl CertificateFormat {
    /// Create a new certificate format
    pub fn new(
        certificate_id: String,
        spec_hash: Vec<u8>,
        lean_proof_hash: Vec<u8>,
        smt_proof_hashes: Vec<Vec<u8>>,
        model_hash: Vec<u8>,
        solver_version: String,
        lean_version: String,
        sbom_components: Vec<String>,
    ) -> Self {
        Self {
            certificate_id,
            created_at: SystemTime::now(),
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
            git_commit: String::new(),
            build_id: String::new(),
            pipeline_run_id: String::new(),
            metadata: HashMap::new(),
        }
    }

    /// Validate the certificate format
    pub fn validate(&self) -> Result<(), CertificateError> {
        // Check certificate ID
        if self.certificate_id.is_empty() {
            return Err(CertificateError::InvalidCertificateId);
        }

        // Check version
        if self.version.is_empty() {
            return Err(CertificateError::InvalidVersion);
        }

        // Check hashes
        if self.spec_hash.is_empty() {
            return Err(CertificateError::InvalidSpecHash);
        }

        if self.lean_proof_hash.is_empty() {
            return Err(CertificateError::InvalidLeanProofHash);
        }

        if self.model_hash.is_empty() {
            return Err(CertificateError::InvalidModelHash);
        }

        // Check versions
        if self.solver_version.is_empty() {
            return Err(CertificateError::InvalidSolverVersion);
        }

        if self.lean_version.is_empty() {
            return Err(CertificateError::InvalidLeanVersion);
        }

        // Check SBOM components
        if self.sbom_components.is_empty() {
            return Err(CertificateError::InvalidSBOMComponents);
        }

        // Check signatures (at least one must be present)
        if self.ed25519_signature.is_none() && self.sigstore_signature.is_none() {
            return Err(CertificateError::MissingSignatures);
        }

        Ok(())
    }

    /// Get certificate fingerprint
    pub fn fingerprint(&self) -> Result<String, CertificateError> {
        use sha2::{Sha256, Digest};
        let mut hasher = Sha256::new();
        
        // Hash the certificate content (excluding signatures)
        hasher.update(self.certificate_id.as_bytes());
        hasher.update(self.version.as_bytes());
        hasher.update(&self.spec_hash);
        hasher.update(&self.lean_proof_hash);
        hasher.update(&self.model_hash);
        hasher.update(self.solver_version.as_bytes());
        hasher.update(self.lean_version.as_bytes());
        
        for component in &self.sbom_components {
            hasher.update(component.as_bytes());
        }
        
        for hash in &self.smt_proof_hashes {
            hasher.update(hash);
        }
        
        Ok(format!("{:x}", hasher.finalize()))
    }

    /// Check if certificate is expired
    pub fn is_expired(&self, max_age_seconds: u64) -> bool {
        let age = SystemTime::now()
            .duration_since(self.created_at)
            .unwrap_or_default()
            .as_secs();
        age > max_age_seconds
    }

    /// Get certificate as JSON
    pub fn to_json(&self) -> Result<String, CertificateError> {
        serde_json::to_string_pretty(self)
            .map_err(|e| CertificateError::SerializationError(e.to_string()))
    }

    /// Create certificate from JSON
    pub fn from_json(json: &str) -> Result<Self, CertificateError> {
        serde_json::from_str(json)
            .map_err(|e| CertificateError::DeserializationError(e.to_string()))
    }

    /// Add metadata
    pub fn add_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }

    /// Get metadata value
    pub fn get_metadata(&self, key: &str) -> Option<&String> {
        self.metadata.get(key)
    }

    /// Set Ed25519 signature
    pub fn set_ed25519_signature(&mut self, signature: Vec<u8>) {
        self.ed25519_signature = Some(signature);
    }

    /// Set Sigstore signature
    pub fn set_sigstore_signature(&mut self, signature: Vec<u8>) {
        self.sigstore_signature = Some(signature);
    }

    /// Check if certificate is signed
    pub fn is_signed(&self) -> bool {
        self.ed25519_signature.is_some() || self.sigstore_signature.is_some()
    }

    /// Get signature count
    pub fn signature_count(&self) -> usize {
        let mut count = 0;
        if self.ed25519_signature.is_some() {
            count += 1;
        }
        if self.sigstore_signature.is_some() {
            count += 1;
        }
        count
    }
}

/// Certificate metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertificateMetadata {
    pub certificate_id: String,
    pub created_at: SystemTime,
    pub version: String,
    pub issuer: String,
    pub subject: String,
    pub validity_period: ValidityPeriod,
    pub extensions: HashMap<String, String>,
}

/// Certificate validity period
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidityPeriod {
    pub not_before: SystemTime,
    pub not_after: SystemTime,
}

impl ValidityPeriod {
    /// Create a new validity period
    pub fn new(not_before: SystemTime, not_after: SystemTime) -> Self {
        Self {
            not_before,
            not_after,
        }
    }

    /// Check if the certificate is currently valid
    pub fn is_valid(&self) -> bool {
        let now = SystemTime::now();
        now >= self.not_before && now <= self.not_after
    }

    /// Get remaining validity time
    pub fn remaining_time(&self) -> Option<std::time::Duration> {
        let now = SystemTime::now();
        if now <= self.not_after {
            self.not_after.duration_since(now).ok()
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_certificate_format_creation() {
        let certificate = CertificateFormat::new(
            "test-cert".to_string(),
            vec![1, 2, 3, 4],
            vec![5, 6, 7, 8],
            vec![vec![9, 10, 11, 12]],
            vec![13, 14, 15, 16],
            "z3-4.13.0".to_string(),
            "lean-4.0.0".to_string(),
            vec!["component1".to_string()],
        );

        assert_eq!(certificate.certificate_id, "test-cert");
        assert_eq!(certificate.version, "1.0.0");
        assert_eq!(certificate.solver_version, "z3-4.13.0");
    }

    #[test]
    fn test_certificate_validation() {
        let mut certificate = CertificateFormat::new(
            "test-cert".to_string(),
            vec![1, 2, 3, 4],
            vec![5, 6, 7, 8],
            vec![vec![9, 10, 11, 12]],
            vec![13, 14, 15, 16],
            "z3-4.13.0".to_string(),
            "lean-4.0.0".to_string(),
            vec!["component1".to_string()],
        );

        // Should fail validation (no signatures)
        assert!(certificate.validate().is_err());

        // Add signature
        certificate.set_ed25519_signature(vec![1, 2, 3, 4]);
        assert!(certificate.validate().is_ok());
    }

    #[test]
    fn test_certificate_fingerprint() {
        let certificate = CertificateFormat::new(
            "test-cert".to_string(),
            vec![1, 2, 3, 4],
            vec![5, 6, 7, 8],
            vec![vec![9, 10, 11, 12]],
            vec![13, 14, 15, 16],
            "z3-4.13.0".to_string(),
            "lean-4.0.0".to_string(),
            vec!["component1".to_string()],
        );

        let fingerprint = certificate.fingerprint().unwrap();
        assert!(!fingerprint.is_empty());
        assert_eq!(fingerprint.len(), 64); // SHA256 hex string
    }

    #[test]
    fn test_certificate_json() {
        let certificate = CertificateFormat::new(
            "test-cert".to_string(),
            vec![1, 2, 3, 4],
            vec![5, 6, 7, 8],
            vec![vec![9, 10, 11, 12]],
            vec![13, 14, 15, 16],
            "z3-4.13.0".to_string(),
            "lean-4.0.0".to_string(),
            vec!["component1".to_string()],
        );

        let json = certificate.to_json().unwrap();
        let certificate2 = CertificateFormat::from_json(&json).unwrap();

        assert_eq!(certificate.certificate_id, certificate2.certificate_id);
        assert_eq!(certificate.version, certificate2.version);
    }

    #[test]
    fn test_validity_period() {
        let now = SystemTime::now();
        let later = now + std::time::Duration::from_secs(3600);
        
        let validity = ValidityPeriod::new(now, later);
        assert!(validity.is_valid());
        
        let remaining = validity.remaining_time();
        assert!(remaining.is_some());
        assert!(remaining.unwrap().as_secs() > 0);
    }
} 