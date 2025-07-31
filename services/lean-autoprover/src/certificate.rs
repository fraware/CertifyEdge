//! Certificate generation for Lean 4 autoprover
//! 
//! This module handles the creation and validation of certificates
//! from successful Lean 4 proofs.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::SystemTime;

/// Certificate generated from a successful Lean 4 proof
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Certificate {
    pub certificate_id: String,
    pub created_at: SystemTime,
    pub version: String,
    pub spec_hash: Vec<u8>,
    pub lean_proof_hash: Vec<u8>,
    pub tactic_used: String,
    pub proof_time_ms: u64,
    pub lean_commit: String,
    pub metadata: HashMap<String, String>,
}

impl Certificate {
    /// Create a new certificate
    pub fn new(
        spec_hash: Vec<u8>,
        lean_proof_hash: Vec<u8>,
        tactic_used: String,
        proof_time_ms: u64,
        lean_commit: String,
    ) -> Self {
        Self {
            certificate_id: uuid::Uuid::new_v4().to_string(),
            created_at: SystemTime::now(),
            version: "1.0.0".to_string(),
            spec_hash,
            lean_proof_hash,
            tactic_used,
            proof_time_ms,
            lean_commit,
            metadata: HashMap::new(),
        }
    }

    /// Add metadata to the certificate
    pub fn with_metadata(mut self, key: String, value: String) -> Self {
        self.metadata.insert(key, value);
        self
    }

    /// Validate the certificate
    pub fn validate(&self) -> Result<(), CertificateError> {
        if self.certificate_id.is_empty() {
            return Err(CertificateError::InvalidCertificateId);
        }

        if self.spec_hash.is_empty() {
            return Err(CertificateError::InvalidSpecHash);
        }

        if self.lean_proof_hash.is_empty() {
            return Err(CertificateError::InvalidProofHash);
        }

        if self.tactic_used.is_empty() {
            return Err(CertificateError::InvalidTacticUsed);
        }

        if self.lean_commit.is_empty() {
            return Err(CertificateError::InvalidLeanCommit);
        }

        Ok(())
    }

    /// Get the certificate as JSON
    pub fn to_json(&self) -> Result<String, CertificateError> {
        serde_json::to_string_pretty(self)
            .map_err(|e| CertificateError::SerializationError(e.to_string()))
    }

    /// Create certificate from JSON
    pub fn from_json(json: &str) -> Result<Self, CertificateError> {
        serde_json::from_str(json)
            .map_err(|e| CertificateError::DeserializationError(e.to_string()))
    }

    /// Get the certificate fingerprint
    pub fn fingerprint(&self) -> String {
        use sha2::{Sha256, Digest};
        let mut hasher = Sha256::new();
        hasher.update(&self.spec_hash);
        hasher.update(&self.lean_proof_hash);
        hasher.update(self.tactic_used.as_bytes());
        hasher.update(self.lean_commit.as_bytes());
        format!("{:x}", hasher.finalize())
    }

    /// Check if the certificate is expired
    pub fn is_expired(&self, max_age_seconds: u64) -> bool {
        let age = SystemTime::now()
            .duration_since(self.created_at)
            .unwrap_or_default()
            .as_secs();
        age > max_age_seconds
    }
}

/// Certificate validation error
#[derive(Debug, thiserror::Error)]
pub enum CertificateError {
    #[error("Invalid certificate ID")]
    InvalidCertificateId,
    
    #[error("Invalid specification hash")]
    InvalidSpecHash,
    
    #[error("Invalid proof hash")]
    InvalidProofHash,
    
    #[error("Invalid tactic used")]
    InvalidTacticUsed,
    
    #[error("Invalid Lean commit")]
    InvalidLeanCommit,
    
    #[error("Serialization error: {0}")]
    SerializationError(String),
    
    #[error("Deserialization error: {0}")]
    DeserializationError(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_certificate_creation() {
        let cert = Certificate::new(
            vec![1, 2, 3, 4],
            vec![5, 6, 7, 8],
            "simp".to_string(),
            100,
            "lean-commit".to_string(),
        );

        assert!(!cert.certificate_id.is_empty());
        assert_eq!(cert.tactic_used, "simp");
        assert_eq!(cert.proof_time_ms, 100);
    }

    #[test]
    fn test_certificate_validation() {
        let cert = Certificate::new(
            vec![1, 2, 3, 4],
            vec![5, 6, 7, 8],
            "simp".to_string(),
            100,
            "lean-commit".to_string(),
        );

        assert!(cert.validate().is_ok());
    }

    #[test]
    fn test_certificate_json() {
        let cert = Certificate::new(
            vec![1, 2, 3, 4],
            vec![5, 6, 7, 8],
            "simp".to_string(),
            100,
            "lean-commit".to_string(),
        );

        let json = cert.to_json().unwrap();
        let cert2 = Certificate::from_json(&json).unwrap();
        
        assert_eq!(cert.certificate_id, cert2.certificate_id);
        assert_eq!(cert.tactic_used, cert2.tactic_used);
    }

    #[test]
    fn test_certificate_fingerprint() {
        let cert = Certificate::new(
            vec![1, 2, 3, 4],
            vec![5, 6, 7, 8],
            "simp".to_string(),
            100,
            "lean-commit".to_string(),
        );

        let fingerprint = cert.fingerprint();
        assert!(!fingerprint.is_empty());
        assert_eq!(fingerprint.len(), 64); // SHA256 hex string
    }

    #[test]
    fn test_certificate_expiration() {
        let cert = Certificate::new(
            vec![1, 2, 3, 4],
            vec![5, 6, 7, 8],
            "simp".to_string(),
            100,
            "lean-commit".to_string(),
        );

        // Certificate should not be expired immediately
        assert!(!cert.is_expired(3600));
    }
} 