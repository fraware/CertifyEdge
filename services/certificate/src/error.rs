//! Error types for certificate service
//! 
//! This module defines error types used throughout the certificate service.

use thiserror::Error;

/// Main error type for the certificate service
#[derive(Error, Debug)]
pub enum CertificateError {
    #[error("Invalid certificate ID")]
    InvalidCertificateId,

    #[error("Invalid version")]
    InvalidVersion,

    #[error("Invalid specification hash")]
    InvalidSpecHash,

    #[error("Invalid Lean proof hash")]
    InvalidLeanProofHash,

    #[error("Invalid model hash")]
    InvalidModelHash,

    #[error("Invalid solver version")]
    InvalidSolverVersion,

    #[error("Invalid Lean version")]
    InvalidLeanVersion,

    #[error("Invalid SBOM components")]
    InvalidSBOMComponents,

    #[error("Missing signatures")]
    MissingSignatures,

    #[error("Invalid Ed25519 signature")]
    InvalidEd25519Signature,

    #[error("Invalid Sigstore signature")]
    InvalidSigstoreSignature,

    #[error("Signature verification failed")]
    SignatureVerificationFailed,

    #[error("Certificate expired")]
    CertificateExpired,

    #[error("Certificate not yet valid")]
    CertificateNotYetValid,

    #[error("Serialization error: {0}")]
    SerializationError(String),

    #[error("Deserialization error: {0}")]
    DeserializationError(String),

    #[error("IO error: {0}")]
    IOError(String),

    #[error("Configuration error: {0}")]
    ConfigError(String),

    #[error("Signing error: {0}")]
    SigningError(String),

    #[error("Verification error: {0}")]
    VerificationError(String),

    #[error("Sigstore error: {0}")]
    SigstoreError(String),

    #[error("Internal error: {0}")]
    InternalError(String),
}

impl From<serde_json::Error> for CertificateError {
    fn from(err: serde_json::Error) -> Self {
        CertificateError::SerializationError(err.to_string())
    }
}

impl From<std::io::Error> for CertificateError {
    fn from(err: std::io::Error) -> Self {
        CertificateError::IOError(err.to_string())
    }
}

impl From<ed25519_dalek::ed25519::Error> for CertificateError {
    fn from(err: ed25519_dalek::ed25519::Error) -> Self {
        CertificateError::SigningError(err.to_string())
    }
}

/// Result type for certificate operations
pub type CertificateResult<T> = Result<T, CertificateError>; 