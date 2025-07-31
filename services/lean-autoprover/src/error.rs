//! Error types for Lean 4 autoprover
//! 
//! This module defines error types used throughout the autoprover.

use thiserror::Error;

/// Main error type for the Lean autoprover
#[derive(Error, Debug)]
pub enum AutoproverError {
    #[error("Lean 4 execution error: {0}")]
    LeanExecutionError(String),

    #[error("Cache error: {0}")]
    CacheError(String),

    #[error("Configuration error: {0}")]
    ConfigError(String),

    #[error("Certificate error: {0}")]
    CertificateError(#[from] crate::certificate::CertificateError),

    #[error("STL compiler error: {0}")]
    STLCompilerError(String),

    #[error("Tactic execution error: {0}")]
    TacticError(String),

    #[error("Timeout error: {0}")]
    TimeoutError(String),

    #[error("Memory limit exceeded: {0}MB")]
    MemoryLimitExceeded(u64),

    #[error("Invalid input: {0}")]
    InvalidInput(String),

    #[error("Serialization error: {0}")]
    SerializationError(String),

    #[error("Deserialization error: {0}")]
    DeserializationError(String),

    #[error("Database error: {0}")]
    DatabaseError(String),

    #[error("Internal error: {0}")]
    InternalError(String),
}

impl From<sqlx::Error> for AutoproverError {
    fn from(err: sqlx::Error) -> Self {
        AutoproverError::DatabaseError(err.to_string())
    }
}

impl From<serde_json::Error> for AutoproverError {
    fn from(err: serde_json::Error) -> Self {
        AutoproverError::SerializationError(err.to_string())
    }
}

impl From<std::io::Error> for AutoproverError {
    fn from(err: std::io::Error) -> Self {
        AutoproverError::LeanExecutionError(err.to_string())
    }
}

impl From<tokio::time::error::Elapsed> for AutoproverError {
    fn from(err: tokio::time::error::Elapsed) -> Self {
        AutoproverError::TimeoutError(err.to_string())
    }
}

/// Result type for autoprover operations
pub type AutoproverResult<T> = Result<T, AutoproverError>; 