//! Error types for SMT verification service
//! 
//! This module defines error types used throughout the SMT verification service.

use thiserror::Error;

/// Main error type for the SMT verifier
#[derive(Error, Debug)]
pub enum VerifierError {
    #[error("No solvers available")]
    NoSolversAvailable,

    #[error("Invalid script: {0}")]
    InvalidScript(String),

    #[error("No results available")]
    NoResultsAvailable,

    #[error("Solver disagreement for verification {verification_id}: {results:?}")]
    SolverDisagreement {
        verification_id: String,
        results: Vec<crate::verifier::SMTResult>,
    },

    #[error("Solver execution error: {0}")]
    SolverExecutionError(String),

    #[error("Invalid solver configuration: {0}")]
    InvalidSolverConfig(String),

    #[error("Sandbox execution error: {0}")]
    SandboxError(String),

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

    #[error("IO error: {0}")]
    IOError(String),

    #[error("Configuration error: {0}")]
    ConfigError(String),

    #[error("Metrics error: {0}")]
    MetricsError(String),

    #[error("Internal error: {0}")]
    InternalError(String),
}

impl From<serde_json::Error> for VerifierError {
    fn from(err: serde_json::Error) -> Self {
        VerifierError::SerializationError(err.to_string())
    }
}

impl From<std::io::Error> for VerifierError {
    fn from(err: std::io::Error) -> Self {
        VerifierError::IOError(err.to_string())
    }
}

impl From<tokio::time::error::Elapsed> for VerifierError {
    fn from(err: tokio::time::error::Elapsed) -> Self {
        VerifierError::TimeoutError(err.to_string())
    }
}

impl From<wasmtime::Error> for VerifierError {
    fn from(err: wasmtime::Error) -> Self {
        VerifierError::SandboxError(err.to_string())
    }
}

/// Result type for verifier operations
pub type VerifierResult<T> = Result<T, VerifierError>; 