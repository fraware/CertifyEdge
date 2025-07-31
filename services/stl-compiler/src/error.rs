//! Error handling for the STL compiler

use thiserror::Error;

/// Main error type for the STL compiler
#[derive(Error, Debug)]
pub enum CompilerError {
    #[error("Parse error: {0}")]
    ParseError(#[from] ParseError),

    #[error("Lean 4 translation error: {0}")]
    Lean4Error(#[from] Lean4Error),

    #[error("SMT translation error: {0}")]
    SMTError(#[from] SMTError),

    #[error("Configuration error: {0}")]
    ConfigError(#[from] ConfigError),

    #[error("Serialization error: {0}")]
    SerializationError(#[from] serde_json::Error),

    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),

    #[error("External command error: {0}")]
    CommandError(String),

    #[error("Validation error: {0}")]
    ValidationError(String),

    #[error("Timeout error: {0}")]
    TimeoutError(String),

    #[error("Internal error: {0}")]
    InternalError(String),
}

/// Parse-specific errors
#[derive(Error, Debug)]
pub enum ParseError {
    #[error("Invalid syntax at position {position}: {message}")]
    SyntaxError { position: usize, message: String },

    #[error("Unexpected token '{token}' at position {position}")]
    UnexpectedToken { token: String, position: usize },

    #[error("Expected token '{expected}' but found '{found}' at position {position}")]
    ExpectedToken { expected: String, found: String, position: usize },

    #[error("Unterminated string at position {position}")]
    UnterminatedString { position: usize },

    #[error("Invalid number format at position {position}: {message}")]
    InvalidNumber { position: usize, message: String },

    #[error("Unknown variable '{variable}' at position {position}")]
    UnknownVariable { variable: String, position: usize },

    #[error("Circular dependency detected for variable '{variable}'")]
    CircularDependency { variable: String },

    #[error("Missing required parameter '{parameter}'")]
    MissingParameter { parameter: String },

    #[error("Invalid parameter type: expected {expected}, got {actual}")]
    InvalidParameterType { expected: String, actual: String },
}

/// Lean 4 translation errors
#[derive(Error, Debug)]
pub enum Lean4Error {
    #[error("Lean 4 not found at path: {path}")]
    Lean4NotFound { path: String },

    #[error("Lean 4 compilation failed: {output}")]
    CompilationFailed { output: String },

    #[error("Lean 4 type checking failed: {output}")]
    TypeCheckFailed { output: String },

    #[error("Lean 4 proof generation failed: {output}")]
    ProofGenerationFailed { output: String },

    #[error("Lean 4 tactic application failed: {tactic} - {output}")]
    TacticFailed { tactic: String, output: String },

    #[error("Lean 4 timeout after {timeout_ms}ms")]
    Timeout { timeout_ms: u64 },

    #[error("Lean 4 memory limit exceeded")]
    MemoryLimitExceeded,

    #[error("Lean 4 unsupported feature: {feature}")]
    UnsupportedFeature { feature: String },
}

/// SMT translation errors
#[derive(Error, Debug)]
pub enum SMTError {
    #[error("SMT solver not found: {solver}")]
    SolverNotFound { solver: String },

    #[error("SMT solver execution failed: {output}")]
    SolverExecutionFailed { output: String },

    #[error("SMT solver timeout after {timeout_ms}ms")]
    Timeout { timeout_ms: u64 },

    #[error("SMT solver memory limit exceeded")]
    MemoryLimitExceeded,

    #[error("Invalid SMT-LIB syntax: {message}")]
    InvalidSyntax { message: String },

    #[error("SMT solver unsupported feature: {feature}")]
    UnsupportedFeature { feature: String },

    #[error("SMT solver version mismatch: expected {expected}, got {actual}")]
    VersionMismatch { expected: String, actual: String },
}

/// Configuration errors
#[derive(Error, Debug)]
pub enum ConfigError {
    #[error("Configuration file not found: {path}")]
    FileNotFound { path: String },

    #[error("Invalid configuration format: {message}")]
    InvalidFormat { message: String },

    #[error("Missing required configuration key: {key}")]
    MissingKey { key: String },

    #[error("Invalid configuration value for key '{key}': {value}")]
    InvalidValue { key: String, value: String },

    #[error("Configuration validation failed: {message}")]
    ValidationFailed { message: String },
}

impl From<ParseError> for CompilerError {
    fn from(err: ParseError) -> Self {
        CompilerError::ParseError(err)
    }
}

impl From<Lean4Error> for CompilerError {
    fn from(err: Lean4Error) -> Self {
        CompilerError::Lean4Error(err)
    }
}

impl From<SMTError> for CompilerError {
    fn from(err: SMTError) -> Self {
        CompilerError::SMTError(err)
    }
}

impl From<ConfigError> for CompilerError {
    fn from(err: ConfigError) -> Self {
        CompilerError::ConfigError(err)
    }
}

/// Result type for the STL compiler
pub type CompilerResult<T> = Result<T, CompilerError>;

/// Result type for parsing operations
pub type ParseResult<T> = Result<T, ParseError>;

/// Result type for Lean 4 operations
pub type Lean4Result<T> = Result<T, Lean4Error>;

/// Result type for SMT operations
pub type SMTResult<T> = Result<T, SMTError>;

/// Result type for configuration operations
pub type ConfigResult<T> = Result<T, ConfigError>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_error_conversion() {
        let parse_err = ParseError::SyntaxError {
            position: 10,
            message: "Invalid syntax".to_string(),
        };
        let compiler_err: CompilerError = parse_err.into();
        
        match compiler_err {
            CompilerError::ParseError(_) => (),
            _ => panic!("Expected ParseError"),
        }
    }

    #[test]
    fn test_lean4_error_conversion() {
        let lean4_err = Lean4Error::Lean4NotFound {
            path: "/usr/bin/lean".to_string(),
        };
        let compiler_err: CompilerError = lean4_err.into();
        
        match compiler_err {
            CompilerError::Lean4Error(_) => (),
            _ => panic!("Expected Lean4Error"),
        }
    }

    #[test]
    fn test_smt_error_conversion() {
        let smt_err = SMTError::SolverNotFound {
            solver: "z3".to_string(),
        };
        let compiler_err: CompilerError = smt_err.into();
        
        match compiler_err {
            CompilerError::SMTError(_) => (),
            _ => panic!("Expected SMTError"),
        }
    }
} 