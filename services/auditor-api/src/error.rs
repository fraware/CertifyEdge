//! Error handling for the CertifyEdge Auditor API

use thiserror::Error;
use std::collections::HashMap;

/// Main error type for the auditor API
#[derive(Error, Debug)]
pub enum AuditorError {
    #[error("Authentication error: {0}")]
    AuthenticationError(String),
    
    #[error("Authorization error: {0}")]
    AuthorizationError(String),
    
    #[error("Certificate not found: {0}")]
    CertificateNotFound(String),
    
    #[error("Invalid certificate format: {0}")]
    InvalidCertificateFormat(String),
    
    #[error("Storage error: {0}")]
    StorageError(String),
    
    #[error("Database error: {0}")]
    DatabaseError(String),
    
    #[error("OPA policy evaluation error: {0}")]
    OpaError(String),
    
    #[error("Query error: {0}")]
    QueryError(String),
    
    #[error("Validation error: {0}")]
    ValidationError(String),
    
    #[error("Configuration error: {0}")]
    ConfigError(String),
    
    #[error("Rate limit exceeded: {0}")]
    RateLimitExceeded(String),
    
    #[error("Timeout error: {0}")]
    TimeoutError(String),
    
    #[error("Internal error: {0}")]
    InternalError(String),
    
    #[error("Serialization error: {0}")]
    SerializationError(String),
    
    #[error("Deserialization error: {0}")]
    DeserializationError(String),
    
    #[error("IO error: {0}")]
    IOError(String),
    
    #[error("Network error: {0}")]
    NetworkError(String),
}

impl From<serde_json::Error> for AuditorError {
    fn from(err: serde_json::Error) -> Self {
        AuditorError::SerializationError(err.to_string())
    }
}

impl From<std::io::Error> for AuditorError {
    fn from(err: std::io::Error) -> Self {
        AuditorError::IOError(err.to_string())
    }
}

impl From<sqlx::Error> for AuditorError {
    fn from(err: sqlx::Error) -> Self {
        AuditorError::DatabaseError(err.to_string())
    }
}

impl From<reqwest::Error> for AuditorError {
    fn from(err: reqwest::Error) -> Self {
        AuditorError::NetworkError(err.to_string())
    }
}

impl From<jsonwebtoken::errors::Error> for AuditorError {
    fn from(err: jsonwebtoken::errors::Error) -> Self {
        AuditorError::AuthenticationError(format!("JWT error: {}", err))
    }
}

/// Error context for additional debugging information
#[derive(Debug, Clone)]
pub struct ErrorContext {
    pub error_code: String,
    pub user_id: Option<String>,
    pub request_id: Option<String>,
    pub timestamp: std::time::SystemTime,
    pub metadata: HashMap<String, String>,
}

impl ErrorContext {
    pub fn new(error_code: String) -> Self {
        Self {
            error_code,
            user_id: None,
            request_id: None,
            timestamp: std::time::SystemTime::now(),
            metadata: HashMap::new(),
        }
    }
    
    pub fn with_user_id(mut self, user_id: String) -> Self {
        self.user_id = Some(user_id);
        self
    }
    
    pub fn with_request_id(mut self, request_id: String) -> Self {
        self.request_id = Some(request_id);
        self
    }
    
    pub fn with_metadata(mut self, key: String, value: String) -> Self {
        self.metadata.insert(key, value);
        self
    }
}

/// Error response for API endpoints
#[derive(Debug, serde::Serialize)]
pub struct ErrorResponse {
    pub error: String,
    pub code: String,
    pub message: String,
    pub timestamp: std::time::SystemTime,
    pub request_id: Option<String>,
    pub details: Option<HashMap<String, String>>,
}

impl From<AuditorError> for ErrorResponse {
    fn from(error: AuditorError) -> Self {
        Self {
            error: error.to_string(),
            code: format!("{:?}", error),
            message: error.to_string(),
            timestamp: std::time::SystemTime::now(),
            request_id: None,
            details: None,
        }
    }
}

/// Error codes for consistent error handling
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ErrorCode {
    // Authentication errors (1000-1099)
    InvalidToken = 1000,
    TokenExpired = 1001,
    MissingAuthorization = 1002,
    InvalidCredentials = 1003,
    
    // Authorization errors (1100-1199)
    InsufficientPermissions = 1100,
    RoleNotFound = 1101,
    PolicyEvaluationFailed = 1102,
    AccessDenied = 1103,
    
    // Certificate errors (2000-2099)
    CertificateNotFound = 2000,
    InvalidCertificateFormat = 2001,
    CertificateExpired = 2002,
    CertificateRevoked = 2003,
    InvalidSignature = 2004,
    
    // Storage errors (3000-3099)
    StorageUnavailable = 3000,
    DatabaseConnectionFailed = 3001,
    QueryTimeout = 3002,
    DataCorruption = 3003,
    
    // Query errors (4000-4099)
    InvalidQuery = 4000,
    QueryTimeout = 4001,
    TooManyResults = 4002,
    InvalidFilter = 4003,
    
    // Validation errors (5000-5099)
    InvalidInput = 5000,
    MissingRequiredField = 5001,
    InvalidFormat = 5002,
    OutOfRange = 5003,
    
    // Rate limiting errors (6000-6099)
    RateLimitExceeded = 6000,
    TooManyRequests = 6001,
    QuotaExceeded = 6002,
    
    // Internal errors (9000-9099)
    InternalError = 9000,
    ServiceUnavailable = 9001,
    ConfigurationError = 9002,
    NetworkError = 9003,
}

impl ErrorCode {
    pub fn as_u16(&self) -> u16 {
        *self as u16
    }
    
    pub fn as_string(&self) -> String {
        format!("{:04}", self.as_u16())
    }
    
    pub fn get_http_status(&self) -> u16 {
        match self {
            // 4xx Client Errors
            ErrorCode::InvalidToken | ErrorCode::TokenExpired | ErrorCode::MissingAuthorization => 401,
            ErrorCode::InvalidCredentials => 401,
            ErrorCode::InsufficientPermissions | ErrorCode::AccessDenied => 403,
            ErrorCode::CertificateNotFound => 404,
            ErrorCode::InvalidCertificateFormat | ErrorCode::InvalidInput | ErrorCode::MissingRequiredField => 400,
            ErrorCode::InvalidQuery | ErrorCode::InvalidFilter => 400,
            ErrorCode::TooManyResults => 413,
            
            // 5xx Server Errors
            ErrorCode::StorageUnavailable | ErrorCode::DatabaseConnectionFailed => 503,
            ErrorCode::QueryTimeout => 504,
            ErrorCode::DataCorruption => 500,
            ErrorCode::InternalError | ErrorCode::ServiceUnavailable => 500,
            ErrorCode::ConfigurationError => 500,
            ErrorCode::NetworkError => 502,
            
            // Rate limiting
            ErrorCode::RateLimitExceeded | ErrorCode::TooManyRequests | ErrorCode::QuotaExceeded => 429,
            
            // Default
            _ => 500,
        }
    }
    
    pub fn get_message(&self) -> &'static str {
        match self {
            ErrorCode::InvalidToken => "Invalid authentication token",
            ErrorCode::TokenExpired => "Authentication token has expired",
            ErrorCode::MissingAuthorization => "Missing authorization header",
            ErrorCode::InvalidCredentials => "Invalid credentials provided",
            ErrorCode::InsufficientPermissions => "Insufficient permissions for this operation",
            ErrorCode::AccessDenied => "Access denied",
            ErrorCode::CertificateNotFound => "Certificate not found",
            ErrorCode::InvalidCertificateFormat => "Invalid certificate format",
            ErrorCode::CertificateExpired => "Certificate has expired",
            ErrorCode::CertificateRevoked => "Certificate has been revoked",
            ErrorCode::InvalidSignature => "Invalid certificate signature",
            ErrorCode::StorageUnavailable => "Storage service unavailable",
            ErrorCode::DatabaseConnectionFailed => "Database connection failed",
            ErrorCode::QueryTimeout => "Query execution timed out",
            ErrorCode::DataCorruption => "Data corruption detected",
            ErrorCode::InvalidQuery => "Invalid query parameters",
            ErrorCode::TooManyResults => "Query returned too many results",
            ErrorCode::InvalidFilter => "Invalid filter parameters",
            ErrorCode::InvalidInput => "Invalid input provided",
            ErrorCode::MissingRequiredField => "Missing required field",
            ErrorCode::InvalidFormat => "Invalid data format",
            ErrorCode::OutOfRange => "Value out of valid range",
            ErrorCode::RateLimitExceeded => "Rate limit exceeded",
            ErrorCode::TooManyRequests => "Too many requests",
            ErrorCode::QuotaExceeded => "Quota exceeded",
            ErrorCode::InternalError => "Internal server error",
            ErrorCode::ServiceUnavailable => "Service temporarily unavailable",
            ErrorCode::ConfigurationError => "Configuration error",
            ErrorCode::NetworkError => "Network error",
            _ => "Unknown error",
        }
    }
}

/// Error with context for detailed debugging
#[derive(Debug)]
pub struct ContextualError {
    pub error: AuditorError,
    pub context: ErrorContext,
}

impl ContextualError {
    pub fn new(error: AuditorError, context: ErrorContext) -> Self {
        Self { error, context }
    }
    
    pub fn into_error_response(self) -> ErrorResponse {
        ErrorResponse {
            error: self.error.to_string(),
            code: self.context.error_code,
            message: self.error.to_string(),
            timestamp: self.context.timestamp,
            request_id: self.context.request_id,
            details: Some(self.context.metadata),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_code_http_status() {
        assert_eq!(ErrorCode::InvalidToken.get_http_status(), 401);
        assert_eq!(ErrorCode::AccessDenied.get_http_status(), 403);
        assert_eq!(ErrorCode::CertificateNotFound.get_http_status(), 404);
        assert_eq!(ErrorCode::RateLimitExceeded.get_http_status(), 429);
        assert_eq!(ErrorCode::InternalError.get_http_status(), 500);
    }

    #[test]
    fn test_error_code_messages() {
        assert_eq!(ErrorCode::InvalidToken.get_message(), "Invalid authentication token");
        assert_eq!(ErrorCode::CertificateNotFound.get_message(), "Certificate not found");
        assert_eq!(ErrorCode::InternalError.get_message(), "Internal server error");
    }

    #[test]
    fn test_error_context() {
        let context = ErrorContext::new("TEST001".to_string())
            .with_user_id("user123".to_string())
            .with_request_id("req456".to_string())
            .with_metadata("key".to_string(), "value".to_string());
        
        assert_eq!(context.error_code, "TEST001");
        assert_eq!(context.user_id, Some("user123".to_string()));
        assert_eq!(context.request_id, Some("req456".to_string()));
        assert_eq!(context.metadata.get("key"), Some(&"value".to_string()));
    }
} 