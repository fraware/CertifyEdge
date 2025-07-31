//! CertifyEdge Auditor API
//! 
//! This crate provides a REST API for auditing and provenance tracking with
//! OIDC JWT authentication and OPA/Rego policies per auditor role.

pub mod api;
pub mod auth;
pub mod diff;
pub mod query;
pub mod storage;
pub mod error;
pub mod config;
pub mod opa;

use axum::{
    routing::{get, post},
    Router,
    http::{HeaderValue, Method},
    middleware,
};
use tower_http::cors::CorsLayer;
use std::collections::HashMap;
use std::time::SystemTime;
use uuid::Uuid;

use crate::error::AuditorError;
use crate::config::AuditorConfig;
use crate::storage::CertificateStorage;
use crate::auth::AuthMiddleware;

/// Main auditor API service
#[derive(Debug, Clone)]
pub struct AuditorAPI {
    config: AuditorConfig,
    storage: CertificateStorage,
}

impl AuditorAPI {
    /// Create a new auditor API with default configuration
    pub fn new() -> Result<Self, AuditorError> {
        let config = AuditorConfig::default();
        let storage = CertificateStorage::new(&config)?;
        
        Ok(Self { config, storage })
    }

    /// Create a new auditor API with custom configuration
    pub fn with_config(config: AuditorConfig) -> Result<Self, AuditorError> {
        let storage = CertificateStorage::new(&config)?;
        
        Ok(Self { config, storage })
    }

    /// Create the Axum router with all routes and middleware
    pub fn create_router(&self) -> Router {
        let cors = CorsLayer::new()
            .allow_origin("http://localhost:3000".parse::<HeaderValue>().unwrap())
            .allow_methods([Method::GET, Method::POST])
            .allow_headers(vec![
                "authorization".parse::<HeaderValue>().unwrap(),
                "content-type".parse::<HeaderValue>().unwrap(),
            ]);

        Router::new()
            .route("/health", get(api::health_check))
            .route("/cert/:model_sha", get(api::get_certificate))
            .route("/diff/:old_sha/:new_sha", get(api::get_certificate_diff))
            .route("/query", post(api::query_certificates))
            .route("/metrics", get(api::get_metrics))
            .layer(cors)
            .layer(middleware::from_fn_with_state(
                self.clone(),
                AuthMiddleware::authenticate,
            ))
    }

    /// Get certificate by model SHA
    pub async fn get_certificate(
        &self,
        model_sha: &str,
        include_proofs: bool,
    ) -> Result<CertificateResponse, AuditorError> {
        let certificate = self.storage.get_certificate(model_sha).await?;
        
        let response = if include_proofs {
            CertificateResponse::Full(certificate)
        } else {
            CertificateResponse::Summary(certificate.into_summary())
        };
        
        Ok(response)
    }

    /// Get differences between two certificates
    pub async fn get_certificate_diff(
        &self,
        old_sha: &str,
        new_sha: &str,
    ) -> Result<CertificateDiff, AuditorError> {
        let old_cert = self.storage.get_certificate(old_sha).await?;
        let new_cert = self.storage.get_certificate(new_sha).await?;
        
        let diff = diff::CertificateDiffer::new().diff(&old_cert, &new_cert)?;
        
        Ok(diff)
    }

    /// Query certificates with regulatory clause tags
    pub async fn query_certificates(
        &self,
        query: &QueryRequest,
    ) -> Result<QueryResponse, AuditorError> {
        let query_engine = query::QueryEngine::new(&self.config);
        let results = query_engine.execute_query(query).await?;
        
        Ok(QueryResponse {
            query_id: Uuid::new_v4().to_string(),
            results,
            total_count: results.len(),
            query_time_ms: 0, // Will be set by caller
        })
    }

    /// Get API metrics
    pub fn get_metrics(&self) -> Result<Metrics, AuditorError> {
        let stats = self.storage.get_stats()?;
        
        Ok(Metrics {
            total_certificates: stats.total_certificates,
            total_queries: stats.total_queries,
            average_response_time_ms: stats.average_response_time_ms,
            cache_hit_rate: stats.cache_hit_rate,
            uptime_seconds: SystemTime::now()
                .duration_since(self.config.start_time)
                .unwrap_or_default()
                .as_secs(),
        })
    }

    /// Validate API configuration
    pub fn validate_config(&self) -> Result<(), AuditorError> {
        self.config.validate()
    }
}

impl Default for AuditorAPI {
    fn default() -> Self {
        Self::new().expect("Failed to create default auditor API")
    }
}

/// Certificate response types
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum CertificateResponse {
    /// Full certificate with all proofs
    Full(crate::storage::Certificate),
    /// Summary without proofs
    Summary(CertificateSummary),
}

/// Certificate summary for API responses
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CertificateSummary {
    pub certificate_id: String,
    pub model_sha: String,
    pub created_at: SystemTime,
    pub version: String,
    pub solver_version: String,
    pub lean_version: String,
    pub is_verified: bool,
    pub verification_time_ms: u64,
}

/// Certificate differences
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct CertificateDiff {
    pub old_sha: String,
    pub new_sha: String,
    pub diff_type: DiffType,
    pub changes: Vec<Change>,
    pub summary: DiffSummary,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum DiffType {
    SpecChanged,
    ProofChanged,
    SolverChanged,
    VersionChanged,
    NoChange,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Change {
    pub field: String,
    pub old_value: String,
    pub new_value: String,
    pub severity: ChangeSeverity,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum ChangeSeverity {
    Low,
    Medium,
    High,
    Critical,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct DiffSummary {
    pub total_changes: usize,
    pub critical_changes: usize,
    pub high_changes: usize,
    pub medium_changes: usize,
    pub low_changes: usize,
}

/// Query request for regulatory compliance
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct QueryRequest {
    pub regulation_tags: Vec<String>,
    pub date_range: Option<DateRange>,
    pub solver_preferences: Option<Vec<String>>,
    pub verification_status: Option<VerificationStatus>,
    pub limit: Option<usize>,
    pub offset: Option<usize>,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct DateRange {
    pub start: SystemTime,
    pub end: SystemTime,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum VerificationStatus {
    Verified,
    Unverified,
    Failed,
    Pending,
}

/// Query response
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct QueryResponse {
    pub query_id: String,
    pub results: Vec<CertificateSummary>,
    pub total_count: usize,
    pub query_time_ms: u64,
}

/// API metrics
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Metrics {
    pub total_certificates: u64,
    pub total_queries: u64,
    pub average_response_time_ms: u64,
    pub cache_hit_rate: f64,
    pub uptime_seconds: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_auditor_api_creation() {
        let api = AuditorAPI::new();
        assert!(api.is_ok());
    }

    #[tokio::test]
    async fn test_router_creation() {
        let api = AuditorAPI::new().unwrap();
        let router = api.create_router();
        assert!(router.into_make_service().into_make_service().is_ok());
    }

    #[test]
    fn test_metrics_creation() {
        let api = AuditorAPI::new().unwrap();
        let metrics = api.get_metrics();
        assert!(metrics.is_ok());
    }
} 