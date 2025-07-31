//! API routes for the CertifyEdge Auditor API

use axum::{
    extract::{Path, Query, State},
    http::StatusCode,
    response::Json,
    routing::{get, post},
    Router,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::Instant;

use crate::{
    AuditorAPI, CertificateResponse, CertificateDiff, QueryRequest, QueryResponse, Metrics,
    error::AuditorError,
};

/// Health check endpoint
pub async fn health_check() -> Json<HealthResponse> {
    Json(HealthResponse {
        status: "healthy".to_string(),
        timestamp: std::time::SystemTime::now(),
        version: env!("CARGO_PKG_VERSION").to_string(),
    })
}

/// Get certificate by model SHA
pub async fn get_certificate(
    State(api): State<AuditorAPI>,
    Path(model_sha): Path<String>,
    Query(params): Query<CertificateQueryParams>,
) -> Result<Json<CertificateResponse>, (StatusCode, String)> {
    let start_time = Instant::now();
    
    let include_proofs = params.include_proofs.unwrap_or(false);
    
    let certificate = api
        .get_certificate(&model_sha, include_proofs)
        .await
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    
    // Record metrics
    let response_time = start_time.elapsed().as_millis() as u64;
    // TODO: Update metrics
    
    Ok(Json(certificate))
}

/// Get certificate differences
pub async fn get_certificate_diff(
    State(api): State<AuditorAPI>,
    Path((old_sha, new_sha)): Path<(String, String)>,
) -> Result<Json<CertificateDiff>, (StatusCode, String)> {
    let start_time = Instant::now();
    
    let diff = api
        .get_certificate_diff(&old_sha, &new_sha)
        .await
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    
    // Record metrics
    let response_time = start_time.elapsed().as_millis() as u64;
    // TODO: Update metrics
    
    Ok(Json(diff))
}

/// Query certificates with regulatory clause tags
pub async fn query_certificates(
    State(api): State<AuditorAPI>,
    Json(query): Json<QueryRequest>,
) -> Result<Json<QueryResponse>, (StatusCode, String)> {
    let start_time = Instant::now();
    
    let mut response = api
        .query_certificates(&query)
        .await
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    
    // Set query time
    response.query_time_ms = start_time.elapsed().as_millis() as u64;
    
    Ok(Json(response))
}

/// Get API metrics
pub async fn get_metrics(
    State(api): State<AuditorAPI>,
) -> Result<Json<Metrics>, (StatusCode, String)> {
    let metrics = api
        .get_metrics()
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    
    Ok(Json(metrics))
}

/// Health check response
#[derive(Debug, Serialize)]
pub struct HealthResponse {
    pub status: String,
    pub timestamp: std::time::SystemTime,
    pub version: String,
}

/// Query parameters for certificate endpoint
#[derive(Debug, Deserialize)]
pub struct CertificateQueryParams {
    pub include_proofs: Option<bool>,
    pub format: Option<String>,
}

/// Error response
#[derive(Debug, Serialize)]
pub struct ErrorResponse {
    pub error: String,
    pub code: String,
    pub timestamp: std::time::SystemTime,
}

impl From<AuditorError> for ErrorResponse {
    fn from(error: AuditorError) -> Self {
        Self {
            error: error.to_string(),
            code: format!("{:?}", error),
            timestamp: std::time::SystemTime::now(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axum::http::StatusCode;

    #[tokio::test]
    async fn test_health_check() {
        let response = health_check().await;
        assert_eq!(response.0.status, "healthy");
    }

    #[tokio::test]
    async fn test_get_metrics() {
        let api = AuditorAPI::new().unwrap();
        let response = get_metrics(State(api)).await;
        assert!(response.is_ok());
    }
} 