//! Provenance Service for CertifyEdge
//! 
//! This service tracks the complete provenance chain for certificates,
//! providing immutable audit trails and compliance verification.

pub mod api;
pub mod config;
pub mod error;
pub mod models;
pub mod storage;
pub mod tracing;
pub mod validation;

use crate::config::ProvenanceConfig;
use crate::error::ProvenanceError;
use crate::storage::ProvenanceStorage;
use axum::Router;
use std::sync::Arc;
use tokio::sync::RwLock;

/// Main provenance service
pub struct ProvenanceService {
    config: ProvenanceConfig,
    storage: Arc<ProvenanceStorage>,
    metrics: Arc<RwLock<ProvenanceMetrics>>,
}

impl ProvenanceService {
    /// Create a new provenance service
    pub async fn new() -> Result<Self, ProvenanceError> {
        let config = ProvenanceConfig::from_env()?;
        let storage = ProvenanceStorage::new(&config).await?;
        let metrics = Arc::new(RwLock::new(ProvenanceMetrics::default()));
        
        Ok(Self {
            config,
            storage,
            metrics,
        })
    }
    
    /// Create a new provenance service with custom config
    pub async fn with_config(config: ProvenanceConfig) -> Result<Self, ProvenanceError> {
        let storage = ProvenanceStorage::new(&config).await?;
        let metrics = Arc::new(RwLock::new(ProvenanceMetrics::default()));
        
        Ok(Self {
            config,
            storage,
            metrics,
        })
    }
    
    /// Create the API router
    pub fn create_router(&self) -> Router {
        api::create_router(self)
    }
    
    /// Record a new provenance event
    pub async fn record_event(
        &self,
        event: models::ProvenanceEvent,
    ) -> Result<models::ProvenanceRecord, ProvenanceError> {
        let record = models::ProvenanceRecord::from_event(event);
        self.storage.store_record(&record).await?;
        
        // Update metrics
        {
            let mut metrics = self.metrics.write().await;
            metrics.events_recorded += 1;
        }
        
        Ok(record)
    }
    
    /// Get provenance chain for a certificate
    pub async fn get_provenance_chain(
        &self,
        certificate_id: &str,
    ) -> Result<Vec<models::ProvenanceRecord>, ProvenanceError> {
        self.storage.get_provenance_chain(certificate_id).await
    }
    
    /// Verify provenance integrity
    pub async fn verify_provenance(
        &self,
        certificate_id: &str,
    ) -> Result<models::ProvenanceVerification, ProvenanceError> {
        let chain = self.get_provenance_chain(certificate_id).await?;
        validation::verify_provenance_chain(&chain)
    }
    
    /// Get service metrics
    pub async fn get_metrics(&self) -> ProvenanceMetrics {
        self.metrics.read().await.clone()
    }
}

/// Service metrics
#[derive(Debug, Clone, Default)]
pub struct ProvenanceMetrics {
    pub events_recorded: u64,
    pub provenance_chains_retrieved: u64,
    pub verifications_performed: u64,
    pub errors_encountered: u64,
}

impl Default for ProvenanceService {
    fn default() -> Self {
        // This will panic if the service can't be created
        // In production, you'd want to handle this more gracefully
        tokio::runtime::Runtime::new()
            .unwrap()
            .block_on(Self::new())
            .expect("Failed to create default ProvenanceService")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::{ProvenanceEvent, EventType};
    
    #[tokio::test]
    async fn test_provenance_service_creation() {
        let service = ProvenanceService::new().await;
        assert!(service.is_ok());
    }
    
    #[tokio::test]
    async fn test_event_recording() {
        let service = ProvenanceService::new().await.unwrap();
        
        let event = ProvenanceEvent {
            certificate_id: "test-cert-123".to_string(),
            event_type: EventType::CertificateCreated,
            timestamp: chrono::Utc::now(),
            actor: "test-user".to_string(),
            details: serde_json::json!({"test": "data"}),
        };
        
        let result = service.record_event(event).await;
        assert!(result.is_ok());
    }
} 