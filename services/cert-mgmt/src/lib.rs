//! Certificate Management Service for CertifyEdge
//! 
//! This service handles certificate lifecycle operations including
//! creation, validation, revocation, and renewal.

pub mod api;
pub mod config;
pub mod error;
pub mod models;
pub mod storage;
pub mod lifecycle;
pub mod validation;

use crate::config::CertMgmtConfig;
use crate::error::CertMgmtError;
use crate::storage::CertStorage;
use crate::lifecycle::LifecycleManager;
use axum::Router;
use std::sync::Arc;
use tokio::sync::RwLock;

/// Main certificate management service
pub struct CertMgmtService {
    config: CertMgmtConfig,
    storage: Arc<CertStorage>,
    lifecycle: Arc<LifecycleManager>,
    metrics: Arc<RwLock<CertMgmtMetrics>>,
}

impl CertMgmtService {
    /// Create a new certificate management service
    pub async fn new() -> Result<Self, CertMgmtError> {
        let config = CertMgmtConfig::from_env()?;
        let storage = Arc::new(CertStorage::new(&config).await?);
        let lifecycle = Arc::new(LifecycleManager::new(&config).await?);
        let metrics = Arc::new(RwLock::new(CertMgmtMetrics::default()));
        
        Ok(Self {
            config,
            storage,
            lifecycle,
            metrics,
        })
    }
    
    /// Create a new certificate management service with custom config
    pub async fn with_config(config: CertMgmtConfig) -> Result<Self, CertMgmtError> {
        let storage = Arc::new(CertStorage::new(&config).await?);
        let lifecycle = Arc::new(LifecycleManager::new(&config).await?);
        let metrics = Arc::new(RwLock::new(CertMgmtMetrics::default()));
        
        Ok(Self {
            config,
            storage,
            lifecycle,
            metrics,
        })
    }
    
    /// Create the API router
    pub fn create_router(&self) -> Router {
        api::create_router(self)
    }
    
    /// Create a new certificate
    pub async fn create_certificate(
        &self,
        request: models::CreateCertificateRequest,
    ) -> Result<models::Certificate, CertMgmtError> {
        let certificate = models::Certificate::from_request(request)?;
        
        // Validate certificate
        validation::validate_certificate(&certificate)?;
        
        // Store certificate
        self.storage.store_certificate(&certificate).await?;
        
        // Initialize lifecycle
        self.lifecycle.initialize_lifecycle(&certificate.id).await?;
        
        // Update metrics
        {
            let mut metrics = self.metrics.write().await;
            metrics.certificates_created += 1;
        }
        
        Ok(certificate)
    }
    
    /// Get certificate by ID
    pub async fn get_certificate(
        &self,
        certificate_id: &str,
    ) -> Result<models::Certificate, CertMgmtError> {
        self.storage.get_certificate(certificate_id).await
    }
    
    /// Revoke a certificate
    pub async fn revoke_certificate(
        &self,
        certificate_id: &str,
        reason: &str,
    ) -> Result<models::RevocationRecord, CertMgmtError> {
        let certificate = self.get_certificate(certificate_id).await?;
        
        // Check if certificate can be revoked
        if !self.lifecycle.can_revoke(&certificate).await? {
            return Err(CertMgmtError::InvalidOperation(
                "Certificate cannot be revoked".to_string(),
            ));
        }
        
        // Create revocation record
        let revocation = models::RevocationRecord {
            certificate_id: certificate_id.to_string(),
            revoked_at: chrono::Utc::now(),
            reason: reason.to_string(),
            revoked_by: "system".to_string(), // TODO: Get from auth context
        };
        
        // Store revocation
        self.storage.store_revocation(&revocation).await?;
        
        // Update lifecycle
        self.lifecycle.revoke(&certificate_id).await?;
        
        // Update metrics
        {
            let mut metrics = self.metrics.write().await;
            metrics.certificates_revoked += 1;
        }
        
        Ok(revocation)
    }
    
    /// Renew a certificate
    pub async fn renew_certificate(
        &self,
        certificate_id: &str,
    ) -> Result<models::Certificate, CertMgmtError> {
        let original = self.get_certificate(certificate_id).await?;
        
        // Check if certificate can be renewed
        if !self.lifecycle.can_renew(&original).await? {
            return Err(CertMgmtError::InvalidOperation(
                "Certificate cannot be renewed".to_string(),
            ));
        }
        
        // Create renewal request
        let renewal_request = models::CreateCertificateRequest {
            spec_hash: original.spec_hash.clone(),
            lean_proof_hash: original.lean_proof_hash.clone(),
            smt_proof_hashes: original.smt_proof_hashes.clone(),
            model_hash: original.model_hash.clone(),
            solver_version: original.solver_version.clone(),
            lean_version: original.lean_version.clone(),
            sbom_components: original.sbom_components.clone(),
            parent_certificate_id: Some(certificate_id.to_string()),
        };
        
        // Create new certificate
        let renewed = self.create_certificate(renewal_request).await?;
        
        // Update lifecycle
        self.lifecycle.renew(&certificate_id, &renewed.id).await?;
        
        // Update metrics
        {
            let mut metrics = self.metrics.write().await;
            metrics.certificates_renewed += 1;
        }
        
        Ok(renewed)
    }
    
    /// Get certificate lifecycle status
    pub async fn get_lifecycle_status(
        &self,
        certificate_id: &str,
    ) -> Result<models::LifecycleStatus, CertMgmtError> {
        self.lifecycle.get_status(certificate_id).await
    }
    
    /// Get service metrics
    pub async fn get_metrics(&self) -> CertMgmtMetrics {
        self.metrics.read().await.clone()
    }
}

/// Service metrics
#[derive(Debug, Clone, Default)]
pub struct CertMgmtMetrics {
    pub certificates_created: u64,
    pub certificates_revoked: u64,
    pub certificates_renewed: u64,
    pub lifecycle_checks: u64,
    pub errors: u64,
}

impl Default for CertMgmtService {
    fn default() -> Self {
        // This will panic if the service can't be created
        // In production, you'd want to handle this more gracefully
        tokio::runtime::Runtime::new()
            .unwrap()
            .block_on(Self::new())
            .expect("Failed to create default CertMgmtService")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::{CreateCertificateRequest, CertificateStatus};
    
    #[tokio::test]
    async fn test_cert_mgmt_service_creation() {
        let service = CertMgmtService::new().await;
        assert!(service.is_ok());
    }
    
    #[tokio::test]
    async fn test_certificate_creation() {
        let service = CertMgmtService::new().await.unwrap();
        
        let request = CreateCertificateRequest {
            spec_hash: vec![1, 2, 3, 4],
            lean_proof_hash: vec![5, 6, 7, 8],
            smt_proof_hashes: vec![vec![9, 10, 11, 12]],
            model_hash: vec![13, 14, 15, 16],
            solver_version: "1.0.0".to_string(),
            lean_version: "4.0.0".to_string(),
            sbom_components: vec!["component1".to_string()],
            parent_certificate_id: None,
        };
        
        let result = service.create_certificate(request).await;
        assert!(result.is_ok());
    }
} 