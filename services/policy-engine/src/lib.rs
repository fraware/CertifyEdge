//! Policy Engine for CertifyEdge
//! 
//! This service provides OPA (Open Policy Agent) integration for
//! authorization, compliance, and policy enforcement across the platform.

pub mod api;
pub mod config;
pub mod error;
pub mod models;
pub mod opa;
pub mod policies;
pub mod validation;

use crate::config::PolicyEngineConfig;
use crate::error::PolicyEngineError;
use crate::opa::OpaClient;
use axum::Router;
use std::sync::Arc;
use tokio::sync::RwLock;

/// Main policy engine service
pub struct PolicyEngine {
    config: PolicyEngineConfig,
    opa_client: Arc<OpaClient>,
    metrics: Arc<RwLock<PolicyMetrics>>,
}

impl PolicyEngine {
    /// Create a new policy engine
    pub async fn new() -> Result<Self, PolicyEngineError> {
        let config = PolicyEngineConfig::from_env()?;
        let opa_client = Arc::new(OpaClient::new(&config.opa_endpoint)?);
        let metrics = Arc::new(RwLock::new(PolicyMetrics::default()));
        
        Ok(Self {
            config,
            opa_client,
            metrics,
        })
    }
    
    /// Create a new policy engine with custom config
    pub async fn with_config(config: PolicyEngineConfig) -> Result<Self, PolicyEngineError> {
        let opa_client = Arc::new(OpaClient::new(&config.opa_endpoint)?);
        let metrics = Arc::new(RwLock::new(PolicyMetrics::default()));
        
        Ok(Self {
            config,
            opa_client,
            metrics,
        })
    }
    
    /// Create the API router
    pub fn create_router(&self) -> Router {
        api::create_router(self)
    }
    
    /// Evaluate a policy decision
    pub async fn evaluate_policy(
        &self,
        policy_name: &str,
        input: serde_json::Value,
    ) -> Result<models::PolicyDecision, PolicyEngineError> {
        let decision = self.opa_client.evaluate_policy(policy_name, input).await?;
        
        // Update metrics
        {
            let mut metrics = self.metrics.write().await;
            metrics.policy_evaluations += 1;
            if decision.allowed {
                metrics.allowed_decisions += 1;
            } else {
                metrics.denied_decisions += 1;
            }
        }
        
        Ok(decision)
    }
    
    /// Check authorization for a request
    pub async fn check_authorization(
        &self,
        user: &models::User,
        resource: &models::Resource,
        action: &str,
    ) -> Result<bool, PolicyEngineError> {
        let input = serde_json::json!({
            "user": user,
            "resource": resource,
            "action": action,
        });
        
        let decision = self.evaluate_policy("authorization", input).await?;
        Ok(decision.allowed)
    }
    
    /// Validate compliance for a certificate
    pub async fn validate_compliance(
        &self,
        certificate: &models::Certificate,
        regulation: &str,
    ) -> Result<models::ComplianceResult, PolicyEngineError> {
        let input = serde_json::json!({
            "certificate": certificate,
            "regulation": regulation,
        });
        
        let decision = self.evaluate_policy("compliance", input).await?;
        
        Ok(models::ComplianceResult {
            compliant: decision.allowed,
            violations: decision.violations.unwrap_or_default(),
            recommendations: decision.recommendations.unwrap_or_default(),
        })
    }
    
    /// Get service metrics
    pub async fn get_metrics(&self) -> PolicyMetrics {
        self.metrics.read().await.clone()
    }
    
    /// Load a new policy
    pub async fn load_policy(
        &self,
        policy_name: &str,
        policy_content: &str,
    ) -> Result<(), PolicyEngineError> {
        self.opa_client.load_policy(policy_name, policy_content).await
    }
}

/// Service metrics
#[derive(Debug, Clone, Default)]
pub struct PolicyMetrics {
    pub policy_evaluations: u64,
    pub allowed_decisions: u64,
    pub denied_decisions: u64,
    pub policy_loads: u64,
    pub errors: u64,
}

impl Default for PolicyEngine {
    fn default() -> Self {
        // This will panic if the service can't be created
        // In production, you'd want to handle this more gracefully
        tokio::runtime::Runtime::new()
            .unwrap()
            .block_on(Self::new())
            .expect("Failed to create default PolicyEngine")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::{User, Resource, UserRole};
    
    #[tokio::test]
    async fn test_policy_engine_creation() {
        let engine = PolicyEngine::new().await;
        assert!(engine.is_ok());
    }
    
    #[tokio::test]
    async fn test_authorization_check() {
        let engine = PolicyEngine::new().await.unwrap();
        
        let user = User {
            id: "test-user".to_string(),
            roles: vec![UserRole::Auditor],
            permissions: vec!["read".to_string()],
        };
        
        let resource = Resource {
            id: "test-cert".to_string(),
            type_: "certificate".to_string(),
            owner: "test-owner".to_string(),
        };
        
        let result = engine.check_authorization(&user, &resource, "read").await;
        assert!(result.is_ok());
    }
} 