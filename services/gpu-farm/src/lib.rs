//! CertifyEdge GPU-Backed Verification Farm
//! 
//! This crate provides a Kubernetes-based GPU farm for Lean proof search fallback,
//! with autoscaling spot GPU nodes (A10/A100) using Karpenter and budget caps.

pub mod kubernetes;
pub mod autoscaler;
pub mod scheduler;
pub mod monitoring;
pub mod budget;
pub mod chaos;
pub mod error;
pub mod config;

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{Duration, SystemTime};
use uuid::Uuid;

use crate::error::GPUFarmError;
use crate::config::GPUFarmConfig;
use crate::kubernetes::K8sClient;
use crate::autoscaler::Autoscaler;
use crate::scheduler::JobScheduler;
use crate::monitoring::MetricsCollector;
use crate::budget::BudgetManager;
use crate::chaos::ChaosEngine;

/// Main GPU farm service
#[derive(Debug, Clone)]
pub struct GPUFarm {
    config: GPUFarmConfig,
    k8s_client: K8sClient,
    autoscaler: Autoscaler,
    scheduler: JobScheduler,
    metrics: MetricsCollector,
    budget_manager: BudgetManager,
    chaos_engine: ChaosEngine,
}

impl GPUFarm {
    /// Create a new GPU farm with default configuration
    pub fn new() -> Result<Self, GPUFarmError> {
        let config = GPUFarmConfig::default();
        let k8s_client = K8sClient::new(&config)?;
        let autoscaler = Autoscaler::new(&config)?;
        let scheduler = JobScheduler::new(&config)?;
        let metrics = MetricsCollector::new(&config)?;
        let budget_manager = BudgetManager::new(&config)?;
        let chaos_engine = ChaosEngine::new(&config)?;
        
        Ok(Self {
            config,
            k8s_client,
            autoscaler,
            scheduler,
            metrics,
            budget_manager,
            chaos_engine,
        })
    }

    /// Create a new GPU farm with custom configuration
    pub fn with_config(config: GPUFarmConfig) -> Result<Self, GPUFarmError> {
        let k8s_client = K8sClient::new(&config)?;
        let autoscaler = Autoscaler::new(&config)?;
        let scheduler = JobScheduler::new(&config)?;
        let metrics = MetricsCollector::new(&config)?;
        let budget_manager = BudgetManager::new(&config)?;
        let chaos_engine = ChaosEngine::new(&config)?;
        
        Ok(Self {
            config,
            k8s_client,
            autoscaler,
            scheduler,
            metrics,
            budget_manager,
            chaos_engine,
        })
    }

    /// Submit a Lean proof job to the GPU farm
    pub async fn submit_proof_job(
        &mut self,
        job_request: ProofJobRequest,
    ) -> Result<ProofJobResponse, GPUFarmError> {
        let start_time = SystemTime::now();
        
        // Check budget constraints
        self.budget_manager.check_budget_constraints(&job_request).await?;
        
        // Create job specification
        let job_spec = self.create_job_spec(&job_request)?;
        
        // Submit job to Kubernetes
        let job_id = self.scheduler.submit_job(job_spec).await?;
        
        // Update metrics
        self.metrics.record_job_submission(&job_request, &job_id).await?;
        
        // Trigger autoscaling if needed
        self.autoscaler.check_and_scale(&job_request).await?;
        
        let submission_time = start_time.elapsed()?.as_millis() as u64;
        
        Ok(ProofJobResponse {
            job_id,
            status: JobStatus::Submitted,
            submission_time_ms: submission_time,
            estimated_completion_time: self.estimate_completion_time(&job_request),
            estimated_cost: self.estimate_job_cost(&job_request),
        })
    }

    /// Get job status
    pub async fn get_job_status(
        &self,
        job_id: &str,
    ) -> Result<JobStatus, GPUFarmError> {
        self.scheduler.get_job_status(job_id).await
    }

    /// Cancel a running job
    pub async fn cancel_job(
        &mut self,
        job_id: &str,
    ) -> Result<(), GPUFarmError> {
        self.scheduler.cancel_job(job_id).await?;
        self.metrics.record_job_cancellation(job_id).await?;
        Ok(())
    }

    /// Get farm statistics
    pub async fn get_farm_stats(&self) -> Result<FarmStats, GPUFarmError> {
        let node_stats = self.k8s_client.get_node_stats().await?;
        let job_stats = self.scheduler.get_job_stats().await?;
        let budget_stats = self.budget_manager.get_budget_stats().await?;
        let autoscaling_stats = self.autoscaler.get_stats().await?;
        
        Ok(FarmStats {
            total_nodes: node_stats.total_nodes,
            active_nodes: node_stats.active_nodes,
            gpu_nodes: node_stats.gpu_nodes,
            total_gpus: node_stats.total_gpus,
            available_gpus: node_stats.available_gpus,
            total_jobs: job_stats.total_jobs,
            running_jobs: job_stats.running_jobs,
            queued_jobs: job_stats.queued_jobs,
            completed_jobs: job_stats.completed_jobs,
            failed_jobs: job_stats.failed_jobs,
            average_job_duration_ms: job_stats.average_job_duration_ms,
            budget_used: budget_stats.budget_used,
            budget_remaining: budget_stats.budget_remaining,
            budget_limit: budget_stats.budget_limit,
            autoscaling_events: autoscaling_stats.events,
            uptime_seconds: SystemTime::now()
                .duration_since(self.config.start_time)
                .unwrap_or_default()
                .as_secs(),
        })
    }

    /// Run chaos engineering tests
    pub async fn run_chaos_tests(&mut self) -> Result<ChaosTestResult, GPUFarmError> {
        self.chaos_engine.run_tests().await
    }

    /// Get farm health status
    pub async fn get_health_status(&self) -> Result<HealthStatus, GPUFarmError> {
        let node_health = self.k8s_client.check_node_health().await?;
        let scheduler_health = self.scheduler.check_health().await?;
        let budget_health = self.budget_manager.check_health().await?;
        let autoscaler_health = self.autoscaler.check_health().await?;
        
        let overall_health = if node_health.is_healthy 
            && scheduler_health.is_healthy 
            && budget_health.is_healthy 
            && autoscaler_health.is_healthy {
            HealthStatus::Healthy
        } else {
            HealthStatus::Degraded
        };
        
        Ok(overall_health)
    }

    /// Create job specification
    fn create_job_spec(&self, request: &ProofJobRequest) -> Result<JobSpec, GPUFarmError> {
        let job_id = Uuid::new_v4().to_string();
        
        Ok(JobSpec {
            job_id: job_id.clone(),
            lean_spec: request.lean_spec.clone(),
            proof_goal: request.proof_goal.clone(),
            timeout_seconds: request.timeout_seconds,
            gpu_requirements: request.gpu_requirements.clone(),
            memory_requirements_mb: request.memory_requirements_mb,
            cpu_requirements: request.cpu_requirements,
            priority: request.priority,
            node_selector: self.create_node_selector(&request.gpu_requirements),
            tolerations: self.create_tolerations(),
            resource_limits: self.create_resource_limits(request),
            environment_variables: self.create_environment_variables(request),
        })
    }

    /// Create node selector for GPU requirements
    fn create_node_selector(&self, gpu_req: &GPURequirements) -> HashMap<String, String> {
        let mut selector = HashMap::new();
        selector.insert("gpu-type".to_string(), gpu_req.gpu_type.clone());
        selector.insert("gpu-count".to_string(), gpu_req.gpu_count.to_string());
        selector.insert("spot-instance".to_string(), "true".to_string());
        selector
    }

    /// Create tolerations for spot instances
    fn create_tolerations(&self) -> Vec<Toleration> {
        vec![
            Toleration {
                key: "kubernetes.azure.com/scalesetpriority".to_string(),
                operator: "Equal".to_string(),
                value: "spot".to_string(),
                effect: "NoSchedule".to_string(),
            }
        ]
    }

    /// Create resource limits
    fn create_resource_limits(&self, request: &ProofJobRequest) -> ResourceLimits {
        ResourceLimits {
            cpu: format!("{}", request.cpu_requirements),
            memory: format!("{}Mi", request.memory_requirements_mb),
            gpu: request.gpu_requirements.gpu_count.to_string(),
            ephemeral_storage: "10Gi".to_string(),
        }
    }

    /// Create environment variables
    fn create_environment_variables(&self, request: &ProofJobRequest) -> HashMap<String, String> {
        let mut env_vars = HashMap::new();
        env_vars.insert("LEAN_SPEC".to_string(), request.lean_spec.clone());
        env_vars.insert("PROOF_GOAL".to_string(), request.proof_goal.clone());
        env_vars.insert("TIMEOUT_SECONDS".to_string(), request.timeout_seconds.to_string());
        env_vars.insert("GPU_TYPE".to_string(), request.gpu_requirements.gpu_type.clone());
        env_vars.insert("GPU_COUNT".to_string(), request.gpu_requirements.gpu_count.to_string());
        env_vars
    }

    /// Estimate job completion time
    fn estimate_completion_time(&self, request: &ProofJobRequest) -> SystemTime {
        // Simple estimation based on proof complexity and GPU resources
        let base_time = Duration::from_secs(300); // 5 minutes base
        let complexity_factor = request.proof_goal.len() as u64 / 100;
        let gpu_factor = 1.0 / request.gpu_requirements.gpu_count as f64;
        
        let estimated_duration = base_time * complexity_factor;
        SystemTime::now() + estimated_duration
    }

    /// Estimate job cost
    fn estimate_job_cost(&self, request: &ProofJobRequest) -> f64 {
        // Cost estimation based on GPU type and estimated duration
        let gpu_cost_per_hour = match request.gpu_requirements.gpu_type.as_str() {
            "a10" => 0.50, // $0.50/hour for A10
            "a100" => 2.40, // $2.40/hour for A100
            _ => 1.00, // Default cost
        };
        
        let estimated_hours = request.timeout_seconds as f64 / 3600.0;
        gpu_cost_per_hour * request.gpu_requirements.gpu_count as f64 * estimated_hours
    }

    /// Validate farm configuration
    pub fn validate_config(&self) -> Result<(), GPUFarmError> {
        self.config.validate()
    }
}

impl Default for GPUFarm {
    fn default() -> Self {
        Self::new().expect("Failed to create default GPU farm")
    }
}

/// Proof job request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofJobRequest {
    pub lean_spec: String,
    pub proof_goal: String,
    pub timeout_seconds: u64,
    pub gpu_requirements: GPURequirements,
    pub memory_requirements_mb: u64,
    pub cpu_requirements: f64,
    pub priority: JobPriority,
    pub user_id: String,
    pub project_id: String,
}

/// GPU requirements
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GPURequirements {
    pub gpu_type: String, // "a10", "a100", etc.
    pub gpu_count: u32,
    pub memory_per_gpu_gb: u32,
}

/// Job priority
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum JobPriority {
    Low = 1,
    Normal = 5,
    High = 10,
    Critical = 15,
}

/// Proof job response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofJobResponse {
    pub job_id: String,
    pub status: JobStatus,
    pub submission_time_ms: u64,
    pub estimated_completion_time: SystemTime,
    pub estimated_cost: f64,
}

/// Job status
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum JobStatus {
    Submitted,
    Queued,
    Running,
    Completed,
    Failed,
    Cancelled,
    Timeout,
}

/// Job specification
#[derive(Debug, Clone)]
pub struct JobSpec {
    pub job_id: String,
    pub lean_spec: String,
    pub proof_goal: String,
    pub timeout_seconds: u64,
    pub gpu_requirements: GPURequirements,
    pub memory_requirements_mb: u64,
    pub cpu_requirements: f64,
    pub priority: JobPriority,
    pub node_selector: HashMap<String, String>,
    pub tolerations: Vec<Toleration>,
    pub resource_limits: ResourceLimits,
    pub environment_variables: HashMap<String, String>,
}

/// Kubernetes toleration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Toleration {
    pub key: String,
    pub operator: String,
    pub value: String,
    pub effect: String,
}

/// Resource limits
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceLimits {
    pub cpu: String,
    pub memory: String,
    pub gpu: String,
    pub ephemeral_storage: String,
}

/// Farm statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FarmStats {
    pub total_nodes: u32,
    pub active_nodes: u32,
    pub gpu_nodes: u32,
    pub total_gpus: u32,
    pub available_gpus: u32,
    pub total_jobs: u64,
    pub running_jobs: u64,
    pub queued_jobs: u64,
    pub completed_jobs: u64,
    pub failed_jobs: u64,
    pub average_job_duration_ms: u64,
    pub budget_used: f64,
    pub budget_remaining: f64,
    pub budget_limit: f64,
    pub autoscaling_events: u64,
    pub uptime_seconds: u64,
}

/// Health status
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum HealthStatus {
    Healthy,
    Degraded,
    Unhealthy,
}

/// Chaos test result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChaosTestResult {
    pub test_name: String,
    pub success: bool,
    pub recovery_time_ms: u64,
    pub availability_percentage: f64,
    pub details: HashMap<String, String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_gpu_farm_creation() {
        let farm = GPUFarm::new();
        assert!(farm.is_ok());
    }

    #[tokio::test]
    async fn test_job_submission() {
        let mut farm = GPUFarm::new().unwrap();
        
        let request = ProofJobRequest {
            lean_spec: "example lean spec".to_string(),
            proof_goal: "example proof goal".to_string(),
            timeout_seconds: 3600,
            gpu_requirements: GPURequirements {
                gpu_type: "a10".to_string(),
                gpu_count: 1,
                memory_per_gpu_gb: 24,
            },
            memory_requirements_mb: 8192,
            cpu_requirements: 4.0,
            priority: JobPriority::Normal,
            user_id: "user123".to_string(),
            project_id: "project456".to_string(),
        };
        
        let response = farm.submit_proof_job(request).await;
        assert!(response.is_ok());
    }

    #[tokio::test]
    async fn test_farm_stats() {
        let farm = GPUFarm::new().unwrap();
        let stats = farm.get_farm_stats().await;
        assert!(stats.is_ok());
    }
} 