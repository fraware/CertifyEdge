//! CertifyEdge Grid-in-Loop Testing Service
//! 
//! This crate provides a comprehensive testing harness for grid-in-loop validation
//! that spins up GridLAB-D or OpenDSS feeder models, injects stochastic load
//! profiles, wraps ML agents behind certify_policy_adapter, and asserts STL
//! invariants in runtime monitor.

pub mod simulator;
pub mod load_profiles;
pub mod policy_adapter;
pub mod monitor;
pub mod stl_validator;
pub mod metrics;
pub mod error;
pub mod config;

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{Duration, SystemTime};
use uuid::Uuid;

use crate::error::GridInLoopError;
use crate::config::GridInLoopConfig;
use crate::simulator::{GridLABD, OpenDSS, PowerFactory};
use crate::load_profiles::LoadProfileGenerator;
use crate::policy_adapter::PolicyAdapter;
use crate::monitor::RuntimeMonitor;
use crate::stl_validator::STLValidator;
use crate::metrics::MetricsCollector;

/// Main grid-in-loop testing service
#[derive(Debug, Clone)]
pub struct GridInLoopTester {
    config: GridInLoopConfig,
    gridlabd: GridLABD,
    opendss: OpenDSS,
    powerfactory: PowerFactory,
    load_generator: LoadProfileGenerator,
    policy_adapter: PolicyAdapter,
    monitor: RuntimeMonitor,
    validator: STLValidator,
    metrics: MetricsCollector,
}

impl GridInLoopTester {
    /// Create a new grid-in-loop tester with default configuration
    pub fn new() -> Result<Self, GridInLoopError> {
        let config = GridInLoopConfig::default();
        let gridlabd = GridLABD::new(&config)?;
        let opendss = OpenDSS::new(&config)?;
        let powerfactory = PowerFactory::new(&config)?;
        let load_generator = LoadProfileGenerator::new(&config)?;
        let policy_adapter = PolicyAdapter::new(&config)?;
        let monitor = RuntimeMonitor::new(&config)?;
        let validator = STLValidator::new(&config)?;
        let metrics = MetricsCollector::new(&config)?;
        
        Ok(Self {
            config,
            gridlabd,
            opendss,
            powerfactory,
            load_generator,
            policy_adapter,
            monitor,
            validator,
            metrics,
        })
    }

    /// Create a new grid-in-loop tester with custom configuration
    pub fn with_config(config: GridInLoopConfig) -> Result<Self, GridInLoopError> {
        let gridlabd = GridLABD::new(&config)?;
        let opendss = OpenDSS::new(&config)?;
        let powerfactory = PowerFactory::new(&config)?;
        let load_generator = LoadProfileGenerator::new(&config)?;
        let policy_adapter = PolicyAdapter::new(&config)?;
        let monitor = RuntimeMonitor::new(&config)?;
        let validator = STLValidator::new(&config)?;
        let metrics = MetricsCollector::new(&config)?;
        
        Ok(Self {
            config,
            gridlabd,
            opendss,
            powerfactory,
            load_generator,
            policy_adapter,
            monitor,
            validator,
            metrics,
        })
    }

    /// Run a complete grid-in-loop test
    pub async fn run_test(
        &mut self,
        test_request: GridInLoopTestRequest,
    ) -> Result<GridInLoopTestResult, GridInLoopError> {
        let start_time = SystemTime::now();
        let test_id = Uuid::new_v4().to_string();
        
        // Initialize simulator
        let simulator = self.initialize_simulator(&test_request.simulator_type).await?;
        
        // Load feeder model
        let feeder_model = self.load_feeder_model(&simulator, &test_request.feeder_model_path).await?;
        
        // Generate stochastic load profiles
        let load_profiles = self.load_generator.generate_profiles(&test_request.load_config).await?;
        
        // Initialize ML agent with policy adapter
        let agent = self.policy_adapter.initialize_agent(&test_request.agent_config).await?;
        
        // Start runtime monitoring
        let monitor_handle = self.monitor.start_monitoring(&test_request.stl_specs).await?;
        
        // Run Monte Carlo simulation
        let mut results = Vec::new();
        let mut violation_count = 0;
        
        for (run_id, load_profile) in load_profiles.iter().enumerate() {
            let run_result = self.run_single_simulation(
                &simulator,
                &feeder_model,
                load_profile,
                &agent,
                &monitor_handle,
                run_id,
            ).await?;
            
            results.push(run_result.clone());
            
            if !run_result.stl_invariants_valid {
                violation_count += 1;
                self.metrics.record_violation(&run_result).await?;
            }
            
            // Check for early termination on critical violations
            if run_result.critical_violations > 0 {
                self.metrics.record_critical_violation(&run_result).await?;
                break;
            }
        }
        
        let test_duration = start_time.elapsed()?.as_secs();
        
        // Generate test report
        let test_result = GridInLoopTestResult {
            test_id,
            total_runs: results.len(),
            successful_runs: results.iter().filter(|r| r.stl_invariants_valid).count(),
            failed_runs: violation_count,
            critical_violations: results.iter().map(|r| r.critical_violations).sum(),
            average_simulation_time_ms: results.iter().map(|r| r.simulation_time_ms).sum::<u64>() / results.len() as u64,
            test_duration_seconds: test_duration,
            results,
            summary: self.generate_test_summary(&results),
        };
        
        // Store waveform traces for post-mortem analysis
        self.store_waveform_traces(&test_result).await?;
        
        // Update metrics
        self.metrics.record_test_completion(&test_result).await?;
        
        Ok(test_result)
    }

    /// Run a single Monte Carlo simulation
    async fn run_single_simulation(
        &self,
        simulator: &dyn Simulator,
        feeder_model: &FeederModel,
        load_profile: &LoadProfile,
        agent: &MLAgent,
        monitor: &MonitorHandle,
        run_id: usize,
    ) -> Result<SimulationResult, GridInLoopError> {
        let start_time = SystemTime::now();
        
        // Initialize simulation
        let mut simulation = simulator.initialize_simulation(feeder_model).await?;
        
        // Inject load profile
        simulation.inject_load_profile(load_profile).await?;
        
        // Start monitoring
        monitor.start_run(run_id).await?;
        
        // Run simulation with ML agent
        let simulation_result = simulation.run_with_agent(agent).await?;
        
        // Validate STL invariants
        let stl_validation = self.validator.validate_invariants(
            &simulation_result.waveform_data,
            &self.config.stl_specs,
        ).await?;
        
        // Stop monitoring
        monitor.stop_run(run_id).await?;
        
        let simulation_time = start_time.elapsed()?.as_millis() as u64;
        
        Ok(SimulationResult {
            run_id,
            simulation_time_ms: simulation_time,
            stl_invariants_valid: stl_validation.all_valid,
            violations: stl_validation.violations,
            critical_violations: stl_validation.critical_violations,
            waveform_data: simulation_result.waveform_data,
            agent_actions: simulation_result.agent_actions,
            performance_metrics: simulation_result.performance_metrics,
        })
    }

    /// Initialize simulator based on type
    async fn initialize_simulator(
        &self,
        simulator_type: &SimulatorType,
    ) -> Result<Box<dyn Simulator>, GridInLoopError> {
        match simulator_type {
            SimulatorType::GridLABD => Ok(Box::new(self.gridlabd.clone())),
            SimulatorType::OpenDSS => Ok(Box::new(self.opendss.clone())),
            SimulatorType::PowerFactory => Ok(Box::new(self.powerfactory.clone())),
        }
    }

    /// Load feeder model
    async fn load_feeder_model(
        &self,
        simulator: &dyn Simulator,
        model_path: &str,
    ) -> Result<FeederModel, GridInLoopError> {
        simulator.load_model(model_path).await
    }

    /// Store waveform traces for post-mortem analysis
    async fn store_waveform_traces(
        &self,
        test_result: &GridInLoopTestResult,
    ) -> Result<(), GridInLoopError> {
        for result in &test_result.results {
            let trace_data = WaveformTrace {
                test_id: test_result.test_id.clone(),
                run_id: result.run_id,
                timestamp: SystemTime::now(),
                waveform_data: result.waveform_data.clone(),
                violations: result.violations.clone(),
            };
            
            self.metrics.store_waveform_trace(&trace_data).await?;
        }
        
        Ok(())
    }

    /// Generate test summary
    fn generate_test_summary(&self, results: &[SimulationResult]) -> TestSummary {
        let total_runs = results.len();
        let successful_runs = results.iter().filter(|r| r.stl_invariants_valid).count();
        let failed_runs = total_runs - successful_runs;
        let total_violations: usize = results.iter().map(|r| r.violations.len()).sum();
        let critical_violations: usize = results.iter().map(|r| r.critical_violations).sum();
        
        let average_simulation_time = results.iter()
            .map(|r| r.simulation_time_ms)
            .sum::<u64>() / total_runs as u64;
        
        TestSummary {
            total_runs,
            successful_runs,
            failed_runs,
            success_rate: successful_runs as f64 / total_runs as f64,
            total_violations,
            critical_violations,
            average_simulation_time_ms: average_simulation_time,
        }
    }

    /// Get test statistics
    pub async fn get_test_stats(&self) -> Result<TestStats, GridInLoopError> {
        self.metrics.get_test_stats().await
    }

    /// Validate configuration
    pub fn validate_config(&self) -> Result<(), GridInLoopError> {
        self.config.validate()
    }
}

impl Default for GridInLoopTester {
    fn default() -> Self {
        Self::new().expect("Failed to create default grid-in-loop tester")
    }
}

/// Grid-in-loop test request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GridInLoopTestRequest {
    pub simulator_type: SimulatorType,
    pub feeder_model_path: String,
    pub load_config: LoadConfig,
    pub agent_config: AgentConfig,
    pub stl_specs: Vec<STLSpecification>,
    pub num_monte_carlo_runs: usize,
    pub max_violations_before_termination: usize,
}

/// Simulator type
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SimulatorType {
    GridLABD,
    OpenDSS,
    PowerFactory,
}

/// Load configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoadConfig {
    pub load_types: Vec<LoadType>,
    pub time_series_length: Duration,
    pub stochastic_parameters: StochasticParameters,
    pub correlation_matrix: Option<Vec<Vec<f64>>>,
}

/// Load type
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LoadType {
    Residential,
    Commercial,
    Industrial,
    ElectricVehicle,
    Renewable,
}

/// Stochastic parameters
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StochasticParameters {
    pub mean_load: f64,
    pub standard_deviation: f64,
    pub skewness: f64,
    pub kurtosis: f64,
    pub seasonality: SeasonalityConfig,
}

/// Seasonality configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SeasonalityConfig {
    pub daily_pattern: Vec<f64>,
    pub weekly_pattern: Vec<f64>,
    pub monthly_pattern: Vec<f64>,
    pub holiday_effects: HashMap<String, f64>,
}

/// Agent configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AgentConfig {
    pub model_path: String,
    pub model_type: ModelType,
    pub inference_config: InferenceConfig,
    pub safety_constraints: Vec<SafetyConstraint>,
}

/// Model type
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModelType {
    ONNX,
    TensorRT,
    PyTorch,
    TensorFlow,
}

/// Inference configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InferenceConfig {
    pub batch_size: usize,
    pub timeout_ms: u64,
    pub max_memory_mb: u64,
    pub enable_optimization: bool,
}

/// Safety constraint
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SafetyConstraint {
    pub name: String,
    pub constraint_type: ConstraintType,
    pub parameters: HashMap<String, f64>,
}

/// Constraint type
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ConstraintType {
    VoltageLimit,
    CurrentLimit,
    FrequencyLimit,
    PowerLimit,
    TemperatureLimit,
}

/// Grid-in-loop test result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GridInLoopTestResult {
    pub test_id: String,
    pub total_runs: usize,
    pub successful_runs: usize,
    pub failed_runs: usize,
    pub critical_violations: usize,
    pub average_simulation_time_ms: u64,
    pub test_duration_seconds: u64,
    pub results: Vec<SimulationResult>,
    pub summary: TestSummary,
}

/// Simulation result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SimulationResult {
    pub run_id: usize,
    pub simulation_time_ms: u64,
    pub stl_invariants_valid: bool,
    pub violations: Vec<Violation>,
    pub critical_violations: usize,
    pub waveform_data: WaveformData,
    pub agent_actions: Vec<AgentAction>,
    pub performance_metrics: PerformanceMetrics,
}

/// Violation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Violation {
    pub timestamp: SystemTime,
    pub violation_type: ViolationType,
    pub severity: ViolationSeverity,
    pub description: String,
    pub stl_formula: String,
    pub actual_value: f64,
    pub expected_value: f64,
}

/// Violation type
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ViolationType {
    VoltageViolation,
    CurrentViolation,
    FrequencyViolation,
    PowerViolation,
    TemperatureViolation,
    STLViolation,
}

/// Violation severity
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ViolationSeverity {
    Low,
    Medium,
    High,
    Critical,
}

/// Waveform data
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WaveformData {
    pub timestamps: Vec<SystemTime>,
    pub voltages: Vec<Vec<f64>>,
    pub currents: Vec<Vec<f64>>,
    pub powers: Vec<Vec<f64>>,
    pub frequencies: Vec<f64>,
}

/// Agent action
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AgentAction {
    pub timestamp: SystemTime,
    pub action_type: ActionType,
    pub parameters: HashMap<String, f64>,
    pub confidence: f64,
}

/// Action type
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ActionType {
    VoltageRegulation,
    LoadShedding,
    GenerationDispatch,
    FrequencyControl,
    EmergencyShutdown,
}

/// Performance metrics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceMetrics {
    pub cpu_usage_percent: f64,
    pub memory_usage_mb: u64,
    pub gpu_usage_percent: Option<f64>,
    pub inference_latency_ms: u64,
    pub decision_time_ms: u64,
}

/// Test summary
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestSummary {
    pub total_runs: usize,
    pub successful_runs: usize,
    pub failed_runs: usize,
    pub success_rate: f64,
    pub total_violations: usize,
    pub critical_violations: usize,
    pub average_simulation_time_ms: u64,
}

/// Test statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestStats {
    pub total_tests: u64,
    pub total_simulations: u64,
    pub total_violations: u64,
    pub average_success_rate: f64,
    pub average_simulation_time_ms: u64,
    pub most_common_violations: Vec<String>,
}

/// Waveform trace
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WaveformTrace {
    pub test_id: String,
    pub run_id: usize,
    pub timestamp: SystemTime,
    pub waveform_data: WaveformData,
    pub violations: Vec<Violation>,
}

/// Trait for simulator implementations
#[async_trait::async_trait]
pub trait Simulator: Send + Sync {
    async fn initialize_simulation(&self, model: &FeederModel) -> Result<Simulation, GridInLoopError>;
    async fn load_model(&self, path: &str) -> Result<FeederModel, GridInLoopError>;
}

/// Feeder model
#[derive(Debug, Clone)]
pub struct FeederModel {
    pub name: String,
    pub buses: Vec<Bus>,
    pub lines: Vec<Line>,
    pub loads: Vec<Load>,
    pub generators: Vec<Generator>,
    pub transformers: Vec<Transformer>,
}

/// Bus
#[derive(Debug, Clone)]
pub struct Bus {
    pub id: String,
    pub voltage_kv: f64,
    pub bus_type: BusType,
}

/// Bus type
#[derive(Debug, Clone)]
pub enum BusType {
    Slack,
    PV,
    PQ,
}

/// Line
#[derive(Debug, Clone)]
pub struct Line {
    pub from_bus: String,
    pub to_bus: String,
    pub resistance: f64,
    pub reactance: f64,
    pub capacity: f64,
}

/// Load
#[derive(Debug, Clone)]
pub struct Load {
    pub bus_id: String,
    pub active_power: f64,
    pub reactive_power: f64,
    pub load_type: LoadType,
}

/// Generator
#[derive(Debug, Clone)]
pub struct Generator {
    pub bus_id: String,
    pub active_power: f64,
    pub reactive_power: f64,
    pub generator_type: GeneratorType,
}

/// Generator type
#[derive(Debug, Clone)]
pub enum GeneratorType {
    Thermal,
    Hydro,
    Wind,
    Solar,
    Battery,
}

/// Transformer
#[derive(Debug, Clone)]
pub struct Transformer {
    pub from_bus: String,
    pub to_bus: String,
    pub primary_voltage: f64,
    pub secondary_voltage: f64,
    pub capacity: f64,
}

/// Simulation
#[derive(Debug, Clone)]
pub struct Simulation {
    pub model: FeederModel,
    pub time_step: Duration,
    pub duration: Duration,
}

impl Simulation {
    pub async fn inject_load_profile(&mut self, profile: &LoadProfile) -> Result<(), GridInLoopError> {
        // Implementation for injecting load profile
        Ok(())
    }
    
    pub async fn run_with_agent(&self, agent: &MLAgent) -> Result<SimulationResult, GridInLoopError> {
        // Implementation for running simulation with ML agent
        Ok(SimulationResult {
            run_id: 0,
            simulation_time_ms: 0,
            stl_invariants_valid: true,
            violations: vec![],
            critical_violations: 0,
            waveform_data: WaveformData {
                timestamps: vec![],
                voltages: vec![],
                currents: vec![],
                powers: vec![],
                frequencies: vec![],
            },
            agent_actions: vec![],
            performance_metrics: PerformanceMetrics {
                cpu_usage_percent: 0.0,
                memory_usage_mb: 0,
                gpu_usage_percent: None,
                inference_latency_ms: 0,
                decision_time_ms: 0,
            },
        })
    }
}

/// Load profile
#[derive(Debug, Clone)]
pub struct LoadProfile {
    pub timestamps: Vec<SystemTime>,
    pub active_powers: Vec<f64>,
    pub reactive_powers: Vec<f64>,
}

/// ML agent
#[derive(Debug, Clone)]
pub struct MLAgent {
    pub model_path: String,
    pub model_type: ModelType,
    pub config: InferenceConfig,
}

/// Monitor handle
#[derive(Debug, Clone)]
pub struct MonitorHandle {
    pub monitor_id: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_grid_in_loop_tester_creation() {
        let tester = GridInLoopTester::new();
        assert!(tester.is_ok());
    }

    #[tokio::test]
    async fn test_test_request_creation() {
        let request = GridInLoopTestRequest {
            simulator_type: SimulatorType::GridLABD,
            feeder_model_path: "test_model.glm".to_string(),
            load_config: LoadConfig {
                load_types: vec![LoadType::Residential],
                time_series_length: Duration::from_secs(3600),
                stochastic_parameters: StochasticParameters {
                    mean_load: 100.0,
                    standard_deviation: 10.0,
                    skewness: 0.0,
                    kurtosis: 3.0,
                    seasonality: SeasonalityConfig {
                        daily_pattern: vec![1.0; 24],
                        weekly_pattern: vec![1.0; 7],
                        monthly_pattern: vec![1.0; 12],
                        holiday_effects: HashMap::new(),
                    },
                },
                correlation_matrix: None,
            },
            agent_config: AgentConfig {
                model_path: "test_model.onnx".to_string(),
                model_type: ModelType::ONNX,
                inference_config: InferenceConfig {
                    batch_size: 1,
                    timeout_ms: 1000,
                    max_memory_mb: 1024,
                    enable_optimization: true,
                },
                safety_constraints: vec![],
            },
            stl_specs: vec![],
            num_monte_carlo_runs: 100,
            max_violations_before_termination: 10,
        };
        
        assert_eq!(request.num_monte_carlo_runs, 100);
    }
} 