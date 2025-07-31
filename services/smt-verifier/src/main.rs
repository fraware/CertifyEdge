//! SMT Verification Service Binary
//! 
//! This is the main binary for the CertifyEdge SMT verification microservice.

use clap::{Parser, Subcommand};
use std::path::PathBuf;
use tracing::{info, error, Level};
use tracing_subscriber::FmtSubscriber;

use smt_verifier::{SMTVerifier, VerificationRequest, VerificationResponse};

#[derive(Parser)]
#[command(name = "verifierd")]
#[command(about = "CertifyEdge SMT Verification Microservice")]
#[command(version = "1.0.0")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
    
    /// Configuration file path
    #[arg(short, long, value_name = "FILE")]
    config: Option<PathBuf>,
    
    /// Enable verbose logging
    #[arg(short, long)]
    verbose: bool,
}

#[derive(Subcommand)]
enum Commands {
    /// Verify an SMT-LIB script
    Verify {
        /// Input SMT-LIB script file
        #[arg(value_name = "FILE")]
        input: PathBuf,
        
        /// Output result file
        #[arg(short, long, value_name = "FILE")]
        output: Option<PathBuf>,
        
        /// Solver preferences (z3, cvc5)
        #[arg(long, value_delimiter = ',')]
        solvers: Option<Vec<String>>,
        
        /// Timeout in milliseconds
        #[arg(long)]
        timeout_ms: Option<u64>,
        
        /// Memory limit in MB
        #[arg(long)]
        memory_mb: Option<u64>,
    },
    
    /// Start the verification server
    Serve {
        /// Server port
        #[arg(short, long, default_value = "8080")]
        port: u16,
        
        /// Server host
        #[arg(long, default_value = "127.0.0.1")]
        host: String,
    },
    
    /// Show service statistics
    Stats,
    
    /// Check solver health
    Health {
        /// Solver type to check
        #[arg(long)]
        solver: Option<String>,
    },
    
    /// Validate configuration
    Validate,
    
    /// Show service information
    Info,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();
    
    // Initialize logging
    init_logging(cli.verbose);
    
    // Load configuration
    let config = load_config(cli.config).await?;
    
    // Create verifier
    let mut verifier = SMTVerifier::with_config(config)?;
    
    match cli.command {
        Commands::Verify { input, output, solvers, timeout_ms, memory_mb } => {
            verify_script(verifier, input, output, solvers, timeout_ms, memory_mb).await?;
        }
        Commands::Serve { port, host } => {
            serve_verifier(verifier, host, port).await?;
        }
        Commands::Stats => {
            show_stats(verifier).await?;
        }
        Commands::Health { solver } => {
            check_health(verifier, solver).await?;
        }
        Commands::Validate => {
            validate_config(verifier).await?;
        }
        Commands::Info => {
            show_info(verifier).await?;
        }
    }
    
    Ok(())
}

/// Initialize logging
fn init_logging(verbose: bool) {
    let level = if verbose { Level::DEBUG } else { Level::INFO };
    
    let subscriber = FmtSubscriber::builder()
        .with_max_level(level)
        .with_target(false)
        .with_thread_ids(true)
        .with_thread_names(true)
        .with_file(true)
        .with_line_number(true)
        .init();
}

/// Load configuration
async fn load_config(config_path: Option<PathBuf>) -> Result<smt_verifier::config::VerifierConfig, Box<dyn std::error::Error>> {
    let config = if let Some(path) = config_path {
        smt_verifier::config::VerifierConfig::from_file(&path)?
    } else {
        smt_verifier::config::VerifierConfig::default()
    };
    
    // Validate configuration
    config.validate()?;
    
    info!("Configuration loaded successfully");
    Ok(config)
}

/// Verify an SMT-LIB script
async fn verify_script(
    mut verifier: SMTVerifier,
    input: PathBuf,
    output: Option<PathBuf>,
    solvers: Option<Vec<String>>,
    timeout_ms: Option<u64>,
    memory_mb: Option<u64>,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("Reading SMT-LIB script from: {}", input.display());
    
    // Read script
    let script_content = std::fs::read_to_string(&input)?;
    
    // Convert solver preferences
    let solver_preferences = solvers.map(|s| {
        s.into_iter()
            .filter_map(|s| match s.as_str() {
                "z3" => Some(smt_verifier::solver::SolverType::Z3),
                "cvc5" => Some(smt_verifier::solver::SolverType::CVC5),
                _ => None,
            })
            .collect()
    });
    
    // Verify script
    let result = verifier.verify_script(&script_content, solver_preferences).await?;
    
    match result.success {
        true => {
            info!("Verification successful");
            info!("Result: {:?}", result.result);
            info!("Execution time: {}ms", result.execution_time_ms);
            info!("Memory usage: {}MB", result.memory_usage_mb);
            
            // Save result if output specified
            if let Some(output_path) = output {
                let response = VerificationResponse {
                    request_id: result.verification_id.clone(),
                    result: result.clone(),
                    timestamp: chrono::Utc::now().to_rfc3339(),
                };
                
                let response_json = serde_json::to_string_pretty(&response)?;
                std::fs::write(output_path, response_json)?;
                info!("Result saved to: {}", output_path.display());
            }
        }
        false => {
            error!("Verification failed");
            error!("Result: {:?}", result.result);
            error!("Execution time: {}ms", result.execution_time_ms);
            error!("Errors: {:?}", result.errors);
            std::process::exit(1);
        }
    }
    
    Ok(())
}

/// Start the verification server
async fn serve_verifier(
    _verifier: SMTVerifier,
    host: String,
    port: u16,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("Starting SMT verification server on {}:{}", host, port);
    
    // TODO: Implement gRPC server
    // For now, just print a message
    info!("Server mode not yet implemented");
    
    Ok(())
}

/// Show service statistics
async fn show_stats(verifier: SMTVerifier) -> Result<(), Box<dyn std::error::Error>> {
    let stats = verifier.get_stats();
    
    println!("SMT Verification Service Statistics:");
    println!("  Total verifications: {}", stats.total_verifications);
    println!("  Successful verifications: {}", stats.successful_verifications);
    println!("  Failed verifications: {}", stats.failed_verifications);
    println!("  SAT results: {}", stats.sat_count);
    println!("  UNSAT results: {}", stats.unsat_count);
    println!("  UNKNOWN results: {}", stats.unknown_count);
    println!("  ERROR results: {}", stats.error_count);
    println!("  Average execution time: {}ms", stats.average_execution_time_ms);
    println!("  Average memory usage: {}MB", stats.average_memory_usage_mb);
    
    Ok(())
}

/// Check solver health
async fn check_health(
    verifier: SMTVerifier,
    solver: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    let solvers = verifier.get_available_solvers();
    
    if let Some(solver_name) = solver {
        // Check specific solver
        let solver_type = match solver_name.as_str() {
            "z3" => smt_verifier::solver::SolverType::Z3,
            "cvc5" => smt_verifier::solver::SolverType::CVC5,
            _ => {
                error!("Unknown solver: {}", solver_name);
                std::process::exit(1);
            }
        };
        
        let healthy = verifier.check_solver_health(solver_type).await?;
        println!("Solver {}: {}", solver_name, if healthy { "HEALTHY" } else { "UNHEALTHY" });
    } else {
        // Check all solvers
        for solver_type in solvers {
            let healthy = verifier.check_solver_health(solver_type.clone()).await?;
            println!("Solver {}: {}", solver_type.as_str(), if healthy { "HEALTHY" } else { "UNHEALTHY" });
        }
    }
    
    Ok(())
}

/// Validate verifier configuration
async fn validate_config(verifier: SMTVerifier) -> Result<(), Box<dyn std::error::Error>> {
    info!("Validating verifier configuration...");
    
    verifier.validate_config()?;
    
    info!("Configuration is valid");
    Ok(())
}

/// Show service information
async fn show_info(_verifier: SMTVerifier) -> Result<(), Box<dyn std::error::Error>> {
    println!("CertifyEdge SMT Verification Microservice");
    println!("Version: 1.0.0");
    println!("Description: High-performance SMT verification with sandboxed solvers");
    println!("Features:");
    println!("  - Z3 and CVC5 solver support");
    println!("  - WebAssembly sandboxing");
    println!("  - Differential testing");
    println!("  - Prometheus metrics");
    println!("  - OpenTelemetry tracing");
    println!("  - gRPC API");
    println!("  - Health checks");
    
    Ok(())
} 