//! Lean 4 Autoprover Binary
//! 
//! This is the main binary for the CertifyEdge Lean 4 autoprover plugin.

use clap::{Parser, Subcommand};
use std::path::PathBuf;
use tracing::{info, error, Level};
use tracing_subscriber::FmtSubscriber;

use lean_autoprover::{LeanAutoprover, AutoproverResult};

#[derive(Parser)]
#[command(name = "lean-autoprover")]
#[command(about = "CertifyEdge Lean 4 Autoprover Plugin")]
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
    /// Prove an STL specification
    Prove {
        /// Input STL specification file
        #[arg(value_name = "FILE")]
        input: PathBuf,
        
        /// Output certificate file
        #[arg(short, long, value_name = "FILE")]
        output: Option<PathBuf>,
        
        /// AST hash for caching
        #[arg(long, value_name = "HASH")]
        ast_hash: Option<String>,
    },
    
    /// Start the autoprover server
    Serve {
        /// Server port
        #[arg(short, long, default_value = "8080")]
        port: u16,
        
        /// Server host
        #[arg(long, default_value = "127.0.0.1")]
        host: String,
    },
    
    /// Show autoprover statistics
    Stats,
    
    /// Validate configuration
    Validate,
    
    /// Show autoprover information
    Info,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();
    
    // Initialize logging
    init_logging(cli.verbose);
    
    // Load configuration
    let config = load_config(cli.config).await?;
    
    // Create autoprover
    let mut autoprover = LeanAutoprover::with_config(config)?;
    
    match cli.command {
        Commands::Prove { input, output, ast_hash } => {
            prove_specification(autoprover, input, output, ast_hash).await?;
        }
        Commands::Serve { port, host } => {
            serve_autoprover(autoprover, host, port).await?;
        }
        Commands::Stats => {
            show_stats(autoprover).await?;
        }
        Commands::Validate => {
            validate_config(autoprover).await?;
        }
        Commands::Info => {
            show_info(autoprover).await?;
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
async fn load_config(config_path: Option<PathBuf>) -> Result<lean_autoprover::config::AutoproverConfig, Box<dyn std::error::Error>> {
    let config = if let Some(path) = config_path {
        lean_autoprover::config::AutoproverConfig::from_file(&path)?
    } else {
        lean_autoprover::config::AutoproverConfig::default()
    };
    
    // Validate configuration
    config.validate()?;
    
    info!("Configuration loaded successfully");
    Ok(config)
}

/// Prove an STL specification
async fn prove_specification(
    mut autoprover: LeanAutoprover,
    input: PathBuf,
    output: Option<PathBuf>,
    ast_hash: Option<String>,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("Reading STL specification from: {}", input.display());
    
    // Read specification
    let spec_content = std::fs::read_to_string(&input)?;
    
    // Generate AST hash if not provided
    let ast_hash = ast_hash.unwrap_or_else(|| {
        use sha2::{Sha256, Digest};
        let mut hasher = Sha256::new();
        hasher.update(spec_content.as_bytes());
        format!("{:x}", hasher.finalize())
    });
    
    info!("AST hash: {}", ast_hash);
    
    // Attempt to prove the specification
    let result = autoprover.autoprove(&spec_content, &ast_hash).await?;
    
    match result.certificate {
        Some(certificate) => {
            info!("Proof successful using tactic: {}", result.tactic_used);
            info!("Proof time: {}ms", result.proof_time_ms);
            
            // Save certificate if output specified
            if let Some(output_path) = output {
                let cert_json = certificate.to_json()?;
                std::fs::write(output_path, cert_json)?;
                info!("Certificate saved to: {}", output_path.display());
            }
            
            // Print certificate fingerprint
            info!("Certificate fingerprint: {}", certificate.fingerprint());
        }
        None => {
            error!("Proof failed");
            error!("Tactic used: {}", result.tactic_used);
            error!("Proof time: {}ms", result.proof_time_ms);
            std::process::exit(1);
        }
    }
    
    Ok(())
}

/// Start the autoprover server
async fn serve_autoprover(
    _autoprover: LeanAutoprover,
    host: String,
    port: u16,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("Starting autoprover server on {}:{}", host, port);
    
    // TODO: Implement gRPC server
    // For now, just print a message
    info!("Server mode not yet implemented");
    
    Ok(())
}

/// Show autoprover statistics
async fn show_stats(autoprover: LeanAutoprover) -> Result<(), Box<dyn std::error::Error>> {
    let stats = autoprover.get_stats().await?;
    
    println!("Autoprover Statistics:");
    println!("  Total proofs: {}", stats.total_proofs);
    println!("  Successful proofs: {}", stats.successful_proofs);
    println!("  Cache hit rate: {:.2}%", stats.cache_hit_rate * 100.0);
    println!("  Average proof time: {}ms", stats.average_proof_time_ms);
    println!("  Most used tactic: {}", stats.most_used_tactic);
    
    Ok(())
}

/// Validate autoprover configuration
async fn validate_config(autoprover: LeanAutoprover) -> Result<(), Box<dyn std::error::Error>> {
    info!("Validating autoprover configuration...");
    
    autoprover.validate_config()?;
    
    info!("Configuration is valid");
    Ok(())
}

/// Show autoprover information
async fn show_info(_autoprover: LeanAutoprover) -> Result<(), Box<dyn std::error::Error>> {
    println!("CertifyEdge Lean 4 Autoprover Plugin");
    println!("Version: 1.0.0");
    println!("Description: Automatic proof generation for STL specifications");
    println!("Features:");
    println!("  - Lean 4 integration");
    println!("  - Proof caching");
    println!("  - Multiple tactics (simp, linarith, aesop, etc.)");
    println!("  - Certificate generation");
    println!("  - Performance monitoring");
    
    Ok(())
} 