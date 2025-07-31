//! STL Compiler - Main binary

use clap::{Parser, Subcommand};
use stl_compiler::{Compiler, CompilerConfig};
use std::path::PathBuf;
use tracing::{info, error, warn};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

#[derive(Parser)]
#[command(name = "stl-compiler")]
#[command(about = "STL to Lean 4 compiler for CertifyEdge platform")]
#[command(version = "0.1.0")]
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
    /// Compile STL specification to Lean 4 and SMT-LIB
    Compile {
        /// Input STL specification file
        #[arg(value_name = "FILE")]
        input: PathBuf,
        
        /// Output directory
        #[arg(short, long, value_name = "DIR")]
        output: Option<PathBuf>,
        
        /// Generate Lean 4 output
        #[arg(long)]
        lean4: bool,
        
        /// Generate SMT-LIB output
        #[arg(long)]
        smt: bool,
    },
    
    /// Start the STL compiler server
    Serve {
        /// Server port
        #[arg(short, long, default_value = "8080")]
        port: u16,
        
        /// Server host
        #[arg(long, default_value = "127.0.0.1")]
        host: String,
    },
    
    /// Validate STL specification
    Validate {
        /// Input STL specification file
        #[arg(value_name = "FILE")]
        input: PathBuf,
    },
    
    /// Show compiler information
    Info,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();
    
    // Initialize logging
    init_logging(cli.verbose);
    
    // Load configuration
    let config = load_config(cli.config)?;
    
    // Create compiler
    let compiler = Compiler::new(config);
    
    match cli.command {
        Commands::Compile { input, output, lean4, smt } => {
            compile_specification(compiler, input, output, lean4, smt).await?;
        }
        Commands::Serve { port, host } => {
            serve_compiler(compiler, host, port).await?;
        }
        Commands::Validate { input } => {
            validate_specification(compiler, input).await?;
        }
        Commands::Info => {
            show_info(compiler);
        }
    }
    
    Ok(())
}

/// Initialize logging
fn init_logging(verbose: bool) {
    let level = if verbose {
        tracing::Level::DEBUG
    } else {
        tracing::Level::INFO
    };
    
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new(
            std::env::var("RUST_LOG").unwrap_or_else(|_| format!("stl_compiler={}", level))
        ))
        .with(tracing_subscriber::fmt::layer())
        .init();
}

/// Load configuration
fn load_config(config_path: Option<PathBuf>) -> Result<CompilerConfig, Box<dyn std::error::Error>> {
    match config_path {
        Some(path) => {
            info!("Loading configuration from: {:?}", path);
            CompilerConfig::from_file(&path).map_err(|e| e.into())
        }
        None => {
            info!("Using default configuration");
            Ok(CompilerConfig::default())
        }
    }
}

/// Compile STL specification
async fn compile_specification(
    compiler: Compiler,
    input: PathBuf,
    output: Option<PathBuf>,
    lean4: bool,
    smt: bool,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("Compiling STL specification: {:?}", input);
    
    // Read input file
    let spec_text = std::fs::read_to_string(&input)?;
    
    // Compile specification
    let result = compiler.compile(&spec_text).await?;
    
    // Determine output directory
    let output_dir = output.unwrap_or_else(|| {
        input.with_file_name(input.file_stem().unwrap()).with_extension("output")
    });
    
    // Create output directory
    std::fs::create_dir_all(&output_dir)?;
    
    // Write Lean 4 output
    if lean4 || !smt {
        let lean4_path = output_dir.join("spec.lean");
        std::fs::write(&lean4_path, &result.lean4_output.lean4_code)?;
        info!("Lean 4 output written to: {:?}", lean4_path);
        
        let proof_path = output_dir.join("proof.lean");
        std::fs::write(&proof_path, &result.lean4_output.proof_skeleton)?;
        info!("Proof skeleton written to: {:?}", proof_path);
    }
    
    // Write SMT-LIB output
    if smt || !lean4 {
        let smt_path = output_dir.join("spec.smt2");
        std::fs::write(&smt_path, &result.smt_output.smt_lib_code)?;
        info!("SMT-LIB output written to: {:?}", smt_path);
    }
    
    // Write compilation report
    let report_path = output_dir.join("compilation_report.json");
    let report_json = serde_json::to_string_pretty(&result)?;
    std::fs::write(&report_path, report_json)?;
    info!("Compilation report written to: {:?}", report_path);
    
    // Print summary
    println!("Compilation completed successfully!");
    println!("Total time: {}ms", result.stats.total_time_ms);
    println!("Parse time: {}ms", result.stats.parse_time_ms);
    println!("Lean 4 time: {}ms", result.stats.lean4_time_ms);
    println!("SMT time: {}ms", result.stats.smt_time_ms);
    println!("Validation: {}", if result.validation.all_valid { "PASSED" } else { "FAILED" });
    
    if !result.validation.all_valid {
        for error in &result.validation.errors {
            error!("Validation error: {}", error);
        }
        std::process::exit(1);
    }
    
    Ok(())
}

/// Start compiler server
async fn serve_compiler(
    compiler: Compiler,
    host: String,
    port: u16,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("Starting STL compiler server on {}:{}", host, port);
    
    // For now, just print that the server would start
    // In practice, this would start an Axum server with gRPC endpoints
    println!("STL Compiler Server");
    println!("Host: {}", host);
    println!("Port: {}", port);
    println!("Status: Not implemented yet");
    
    // TODO: Implement Axum server with gRPC endpoints
    // let app = Router::new()
    //     .route("/compile", post(compile_handler))
    //     .route("/validate", post(validate_handler))
    //     .route("/health", get(health_handler));
    // 
    // let addr = format!("{}:{}", host, port).parse()?;
    // axum::Server::bind(&addr)
    //     .serve(app.into_make_service())
    //     .await?;
    
    Ok(())
}

/// Validate STL specification
async fn validate_specification(
    compiler: Compiler,
    input: PathBuf,
) -> Result<(), Box<dyn std::error::Error>> {
    info!("Validating STL specification: {:?}", input);
    
    // Read input file
    let spec_text = std::fs::read_to_string(&input)?;
    
    // Parse specification
    let spec = compiler.parse_specification(&spec_text)?;
    
    // Validate round-trip
    let roundtrip_valid = compiler.validate_roundtrip(&spec);
    
    // Print validation results
    println!("STL Specification Validation");
    println!("File: {:?}", input);
    println!("Name: {}", spec.name);
    println!("Description: {}", spec.description.as_deref().unwrap_or("None"));
    println!("Formula: {:?}", spec.formula);
    println!("Variables: {:?}", spec.formula.variables());
    println!("Temporal depth: {}", spec.formula.temporal_depth());
    println!("Parameters: {}", spec.parameters.len());
    println!("Constraints: {}", spec.constraints.len());
    println!("Round-trip validation: {}", if roundtrip_valid { "PASSED" } else { "FAILED" });
    
    if !roundtrip_valid {
        error!("Round-trip validation failed");
        std::process::exit(1);
    }
    
    println!("Validation completed successfully!");
    
    Ok(())
}

/// Show compiler information
fn show_info(compiler: Compiler) {
    println!("STL Compiler Information");
    println!("Version: 0.1.0");
    println!("Description: STL to Lean 4 compiler for CertifyEdge platform");
    println!();
    
    println!("Supported Features:");
    for feature in compiler.get_supported_features() {
        println!("  - {}", feature);
    }
    println!();
    
    println!("Configuration:");
    let config = compiler.config;
    println!("  Lean 4 version: {}", config.lean4.version);
    println!("  Z3 version: {}", config.smt.z3.version);
    println!("  CVC5 version: {}", config.smt.cvc5.version);
    println!("  Default solver: {}", config.smt.default_solver);
    println!("  Parallel compilation: {}", config.performance.parallel);
    println!("  Number of threads: {}", config.performance.num_threads);
    println!();
    
    println!("Usage:");
    println!("  stl-compiler compile <input> [options]  - Compile STL specification");
    println!("  stl-compiler serve [options]            - Start compiler server");
    println!("  stl-compiler validate <input>           - Validate STL specification");
    println!("  stl-compiler info                       - Show compiler information");
} 