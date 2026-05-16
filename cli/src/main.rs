use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use labtrust_adapter::{
    check_property, parse_and_validate_json, Counterexample, PropertySpec,
    TraceView,
};
use pcs_certificate::{
    build_certificate, certificate_to_json, counterexample_from_json,
    counterexample_to_json, explain_counterexample, verify_certificate_document,
    CertifyEdgeMetadata,
};

#[derive(Parser)]
#[command(name = "certifyedge", version, about = "PCS temporal trace certification")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Check a LabTrust trace against an STL temporal property spec.
    CheckTrace {
        #[arg(long)]
        spec: PathBuf,
        #[arg(long)]
        trace: PathBuf,
        #[arg(long)]
        counterexample_out: Option<PathBuf>,
    },
    /// Emit a PCS TraceCertificate.v0 for a trace/spec pair.
    EmitPcsCertificate {
        #[arg(long)]
        spec: PathBuf,
        #[arg(long)]
        trace: PathBuf,
        #[arg(long)]
        out: PathBuf,
        #[arg(long)]
        counterexample_out: Option<PathBuf>,
    },
    /// Verify a TraceCertificate.v0 document (schema + digest).
    VerifyCertificate {
        certificate: PathBuf,
        #[arg(long)]
        trace: Option<PathBuf>,
    },
    /// Print a human-readable explanation of a counterexample JSON file.
    ExplainCounterexample {
        counterexample: PathBuf,
    },
}

fn main() -> ExitCode {
    match run(Cli::parse()) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}

fn run(cli: Cli) -> Result<(), String> {
    match cli.command {
        Commands::CheckTrace {
            spec,
            trace,
            counterexample_out,
        } => cmd_check_trace(&spec, &trace, counterexample_out.as_deref()),
        Commands::EmitPcsCertificate {
            spec,
            trace,
            out,
            counterexample_out,
        } => cmd_emit_certificate(&spec, &trace, &out, counterexample_out.as_deref()),
        Commands::VerifyCertificate { certificate, trace } => {
            cmd_verify_certificate(&certificate, trace.as_deref())
        }
        Commands::ExplainCounterexample { counterexample } => {
            cmd_explain_counterexample(&counterexample)
        }
    }
}

fn load_trace(path: &Path) -> Result<labtrust_adapter::LabTrustTrace, String> {
    let text = fs::read_to_string(path).map_err(|e| e.to_string())?;
    parse_and_validate_json(&text).map_err(|e| e.to_string())
}

fn load_spec(path: &Path) -> Result<PropertySpec, String> {
    PropertySpec::load(path)
}

fn cmd_check_trace(
    spec_path: &Path,
    trace_path: &Path,
    counterexample_out: Option<&Path>,
) -> Result<(), String> {
    let spec = load_spec(spec_path)?;
    let trace = load_trace(trace_path)?;
    let view = TraceView::from(trace);
    let result = check_property(&view, &spec);

    if result.passed {
        println!("PASS: {}", spec.property_id.as_str());
        return Ok(());
    }

    let cx = result
        .counterexample
        .as_ref()
        .ok_or_else(|| "check failed without counterexample".to_string())?;
    if let Some(out) = counterexample_out {
        write_counterexample(out, cx)?;
        eprintln!("FAIL: {} (counterexample -> {})", spec.property_id.as_str(), out.display());
    } else {
        eprintln!("FAIL: {}", spec.property_id.as_str());
        println!("{}", counterexample_to_json(cx).map_err(|e| e.to_string())?);
    }
    Err("temporal property check failed".into())
}

fn cmd_emit_certificate(
    spec_path: &Path,
    trace_path: &Path,
    out_path: &Path,
    counterexample_out: Option<&Path>,
) -> Result<(), String> {
    let spec = load_spec(spec_path)?;
    let trace = load_trace(trace_path)?;
    let trace_hash = trace.trace_hash.clone();
    let view = TraceView::from(trace);
    let check = check_property(&view, &spec);

    let cx_path = if !check.passed {
        let path = counterexample_out
            .map(PathBuf::from)
            .unwrap_or_else(|| out_path.with_file_name("counterexample.json"));
        if let Some(cx) = &check.counterexample {
            write_counterexample(&path, cx)?;
        }
        Some(path)
    } else {
        None
    };

    let cx_ref = cx_path.as_ref().map(|p| p.to_string_lossy().to_string());
    let outcome = build_certificate(
        &trace_hash,
        &spec,
        &check,
        &CertifyEdgeMetadata::default(),
        cx_ref,
    );

    let cert_json = certificate_to_json(&outcome.certificate).map_err(|e| e.to_string())?;
    fs::write(out_path, cert_json).map_err(|e| e.to_string())?;

    if check.passed {
        println!(
            "CertificateChecked -> {} ({})",
            out_path.display(),
            outcome.certificate.certificate_id
        );
    } else {
        println!(
            "Rejected -> {} ({})",
            out_path.display(),
            outcome.certificate.certificate_id
        );
    }

    Ok(())
}

fn cmd_verify_certificate(cert_path: &Path, trace_path: Option<&Path>) -> Result<(), String> {
    let cert_text = fs::read_to_string(cert_path).map_err(|e| e.to_string())?;
    let expected_trace_hash = if let Some(trace_path) = trace_path {
        let trace = load_trace(trace_path)?;
        Some(trace.trace_hash)
    } else {
        None
    };

    let cert = verify_certificate_document(
        &cert_text,
        expected_trace_hash.as_deref(),
    )
    .map_err(|e| e.to_string())?;

    println!(
        "valid TraceCertificate.v0: {} status={}",
        cert.certificate_id, cert.status
    );
    Ok(())
}

fn cmd_explain_counterexample(path: &Path) -> Result<(), String> {
    let text = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let cx: Counterexample = counterexample_from_json(&text).map_err(|e| e.to_string())?;
    println!("{}", explain_counterexample(&cx));
    Ok(())
}

fn write_counterexample(path: &Path, cx: &Counterexample) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent).map_err(|e| e.to_string())?;
        }
    }
    let json = counterexample_to_json(cx).map_err(|e| e.to_string())?;
    fs::write(path, json).map_err(|e| e.to_string())
}
