//! CertifyEdge CLI — stable runbook commands for PCS v0.1 LabTrust trace certification.
//!
//! Runbook entry points (also searchable in this crate):
//! - `certifyedge check-trace`
//! - `certifyedge emit-pcs-certificate`
//! - `certifyedge verify-certificate`
//! - `certifyedge explain-counterexample`

use std::fs;
use std::path::{Path, PathBuf};

use clap::{Parser, Subcommand};
use labtrust_adapter::{
    check_property, parse_and_validate_json, Counterexample, PropertySpec, TraceView,
};
use pcs_certificate::{
    build_certificate, certificate_to_json, counterexample_from_json, counterexample_to_json,
    explain_counterexample, validate_certificate_artifact, verify_certificate_document,
    CertifyEdgeMetadata,
};

/// Runbook: `certifyedge check-trace`
pub const CMD_CHECK_TRACE: &str = "check-trace";
/// Runbook: `certifyedge emit-pcs-certificate`
pub const CMD_EMIT_PCS_CERTIFICATE: &str = "emit-pcs-certificate";
/// Runbook: `certifyedge verify-certificate`
pub const CMD_VERIFY_CERTIFICATE: &str = "verify-certificate";
/// Runbook: `certifyedge explain-counterexample`
pub const CMD_EXPLAIN_COUNTEREXAMPLE: &str = "explain-counterexample";

#[derive(Parser)]
#[command(
    name = "certifyedge",
    version,
    about = "PCS temporal trace certification (LabTrust v0.1)"
)]
pub struct Cli {
    /// Require real `source_commit` and pcs-core schema validation (CI / release artifacts).
    #[arg(long, global = true, env = "CERTIFYEDGE_RELEASE_MODE")]
    pub release_mode: bool,

    #[command(subcommand)]
    pub command: Commands,
}

#[derive(Subcommand)]
pub enum Commands {
    /// Runbook: `certifyedge check-trace --spec <stl> --trace <trace.json>`
    #[command(name = CMD_CHECK_TRACE, visible_alias = "check_trace")]
    CheckTrace {
        #[arg(long)]
        spec: PathBuf,
        #[arg(long)]
        trace: PathBuf,
        #[arg(long)]
        counterexample_out: Option<PathBuf>,
    },
    /// Runbook: `certifyedge emit-pcs-certificate --spec <stl> --trace <trace.json> --out <cert.json>`
    #[command(name = CMD_EMIT_PCS_CERTIFICATE, visible_alias = "emit_pcs_certificate")]
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
    /// Runbook: `certifyedge verify-certificate <trace_certificate.json>`
    #[command(name = CMD_VERIFY_CERTIFICATE, visible_alias = "verify_certificate")]
    VerifyCertificate {
        certificate: PathBuf,
        #[arg(long)]
        trace: Option<PathBuf>,
    },
    /// Runbook: `certifyedge explain-counterexample <counterexample.json>`
    #[command(name = CMD_EXPLAIN_COUNTEREXAMPLE, visible_alias = "explain_counterexample")]
    ExplainCounterexample {
        counterexample: PathBuf,
    },
}

pub fn run(cli: Cli) -> Result<(), String> {
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
        } => cmd_emit_certificate(cli.release_mode, &spec, &trace, &out, counterexample_out.as_deref()),
        Commands::VerifyCertificate { certificate, trace } => {
            cmd_verify_certificate(&certificate, trace.as_deref())
        }
        Commands::ExplainCounterexample { counterexample } => {
            cmd_explain_counterexample(&counterexample)
        }
    }
}

pub fn load_trace(path: &Path) -> Result<labtrust_adapter::LabTrustTrace, String> {
    let text = fs::read_to_string(path).map_err(|e| e.to_string())?;
    parse_and_validate_json(&text).map_err(|e| e.to_string())
}

pub fn load_spec(path: &Path) -> Result<PropertySpec, String> {
    PropertySpec::load(path)
}

pub fn cmd_check_trace(
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
        eprintln!(
            "FAIL: {} (counterexample -> {})",
            spec.property_id.as_str(),
            out.display()
        );
    } else {
        eprintln!("FAIL: {}", spec.property_id.as_str());
        println!("{}", counterexample_to_json(cx).map_err(|e| e.to_string())?);
    }
    Err("temporal property check failed".into())
}

pub fn cmd_emit_certificate(
    release_mode: bool,
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

    let meta = CertifyEdgeMetadata::resolve(release_mode)?;
    let cx_ref = cx_path.as_ref().map(|p| p.to_string_lossy().to_string());
    let outcome = build_certificate(&trace_hash, &spec, &check, &meta, cx_ref);

    if outcome.certificate.trace_hash != trace_hash {
        return Err(format!(
            "internal error: certificate trace_hash {} != trace {}",
            outcome.certificate.trace_hash, trace_hash
        ));
    }

    let cert_json = certificate_to_json(&outcome.certificate).map_err(|e| e.to_string())?;
    if let Some(parent) = out_path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent).map_err(|e| e.to_string())?;
        }
    }
    fs::write(out_path, cert_json).map_err(|e| e.to_string())?;

    validate_certificate_artifact(out_path, release_mode)?;

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

pub fn cmd_verify_certificate(cert_path: &Path, trace_path: Option<&Path>) -> Result<(), String> {
    let cert_text = fs::read_to_string(cert_path).map_err(|e| e.to_string())?;
    let expected_trace_hash = if let Some(trace_path) = trace_path {
        let trace = load_trace(trace_path)?;
        Some(trace.trace_hash)
    } else {
        None
    };

    let cert = verify_certificate_document(&cert_text, expected_trace_hash.as_deref())
        .map_err(|e| e.to_string())?;

    println!(
        "valid TraceCertificate.v0: {} status={}",
        cert.certificate_id, cert.status
    );
    Ok(())
}

pub fn cmd_explain_counterexample(path: &Path) -> Result<(), String> {
    let text = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let cx: Counterexample = counterexample_from_json(&text).map_err(|e| e.to_string())?;
    println!("{}", explain_counterexample(&cx));
    Ok(())
}

pub fn write_counterexample(path: &Path, cx: &Counterexample) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent).map_err(|e| e.to_string())?;
        }
    }
    let json = counterexample_to_json(cx).map_err(|e| e.to_string())?;
    fs::write(path, json).map_err(|e| e.to_string())
}
