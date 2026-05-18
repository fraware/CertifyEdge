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
    build_certificate, build_certificate_to_bundle_handoff, certificate_to_json,
    counterexample_from_json, counterexample_to_json, explain_counterexample,
    finalize_handoff_digest, load_handoff_manifest, plan_emit_from_handoff,
    registry_check_artifact, summary_to_json, validate_certificate_artifact,
    validate_handoff_artifact, verify_certificate_document, write_handoff_manifest,
    CertificateEmitSummary, CertifyEdgeMetadata,
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
        spec: Option<PathBuf>,
        #[arg(long)]
        trace: Option<PathBuf>,
        #[arg(long)]
        out: Option<PathBuf>,
        /// PCS `HandoffManifest.v0` input (`runtime_to_certificate` from LabTrust-Gym).
        #[arg(long)]
        handoff: Option<PathBuf>,
        #[arg(long)]
        counterexample_out: Option<PathBuf>,
        /// Write certificate identity summary JSON for PCS release-run handoff.
        #[arg(long)]
        summary_out: Option<PathBuf>,
        /// Write outbound `HandoffManifest.v0` after certificate emission.
        #[arg(long)]
        handoff_out: Option<PathBuf>,
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
    ExplainCounterexample { counterexample: PathBuf },
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
            handoff,
            counterexample_out,
            summary_out,
            handoff_out,
        } => cmd_emit_certificate(EmitCertificateOptions {
            release_mode: cli.release_mode,
            handoff_path: handoff.as_deref(),
            spec_path: spec.as_deref(),
            trace_path: trace.as_deref(),
            out_path: out.as_deref(),
            counterexample_out: counterexample_out.as_deref(),
            summary_out: summary_out.as_deref(),
            handoff_out: handoff_out.as_deref(),
        }),
        Commands::VerifyCertificate { certificate, trace } => {
            cmd_verify_certificate(cli.release_mode, &certificate, trace.as_deref())
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

fn certifyedge_root() -> PathBuf {
    std::env::var("CERTIFYEDGE_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|_| std::env::current_dir().unwrap_or_else(|_| PathBuf::from(".")))
}

pub struct EmitCertificateOptions<'a> {
    pub release_mode: bool,
    pub handoff_path: Option<&'a Path>,
    pub spec_path: Option<&'a Path>,
    pub trace_path: Option<&'a Path>,
    pub out_path: Option<&'a Path>,
    pub counterexample_out: Option<&'a Path>,
    pub summary_out: Option<&'a Path>,
    pub handoff_out: Option<&'a Path>,
}

pub fn cmd_emit_certificate(opts: EmitCertificateOptions<'_>) -> Result<(), String> {
    let root = certifyedge_root();
    let (spec_path, trace_path, out_path) = if let Some(handoff_path) = opts.handoff_path {
        if opts.release_mode {
            validate_handoff_artifact(handoff_path, true)?;
        }
        let handoff = load_handoff_manifest(handoff_path)?;
        let plan = plan_emit_from_handoff(
            handoff_path,
            &handoff,
            &root,
            opts.spec_path,
            opts.trace_path,
            opts.out_path,
            opts.release_mode,
        )?;
        (plan.spec_path, plan.trace_path, plan.out_path)
    } else {
        let spec = opts.spec_path.ok_or_else(|| {
            "emit-pcs-certificate requires --spec and --trace, or --handoff".to_string()
        })?;
        let trace = opts.trace_path.ok_or_else(|| {
            "emit-pcs-certificate requires --spec and --trace, or --handoff".to_string()
        })?;
        let out = opts.out_path.ok_or_else(|| {
            "emit-pcs-certificate requires --out (or --handoff with expected_outputs)".to_string()
        })?;
        (spec.to_path_buf(), trace.to_path_buf(), out.to_path_buf())
    };

    let spec = load_spec(&spec_path)?;
    let trace = load_trace(&trace_path)?;
    let trace_hash = trace.trace_hash.clone();
    let view = TraceView::from(trace);
    let check = check_property(&view, &spec);

    let cx_path = if !check.passed {
        let path = opts
            .counterexample_out
            .map(PathBuf::from)
            .unwrap_or_else(|| out_path.with_file_name("counterexample.json"));
        if let Some(cx) = &check.counterexample {
            write_counterexample(&path, cx)?;
        }
        Some(path)
    } else {
        None
    };

    let meta = CertifyEdgeMetadata::resolve(opts.release_mode)?;
    println!(
        "source_commit_resolution={}",
        meta.source_commit_resolution.as_str()
    );
    let cx_ref = cx_path.as_ref().map(|p| p.to_string_lossy().to_string());
    let outcome = build_certificate(&trace_hash, &spec, &check, &meta, cx_ref)?;

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
    fs::write(&out_path, cert_json).map_err(|e| e.to_string())?;

    validate_certificate_artifact(&out_path, opts.release_mode)?;
    registry_check_artifact(&out_path, opts.release_mode)?;

    let summary = CertificateEmitSummary::from_certificate(&outcome.certificate);
    let summary_json = summary_to_json(&summary).map_err(|e| e.to_string())?;
    if let Some(path) = opts.summary_out {
        if let Some(parent) = path.parent() {
            if !parent.as_os_str().is_empty() {
                fs::create_dir_all(parent).map_err(|e| e.to_string())?;
            }
        }
        fs::write(path, format!("{summary_json}\n")).map_err(|e| e.to_string())?;
    }
    println!("{summary_json}");

    if let Some(path) = opts.handoff_out {
        let mut outbound = build_certificate_to_bundle_handoff(&outcome.certificate, &out_path)?;
        finalize_handoff_digest(&mut outbound);
        write_handoff_manifest(path, &outbound)?;
        validate_handoff_artifact(path, opts.release_mode)?;
        println!("handoff_out={}", path.display());
    }

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

pub fn cmd_verify_certificate(
    release_mode: bool,
    cert_path: &Path,
    trace_path: Option<&Path>,
) -> Result<(), String> {
    let cert_text = fs::read_to_string(cert_path).map_err(|e| e.to_string())?;
    let expected_trace_hash = if let Some(trace_path) = trace_path {
        let trace = load_trace(trace_path)?;
        Some(trace.trace_hash)
    } else {
        None
    };

    let cert =
        verify_certificate_document(&cert_text, expected_trace_hash.as_deref(), release_mode)
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
