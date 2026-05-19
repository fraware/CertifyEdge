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
    build_certificate_formal_facts, build_certificate_to_bundle_handoff, counterexample_from_json,
    counterexample_to_json, emit_certificate_for_profile, emit_check_failure_stderr,
    explain_counterexample, finalize_handoff_digest, formal_facts_to_json_pretty,
    load_handoff_manifest, plan_emit_from_handoff, registry_check_artifact,
    repair_temporal_check_failed, repair_tool_use_check_failed, resolve_profile_registry,
    run_certificate_benchmark, summary_to_json, validate_certificate_artifact,
    validate_certificate_benchmark_cases_tree,
    validate_certificate_formal_facts_schema, validate_certificate_json_for_profile,
    validate_formal_facts_consistency, validate_handoff_artifact, validate_release_mode_fields,
    verify_certificate_document, write_handoff_manifest, BenchmarkCertificatesOptions,
    CertificateEmitSummary, CertifyEdgeMetadata, PropertyProfileRegistry,
};
use serde_json::Value;

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
        /// Write `CertificateFormalFacts.v0` Lean-fact source JSON alongside the certificate.
        #[arg(long)]
        formal_facts_out: Option<PathBuf>,
        /// Property profile registry directory (default: `<CERTIFYEDGE_ROOT>/templates/profiles`).
        #[arg(long, value_name = "DIR")]
        profile_registry: Option<PathBuf>,
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
    /// Property profile registry commands (`list`, `explain`, `validate`).
    Profiles {
        #[command(subcommand)]
        command: ProfilesCommands,
    },
    /// Certificate benchmark suites (`benchmark certificates`).
    Benchmark {
        #[command(subcommand)]
        command: BenchmarkCommands,
    },
}

#[derive(Subcommand)]
pub enum BenchmarkCommands {
    /// Run profile-driven certificate benchmark cases.
    Certificates {
        #[arg(long)]
        profile: String,
        #[arg(long)]
        cases: PathBuf,
        #[arg(long)]
        out: PathBuf,
        #[arg(long, value_name = "DIR")]
        profile_registry: Option<PathBuf>,
    },
    /// Validate committed `benchmarks/certificates/**/case.json` files.
    ValidateCases,
}

#[derive(Subcommand)]
pub enum ProfilesCommands {
    /// List registered property profile IDs.
    List {
        #[arg(long, value_name = "DIR")]
        profile_registry: Option<PathBuf>,
    },
    /// Show a property profile document (JSON).
    Explain {
        property_id: String,
        #[arg(long, value_name = "DIR")]
        profile_registry: Option<PathBuf>,
    },
    /// Validate a property profile file against `schema.json`.
    Validate {
        path: PathBuf,
        #[arg(long, value_name = "DIR")]
        profile_registry: Option<PathBuf>,
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
            handoff,
            counterexample_out,
            summary_out,
            handoff_out,
            formal_facts_out,
            profile_registry,
        } => cmd_emit_certificate(EmitCertificateOptions {
            release_mode: cli.release_mode,
            handoff_path: handoff.as_deref(),
            spec_path: spec.as_deref(),
            trace_path: trace.as_deref(),
            out_path: out.as_deref(),
            counterexample_out: counterexample_out.as_deref(),
            summary_out: summary_out.as_deref(),
            handoff_out: handoff_out.as_deref(),
            formal_facts_out: formal_facts_out.as_deref(),
            profile_registry: profile_registry.as_deref(),
        }),
        Commands::Profiles { command } => cmd_profiles(command),
        Commands::Benchmark { command } => cmd_benchmark(command),
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

/// Runbook filename when the committed LabTrust fixture should be used instead.
const HANDOFF_DOC_ALIASES: &[(&str, &str)] = &[(
    "handoff_to_certifyedge.json",
    "tests/fixtures/handoff/labtrust_to_certifyedge_handoff.json",
)];

/// Resolve `--handoff` to an on-disk `HandoffManifest.v0` (with doc-name fallbacks).
pub fn resolve_handoff_path(handoff: &Path, certifyedge_root: &Path) -> Result<PathBuf, String> {
    let mut candidates = vec![handoff.to_path_buf()];
    if let Ok(cwd) = std::env::current_dir() {
        candidates.push(cwd.join(handoff));
    }
    candidates.push(certifyedge_root.join(handoff));
    for candidate in &candidates {
        if candidate.is_file() {
            return Ok(candidate.clone());
        }
    }
    if let Some(name) = handoff.file_name().and_then(|n| n.to_str()) {
        for (alias, fixture_rel) in HANDOFF_DOC_ALIASES {
            if name == *alias {
                let fixture = certifyedge_root.join(fixture_rel);
                if fixture.is_file() {
                    eprintln!(
                        "note: --handoff {} -> {}",
                        handoff.display(),
                        fixture.display()
                    );
                    return Ok(fixture);
                }
            }
        }
    }
    Err(format!(
        "handoff manifest not found: {}\n\
         Committed LabTrust fixture (run from CertifyEdge repo root):\n  \
         tests/fixtures/handoff/labtrust_to_certifyedge_handoff.json\n\
         Regenerate: make write-handoff-fixture",
        handoff.display()
    ))
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
    pub formal_facts_out: Option<&'a Path>,
    pub profile_registry: Option<&'a Path>,
}

fn profile_registry_for_cli(
    registry_override: Option<&Path>,
) -> Result<PropertyProfileRegistry, String> {
    let root = certifyedge_root();
    resolve_profile_registry(&root, registry_override)
}

pub fn cmd_benchmark(command: BenchmarkCommands) -> Result<(), String> {
    match command {
        BenchmarkCommands::ValidateCases => {
            let root = certifyedge_root();
            validate_certificate_benchmark_cases_tree(&root)?;
            println!("OK certificate benchmark case tree under benchmarks/certificates/");
            Ok(())
        }
        BenchmarkCommands::Certificates {
            profile,
            cases,
            out,
            profile_registry,
        } => {
            let root = certifyedge_root();
            let run = run_certificate_benchmark(BenchmarkCertificatesOptions {
                profile_id: &profile,
                cases_dir: &cases,
                out_dir: &out,
                certifyedge_root: &root,
                profile_registry: profile_registry.as_deref(),
                // Certificate benchmarks exercise release-mode checks (policy_hash, handoff fields).
                release_mode: true,
            })?;
            println!(
                "benchmark complete: {}/{} cases passed",
                run.cases_passed, run.cases_run
            );
            println!("benchmark_run={}/benchmark_run.v0.json", out.display());
            println!(
                "coverage_report={}/certificate_coverage_report.v0.json",
                out.display()
            );
            if run.cases_passed != run.cases_run {
                return Err(format!(
                    "certificate benchmark failed: {} of {} cases",
                    run.cases_run - run.cases_passed,
                    run.cases_run
                ));
            }
            Ok(())
        }
    }
}

pub fn cmd_profiles(command: ProfilesCommands) -> Result<(), String> {
    match command {
        ProfilesCommands::List { profile_registry } => {
            let registry = profile_registry_for_cli(profile_registry.as_deref())?;
            for id in registry.list()? {
                println!("{id}");
            }
            Ok(())
        }
        ProfilesCommands::Explain {
            property_id,
            profile_registry,
        } => {
            let registry = profile_registry_for_cli(profile_registry.as_deref())?;
            println!("{}", registry.explain_json(&property_id)?);
            Ok(())
        }
        ProfilesCommands::Validate {
            path,
            profile_registry,
        } => {
            let registry = profile_registry_for_cli(profile_registry.as_deref())?;
            let profile = registry.validate_file(&path)?;
            println!(
                "OK property profile {} ({})",
                profile.property_id,
                path.display()
            );
            Ok(())
        }
    }
}

pub fn cmd_emit_certificate(opts: EmitCertificateOptions<'_>) -> Result<(), String> {
    let root = certifyedge_root();
    let registry = resolve_profile_registry(&root, opts.profile_registry)?;
    let (spec_path, trace_path, out_path, handoff_profile, computation_inputs) =
        if let Some(handoff_arg) = opts.handoff_path {
            let handoff_path = resolve_handoff_path(handoff_arg, &root)?;
            if opts.release_mode {
                validate_handoff_artifact(&handoff_path, true)?;
            }
            let handoff = load_handoff_manifest(&handoff_path)?;
            let plan = plan_emit_from_handoff(
                &handoff_path,
                &handoff,
                &registry,
                opts.spec_path,
                opts.trace_path,
                opts.out_path,
                opts.release_mode,
            )?;
            (
                plan.spec_path,
                plan.trace_path,
                plan.out_path,
                Some(plan.property_profile),
                plan.computation_inputs,
            )
        } else {
            let spec = opts.spec_path.ok_or_else(|| {
                "emit-pcs-certificate requires --spec and --trace, or --handoff".to_string()
            })?;
            let trace = opts.trace_path.ok_or_else(|| {
                "emit-pcs-certificate requires --spec and --trace, or --handoff".to_string()
            })?;
            let out = opts.out_path.ok_or_else(|| {
                "emit-pcs-certificate requires --out (or --handoff with expected_outputs)"
                    .to_string()
            })?;
            (
                spec.to_path_buf(),
                trace.to_path_buf(),
                out.to_path_buf(),
                None,
                None,
            )
        };

    let trace_bytes = fs::read(&trace_path).map_err(|e| e.to_string())?;
    let profile = if let Some(p) = handoff_profile.as_ref() {
        p.clone()
    } else if let Ok(tool_spec) = pcs_certificate::ToolUsePropertySpec::load(&spec_path) {
        registry.load(&tool_spec.property_id)?
    } else if let Ok(comp_spec) = pcs_certificate::ComputationPropertySpec::load(&spec_path) {
        registry.load(&comp_spec.property_id)?
    } else {
        let spec = load_spec(&spec_path)?;
        registry.load(spec.property_id.as_str())?
    };

    let cx_path = opts
        .counterexample_out
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            out_path.with_file_name(pcs_certificate::default_counterexample_filename(&profile))
        });
    let cx_ref = cx_path
        .file_name()
        .map(|name| name.to_string_lossy().into_owned());

    let meta = CertifyEdgeMetadata::resolve(opts.release_mode)?;
    println!(
        "source_commit_resolution={}",
        meta.source_commit_resolution.as_str()
    );

    let emit_outcome = emit_certificate_for_profile(
        &profile,
        &registry,
        &spec_path,
        &trace_bytes,
        &meta,
        cx_ref.clone(),
        computation_inputs,
    )?;

    let failure_code = emit_outcome.failure_code.as_deref();
    let passed = emit_outcome.certificate.status() == profile.valid_success_status;

    if opts.release_mode && failure_code == Some("policy_hash_missing") {
        let stderr = repair_tool_use_check_failed(
            &profile,
            "policy_hash_missing",
            &trace_path.display().to_string(),
        );
        eprintln!("{stderr}");
        return Err("release mode: tool-use trace missing policy_hash".to_string());
    }

    if !passed {
        let failure_code = failure_code.unwrap_or("certificate_check_failed");
        let stderr = if emit_outcome.labtrust_counterexample.is_some() {
            repair_temporal_check_failed(
                &profile,
                &trace_path.display().to_string(),
                &spec_path.display().to_string(),
            )
        } else if emit_outcome.tool_use_counterexample.is_some() {
            repair_tool_use_check_failed(&profile, failure_code, &trace_path.display().to_string())
        } else if emit_outcome.computation_counterexample.is_some() {
            emit_check_failure_stderr(
                &profile,
                failure_code,
                &trace_path.display().to_string(),
                format!(
                    "computation reproducibility check failed for property_id={}",
                    profile.property_id
                ),
            )
        } else {
            emit_check_failure_stderr(
                &profile,
                failure_code,
                &trace_path.display().to_string(),
                format!(
                    "certificate check failed for property_id={}",
                    profile.property_id
                ),
            )
        };
        eprintln!("{stderr}");

        if let Some(cx) = &emit_outcome.labtrust_counterexample {
            write_counterexample(&cx_path, cx)?;
        } else if let Some(cx) = &emit_outcome.tool_use_counterexample {
            fs::write(
                &cx_path,
                format!(
                    "{}\n",
                    serde_json::to_string_pretty(cx).map_err(|e| e.to_string())?
                ),
            )
            .map_err(|e| e.to_string())?;
        } else if let Some(cx) = &emit_outcome.computation_counterexample {
            fs::write(
                &cx_path,
                format!(
                    "{}\n",
                    serde_json::to_string_pretty(cx).map_err(|e| e.to_string())?
                ),
            )
            .map_err(|e| e.to_string())?;
        }
    }

    let cert_json = emit_outcome.certificate.to_json_pretty()?;
    if let Some(parent) = out_path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent).map_err(|e| e.to_string())?;
        }
    }
    fs::write(&out_path, format!("{cert_json}\n")).map_err(|e| e.to_string())?;

    let cert_value: Value = serde_json::from_str(&cert_json).map_err(|e| e.to_string())?;
    validate_certificate_json_for_profile(&cert_value, &profile)?;
    validate_certificate_artifact(&out_path, opts.release_mode)?;
    registry_check_artifact(&out_path, opts.release_mode)?;

    if opts.release_mode {
        validate_release_mode_fields(&cert_value, &profile)?;
    }

    if let Some(formal_path) = opts.formal_facts_out {
        let artifact_name = out_path
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| "certificate.json".to_string());
        let profile_repair = failure_code.and_then(|code| profile.repair_hint_for(code));
        let facts = build_certificate_formal_facts(
            &emit_outcome.certificate,
            &profile,
            &artifact_name,
            failure_code,
            profile_repair,
        )?;
        validate_formal_facts_consistency(&facts, &emit_outcome.certificate, &profile)?;
        validate_certificate_formal_facts_schema(&facts)?;
        let facts_json = formal_facts_to_json_pretty(&facts)?;
        if let Some(parent) = formal_path.parent() {
            if !parent.as_os_str().is_empty() {
                fs::create_dir_all(parent).map_err(|e| e.to_string())?;
            }
        }
        fs::write(formal_path, format!("{facts_json}\n")).map_err(|e| e.to_string())?;
        println!("formal_facts_out={}", formal_path.display());
    }

    let summary_failure = if passed {
        None
    } else {
        Some(failure_code.unwrap_or("certificate_check_failed"))
    };
    let summary = CertificateEmitSummary::from_emitted_with_rejection(
        &emit_outcome.certificate,
        summary_failure,
        Some(&profile),
    );
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

    let cx_handoff_ref = if passed { None } else { cx_ref.as_deref() };

    if let Some(path) = opts.handoff_out {
        let mut outbound = build_certificate_to_bundle_handoff(
            &emit_outcome.certificate,
            &out_path,
            &registry,
            cx_handoff_ref,
            summary_failure,
            opts.formal_facts_out,
        )?;
        finalize_handoff_digest(&mut outbound);
        write_handoff_manifest(path, &outbound)?;
        validate_handoff_artifact(path, opts.release_mode)?;
        println!("handoff_out={}", path.display());
    }

    if passed {
        println!(
            "CertificateChecked -> {} ({})",
            out_path.display(),
            emit_outcome.certificate.certificate_id()
        );
    } else {
        println!(
            "Rejected -> {} ({})",
            out_path.display(),
            emit_outcome.certificate.certificate_id()
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
