//! Profile-driven certificate benchmark runner (pcs-core reports + CertifyEdge suite metrics).

use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::pcs_benchmark_bridge::{
    build_json_summary, emit_pcs_benchmark_artifacts, repair_hint_quality_from_hint,
    BenchmarkCertificatesJsonSummary, PcsBenchmarkEmitInput, RepairHintQuality,
    CERTIFICATE_BENCHMARK_SUITE_SCHEMA,
};
use crate::trace_certificate::counterexample_to_json;

use crate::emitted_certificate::{default_certificate_output_name, emit_certificate_for_profile};
use crate::handoff::{
    load_handoff_manifest, plan_emit_from_handoff, refresh_handoff_digest_file,
    validate_handoff_artifact,
};
use crate::metadata::CertifyEdgeMetadata;
use crate::property_profile::{PropertyProfile, PropertyProfileRegistry};
use crate::repair_hint::{rejection_repair_context, CertificateFailure, RepairHint};

fn default_expect_cli_success() -> bool {
    true
}

pub const CERTIFICATE_COVERAGE_REPORT_SCHEMA: &str = "CertificateCoverageReport.v0";
pub const PROFILE_COVERAGE_REPORT_SCHEMA: &str = "ProfileCoverageReport.v0";
pub const BENCHMARK_CASE_SPEC_SCHEMA: &str = "BenchmarkCaseSpec.v0";

/// Property profiles with committed certificate benchmark suites.
pub const BENCHMARKED_PROFILE_IDS: &[&str] = &[
    "hospital_lab.qc_release",
    "agent_tool_use.safety_v0",
    "scientific_computation.reproducibility_v0",
];

/// Maps `property_id` to `benchmarks/certificates/<suite>/` directory name.
pub fn benchmark_suite_dir_for_profile(property_id: &str) -> Option<&'static str> {
    match property_id {
        "hospital_lab.qc_release" => Some("hospital_lab_qc_release"),
        "agent_tool_use.safety_v0" => Some("tool_use_safety"),
        "scientific_computation.reproducibility_v0" => Some("computation_reproducibility"),
        _ => None,
    }
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct BenchmarkCaseSpec {
    pub schema_version: String,
    pub case_id: String,
    pub profile_id: String,
    pub kind: String,
    #[serde(default)]
    pub case_category: Option<String>,
    pub handoff_file: String,
    #[serde(default = "default_expect_cli_success")]
    pub expect_cli_success: bool,
    pub expected_certificate_status: Option<String>,
    pub expected_failure_code: Option<String>,
    #[serde(default)]
    pub expect_counterexample: bool,
    #[serde(default)]
    pub expected_repair_hint: Option<ExpectedRepairHintSpec>,
    #[serde(default)]
    pub unsupported: bool,
    #[serde(default)]
    pub notes: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize, Default)]
pub struct ExpectedRepairHintSpec {
    pub kind: String,
    #[serde(default)]
    pub command_contains: Option<String>,
    #[serde(default)]
    pub responsible_component: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct CaseRunResult {
    pub case_id: String,
    pub kind: String,
    pub passed: bool,
    pub profile_resolution_ok: bool,
    pub handoff_validation_ok: bool,
    pub status_match: bool,
    pub failure_code_match: bool,
    pub counterexample_match: bool,
    pub repair_hint_present: bool,
    pub repair_hint_kind_correct: bool,
    pub repair_hint_command_present: bool,
    pub responsible_component_correct: bool,
    pub actual_certificate_status: Option<String>,
    pub actual_failure_code: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub case_category: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub repair_hint_quality: Option<RepairHintQuality>,
    #[serde(skip)]
    pub expected_failure_code: Option<String>,
    #[serde(skip)]
    pub expect_counterexample: bool,
    #[serde(skip)]
    pub started_at: String,
    #[serde(skip)]
    pub completed_at: String,
    #[serde(skip)]
    pub duration_ms: u64,
    pub errors: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct RepairHintMetrics {
    pub repair_hint_accuracy: f64,
    pub cases_with_expected_repair_hint: usize,
    pub repair_hint_matches: usize,
    pub missing_repair_hints: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ProfileCoverageReport {
    pub schema_version: String,
    pub artifact: String,
    pub profile_id: String,
    pub templates_checked: bool,
    pub valid_cases: usize,
    pub invalid_cases: usize,
    pub properties_covered: Vec<String>,
    pub counterexample_types_covered: Vec<String>,
    pub unsupported_cases: Vec<String>,
    pub coverage_score: f64,
}

#[derive(Debug, Clone, Serialize)]
pub struct CertificateCoverageReport {
    pub schema_version: String,
    pub artifact: String,
    pub profile_id: String,
    pub cases_dir: String,
    pub valid_certificates_accepted: usize,
    pub valid_cases_total: usize,
    pub invalid_certificates_rejected: usize,
    pub invalid_cases_total: usize,
    pub failure_code_accuracy: f64,
    pub counterexample_completeness: f64,
    pub profile_resolution_accuracy: f64,
    pub handoff_validation_accuracy: f64,
    pub repair_hint_metrics: RepairHintMetrics,
    pub profile_coverage: ProfileCoverageReport,
    pub case_results: Vec<CaseRunResult>,
}

#[derive(Debug, Clone, Serialize)]
pub struct CertificateBenchmarkSuiteV0 {
    pub schema_version: String,
    pub artifact: String,
    pub profile_id: String,
    pub cases_dir: String,
    pub out_dir: String,
    pub started_at: String,
    pub finished_at: String,
    pub cases_run: usize,
    pub cases_passed: usize,
    pub coverage: CertificateCoverageReport,
}

pub struct BenchmarkCertificatesOptions<'a> {
    pub profile_id: &'a str,
    pub cases_dir: &'a Path,
    pub out_dir: &'a Path,
    pub certifyedge_root: &'a Path,
    pub profile_registry: Option<&'a Path>,
    pub release_mode: bool,
    pub json_summary: bool,
}

pub struct CertificateBenchmarkOutcome {
    pub suite: CertificateBenchmarkSuiteV0,
    pub json_summary: Option<BenchmarkCertificatesJsonSummary>,
}

pub fn run_certificate_benchmark(
    opts: BenchmarkCertificatesOptions<'_>,
) -> Result<CertificateBenchmarkOutcome, String> {
    let started_at = chrono::Utc::now().format("%Y-%m-%dT%H:%M:%SZ").to_string();
    std::fs::create_dir_all(opts.out_dir).map_err(|e| e.to_string())?;

    let registry = if let Some(dir) = opts.profile_registry {
        PropertyProfileRegistry::with_registry_dir(
            dir.to_path_buf(),
            opts.certifyedge_root.to_path_buf(),
        )
    } else {
        PropertyProfileRegistry::from_certifyedge_root(opts.certifyedge_root)
    };

    let profile = registry.load(opts.profile_id)?;
    let spec_path = registry.spec_path(&profile);
    assert_profile_template(&profile, &spec_path)?;

    let mut case_results = Vec::new();
    for kind in ["valid", "invalid"] {
        let kind_dir = opts.cases_dir.join(kind);
        if !kind_dir.is_dir() {
            continue;
        }
        for entry in std::fs::read_dir(&kind_dir).map_err(|e| e.to_string())? {
            let entry = entry.map_err(|e| e.to_string())?;
            if !entry.file_type().map_err(|e| e.to_string())?.is_dir() {
                continue;
            }
            let case_dir = entry.path();
            let result = run_single_case(
                &case_dir,
                kind,
                opts.profile_id,
                &profile,
                &registry,
                opts.release_mode,
            )?;
            case_results.push(result);
        }
    }

    case_results.sort_by(|a, b| a.case_id.cmp(&b.case_id));
    let coverage = build_coverage_report(opts.profile_id, opts.cases_dir, &profile, &case_results);
    let cases_passed = case_results.iter().filter(|c| c.passed).count();
    let finished_at = chrono::Utc::now().format("%Y-%m-%dT%H:%M:%SZ").to_string();

    let suite = CertificateBenchmarkSuiteV0 {
        schema_version: "v0".into(),
        artifact: CERTIFICATE_BENCHMARK_SUITE_SCHEMA.into(),
        profile_id: opts.profile_id.to_string(),
        cases_dir: opts.cases_dir.display().to_string(),
        out_dir: opts.out_dir.display().to_string(),
        started_at,
        finished_at,
        cases_run: case_results.len(),
        cases_passed,
        coverage: coverage.clone(),
    };

    let suite_path = opts.out_dir.join("certificate_benchmark_suite.v0.json");
    write_json(suite_path, &suite)?;
    validate_certifyedge_suite_outputs(&suite)?;

    let meta = CertifyEdgeMetadata::resolve(opts.release_mode)?;
    emit_pcs_benchmark_artifacts(PcsBenchmarkEmitInput {
        profile_id: opts.profile_id,
        profile: &profile,
        cases_dir: opts.cases_dir,
        out_dir: opts.out_dir,
        suite: &suite,
        coverage: &coverage,
        case_results: &case_results,
        meta: &meta,
    })?;

    let json_summary = if opts.json_summary {
        let summary = build_json_summary(opts.profile_id, opts.out_dir, &suite, &coverage);
        write_json(opts.out_dir.join("benchmark_summary.v0.json"), &summary)?;
        Some(summary)
    } else {
        None
    };

    Ok(CertificateBenchmarkOutcome {
        suite,
        json_summary,
    })
}

fn validate_certifyedge_suite_outputs(suite: &CertificateBenchmarkSuiteV0) -> Result<(), String> {
    let suite_value = serde_json::to_value(suite).map_err(|e| e.to_string())?;
    let coverage_value = serde_json::to_value(&suite.coverage).map_err(|e| e.to_string())?;
    crate::pcs_schema::validate_certificate_benchmark_suite_schema(&suite_value)
        .map_err(|e| format!("certificate benchmark suite schema: {e}"))?;
    crate::pcs_schema::validate_certificate_coverage_report_schema(&coverage_value)
        .map_err(|e| format!("certificate coverage report schema: {e}"))?;
    Ok(())
}

fn run_single_case(
    case_dir: &Path,
    kind: &str,
    expected_profile_id: &str,
    profile: &PropertyProfile,
    registry: &PropertyProfileRegistry,
    release_mode: bool,
) -> Result<CaseRunResult, String> {
    let spec_path = case_dir.join("case.json");
    let spec_text = std::fs::read_to_string(&spec_path)
        .map_err(|e| format!("{}: read case.json: {e}", case_dir.display()))?;
    let spec: BenchmarkCaseSpec =
        serde_json::from_str(&spec_text).map_err(|e| format!("{}: {e}", case_dir.display()))?;
    let spec_value = serde_json::to_value(&spec).map_err(|e| e.to_string())?;
    crate::pcs_schema::validate_benchmark_case_spec_schema(&spec_value)
        .map_err(|e| format!("{}: case.json schema: {e}", case_dir.display()))?;

    let case_started = chrono::Utc::now();
    let case_category = spec
        .case_category
        .clone()
        .or_else(|| infer_case_category(&spec.case_id, kind));

    if spec.unsupported {
        let completed = chrono::Utc::now();
        return Ok(CaseRunResult {
            case_id: spec.case_id,
            kind: kind.to_string(),
            passed: true,
            profile_resolution_ok: true,
            handoff_validation_ok: true,
            status_match: true,
            failure_code_match: true,
            counterexample_match: true,
            repair_hint_present: true,
            repair_hint_kind_correct: true,
            repair_hint_command_present: true,
            responsible_component_correct: true,
            actual_certificate_status: None,
            actual_failure_code: Some("unsupported".into()),
            case_category,
            repair_hint_quality: None,
            expected_failure_code: spec.expected_failure_code.clone(),
            expect_counterexample: spec.expect_counterexample,
            started_at: case_started.format("%Y-%m-%dT%H:%M:%SZ").to_string(),
            completed_at: completed.format("%Y-%m-%dT%H:%M:%SZ").to_string(),
            duration_ms: (completed - case_started).num_milliseconds().max(0) as u64,
            errors: vec!["skipped: case marked unsupported".into()],
        });
    }

    let profile_resolution_ok = spec.profile_id == expected_profile_id
        && spec.profile_id == profile.property_id;

    let handoff_path = case_dir.join(&spec.handoff_file);
    let handoff_validation_ok = refresh_handoff_digest_file(&handoff_path).is_ok()
        && validate_handoff_artifact(&handoff_path, false).is_ok();

    let work = case_dir.join(".benchmark_work");
    let _ = std::fs::remove_dir_all(&work);
    std::fs::create_dir_all(&work).map_err(|e| e.to_string())?;

    let cert_name = default_certificate_output_name(profile);
    let cert_out = work.join(cert_name);
    let cx_out = work.join(default_counterexample_filename(profile));
    let cx_ref = cx_out.file_name().map(|n| n.to_string_lossy().into_owned());

    let emit_result = run_emit_for_case(
        &handoff_path,
        profile,
        registry,
        &cert_out,
        cx_ref.as_deref(),
        release_mode,
    );

    let mut errors = Vec::new();
    let (
        actual_status,
        actual_failure_code,
        repair_present,
        repair_kind_ok,
        repair_cmd_ok,
        responsible_ok,
        captured_hint,
        captured_responsible,
    ) = match emit_result {
        Ok(outcome) => {
            if !spec.expect_cli_success {
                errors.push("expected emit to fail but succeeded".into());
            }
            let status = outcome.certificate.status().to_string();
            let failure_code = outcome.failure_code.clone();
            let repair = evaluate_repair_hint_with_capture(profile, failure_code.as_deref(), &spec);
            (
                Some(status),
                failure_code,
                repair.checks.0,
                repair.checks.1,
                repair.checks.2,
                repair.checks.3,
                repair.hint,
                repair.responsible,
            )
        }
        Err(err) => {
            if spec.expect_cli_success {
                errors.push(format!("emit failed: {err}"));
            }
            let parsed = parse_failure_from_error(&err, profile, &spec);
            (
                None,
                parsed.failure_code,
                parsed.checks.0,
                parsed.checks.1,
                parsed.checks.2,
                parsed.checks.3,
                parsed.hint,
                parsed.responsible,
            )
        }
    };

    let cx_exists = cx_out.is_file();
    let expected_status = spec.expected_certificate_status.as_deref();
    let status_match = expected_status == actual_status.as_deref();
    if !status_match {
        errors.push(format!("status: expected {expected_status:?}, got {actual_status:?}"));
    }

    let failure_code_match = match (
        spec.expected_failure_code.as_deref(),
        actual_failure_code.as_deref(),
    ) {
        (None, None) => true,
        (Some(e), Some(a)) => e == a,
        _ => false,
    };
    if !failure_code_match {
        errors.push(format!(
            "failure_code: expected {:?}, got {:?}",
            spec.expected_failure_code, actual_failure_code
        ));
    }

    let counterexample_match = spec.expect_counterexample == cx_exists;
    if !counterexample_match {
        errors.push(format!(
            "counterexample: expected present={}, exists={}",
            spec.expect_counterexample, cx_exists
        ));
    }

    if !profile_resolution_ok {
        errors.push("profile_id mismatch with --profile".into());
    }
    if !handoff_validation_ok {
        errors.push("handoff failed schema/digest validation".into());
    }

    let passed = errors.is_empty()
        && profile_resolution_ok
        && handoff_validation_ok
        && status_match
        && failure_code_match
        && counterexample_match
        && repair_present
        && repair_kind_ok
        && repair_cmd_ok
        && responsible_ok;

    let case_completed = chrono::Utc::now();
    let repair_hint_quality = if spec.expected_repair_hint.is_some() || captured_hint.is_some() {
        Some(repair_hint_quality_from_hint(
            captured_hint.as_ref(),
            captured_responsible.as_deref(),
        ))
    } else {
        None
    };

    Ok(CaseRunResult {
        case_id: spec.case_id,
        kind: kind.to_string(),
        passed,
        profile_resolution_ok,
        handoff_validation_ok,
        status_match,
        failure_code_match,
        counterexample_match,
        repair_hint_present: repair_present,
        repair_hint_kind_correct: repair_kind_ok,
        repair_hint_command_present: repair_cmd_ok,
        responsible_component_correct: responsible_ok,
        actual_certificate_status: actual_status,
        actual_failure_code,
        case_category,
        repair_hint_quality,
        expected_failure_code: spec.expected_failure_code.clone(),
        expect_counterexample: spec.expect_counterexample,
        started_at: case_started.format("%Y-%m-%dT%H:%M:%SZ").to_string(),
        completed_at: case_completed.format("%Y-%m-%dT%H:%M:%SZ").to_string(),
        duration_ms: (case_completed - case_started).num_milliseconds().max(0) as u64,
        errors,
    })
}

fn infer_case_category(case_id: &str, folder_kind: &str) -> Option<String> {
    if folder_kind == "valid" {
        return Some("valid".into());
    }
    const MAP: &[(&str, &str)] = &[
        ("missing_qc_event", "rejected_certificate"),
        ("unauthorized_release", "invalid_policy_or_property_violation"),
        ("trace_hash_mismatch", "invalid_hash_mismatch"),
        ("property_id_mismatch", "invalid_source_provenance"),
        ("unauthorized_tool_call", "unauthorized_tool_call"),
        ("missing_policy_hash", "missing_policy_hash"),
        ("unknown_authorization_status", "unknown_authorization_status"),
        ("policy_hash_mismatch", "policy_hash_mismatch"),
        ("dataset_hash_mismatch", "dataset_hash_mismatch"),
        ("environment_digest_mismatch", "environment_digest_mismatch"),
        ("result_hash_mismatch", "result_hash_mismatch"),
        ("missing_code_commit", "missing_code_commit"),
        ("nonzero_exit_code", "nonzero_exit_code"),
    ];
    for (id, category) in MAP {
        if *id == case_id {
            return Some(category.to_string());
        }
    }
    Some("invalid_policy_or_property_violation".into())
}

fn default_counterexample_filename(profile: &PropertyProfile) -> String {
    if profile.is_computation_profile() {
        "computation_counterexample.json".into()
    } else {
        "counterexample.json".into()
    }
}

struct EmitRunOutcome {
    certificate: crate::emitted_certificate::EmittedCertificate,
    failure_code: Option<String>,
}

fn run_emit_for_case(
    handoff_path: &Path,
    _profile: &PropertyProfile,
    registry: &PropertyProfileRegistry,
    cert_out: &Path,
    counterexample_ref: Option<&str>,
    release_mode: bool,
) -> Result<EmitRunOutcome, String> {
    let handoff = load_handoff_manifest(handoff_path)?;
    let plan = plan_emit_from_handoff(
        handoff_path,
        &handoff,
        registry,
        None,
        None,
        Some(cert_out),
        release_mode,
    )?;

    let trace_bytes = std::fs::read(&plan.trace_path).map_err(|e| e.to_string())?;
    let meta = CertifyEdgeMetadata::resolve(release_mode)?;
    let outcome = emit_certificate_for_profile(
        &plan.property_profile,
        registry,
        &plan.spec_path,
        &trace_bytes,
        &meta,
        counterexample_ref.map(String::from),
        plan.computation_inputs,
    )?;

    let cert_json = outcome.certificate.to_json_pretty()?;
    if let Some(parent) = cert_out.parent() {
        std::fs::create_dir_all(parent).ok();
    }
    std::fs::write(cert_out, format!("{cert_json}\n")).map_err(|e| e.to_string())?;

    if let Some(cx) = &outcome.labtrust_counterexample {
        let cx_path = cert_out
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .join("counterexample.json");
        let json = counterexample_to_json(cx).map_err(|e| e.to_string())?;
        std::fs::write(cx_path, format!("{json}\n")).ok();
    } else if let Some(cx) = &outcome.tool_use_counterexample {
        let cx_path = cert_out
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .join("counterexample.json");
        std::fs::write(
            cx_path,
            format!(
                "{}\n",
                serde_json::to_string_pretty(cx).map_err(|e| e.to_string())?
            ),
        )
        .ok();
    } else if let Some(cx) = &outcome.computation_counterexample {
        let cx_path = cert_out
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .join("computation_counterexample.json");
        std::fs::write(
            cx_path,
            format!(
                "{}\n",
                serde_json::to_string_pretty(cx).map_err(|e| e.to_string())?
            ),
        )
        .ok();
    }

    Ok(EmitRunOutcome {
        certificate: outcome.certificate,
        failure_code: outcome.failure_code,
    })
}

fn parse_failure_from_error(
    err: &str,
    profile: &PropertyProfile,
    spec: &BenchmarkCaseSpec,
) -> RepairEvalOutcome {
    if let Ok(failure) = serde_json::from_str::<CertificateFailure>(err) {
        let repair = evaluate_repair_hint_from_actual(
            profile,
            spec,
            Some(&failure.repair_hint),
            failure.responsible_component.as_deref(),
        );
        return RepairEvalOutcome {
            checks: repair,
            hint: Some(failure.repair_hint),
            responsible: failure.responsible_component,
            failure_code: Some(failure.failure_code),
        };
    }
    let code = spec.expected_failure_code.clone();
    let mut outcome = evaluate_repair_hint_with_capture(profile, code.as_deref(), spec);
    outcome.failure_code = code;
    outcome
}

struct RepairEvalOutcome {
    checks: (bool, bool, bool, bool),
    hint: Option<RepairHint>,
    responsible: Option<String>,
    failure_code: Option<String>,
}

fn evaluate_repair_hint_with_capture(
    profile: &PropertyProfile,
    failure_code: Option<&str>,
    spec: &BenchmarkCaseSpec,
) -> RepairEvalOutcome {
    let Some(_expected) = &spec.expected_repair_hint else {
        return RepairEvalOutcome {
            checks: (true, true, true, true),
            hint: None,
            responsible: None,
            failure_code: failure_code.map(str::to_string),
        };
    };
    let Some(code) = failure_code else {
        return RepairEvalOutcome {
            checks: (false, false, false, false),
            hint: None,
            responsible: None,
            failure_code: None,
        };
    };
    let Some((_code, responsible, hint)) = rejection_repair_context(profile, code) else {
        return RepairEvalOutcome {
            checks: (false, false, false, false),
            hint: None,
            responsible: None,
            failure_code: Some(code.to_string()),
        };
    };
    let repair = evaluate_repair_hint_from_actual(profile, spec, Some(&hint), responsible.as_deref());
    RepairEvalOutcome {
        checks: repair,
        hint: Some(hint),
        responsible,
        failure_code: Some(code.to_string()),
    }
}

fn evaluate_repair_hint_from_actual(
    _profile: &PropertyProfile,
    spec: &BenchmarkCaseSpec,
    actual: Option<&crate::repair_hint::RepairHint>,
    responsible: Option<&str>,
) -> (bool, bool, bool, bool) {
    let Some(expected) = &spec.expected_repair_hint else {
        return (true, true, true, true);
    };
    let Some(hint) = actual else {
        return (false, false, false, false);
    };
    let kind_ok = hint.kind == expected.kind;
    let cmd_ok = expected
        .command_contains
        .as_ref()
        .map(|needle| hint.command.contains(needle))
        .unwrap_or(!hint.command.is_empty());
    let resp_ok = expected
        .responsible_component
        .as_ref()
        .map(|r| responsible == Some(r.as_str()))
        .unwrap_or(true);
    (true, kind_ok, cmd_ok, resp_ok)
}

fn build_coverage_report(
    profile_id: &str,
    cases_dir: &Path,
    profile: &PropertyProfile,
    results: &[CaseRunResult],
) -> CertificateCoverageReport {
    let valid_results: Vec<_> = results.iter().filter(|r| r.kind == "valid").collect();
    let invalid_results: Vec<_> = results.iter().filter(|r| r.kind == "invalid").collect();

    let valid_accepted = valid_results
        .iter()
        .filter(|r| r.status_match && r.actual_certificate_status.as_deref() == Some("CertificateChecked"))
        .count();
    let invalid_rejected = invalid_results
        .iter()
        .filter(|r| {
            r.status_match
                && r.actual_certificate_status.as_deref() == Some("Rejected")
        })
        .count();

    let failure_denom = results
        .iter()
        .filter(|r| r.expected_failure_code.is_some())
        .count();
    let failure_num = results
        .iter()
        .filter(|r| r.expected_failure_code.is_some() && r.failure_code_match)
        .count();

    let cx_denom = results.iter().filter(|r| r.expect_counterexample).count();
    let cx_num = results
        .iter()
        .filter(|r| r.expect_counterexample && r.counterexample_match)
        .count();

    let profile_res = results.iter().filter(|r| r.profile_resolution_ok).count();
    let handoff_val = results.iter().filter(|r| r.handoff_validation_ok).count();

    let repair_expected: Vec<_> = results
        .iter()
        .filter(|r| r.kind == "invalid" && !r.errors.iter().any(|e| e.contains("unsupported")))
        .collect();
    let repair_matches = repair_expected
        .iter()
        .filter(|r| {
            r.repair_hint_present
                && r.repair_hint_kind_correct
                && r.repair_hint_command_present
                && r.responsible_component_correct
        })
        .count();
    let missing_repair: Vec<String> = repair_expected
        .iter()
        .filter(|r| !r.repair_hint_present || !r.repair_hint_kind_correct)
        .map(|r| r.case_id.clone())
        .collect();

    let repair_accuracy = if repair_expected.is_empty() {
        1.0
    } else {
        repair_matches as f64 / repair_expected.len() as f64
    };

    let unsupported: Vec<String> = results
        .iter()
        .filter(|r| r.actual_failure_code.as_deref() == Some("unsupported"))
        .map(|r| r.case_id.clone())
        .collect();

    let mut counterexample_types = Vec::new();
    for r in results.iter().filter(|r| r.counterexample_match) {
        if let Some(code) = &r.actual_failure_code {
            if !counterexample_types.contains(code) {
                counterexample_types.push(code.clone());
            }
        }
    }

    let measured = results.len().saturating_sub(unsupported.len());
    let passed = results.iter().filter(|r| r.passed).count();
    let coverage_score = if measured == 0 {
        1.0
    } else {
        passed as f64 / measured as f64
    };

    CertificateCoverageReport {
        schema_version: "v0".into(),
        artifact: CERTIFICATE_COVERAGE_REPORT_SCHEMA.into(),
        profile_id: profile_id.to_string(),
        cases_dir: cases_dir.display().to_string(),
        valid_certificates_accepted: valid_accepted,
        valid_cases_total: valid_results.len(),
        invalid_certificates_rejected: invalid_rejected,
        invalid_cases_total: invalid_results.len(),
        failure_code_accuracy: ratio(failure_num, failure_denom),
        counterexample_completeness: ratio(cx_num, cx_denom),
        profile_resolution_accuracy: ratio(profile_res, results.len()),
        handoff_validation_accuracy: ratio(handoff_val, results.len()),
        repair_hint_metrics: RepairHintMetrics {
            repair_hint_accuracy: repair_accuracy,
            cases_with_expected_repair_hint: repair_expected.len(),
            repair_hint_matches: repair_matches,
            missing_repair_hints: missing_repair,
        },
        profile_coverage: ProfileCoverageReport {
            schema_version: "v0".into(),
            artifact: PROFILE_COVERAGE_REPORT_SCHEMA.into(),
            profile_id: profile_id.to_string(),
            templates_checked: true,
            valid_cases: valid_results.len(),
            invalid_cases: invalid_results.len(),
            properties_covered: vec![profile.property_id.clone()],
            counterexample_types_covered: counterexample_types,
            unsupported_cases: unsupported,
            coverage_score,
        },
        case_results: results.to_vec(),
    }
}

fn assert_profile_template(profile: &PropertyProfile, spec_path: &Path) -> Result<(), String> {
    if profile.is_computation_profile() {
        let spec = crate::computation_check::ComputationPropertySpec::load(spec_path)?;
        if spec.property_id != profile.property_id {
            return Err(format!(
                "template property_id {} != profile {}",
                spec.property_id, profile.property_id
            ));
        }
    } else if profile.input_trace_artifact == crate::property_profile::ARTIFACT_TOOL_USE_TRACE {
        let spec = crate::tool_use_check::ToolUsePropertySpec::load(spec_path)?;
        if spec.property_id != profile.property_id {
            return Err(format!(
                "template property_id {} != profile {}",
                spec.property_id, profile.property_id
            ));
        }
    } else {
        let spec = labtrust_adapter::PropertySpec::load(spec_path)?;
        if spec.property_id.as_str() != profile.property_id {
            return Err(format!(
                "template property_id {} != profile {}",
                spec.property_id.as_str(),
                profile.property_id
            ));
        }
    }
    Ok(())
}

fn ratio(num: usize, denom: usize) -> f64 {
    if denom == 0 {
        1.0
    } else {
        num as f64 / denom as f64
    }
}

/// Validate every `case.json` under `benchmarks/certificates/` against `BenchmarkCaseSpec.v0`.
pub fn validate_certificate_benchmark_cases_tree(certifyedge_root: &Path) -> Result<(), String> {
    let bench_root = certifyedge_root.join("benchmarks/certificates");
    if !bench_root.is_dir() {
        return Err(format!(
            "missing benchmark cases tree: {}",
            bench_root.display()
        ));
    }
    let mut errors = Vec::new();
    for suite in std::fs::read_dir(&bench_root).map_err(|e| e.to_string())? {
        let suite = suite.map_err(|e| e.to_string())?;
        if !suite.file_type().map_err(|e| e.to_string())?.is_dir() {
            continue;
        }
        for kind in ["valid", "invalid"] {
            let kind_dir = suite.path().join(kind);
            if !kind_dir.is_dir() {
                continue;
            }
            for case in std::fs::read_dir(&kind_dir).map_err(|e| e.to_string())? {
                let case = case.map_err(|e| e.to_string())?;
                if !case.file_type().map_err(|e| e.to_string())?.is_dir() {
                    continue;
                }
                let case_dir = case.path();
                let case_json = case_dir.join("case.json");
                if !case_json.is_file() {
                    errors.push(format!("{}: missing case.json", case_dir.display()));
                    continue;
                }
                let text = std::fs::read_to_string(&case_json).map_err(|e| e.to_string())?;
                let value: serde_json::Value =
                    serde_json::from_str(&text).map_err(|e| e.to_string())?;
                if let Err(e) = crate::pcs_schema::validate_benchmark_case_spec_schema(&value) {
                    errors.push(format!("{}: {e}", case_json.display()));
                }
                let handoff_file = value
                    .get("handoff_file")
                    .and_then(|v| v.as_str())
                    .unwrap_or("handoff.json");
                let handoff_path = case_dir.join(handoff_file);
                if !handoff_path.is_file() {
                    errors.push(format!("{}: missing handoff", case_dir.display()));
                }
            }
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors.join("\n"))
    }
}

fn write_json(path: PathBuf, value: &impl Serialize) -> Result<(), String> {
    let json = serde_json::to_string_pretty(value).map_err(|e| e.to_string())?;
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).ok();
    }
    std::fs::write(path, format!("{json}\n")).map_err(|e| e.to_string())
}
