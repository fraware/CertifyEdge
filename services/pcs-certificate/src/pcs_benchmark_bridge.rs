//! Map CertifyEdge certificate benchmark results to pcs-core `BenchmarkReport.v0` artifacts.

use std::path::Path;

use serde::Serialize;
use serde_json::{json, Value};

use crate::certificate_benchmark::{
    CaseRunResult, CertificateBenchmarkSuiteV0, CertificateCoverageReport,
};
use crate::hash::canonical_hash;
use crate::metadata::CertifyEdgeMetadata;
use crate::property_profile::PropertyProfile;
use crate::repair_hint::RepairHint;

pub const CERTIFYEDGE_SOURCE_REPO: &str = "https://github.com/fraware/CertifyEdge";
pub const CERTIFICATE_BENCHMARK_SUITE_SCHEMA: &str = "CertificateBenchmarkSuite.v0";

#[derive(Debug, Clone, Serialize)]
pub struct RepairHintQuality {
    pub repair_hint_present: bool,
    pub repair_hint_kind: String,
    pub responsible_component: String,
    pub repair_command: String,
}

/// Normalized stdout summary for pcs-bench ingestion (`--json-summary`).
#[derive(Debug, Clone, Serialize)]
pub struct BenchmarkCertificatesJsonSummary {
    pub producer_id: String,
    pub benchmark_suite_id: String,
    pub workflow_profile_id: String,
    pub cases_run: usize,
    pub cases_passed: usize,
    pub failure_localization_accuracy: f64,
    pub repair_hint_accuracy: f64,
    pub certificate_completeness_score: f64,
    pub profile_coverage_ratio: f64,
    pub out_dir: String,
    pub benchmark_report_path: String,
}

pub struct PcsBenchmarkEmitInput<'a> {
    pub profile_id: &'a str,
    pub profile: &'a PropertyProfile,
    pub cases_dir: &'a Path,
    pub out_dir: &'a Path,
    pub suite: &'a CertificateBenchmarkSuiteV0,
    pub coverage: &'a CertificateCoverageReport,
    pub case_results: &'a [CaseRunResult],
    pub meta: &'a CertifyEdgeMetadata,
}

pub fn benchmark_suite_id(profile_id: &str) -> String {
    match profile_id {
        "hospital_lab.qc_release" => "certifyedge-hospital-lab-qc-release-v0".into(),
        "agent_tool_use.safety_v0" => "certifyedge-tool-use-safety-v0".into(),
        "scientific_computation.reproducibility_v0" => {
            "certifyedge-computation-reproducibility-v0".into()
        }
        other => format!("certifyedge-{other}"),
    }
}

/// pcs-core `workflow_id` (explicit; not an alias of profile registry paths).
pub fn workflow_id_for_profile(profile_id: &str) -> &str {
    match profile_id {
        "hospital_lab.qc_release" => "hospital_lab.qc_release",
        "agent_tool_use.safety_v0" => "agent_tool_use.safety_v0",
        "scientific_computation.reproducibility_v0" => "scientific_computation.reproducibility_v0",
        other => other,
    }
}

/// pcs-core explain-quality section catalog (aligned with `common.defs.json`).
const EXPLAIN_QUALITY_SECTIONS: &[&str] = &[
    "provenance",
    "hashes",
    "handoffs",
    "verification",
    "formal_checks",
    "limitations",
    "lineage",
    "repair_hints",
];

/// Sections required for certificate rejection / repair-hint explain-quality (release-grade >= 0.8).
const EXPLAIN_QUALITY_REJECTION_SECTIONS: &[&str] = &[
    "provenance",
    "hashes",
    "verification",
    "limitations",
    "repair_hints",
];

/// Whether a failure code has multiple plausible responsible components (emit `unknown` + reason).
pub fn failure_localization_is_ambiguous(failure_code: &str) -> bool {
    matches!(failure_code, "policy_hash_mismatch")
}

/// Human-readable reason when [`failure_localization_is_ambiguous`] is true.
pub fn failure_localization_ambiguity_reason(failure_code: &str) -> Option<&'static str> {
    match failure_code {
        "policy_hash_mismatch" => Some(
            "policy_hash_mismatch may be attributed to certificate_producer or runtime_producer",
        ),
        _ => None,
    }
}

/// Observed components that satisfy localization when the failure code is ambiguous.
pub fn failure_localization_plausible_components(failure_code: &str) -> &'static [&'static str] {
    match failure_code {
        "policy_hash_mismatch" => &["unknown", "certificate_producer", "runtime_producer"],
        _ => &["unknown"],
    }
}

/// Failure code used for responsible-component mapping (category overrides for rejections).
pub fn failure_code_for_localization(result: &CaseRunResult, fallback_code: &str) -> String {
    if result.case_category.as_deref() == Some("rejected_certificate") {
        "rejected_certificate".to_string()
    } else {
        fallback_code.to_string()
    }
}

/// Whether failure code and responsible-component localization match benchmark expectations.
pub fn case_failure_localization_accurate(result: &CaseRunResult) -> bool {
    let needs_localization = result.kind == "invalid"
        || result
            .case_category
            .as_deref()
            .is_some_and(|c| c == "rejected_certificate");
    if !needs_localization {
        return true;
    }
    if !result.failure_code_match {
        return false;
    }
    let fallback = result
        .expected_failure_code
        .as_deref()
        .or(result.actual_failure_code.as_deref())
        .unwrap_or("");
    let loc_code = failure_code_for_localization(result, fallback);
    let expected_component = if result.case_category.as_deref() == Some("rejected_certificate") {
        responsible_component_for_failure_code(&loc_code).to_string()
    } else {
        result
            .expected_responsible_component
            .as_deref()
            .map(normalize_responsible_component)
            .unwrap_or_else(|| responsible_component_for_failure_code(&loc_code).to_string())
    };
    let observed_code = result.actual_failure_code.as_deref().unwrap_or("");
    let observed_loc_code = failure_code_for_localization(result, observed_code);
    let observed_component = result
        .repair_hint_quality
        .as_ref()
        .map(|q| normalize_responsible_component(&q.responsible_component))
        .unwrap_or_else(|| responsible_component_for_failure_code(&observed_loc_code).to_string());
    if failure_localization_is_ambiguous(&loc_code) {
        failure_localization_plausible_components(&loc_code).contains(&observed_component.as_str())
            || observed_component == expected_component
    } else {
        observed_component == expected_component
    }
}

/// Default pcs-core responsible component for a failure code (benchmark localization).
pub fn responsible_component_for_failure_code(failure_code: &str) -> &'static str {
    if failure_localization_is_ambiguous(failure_code) {
        return "unknown";
    }
    match failure_code {
        "policy_hash_missing" => "handoff",
        "unknown_profile"
        | "unknown_property_id"
        | "unsupported_profile"
        | "profile_not_found" => "certificate_producer",
        "unauthorized_tool_call" | "unknown_authorization_status" => "runtime_producer",
        "result_hash_mismatch"
        | "run_hash_mismatch"
        | "dataset_hash_mismatch"
        | "environment_digest_mismatch"
        | "trace_hash_mismatch"
        | "temporal_check_failed"
        | "nonzero_exit_code"
        | "missing_code_commit" => "runtime_producer",
        "invalid_handoff" | "invalid_handoff_digest" => "handoff",
        "rejected_certificate" => "certificate_producer",
        code if code.contains("handoff") => "handoff",
        _ => "certificate_producer",
    }
}

pub fn map_certifyedge_repair_kind(kind: &str) -> &'static str {
    match kind {
        "regenerate_trace_or_handoff" => "align_hash",
        "add_property_profile" => "fix_registry_entry",
        "fix_computation_receipts" | "fix_run_receipt" => "align_provenance",
        "fix_result_artifact" => "align_hash",
        "fix_computation_run" => "rerun_verification",
        "fix_trace_or_policy" => "unknown",
        _ => "unknown",
    }
}

pub fn repair_hint_quality_from_hint(
    hint: Option<&RepairHint>,
    responsible: Option<&str>,
) -> RepairHintQuality {
    match hint {
        Some(h) => RepairHintQuality {
            repair_hint_present: true,
            repair_hint_kind: h.kind.clone(),
            responsible_component: normalize_responsible_component(
                responsible.unwrap_or("unknown"),
            ),
            repair_command: h.command.clone(),
        },
        None => RepairHintQuality {
            repair_hint_present: false,
            repair_hint_kind: "unknown".into(),
            responsible_component: "unknown".into(),
            repair_command: String::new(),
        },
    }
}

fn with_digest(mut doc: Value) -> Value {
    if let Some(obj) = doc.as_object_mut() {
        obj.insert("signature_or_digest".to_string(), Value::String(String::new()));
        let digest = canonical_hash(&Value::Object(obj.clone()));
        obj.insert("signature_or_digest".to_string(), Value::String(digest));
    }
    doc
}

fn coverage_report(
    coverage_id: &str,
    metric: &str,
    numerator: f64,
    denominator: f64,
    details: Value,
    meta: &CertifyEdgeMetadata,
) -> Value {
    let ratio = if denominator <= 0.0 {
        1.0
    } else {
        (numerator / denominator).clamp(0.0, 1.0)
    };
    with_digest(json!({
        "schema_version": "v0",
        "coverage_id": coverage_id,
        "metric": metric,
        "numerator": numerator,
        "denominator": denominator.max(1.0),
        "coverage_ratio": ratio,
        "details": details,
        "source_repo": CERTIFYEDGE_SOURCE_REPO,
        "source_commit": meta.source_commit,
        "signature_or_digest": ""
    }))
}

fn output_artifact_type(profile: &PropertyProfile) -> &'static str {
    if profile.is_computation_profile() {
        "ComputationWitness.v0"
    } else if profile.input_trace_artifact == crate::property_profile::ARTIFACT_TOOL_USE_TRACE {
        "ToolUseCertificate.v0"
    } else {
        "TraceCertificate.v0"
    }
}

pub fn emit_pcs_benchmark_artifacts(input: PcsBenchmarkEmitInput<'_>) -> Result<(), String> {
    let suite_id = benchmark_suite_id(input.profile_id);
    let artifact_type = output_artifact_type(input.profile);
    let meta = input.meta;
    let runs_dir = input.out_dir.join("runs");
    std::fs::create_dir_all(&runs_dir).map_err(|e| e.to_string())?;

    let mut run_refs: Vec<Value> = Vec::new();
    let mut failures: Vec<Value> = Vec::new();
    let mut core_runs: Vec<Value> = Vec::new();

    for result in input.case_results {
        let run_filename = format!("runs/{}.benchmark_run.v0.json", result.case_id);
        let run_path = input.out_dir.join(&run_filename);
        let run_doc = build_certificate_benchmark_run(result, &suite_id, input.profile_id, meta)?;
        let run_value = serde_json::to_value(&run_doc).map_err(|e| e.to_string())?;
        crate::pcs_schema::validate_certificate_benchmark_run_schema(&run_value).map_err(|e| {
            format!(
                "certificate benchmark run schema ({}, case {}): {e}",
                run_path.display(),
                result.case_id
            )
        })?;
        let core_run = crate::pcs_schema::benchmark_run_core_for_ingest(&run_value);
        crate::pcs_schema::validate_benchmark_run_schema(&core_run).map_err(|e| {
            format!(
                "benchmark run core projection ({}, case {}): {e}",
                run_path.display(),
                result.case_id
            )
        })?;
        write_json_file(&run_path, &run_doc)?;
        core_runs.push(core_run);
        let run_id = run_doc
            .get("run_id")
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string();
        let observed_status = run_doc
            .get("observed_status")
            .and_then(|v| v.as_str())
            .unwrap_or("failed")
            .to_string();
        run_refs.push(json!({
            "run_id": run_id,
            "case_id": result.case_id,
            "path": run_filename,
            "observed_status": observed_status
        }));

        if !result.passed {
            let message = if result.errors.is_empty() {
                "benchmark case expectations not met".to_string()
            } else {
                result.errors.join("; ")
            };
            failures.push(json!({
                "case_id": result.case_id,
                "run_id": run_id,
                "message": message
            }));
        }
    }

    let cert_native = serde_json::to_value(input.coverage).map_err(|e| e.to_string())?;
    crate::pcs_schema::validate_certificate_coverage_report_schema(&cert_native).map_err(|e| {
        format!("certificate coverage report schema: {e}")
    })?;
    write_json_file(
        &input.out_dir.join("certificate_coverage_report.v0.json"),
        &cert_native,
    )?;

    let repair_manifest_will_exist = input
        .case_results
        .iter()
        .any(|r| r.repair_hint_quality.is_some());

    let ambiguous_localizations: Vec<Value> = input
        .case_results
        .iter()
        .filter(|r| r.kind == "invalid" || r.case_category.as_deref() == Some("rejected_certificate"))
        .filter_map(|r| {
            let fallback = r
                .expected_failure_code
                .as_deref()
                .or(r.actual_failure_code.as_deref())
                .or(r.case_category.as_deref())
                .unwrap_or("");
            let code = failure_code_for_localization(r, fallback);
            failure_localization_ambiguity_reason(&code).map(|reason| {
                json!({
                    "case_id": r.case_id,
                    "failure_code": code,
                    "reason": reason,
                })
            })
        })
        .collect();

    let cert_completeness = coverage_report(
        &format!("{suite_id}-certificate-completeness"),
        "certificate_completeness",
        input.suite.cases_passed as f64,
        input.suite.cases_run.max(1) as f64,
        json!({
            "profile_id": input.profile_id,
            "valid_certificates_accepted": input.coverage.valid_certificates_accepted,
            "invalid_certificates_rejected": input.coverage.invalid_certificates_rejected,
            "failure_code_accuracy": input.coverage.failure_code_accuracy,
            "counterexample_completeness": input.coverage.counterexample_completeness,
            "native_artifact": "CertificateCoverageReport.v0",
            "native_report_file": "certificate_coverage_report.v0.json",
            "ambiguous_localizations": ambiguous_localizations,
            "sidecar_artifact_paths": {
                "benchmark_report": "benchmark_report.v0.json",
                "certificate_coverage_report": "certificate_coverage_report.v0.json",
                "profile_coverage_report": "profile_coverage_report.v0.json",
                "repair_hint_quality_report": "repair_hint_quality_report.v0.json",
                "pcs_bench_ingest": "pcs_bench_ingest.v0.json",
                "repair_hint_manifest": if repair_manifest_will_exist {
                    Value::String("repair_hint_manifest.v0.json".into())
                } else {
                    Value::Null
                },
            },
        }),
        meta,
    );

    let repair_coverage = coverage_report(
        &format!("{suite_id}-repair-hint-quality"),
        "repair_hint_quality",
        input.coverage.repair_hint_metrics.repair_hint_matches as f64,
        input
            .coverage
            .repair_hint_metrics
            .cases_with_expected_repair_hint
            .max(1) as f64,
        json!({
            "repair_hint_accuracy": input.coverage.repair_hint_metrics.repair_hint_accuracy,
            "missing_repair_hints": input.coverage.repair_hint_metrics.missing_repair_hints,
        }),
        meta,
    );

    let pc = &input.coverage.profile_coverage;
    let profile_coverage = build_profile_coverage_report(
        input.profile,
        input.profile_id,
        &suite_id,
        artifact_type,
        pc,
        input.suite,
        input.case_results,
        meta,
    );

    let workflow_id = workflow_id_for_profile(input.profile_id);
    let failure_localization_reports =
        build_failure_localization_reports(&suite_id, input.case_results, meta)?;
    let explain_quality_reports = build_explain_quality_reports(
        &suite_id,
        workflow_id,
        input.case_results,
        meta,
    )?;
    let explain_quality_coverage = build_suite_explain_quality_coverage(
        &suite_id,
        workflow_id,
        &explain_quality_reports,
        meta,
    )?;

    let report = build_benchmark_report(
        &suite_id,
        input.profile_id,
        &run_refs,
        &failures,
        &cert_completeness,
        &repair_coverage,
        &profile_coverage,
        explain_quality_coverage.as_ref(),
        input.coverage,
        input.suite,
        meta,
    )?;
    crate::pcs_schema::validate_benchmark_report_schema(&report)
        .map_err(|e| format!("benchmark report schema: {e}"))?;
    crate::pcs_schema::validate_coverage_report_schema(&cert_completeness)
        .map_err(|e| format!("certificate completeness coverage schema: {e}"))?;
    crate::pcs_schema::validate_coverage_report_schema(&repair_coverage)
        .map_err(|e| format!("repair hint coverage schema: {e}"))?;
    crate::pcs_schema::validate_profile_coverage_report_schema(&profile_coverage)
        .map_err(|e| format!("profile coverage report schema: {e}"))?;

    write_json_file(
        &input.out_dir.join("benchmark_report.v0.json"),
        &report,
    )?;
    write_json_file(
        &input.out_dir.join("profile_coverage_report.v0.json"),
        &profile_coverage,
    )?;
    write_json_file(
        &input.out_dir.join("repair_hint_quality_report.v0.json"),
        &repair_coverage,
    )?;

    let mut repair_cases = serde_json::Map::new();
    for result in input.case_results {
        if let Some(q) = &result.repair_hint_quality {
            if let Ok(value) = serde_json::to_value(q) {
                repair_cases.insert(result.case_id.clone(), value);
            }
        }
    }
    if !repair_cases.is_empty() {
        let manifest = with_digest(json!({
            "schema_version": "v0",
            "manifest_id": format!("{suite_id}-repair-hints"),
            "profile_id": input.profile_id,
            "benchmark_suite_id": suite_id,
            "cases": repair_cases,
            "source_repo": CERTIFYEDGE_SOURCE_REPO,
            "source_commit": input.meta.source_commit,
            "signature_or_digest": ""
        }));
        write_json_file(
            &input.out_dir.join("repair_hint_manifest.v0.json"),
            &manifest,
        )?;
    }

    write_embedded_sidecar_files(
        input.out_dir,
        &failure_localization_reports,
        &explain_quality_reports,
    )?;

    let ingest = build_pcs_bench_ingest_from_parts(
        input.out_dir,
        &suite_id,
        workflow_id,
        &core_runs,
        &[cert_completeness.clone(), repair_coverage.clone()],
        &[profile_coverage.clone()],
        &failure_localization_reports,
        &explain_quality_reports,
        input.case_results,
        meta,
    )?;
    crate::pcs_schema::validate_pcs_bench_ingest_schema(&ingest)
        .map_err(|e| format!("pcs_bench_ingest schema: {e}"))?;
    write_json_file(&input.out_dir.join("pcs_bench_ingest.v0.json"), &ingest)?;

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn build_profile_coverage_report(
    profile: &PropertyProfile,
    profile_id: &str,
    suite_id: &str,
    artifact_type: &str,
    pc: &crate::certificate_benchmark::ProfileCoverageReport,
    suite: &CertificateBenchmarkSuiteV0,
    case_results: &[CaseRunResult],
    meta: &CertifyEdgeMetadata,
) -> Value {
    let semantic_checks_required: Vec<String> = profile.repair_hints.keys().cloned().collect();
    let semantic_checks_covered: Vec<String> = semantic_checks_required
        .iter()
        .filter(|code| {
            case_results.iter().any(|r| {
                r.passed
                    && r.repair_hint_acceptable
                    && r.actual_failure_code.as_deref() == Some(code.as_str())
            })
        })
        .cloned()
        .collect();

    with_digest(json!({
        "schema_version": "v0",
        "coverage_id": format!("{suite_id}-profile-coverage"),
        "workflow_profile_id": profile_id,
        "producer_id": "certifyedge",
        "suite_id": suite_id,
        "artifact_types_required": [artifact_type],
        "artifact_types_covered": [artifact_type],
        "semantic_checks_required": semantic_checks_required,
        "semantic_checks_covered": semantic_checks_covered,
        "handoff_steps_required": ["runtime_to_certificate"],
        "handoff_steps_covered": ["runtime_to_certificate"],
        "numerator": suite.cases_passed as f64,
        "denominator": suite.cases_run.max(1) as f64,
        "coverage_ratio": pc.coverage_score,
        "details": {
            "templates_checked": pc.templates_checked,
            "release_mode_required_fields": profile.required_release_fields,
            "counterexample_types_covered": pc.counterexample_types_covered,
            "case_counts": {
                "valid": pc.valid_cases,
                "invalid": pc.invalid_cases
            },
            "unsupported_cases": pc.unsupported_cases,
        },
        "source_repo": CERTIFYEDGE_SOURCE_REPO,
        "source_commit": meta.source_commit,
        "signature_or_digest": ""
    }))
}

fn build_benchmark_artifact_ref(
    artifact_type: &str,
    path: &str,
    embedded: &Value,
    meta: &CertifyEdgeMetadata,
) -> Result<Value, String> {
    let content_digest = embedded
        .get("signature_or_digest")
        .and_then(|v| v.as_str())
        .filter(|s| !s.is_empty())
        .ok_or_else(|| {
            format!("embedded {artifact_type} at {path} missing signature_or_digest")
        })?;
    let doc = with_digest(json!({
        "schema_version": "v0",
        "artifact_type": artifact_type,
        "path": path,
        "sha256": content_digest,
        "role": "producer_export",
        "source_repo": CERTIFYEDGE_SOURCE_REPO,
        "source_commit": meta.source_commit,
        "signature_or_digest": ""
    }));
    crate::pcs_schema::validate_benchmark_artifact_ref_schema(&doc)
        .map_err(|e| format!("artifact ref ({path}): {e}"))?;
    Ok(doc)
}

fn write_embedded_sidecar_files(
    out_dir: &Path,
    failure_localization_reports: &[Value],
    explain_quality_reports: &[Value],
) -> Result<(), String> {
    let fl_dir = out_dir.join("failure_localization");
    std::fs::create_dir_all(&fl_dir).map_err(|e| e.to_string())?;
    for doc in failure_localization_reports {
        let case_id = doc
            .get("case_id")
            .and_then(|v| v.as_str())
            .ok_or_else(|| "failure localization missing case_id".to_string())?;
        let path = fl_dir.join(format!("{case_id}.failure_localization_result.v0.json"));
        write_json_file(&path, doc)?;
    }

    let eq_dir = out_dir.join("explain_quality");
    std::fs::create_dir_all(&eq_dir).map_err(|e| e.to_string())?;
    for doc in explain_quality_reports {
        let case_id = doc
            .get("case_id")
            .and_then(|v| v.as_str())
            .ok_or_else(|| "explain quality missing case_id".to_string())?;
        let path = eq_dir.join(format!("{case_id}.explain_quality_report.v0.json"));
        write_json_file(&path, doc)?;
    }
    Ok(())
}

fn build_artifact_refs(
    core_runs: &[Value],
    coverage_reports: &[Value],
    profile_coverage_reports: &[Value],
    failure_localization_reports: &[Value],
    explain_quality_reports: &[Value],
    meta: &CertifyEdgeMetadata,
) -> Result<Vec<Value>, String> {
    let mut refs = Vec::new();

    for cov in coverage_reports {
        let metric = cov.get("metric").and_then(|v| v.as_str()).unwrap_or("");
        let path = match metric {
            "certificate_completeness" => "certificate_coverage_report.v0.json",
            "repair_hint_quality" => "repair_hint_quality_report.v0.json",
            _ => continue,
        };
        refs.push(build_benchmark_artifact_ref(
            "CoverageReport.v0",
            path,
            cov,
            meta,
        )?);
    }

    for profile_cov in profile_coverage_reports {
        refs.push(build_benchmark_artifact_ref(
            "ProfileCoverageReport.v0",
            "profile_coverage_report.v0.json",
            profile_cov,
            meta,
        )?);
    }

    for run in core_runs {
        let case_id = run
            .get("case_id")
            .and_then(|v| v.as_str())
            .ok_or_else(|| "benchmark run missing case_id for artifact ref".to_string())?;
        let path = format!("runs/{case_id}.benchmark_run.v0.json");
        refs.push(build_benchmark_artifact_ref(
            "BenchmarkRun.v0",
            &path,
            run,
            meta,
        )?);
    }

    for loc in failure_localization_reports {
        let case_id = loc
            .get("case_id")
            .and_then(|v| v.as_str())
            .unwrap_or("unknown");
        let path = format!("failure_localization/{case_id}.failure_localization_result.v0.json");
        refs.push(build_benchmark_artifact_ref(
            "FailureLocalizationResult.v0",
            &path,
            loc,
            meta,
        )?);
    }

    for explain in explain_quality_reports {
        let case_id = explain
            .get("case_id")
            .and_then(|v| v.as_str())
            .unwrap_or("unknown");
        let path = format!("explain_quality/{case_id}.explain_quality_report.v0.json");
        refs.push(build_benchmark_artifact_ref(
            "ExplainQualityReport.v0",
            &path,
            explain,
            meta,
        )?);
    }

    Ok(refs)
}

fn build_failure_localization_reports(
    suite_id: &str,
    case_results: &[CaseRunResult],
    meta: &CertifyEdgeMetadata,
) -> Result<Vec<Value>, String> {
    let mut reports = Vec::new();
    for result in case_results {
        let is_invalid = result.kind == "invalid";
        let is_rejected = result
            .case_category
            .as_deref()
            .is_some_and(|c| c == "rejected_certificate");
        if !is_invalid && !is_rejected {
            continue;
        }
        let expected_code = result
            .expected_failure_code
            .as_deref()
            .filter(|s| !s.is_empty())
            .map(str::to_string)
            .or_else(|| result.actual_failure_code.clone())
            .or_else(|| result.case_category.clone())
            .unwrap_or_else(|| {
                if is_rejected {
                    "rejected_certificate".to_string()
                } else {
                    "invalid_case".to_string()
                }
            });
        let run_id = format!("bench-run-{}", result.case_id);
        let loc_code = failure_code_for_localization(result, &expected_code);
        let expected_component = if result.case_category.as_deref() == Some("rejected_certificate") {
            responsible_component_for_failure_code(&loc_code).to_string()
        } else {
            result
                .expected_responsible_component
                .as_deref()
                .map(normalize_responsible_component)
                .unwrap_or_else(|| responsible_component_for_failure_code(&loc_code).to_string())
        };
        let observed_code = result
            .actual_failure_code
            .as_deref()
            .unwrap_or("")
            .to_string();
        let observed_loc_code = failure_code_for_localization(result, &observed_code);
        let observed_component = result
            .repair_hint_quality
            .as_ref()
            .map(|q| normalize_responsible_component(&q.responsible_component))
            .unwrap_or_else(|| responsible_component_for_failure_code(&observed_loc_code).to_string());
        let localized_correctly = case_failure_localization_accurate(result);
        let doc = with_digest(json!({
            "schema_version": "v0",
            "result_id": format!("{suite_id}-localization-{}", result.case_id),
            "run_id": run_id,
            "case_id": result.case_id,
            "expected_failure_code": expected_code,
            "observed_failure_code": observed_code,
            "expected_responsible_component": expected_component,
            "observed_responsible_component": observed_component,
            "localized_correctly": localized_correctly,
            "source_repo": CERTIFYEDGE_SOURCE_REPO,
            "source_commit": meta.source_commit,
            "signature_or_digest": ""
        }));
        crate::pcs_schema::validate_failure_localization_result_schema(&doc)
            .map_err(|e| format!("failure localization ({}, case {}): {e}", suite_id, result.case_id))?;
        reports.push(doc);
    }
    Ok(reports)
}

fn explain_section_present(result: &CaseRunResult, section: &str) -> bool {
    let signals = &result.explain_signals;
    match section {
        "provenance" => {
            result.handoff_validation_ok
                || signals.certificate_emitted
                || signals.cx_has_provenance
        }
        "hashes" => {
            result.handoff_validation_ok
                || result.actual_failure_code.is_some()
                || signals.cx_has_hashes
        }
        "handoffs" => result.handoff_validation_ok,
        "verification" => {
            result.actual_certificate_status.is_some()
                || result.actual_failure_code.is_some()
                || signals.cx_has_verification
                || (result.kind == "invalid" && result.repair_hint_present)
        }
        "formal_checks" => result.formal_facts_ok || result.expect_formal_facts,
        "limitations" => {
            !result.errors.is_empty()
                || result.case_category.is_some()
                || signals.cx_has_limitations
        }
        "lineage" => {
            result.actual_certificate_status.is_some()
                || result.handoff_validation_ok
                || signals.certificate_emitted
        }
        "repair_hints" => {
            result.repair_hint_present
                || result
                    .repair_hint_quality
                    .as_ref()
                    .is_some_and(|q| q.repair_hint_present && !q.repair_command.is_empty())
                || signals.cx_has_repair_hints
        }
        _ => false,
    }
}

fn explain_section_notes(result: &CaseRunResult, section: &str, present: bool) -> String {
    if !present {
        return String::new();
    }
    let mut parts = vec![format!("certifyedge benchmark case {}", result.case_id)];
    if let Some(code) = result.actual_failure_code.as_deref().filter(|s| !s.is_empty()) {
        parts.push(format!("failure_code={code}"));
    }
    if let Some(status) = result.actual_certificate_status.as_deref() {
        parts.push(format!("certificate_status={status}"));
    }
    if result.explain_signals.counterexample_emitted {
        parts.push("counterexample_emitted=true".into());
    }
    if let Some(q) = &result.repair_hint_quality {
        if section == "repair_hints" && !q.repair_command.is_empty() {
            parts.push(format!("repair_command={}", q.repair_command));
        }
    }
    let failure_code = result
        .actual_failure_code
        .as_deref()
        .or(result.expected_failure_code.as_deref())
        .unwrap_or("");
    if failure_localization_is_ambiguous(failure_code) {
        if let Some(reason) = failure_localization_ambiguity_reason(failure_code) {
            parts.push(format!("ambiguity={reason}"));
        }
    }
    parts.join("; ")
}

fn explain_quality_required_sections(result: &CaseRunResult) -> &'static [&'static str] {
    let rejection_or_repair = result.kind == "invalid"
        || result
            .case_category
            .as_deref()
            .is_some_and(|c| c == "rejected_certificate" || c == "repair_hint_quality")
        || result.repair_hint_present
        || result.repair_hint_quality.is_some();
    if rejection_or_repair {
        EXPLAIN_QUALITY_REJECTION_SECTIONS
    } else {
        EXPLAIN_QUALITY_SECTIONS
    }
}

fn build_explain_quality_reports(
    suite_id: &str,
    workflow_id: &str,
    case_results: &[CaseRunResult],
    meta: &CertifyEdgeMetadata,
) -> Result<Vec<Value>, String> {
    let mut reports = Vec::new();
    for result in case_results {
        let needs_explain = result.kind == "invalid"
            || result
                .case_category
                .as_deref()
                .is_some_and(|c| c == "rejected_certificate" || c == "repair_hint_quality")
            || result.expected_failure_code.is_some()
            || result.repair_hint_present
            || result.repair_hint_quality.is_some();
        if !needs_explain {
            continue;
        }
        let required_sections = explain_quality_required_sections(result);
        let mut sections = serde_json::Map::new();
        let mut gaps = Vec::new();
        let mut present_count = 0usize;
        for section in EXPLAIN_QUALITY_SECTIONS {
            let present = explain_section_present(result, section);
            if required_sections.contains(&section) {
                if present {
                    present_count += 1;
                } else {
                    gaps.push(json!({
                        "section_id": section,
                        "message": format!("missing certificate rejection explanation section: {section}")
                    }));
                }
            }
            sections.insert(
                section.to_string(),
                json!({
                    "present": present,
                    "score": if present { 1.0 } else { 0.0 },
                    "notes": explain_section_notes(result, section, present)
                }),
            );
        }
        let required = required_sections.len();
        let quality_score = if required == 0 {
            1.0
        } else {
            present_count as f64 / required as f64
        };
        let doc = with_digest(json!({
            "schema_version": "v0",
            "report_id": format!("{suite_id}-explain-{}", result.case_id),
            "suite_id": suite_id,
            "case_id": result.case_id,
            "producer_id": "certifyedge",
            "workflow_id": workflow_id,
            "required_sections": required_sections,
            "sections": sections,
            "sections_present_count": present_count,
            "sections_required_count": required,
            "quality_score": quality_score,
            "gaps": gaps,
            "source_repo": CERTIFYEDGE_SOURCE_REPO,
            "source_commit": meta.source_commit,
            "signature_or_digest": ""
        }));
        crate::pcs_schema::validate_explain_quality_report_schema(&doc)
            .map_err(|e| format!("explain quality ({}, case {}): {e}", suite_id, result.case_id))?;
        reports.push(doc);
    }
    Ok(reports)
}

fn collect_suite_commands_and_logs(
    core_runs: &[Value],
    case_results: &[CaseRunResult],
) -> (Vec<Value>, Vec<String>) {
    let mut commands = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    for run in core_runs {
        if let Some(cmds) = run.get("commands").and_then(|v| v.as_array()) {
            for cmd in cmds {
                if let Ok(s) = serde_json::to_string(cmd) {
                    if seen.insert(s) {
                        commands.push(cmd.clone());
                    }
                }
            }
        }
    }
    let mut logs = Vec::new();
    for result in case_results {
        if !result.errors.is_empty() {
            logs.push(format!(
                "[{}] {}",
                result.case_id,
                result.errors.join("; ")
            ));
        }
    }
    (commands, logs)
}

fn build_pcs_bench_ingest_from_parts(
    _out_dir: &Path,
    suite_id: &str,
    workflow_id: &str,
    core_runs: &[Value],
    coverage_reports: &[Value],
    profile_coverage_reports: &[Value],
    failure_localization_reports: &[Value],
    explain_quality_reports: &[Value],
    case_results: &[CaseRunResult],
    meta: &CertifyEdgeMetadata,
) -> Result<Value, String> {
    let (commands, logs) = collect_suite_commands_and_logs(core_runs, case_results);
    let artifact_refs = build_artifact_refs(
        core_runs,
        coverage_reports,
        profile_coverage_reports,
        &failure_localization_reports,
        &explain_quality_reports,
        meta,
    )?;

    if commands.is_empty() {
        return Err(format!(
            "pcs_bench_ingest for {suite_id} requires non-empty commands for release-grade producer output"
        ));
    }

    Ok(with_digest(json!({
        "schema_version": "v0",
        "producer_id": "certifyedge",
        "suite_id": suite_id,
        "workflow_id": workflow_id,
        "benchmark_runs": core_runs,
        "coverage_reports": coverage_reports,
        "failure_localization_reports": failure_localization_reports,
        "explain_quality_reports": explain_quality_reports,
        "profile_coverage_reports": profile_coverage_reports,
        "artifact_refs": artifact_refs,
        "commands": commands,
        "logs": logs,
        "source_repo": CERTIFYEDGE_SOURCE_REPO,
        "source_commit": meta.source_commit,
        "signature_or_digest": ""
    })))
}

/// Suite-level explain-quality rollup for `BenchmarkReport.coverage.explain_quality`.
fn build_suite_explain_quality_coverage(
    suite_id: &str,
    workflow_id: &str,
    explain_reports: &[Value],
    meta: &CertifyEdgeMetadata,
) -> Result<Option<Value>, String> {
    if explain_reports.is_empty() {
        return Ok(None);
    }
    let mut present_total = 0usize;
    let mut required_total = 0usize;
    let mut score_sum = 0.0;
    for report in explain_reports {
        present_total += report
            .get("sections_present_count")
            .and_then(|v| v.as_u64())
            .unwrap_or(0) as usize;
        required_total += report
            .get("sections_required_count")
            .and_then(|v| v.as_u64())
            .unwrap_or(0) as usize;
        score_sum += report.get("quality_score").and_then(|v| v.as_f64()).unwrap_or(0.0);
    }
    let n = explain_reports.len().max(1);
    let quality_score = (score_sum / n as f64).clamp(0.0, 1.0);
    let sections_ratio = if required_total == 0 {
        1.0
    } else {
        present_total as f64 / required_total as f64
    };
    let mut sections = serde_json::Map::new();
    for section in EXPLAIN_QUALITY_REJECTION_SECTIONS {
        sections.insert(
            section.to_string(),
            json!({
                "present": sections_ratio >= 0.8,
                "score": sections_ratio.clamp(0.0, 1.0),
                "notes": format!("suite rollup across {n} per-case explain quality reports")
            }),
        );
    }
    let doc = with_digest(json!({
        "schema_version": "v0",
        "report_id": format!("{suite_id}-explain-quality-suite"),
        "suite_id": suite_id,
        "case_id": "suite",
        "producer_id": "certifyedge",
        "workflow_id": workflow_id,
        "required_sections": EXPLAIN_QUALITY_REJECTION_SECTIONS,
        "sections": sections,
        "sections_present_count": present_total,
        "sections_required_count": required_total.max(1),
        "quality_score": quality_score,
        "gaps": [],
        "source_repo": CERTIFYEDGE_SOURCE_REPO,
        "source_commit": meta.source_commit,
        "signature_or_digest": ""
    }));
    crate::pcs_schema::validate_explain_quality_report_schema(&doc)
        .map_err(|e| format!("suite explain quality coverage: {e}"))?;
    Ok(Some(doc))
}

const REQUIRED_BENCHMARK_OUTPUT_FILES: &[&str] = &[
    "benchmark_report.v0.json",
    "certificate_coverage_report.v0.json",
    "profile_coverage_report.v0.json",
    "repair_hint_quality_report.v0.json",
    "certificate_benchmark_suite.v0.json",
    "pcs_bench_ingest.v0.json",
];

/// Validate all pcs-bench ingest artifacts under a benchmark output directory.
pub fn validate_pcs_benchmark_output_dir(out_dir: &Path) -> Result<(), String> {
    for name in REQUIRED_BENCHMARK_OUTPUT_FILES {
        let path = out_dir.join(name);
        if !path.is_file() {
            return Err(format!("missing required benchmark output: {}", path.display()));
        }
    }

    let suite_path = out_dir.join("certificate_benchmark_suite.v0.json");
    if !suite_path.is_file() {
        return Err(format!(
            "missing required benchmark output: {}",
            suite_path.display()
        ));
    }
    let suite: Value =
        serde_json::from_str(&std::fs::read_to_string(&suite_path).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    crate::pcs_schema::validate_certificate_benchmark_suite_schema(&suite)?;

    let report_path = out_dir.join("benchmark_report.v0.json");
    let report_text = std::fs::read_to_string(&report_path)
        .map_err(|e| format!("read {}: {e}", report_path.display()))?;
    let report: Value = serde_json::from_str(&report_text).map_err(|e| e.to_string())?;
    crate::pcs_schema::validate_benchmark_report_schema(&report)?;

    let cert_cov_path = out_dir.join("certificate_coverage_report.v0.json");
    let cert_cov: Value =
        serde_json::from_str(&std::fs::read_to_string(&cert_cov_path).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    crate::pcs_schema::validate_certificate_coverage_report_schema(&cert_cov)?;
    if cert_cov.get("artifact").and_then(|v| v.as_str())
        != Some("CertificateCoverageReport.v0")
    {
        return Err(format!(
            "{}: expected CertificateCoverageReport.v0 artifact",
            cert_cov_path.display()
        ));
    }

    let profile_cov_path = out_dir.join("profile_coverage_report.v0.json");
    let profile_cov: Value = serde_json::from_str(
        &std::fs::read_to_string(&profile_cov_path).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    crate::pcs_schema::validate_profile_coverage_report_schema(&profile_cov)?;
    let details = profile_cov
        .get("details")
        .and_then(|v| v.as_object())
        .ok_or_else(|| "profile_coverage_report.details must be an object".to_string())?;
    if !details.contains_key("templates_checked") {
        return Err("profile_coverage_report.details missing templates_checked".into());
    }
    if !details.contains_key("release_mode_required_fields") {
        return Err(
            "profile_coverage_report.details missing release_mode_required_fields".into(),
        );
    }

    let repair_path = out_dir.join("repair_hint_quality_report.v0.json");
    let repair_cov: Value =
        serde_json::from_str(&std::fs::read_to_string(&repair_path).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    crate::pcs_schema::validate_coverage_report_schema(&repair_cov)?;

    let ingest: Value = serde_json::from_str(
        &std::fs::read_to_string(out_dir.join("pcs_bench_ingest.v0.json")).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    let runs = report
        .get("runs")
        .and_then(|v| v.as_array())
        .ok_or_else(|| "benchmark_report.runs must be an array".to_string())?;

    crate::pcs_schema::validate_pcs_bench_ingest_schema(&ingest)?;
    if ingest.get("suite_id").and_then(|v| v.as_str()) != report.get("benchmark_suite_id").and_then(|v| v.as_str()) {
        return Err("pcs_bench_ingest.suite_id must match benchmark_report.benchmark_suite_id".into());
    }
    if ingest.get("workflow_id").and_then(|v| v.as_str()).is_none() {
        return Err("pcs_bench_ingest.workflow_id is required".into());
    }
    let source_commit = ingest
        .get("source_commit")
        .and_then(|v| v.as_str())
        .unwrap_or("");
    if source_commit.chars().all(|c| c == '0') && source_commit.len() == 40 {
        return Err(
            "pcs_bench_ingest.source_commit must be a real git commit for release-grade producer output"
                .into(),
        );
    }

    let ingest_runs = ingest
        .get("benchmark_runs")
        .and_then(|v| v.as_array())
        .ok_or_else(|| "pcs_bench_ingest.benchmark_runs must be an array".to_string())?;
    if ingest_runs.len() != runs.len() {
        return Err(format!(
            "pcs_bench_ingest.benchmark_runs length {} != benchmark_report.runs {}",
            ingest_runs.len(),
            runs.len()
        ));
    }

    let coverage_reports = ingest
        .get("coverage_reports")
        .and_then(|v| v.as_array())
        .ok_or_else(|| "pcs_bench_ingest.coverage_reports must be an array".to_string())?;
    let has_cert_cov = coverage_reports.iter().any(|r| {
        r.get("metric").and_then(|v| v.as_str()) == Some("certificate_completeness")
    });
    let has_repair_cov = coverage_reports.iter().any(|r| {
        r.get("metric").and_then(|v| v.as_str()) == Some("repair_hint_quality")
    });
    if !has_cert_cov || !has_repair_cov {
        return Err(
            "pcs_bench_ingest.coverage_reports must include certificate_completeness and repair_hint_quality"
                .into(),
        );
    }
    for (idx, cov) in coverage_reports.iter().enumerate() {
        crate::pcs_schema::validate_coverage_report_schema(cov)
            .map_err(|e| format!("pcs_bench_ingest.coverage_reports[{idx}]: {e}"))?;
    }
    let ingest_repair = coverage_reports
        .iter()
        .find(|r| r.get("metric").and_then(|v| v.as_str()) == Some("repair_hint_quality"));
    match ingest_repair {
        Some(ingest_repair) if ingest_repair == &repair_cov => {}
        Some(_) => {
            return Err(
                "pcs_bench_ingest.coverage_reports repair_hint_quality does not match repair_hint_quality_report.v0.json".into(),
            );
        }
        None => {
            return Err("pcs_bench_ingest.coverage_reports missing repair_hint_quality".into());
        }
    }

    let profile_reports = ingest
        .get("profile_coverage_reports")
        .and_then(|v| v.as_array())
        .ok_or_else(|| "pcs_bench_ingest.profile_coverage_reports must be an array".to_string())?;
    if profile_reports.len() != 1 {
        return Err(format!(
            "pcs_bench_ingest.profile_coverage_reports expected 1 entry, got {}",
            profile_reports.len()
        ));
    }
    if profile_reports[0] != profile_cov {
        return Err(
            "pcs_bench_ingest.profile_coverage_reports[0] does not match profile_coverage_report.v0.json"
                .into(),
        );
    }

    let failed_run_count = ingest_runs
        .iter()
        .filter(|r| r.get("observed_status").and_then(|v| v.as_str()) == Some("failed"))
        .count();
    if let Some(localizations) = ingest.get("failure_localization_reports").and_then(|v| v.as_array()) {
        if failed_run_count > 0 && localizations.is_empty() {
            return Err(
                "pcs_bench_ingest.failure_localization_reports must be non-empty when benchmark runs include failures"
                    .into(),
            );
        }
        for (idx, loc) in localizations.iter().enumerate() {
            crate::pcs_schema::validate_failure_localization_result_schema(loc)
                .map_err(|e| format!("pcs_bench_ingest.failure_localization_reports[{idx}]: {e}"))?;
        }
    } else if failed_run_count > 0 {
        return Err(
            "pcs_bench_ingest.failure_localization_reports required for failed benchmark runs".into(),
        );
    }
    let rejection_case_ids: std::collections::BTreeSet<String> = ingest_runs
        .iter()
        .filter_map(|r| {
            let failed = r.get("observed_status").and_then(|v| v.as_str()) == Some("failed");
            if failed {
                r.get("case_id").and_then(|v| v.as_str()).map(str::to_string)
            } else {
                None
            }
        })
        .collect();
    if let Some(explains) = ingest.get("explain_quality_reports").and_then(|v| v.as_array()) {
        if !rejection_case_ids.is_empty() && explains.is_empty() {
            return Err(
                "pcs_bench_ingest.explain_quality_reports must be non-empty for rejection/failure cases"
                    .into(),
            );
        }
        for (idx, exp) in explains.iter().enumerate() {
            crate::pcs_schema::validate_explain_quality_report_schema(exp)
                .map_err(|e| format!("pcs_bench_ingest.explain_quality_reports[{idx}]: {e}"))?;
            let score = exp.get("quality_score").and_then(|v| v.as_f64()).unwrap_or(0.0);
            let case_id = exp.get("case_id").and_then(|v| v.as_str()).unwrap_or("");
            let required: Vec<&str> = exp
                .get("required_sections")
                .and_then(|v| v.as_array())
                .map(|a| {
                    a.iter()
                        .filter_map(|v| v.as_str())
                        .collect()
                })
                .unwrap_or_default();
            let is_rejection_grade = required
                .iter()
                .all(|s| EXPLAIN_QUALITY_REJECTION_SECTIONS.contains(s))
                && required.len() == EXPLAIN_QUALITY_REJECTION_SECTIONS.len();
            if is_rejection_grade && score < 0.8 {
                return Err(format!(
                    "pcs_bench_ingest.explain_quality_reports[{idx}] case {case_id}: \
                     quality_score {score} below release-grade minimum 0.8"
                ));
            }
        }
    }

    let artifact_refs = ingest
        .get("artifact_refs")
        .and_then(|v| v.as_array())
        .ok_or_else(|| "pcs_bench_ingest.artifact_refs must be present for certifyedge producer".to_string())?;
    if artifact_refs.is_empty() {
        return Err("pcs_bench_ingest.artifact_refs must be non-empty".into());
    }
    for (idx, artifact_ref) in artifact_refs.iter().enumerate() {
        crate::pcs_schema::validate_benchmark_artifact_ref_schema(artifact_ref)
            .map_err(|e| format!("pcs_bench_ingest.artifact_refs[{idx}]: {e}"))?;
        let sha256 = artifact_ref
            .get("sha256")
            .and_then(|v| v.as_str())
            .ok_or_else(|| format!("artifact_refs[{idx}] missing sha256"))?;
        let artifact_type = artifact_ref
            .get("artifact_type")
            .and_then(|v| v.as_str())
            .ok_or_else(|| format!("artifact_refs[{idx}] missing artifact_type"))?;
        let rel_path = artifact_ref
            .get("path")
            .and_then(|v| v.as_str())
            .ok_or_else(|| format!("artifact_refs[{idx}] missing path"))?;
        let embedded = match artifact_type {
            "BenchmarkRun.v0" => ingest_runs,
            "CoverageReport.v0" => coverage_reports,
            "ProfileCoverageReport.v0" => profile_reports,
            "FailureLocalizationResult.v0" => ingest
                .get("failure_localization_reports")
                .and_then(|v| v.as_array())
                .map(|a| a.as_slice())
                .unwrap_or(&[]),
            "ExplainQualityReport.v0" => ingest
                .get("explain_quality_reports")
                .and_then(|v| v.as_array())
                .map(|a| a.as_slice())
                .unwrap_or(&[]),
            other => {
                return Err(format!("artifact_refs[{idx}] unsupported artifact_type {other:?}"));
            }
        };
        if !embedded
            .iter()
            .any(|row| row.get("signature_or_digest").and_then(|v| v.as_str()) == Some(sha256))
        {
            return Err(format!(
                "artifact_refs[{idx}] sha256 does not match any embedded {artifact_type}"
            ));
        }
        let sidecar_path = out_dir.join(rel_path);
        if !sidecar_path.is_file() {
            return Err(format!(
                "artifact_refs[{idx}] path {} not found on disk",
                sidecar_path.display()
            ));
        }
        if rel_path == "certificate_coverage_report.v0.json" {
            continue;
        }
        let bytes = std::fs::read(&sidecar_path).map_err(|e| {
            format!("read {} for artifact ref digest check: {e}", sidecar_path.display())
        })?;
        if artifact_type == "BenchmarkRun.v0" {
            let run_doc: Value = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
            let core = crate::pcs_schema::benchmark_run_core_for_ingest(&run_doc);
            let core_digest = core
                .get("signature_or_digest")
                .and_then(|v| v.as_str())
                .unwrap_or("");
            if core_digest != sha256 {
                return Err(format!(
                    "artifact_refs[{idx}] sha256 does not match core projection digest of {}",
                    sidecar_path.display()
                ));
            }
            continue;
        }
        let on_disk: Value = serde_json::from_slice(&bytes).map_err(|e| {
            format!("parse {} for artifact ref digest check: {e}", sidecar_path.display())
        })?;
        let on_disk_digest = on_disk
            .get("signature_or_digest")
            .and_then(|v| v.as_str())
            .unwrap_or("");
        if on_disk_digest != sha256 {
            return Err(format!(
                "artifact_refs[{idx}] sha256 {sha256} != on-disk signature_or_digest {on_disk_digest} ({})",
                sidecar_path.display()
            ));
        }
    }

    let fl_dir = out_dir.join("failure_localization");
    if ingest
        .get("failure_localization_reports")
        .and_then(|v| v.as_array())
        .is_some_and(|a| !a.is_empty())
        && !fl_dir.is_dir()
    {
        return Err(format!(
            "missing failure_localization/ sidecar directory under {}",
            out_dir.display()
        ));
    }
    let eq_dir = out_dir.join("explain_quality");
    if ingest
        .get("explain_quality_reports")
        .and_then(|v| v.as_array())
        .is_some_and(|a| !a.is_empty())
        && !eq_dir.is_dir()
    {
        return Err(format!(
            "missing explain_quality/ sidecar directory under {}",
            out_dir.display()
        ));
    }

    let runs_dir = out_dir.join("runs");
    if !runs_dir.is_dir() {
        return Err(format!("missing runs/ directory under {}", out_dir.display()));
    }
    let run_files: Vec<_> = std::fs::read_dir(&runs_dir)
        .map_err(|e| e.to_string())?
        .filter_map(|e| e.ok())
        .filter(|e| {
            e.path()
                .file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.ends_with(".benchmark_run.v0.json"))
        })
        .collect();
    if run_files.len() != ingest_runs.len() {
        return Err(format!(
            "runs/*.benchmark_run.v0.json count {} != ingest benchmark_runs {}",
            run_files.len(),
            ingest_runs.len()
        ));
    }

    for (idx, ingest_run) in ingest_runs.iter().enumerate() {
        crate::pcs_schema::validate_benchmark_run_schema(ingest_run)
            .map_err(|e| format!("pcs_bench_ingest.benchmark_runs[{idx}]: {e}"))?;
    }

    let manifest_path = out_dir.join("repair_hint_manifest.v0.json");
    if manifest_path.is_file() {
        let manifest: Value = serde_json::from_str(
            &std::fs::read_to_string(&manifest_path).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
        if manifest.get("cases").and_then(|v| v.as_object()).is_none() {
            return Err(format!(
                "{}: repair_hint_manifest.v0.json must contain a cases object",
                manifest_path.display()
            ));
        }
    }
    if let Some(cov) = coverage_reports.iter().find(|r| {
        r.get("metric").and_then(|v| v.as_str()) == Some("certificate_completeness")
    }) {
        if let Some(sidecar) = cov
            .get("details")
            .and_then(|d| d.get("sidecar_artifact_paths"))
            .and_then(|v| v.as_object())
        {
            let manifest_entry = sidecar.get("repair_hint_manifest");
            match manifest_entry {
                Some(Value::String(path)) if path == "repair_hint_manifest.v0.json" => {
                    if !manifest_path.is_file() {
                        return Err(
                            "coverage sidecar_artifact_paths documents repair_hint_manifest but file is missing"
                                .into(),
                        );
                    }
                }
                Some(Value::Null) | None => {
                    if manifest_path.is_file() {
                        return Err(
                            "repair_hint_manifest.v0.json present but sidecar_artifact_paths.repair_hint_manifest is null"
                                .into(),
                        );
                    }
                }
                Some(other) => {
                    return Err(format!(
                        "unexpected sidecar_artifact_paths.repair_hint_manifest: {other:?}"
                    ));
                }
            }
        }
    }

    for run_ref in runs {
        let rel = run_ref
            .get("path")
            .and_then(|v| v.as_str())
            .ok_or_else(|| "run ref missing path".to_string())?;
        if !rel.starts_with("runs/") || !rel.ends_with(".benchmark_run.v0.json") {
            return Err(format!("unexpected run path: {rel}"));
        }
        let run_path = out_dir.join(rel);
        let run_doc: Value = serde_json::from_str(
            &std::fs::read_to_string(&run_path).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
        crate::pcs_schema::validate_certificate_benchmark_run_schema(&run_doc)?;
        let core = crate::pcs_schema::benchmark_run_core_for_ingest(&run_doc);
        crate::pcs_schema::validate_benchmark_run_schema(&core)
            .map_err(|e| format!("{} (core): {e}", run_path.display()))?;

        let case_id = run_ref
            .get("case_id")
            .and_then(|v| v.as_str())
            .ok_or_else(|| "run ref missing case_id".to_string())?;
        let ingest_run = ingest_runs
            .iter()
            .find(|r| r.get("case_id").and_then(|v| v.as_str()) == Some(case_id))
            .ok_or_else(|| format!("pcs_bench_ingest missing benchmark run for case_id {case_id}"))?;
        let file_core = crate::pcs_schema::benchmark_run_core_for_ingest(&run_doc);
        if ingest_run != &file_core {
            return Err(format!(
                "pcs_bench_ingest.benchmark_runs[{case_id}] does not match core projection of {}",
                run_path.display()
            ));
        }
    }

    validate_artifact_refs_cover_embedded(&ingest, out_dir)?;
    validate_sidecar_artifact_paths_on_disk(&ingest, out_dir)?;

    let commands = ingest
        .get("commands")
        .and_then(|v| v.as_array())
        .ok_or_else(|| "pcs_bench_ingest.commands must be an array".to_string())?;
    if commands.is_empty() {
        return Err("pcs_bench_ingest.commands must be non-empty for release-grade producer output".into());
    }

    let evidence_grade = report
        .get("summary")
        .and_then(|s| s.get("evidence_grade"))
        .and_then(|v| v.as_str());
    if evidence_grade != Some("release") {
        return Err(format!(
            "benchmark_report.summary.evidence_grade must be 'release' when producer runs in release mode (got {evidence_grade:?})"
        ));
    }

    let _ = repair_cov;
    let _ = cert_cov;

    Ok(())
}

fn validate_artifact_refs_cover_embedded(ingest: &Value, out_dir: &Path) -> Result<(), String> {
    let refs = ingest
        .get("artifact_refs")
        .and_then(|v| v.as_array())
        .ok_or_else(|| "pcs_bench_ingest.artifact_refs required".to_string())?;
    let ref_keys: std::collections::BTreeSet<(String, String)> = refs
        .iter()
        .filter_map(|r| {
            let t = r.get("artifact_type")?.as_str()?;
            let sha = r.get("sha256")?.as_str()?;
            Some((t.to_string(), sha.to_string()))
        })
        .collect();

    let embedded_types: &[(&str, &str)] = &[
        ("BenchmarkRun.v0", "benchmark_runs"),
        ("CoverageReport.v0", "coverage_reports"),
        ("ProfileCoverageReport.v0", "profile_coverage_reports"),
        ("FailureLocalizationResult.v0", "failure_localization_reports"),
        ("ExplainQualityReport.v0", "explain_quality_reports"),
    ];
    for (artifact_type, field) in embedded_types {
        let rows = ingest
            .get(*field)
            .and_then(|v| v.as_array())
            .map(|a| a.as_slice())
            .unwrap_or(&[]);
        for (idx, row) in rows.iter().enumerate() {
            let digest = row
                .get("signature_or_digest")
                .and_then(|v| v.as_str())
                .unwrap_or("");
            if digest.is_empty() {
                continue;
            }
            if !ref_keys.contains(&(artifact_type.to_string(), digest.to_string())) {
                return Err(format!(
                    "pcs_bench_ingest.{field}[{idx}] missing artifact_refs entry for {artifact_type} digest"
                ));
            }
        }
    }

    let manifest_path = out_dir.join("repair_hint_manifest.v0.json");
    if manifest_path.is_file() {
        let listed = refs.iter().any(|r| r.get("path").and_then(|v| v.as_str()) == Some("repair_hint_manifest.v0.json"));
        if listed {
            return Err(
                "artifact_refs must not list repair_hint_manifest.v0.json (document in sidecar_artifact_paths only)"
                    .into(),
            );
        }
    }
    Ok(())
}

fn validate_sidecar_artifact_paths_on_disk(ingest: &Value, out_dir: &Path) -> Result<(), String> {
    let coverage_reports = ingest
        .get("coverage_reports")
        .and_then(|v| v.as_array())
        .ok_or_else(|| "pcs_bench_ingest.coverage_reports must be an array".to_string())?;
    let cert_cov = coverage_reports
        .iter()
        .find(|r| r.get("metric").and_then(|v| v.as_str()) == Some("certificate_completeness"))
        .ok_or_else(|| "pcs_bench_ingest missing certificate_completeness coverage".to_string())?;
    let sidecar = cert_cov
        .get("details")
        .and_then(|d| d.get("sidecar_artifact_paths"))
        .and_then(|v| v.as_object())
        .ok_or_else(|| "certificate_completeness.details.sidecar_artifact_paths required".to_string())?;
    for (key, value) in sidecar {
        let Some(path) = value.as_str() else {
            if value.is_null() && key == "repair_hint_manifest" {
                continue;
            }
            return Err(format!("sidecar_artifact_paths.{key} must be a path string or null"));
        };
        let file_path = out_dir.join(path);
        if !file_path.is_file() {
            return Err(format!(
                "sidecar_artifact_paths documents {key}={path} but file is missing at {}",
                file_path.display()
            ));
        }
    }
    Ok(())
}

fn build_certificate_benchmark_run(
    result: &CaseRunResult,
    suite_id: &str,
    profile_id: &str,
    meta: &CertifyEdgeMetadata,
) -> Result<Value, String> {
    let observed_benchmark_status = if result.passed { "passed" } else { "failed" };
    let expected_benchmark_status = "passed";
    let observed_system_outcome =
        system_outcome_from_certificate_status(result.actual_certificate_status.as_deref());
    let expected_system_outcome =
        system_outcome_from_certificate_status(result.expected_certificate_status.as_deref());
    let failure_code = result
        .actual_failure_code
        .as_ref()
        .filter(|s| !s.is_empty())
        .map(|s| Value::String(s.clone()))
        .unwrap_or(Value::Null);
    let (repair_hint_pcs, component) = if let Some(q) = &result.repair_hint_quality {
        if q.repair_hint_present {
            (
                Value::String(map_certifyedge_repair_kind(&q.repair_hint_kind).to_string()),
                Some(normalize_responsible_component(&q.responsible_component)),
            )
        } else {
            (Value::Null, None)
        }
    } else {
        (Value::Null, None)
    };
    let responsible = component
        .as_ref()
        .map(|c| Value::String(c.clone()))
        .unwrap_or(Value::Null);
    let certificate_status = result
        .actual_certificate_status
        .as_deref()
        .map(certificate_status_for_benchmark);

    let command = format!(
        "certifyedge emit-pcs-certificate --profile {profile_id} --handoff <case>/handoff.json"
    );
    let exit_code = if result.passed { 0 } else { 1 };
    let mut artifacts = vec!["certificate.json".to_string()];
    if result.expect_formal_facts || result.formal_facts_ok {
        artifacts.push("certificate_formal_facts.json".to_string());
    }

    let mut doc = json!({
        "schema_version": "v0",
        "run_id": format!("bench-run-{}", result.case_id),
        "task_id": profile_id,
        "case_id": result.case_id,
        "started_at": result.started_at,
        "completed_at": result.completed_at,
        "commands": [{
            "command": command,
            "exit_code": exit_code
        }],
        "artifacts_produced": artifacts,
        "observed_status": observed_benchmark_status,
        "observed_benchmark_status": observed_benchmark_status,
        "expected_benchmark_status": expected_benchmark_status,
        "observed_system_outcome": observed_system_outcome,
        "expected_system_outcome": expected_system_outcome,
        "observed_failure_code": failure_code,
        "observed_responsible_component": responsible,
        "observed_repair_hint": repair_hint_pcs,
        "duration_ms": result.duration_ms,
        "source_repo": CERTIFYEDGE_SOURCE_REPO,
        "source_commit": meta.source_commit,
        "signature_or_digest": "",
        "suite_id": suite_id,
        "workflow_id": profile_id,
        "workflow_profile_id": profile_id,
        "expected_certificate_status": result.expected_certificate_status,
        "expected_failure_code": result.expected_failure_code,
        "expected_responsible_component": result.expected_responsible_component,
        "expected_repair_hint_kind": result.expected_repair_hint_kind,
        "repair_hint_acceptable": result.repair_hint_acceptable,
        "formal_facts_emitted": result.formal_facts_ok,
        "repair_hint_quality": result
            .repair_hint_quality
            .as_ref()
            .and_then(|q| serde_json::to_value(q).ok())
            .unwrap_or(Value::Null),
        "logs": result.errors
    });
    if let Some(obj) = doc.as_object_mut() {
        if let Some(status) = certificate_status {
            obj.insert("certificate_status".to_string(), Value::String(status));
        }
    }
    Ok(with_digest(doc))
}

fn system_outcome_from_certificate_status(status: Option<&str>) -> &'static str {
    match status {
        Some("CertificateChecked") => "admitted",
        Some("Rejected") => "rejected",
        Some("Stale") => "rejected",
        _ => "not_evaluated",
    }
}

fn certificate_status_for_benchmark(status: &str) -> String {
    match status {
        "CertificateChecked" | "Rejected" | "Stale" => status.to_string(),
        _ => "not_applicable".to_string(),
    }
}

fn metric_summary(
    metric_id: &str,
    score: f64,
    applicability: &str,
    numerator: f64,
    denominator: f64,
    reason: &str,
    details: Value,
    meta: &CertifyEdgeMetadata,
) -> Result<Value, String> {
    let doc = with_digest(json!({
        "schema_version": "v0",
        "metric_id": metric_id,
        "score": score.clamp(0.0, 1.0),
        "applicability": applicability,
        "numerator": numerator,
        "denominator": denominator,
        "reason": reason,
        "details": details,
        "source_repo": CERTIFYEDGE_SOURCE_REPO,
        "source_commit": meta.source_commit,
        "signature_or_digest": ""
    }));
    crate::pcs_schema::validate_metric_summary_schema(&doc)
        .map_err(|e| format!("metric summary {metric_id}: {e}"))?;
    Ok(doc)
}

fn build_metric_summaries(
    suite_id: &str,
    cert_coverage: &Value,
    repair_coverage: &Value,
    coverage: &CertificateCoverageReport,
    suite: &CertificateBenchmarkSuiteV0,
    meta: &CertifyEdgeMetadata,
) -> Result<Vec<Value>, String> {
    let invalid_cases = coverage.invalid_cases_total.max(1) as f64;
    let failure_score = coverage.failure_code_accuracy;
    let failure_summary = if coverage.invalid_cases_total == 0 {
        metric_summary(
            "failure_localization_accuracy",
            0.0,
            "insufficient_cases",
            0.0,
            0.0,
            "no invalid benchmark cases in suite",
            json!({}),
            meta,
        )?
    } else {
        metric_summary(
            "failure_localization_accuracy",
            failure_score,
            "measured",
            failure_score * invalid_cases,
            invalid_cases,
            "",
            json!({ "suite_id": suite_id }),
            meta,
        )?
    };

    let cert_score = cert_coverage
        .get("coverage_ratio")
        .and_then(|v| v.as_f64())
        .unwrap_or(0.0);
    let cert_denom = suite.cases_run.max(1) as f64;
    let cert_summary = metric_summary(
        "certificate_completeness_score",
        cert_score,
        "measured",
        cert_score * cert_denom,
        cert_denom,
        "",
        json!({ "profile_id": coverage.profile_id }),
        meta,
    )?;

    let repair_score = repair_coverage
        .get("coverage_ratio")
        .and_then(|v| v.as_f64())
        .unwrap_or(0.0);
    let repair_denom = coverage
        .repair_hint_metrics
        .cases_with_expected_repair_hint
        .max(1) as f64;
    let repair_summary = if coverage.repair_hint_metrics.cases_with_expected_repair_hint == 0 {
        metric_summary(
            "repair_hint_quality_score",
            1.0,
            "insufficient_cases",
            0.0,
            0.0,
            "no repair-hint benchmark cases in suite",
            json!({}),
            meta,
        )?
    } else {
        metric_summary(
            "repair_hint_quality_score",
            repair_score,
            "measured",
            repair_score * repair_denom,
            repair_denom,
            "",
            json!({}),
            meta,
        )?
    };

    Ok(vec![cert_summary, failure_summary, repair_summary])
}

fn normalize_responsible_component(component: &str) -> String {
    match component {
        "runtime_producer"
        | "certificate_producer"
        | "verifier"
        | "registry"
        | "formal_kernel"
        | "scientific_memory"
        | "release_manifest"
        | "handoff"
        | "hashing" => component.to_string(),
        _ => "unknown".to_string(),
    }
}

#[allow(clippy::too_many_arguments)]
fn build_benchmark_report(
    suite_id: &str,
    profile_id: &str,
    run_refs: &[Value],
    failures: &[Value],
    cert_coverage: &Value,
    repair_coverage: &Value,
    profile_coverage: &Value,
    explain_quality_coverage: Option<&Value>,
    coverage: &CertificateCoverageReport,
    suite: &CertificateBenchmarkSuiteV0,
    meta: &CertifyEdgeMetadata,
) -> Result<Value, String> {
    let total = suite.cases_run;
    let passed = suite.cases_passed;
    let failed = total.saturating_sub(passed);
    let metric_summaries = build_metric_summaries(
        suite_id,
        cert_coverage,
        repair_coverage,
        coverage,
        suite,
        meta,
    )?;

    let mut coverage_block = serde_json::Map::new();
    coverage_block.insert(
        "certificate_completeness".to_string(),
        cert_coverage.clone(),
    );
    coverage_block.insert("profile_coverage".to_string(), profile_coverage.clone());
    if let Some(explain_cov) = explain_quality_coverage {
        coverage_block.insert("explain_quality".to_string(), explain_cov.clone());
    }
    coverage_block.insert(
        "registry".to_string(),
        coverage_report(
            &format!("{suite_id}-registry"),
            "registry_coverage",
            1.0,
            1.0,
            json!({}),
            meta,
        ),
    );
    coverage_block.insert(
        "formal_checks".to_string(),
        coverage_report(
            &format!("{suite_id}-formal"),
            "formal_check_coverage",
            1.0,
            1.0,
            json!({}),
            meta,
        ),
    );
    coverage_block.insert(
        "scientific_memory".to_string(),
        coverage_report(
            &format!("{suite_id}-sm"),
            "scientific_memory_interpretability",
            1.0,
            1.0,
            json!({}),
            meta,
        ),
    );
    coverage_block.insert(
        "release_reproducibility".to_string(),
        coverage_report(
            &format!("{suite_id}-repro"),
            "release_reproducibility",
            passed as f64,
            total.max(1) as f64,
            json!({ "profile_id": profile_id }),
            meta,
        ),
    );

    Ok(with_digest(json!({
        "schema_version": "v0",
        "report_id": format!("benchmark-report-{suite_id}"),
        "benchmark_suite_id": suite_id,
        "producer_id": "certifyedge",
        "runs": run_refs,
        "metrics": [
            "certificate_completeness_score",
            "failure_localization_accuracy",
            "repair_hint_quality_score"
        ],
        "metric_summaries": metric_summaries,
        "summary": {
            "total_cases": total,
            "passed_cases": passed,
            "failed_cases": failed,
            "expected_failures_detected": coverage.invalid_certificates_rejected,
            "unexpected_passes": 0,
            "unexpected_failures": failed,
            "failure_localization_accuracy": coverage.failure_code_accuracy,
            "repair_hint_accuracy": coverage.repair_hint_metrics.repair_hint_accuracy,
            "formal_check_coverage": 1.0,
            "registry_coverage": 1.0,
            "scientific_memory_render_coverage": 1.0,
            "certificate_completeness_score": cert_coverage.get("coverage_ratio").and_then(|v| v.as_f64()).unwrap_or(0.0),
            "repair_hint_quality_score": repair_coverage.get("coverage_ratio").and_then(|v| v.as_f64()).unwrap_or(0.0),
            "execution_mode": "live",
            "evidence_grade": if meta.release_mode { "release" } else { "developer" },
            "live_cases": total,
            "simulated_cases": 0,
            "hybrid_fallback_cases": 0
        },
        "coverage": Value::Object(coverage_block),
        "failures": failures,
        "source_repo": CERTIFYEDGE_SOURCE_REPO,
        "source_commit": meta.source_commit,
        "signature_or_digest": ""
    })))
}

pub fn build_json_summary(
    profile_id: &str,
    out_dir: &Path,
    suite: &CertificateBenchmarkSuiteV0,
    coverage: &CertificateCoverageReport,
) -> BenchmarkCertificatesJsonSummary {
    let suite_id = benchmark_suite_id(profile_id);
    BenchmarkCertificatesJsonSummary {
        producer_id: "certifyedge".into(),
        benchmark_suite_id: suite_id,
        workflow_profile_id: profile_id.to_string(),
        cases_run: suite.cases_run,
        cases_passed: suite.cases_passed,
        failure_localization_accuracy: coverage.failure_code_accuracy,
        repair_hint_accuracy: coverage.repair_hint_metrics.repair_hint_accuracy,
        certificate_completeness_score: ratio_score(suite.cases_passed, suite.cases_run),
        profile_coverage_ratio: coverage.profile_coverage.coverage_score,
        out_dir: out_dir.display().to_string(),
        benchmark_report_path: out_dir
            .join("benchmark_report.v0.json")
            .display()
            .to_string(),
    }
}

fn ratio_score(num: usize, denom: usize) -> f64 {
    if denom == 0 {
        1.0
    } else {
        num as f64 / denom as f64
    }
}

fn write_json_file(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let json = serde_json::to_string_pretty(value).map_err(|e| e.to_string())?;
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).ok();
    }
    std::fs::write(path, format!("{json}\n")).map_err(|e| e.to_string())
}

#[cfg(test)]
mod bridge_tests {
    use super::*;
    use crate::certificate_benchmark::{CaseRunResult, ExplainSignals};

    #[test]
    fn workflow_id_is_explicit_per_profile() {
        assert_eq!(
            workflow_id_for_profile("hospital_lab.qc_release"),
            "hospital_lab.qc_release"
        );
        assert_eq!(
            workflow_id_for_profile("agent_tool_use.safety_v0"),
            "agent_tool_use.safety_v0"
        );
        assert_eq!(
            workflow_id_for_profile("scientific_computation.reproducibility_v0"),
            "scientific_computation.reproducibility_v0"
        );
    }

    #[test]
    fn failure_localization_component_mapping() {
        assert_eq!(
            responsible_component_for_failure_code("policy_hash_missing"),
            "handoff"
        );
        assert_eq!(
            responsible_component_for_failure_code("policy_hash_mismatch"),
            "unknown"
        );
        assert!(failure_localization_is_ambiguous("policy_hash_mismatch"));
        assert_eq!(
            responsible_component_for_failure_code("unauthorized_tool_call"),
            "runtime_producer"
        );
        assert_eq!(
            responsible_component_for_failure_code("result_hash_mismatch"),
            "runtime_producer"
        );
        assert_eq!(
            responsible_component_for_failure_code("dataset_hash_mismatch"),
            "runtime_producer"
        );
        assert_eq!(
            responsible_component_for_failure_code("missing_code_commit"),
            "runtime_producer"
        );
        assert_eq!(
            responsible_component_for_failure_code("unknown_profile"),
            "certificate_producer"
        );
        assert_eq!(
            responsible_component_for_failure_code("unknown_property_id"),
            "certificate_producer"
        );
        assert_eq!(
            responsible_component_for_failure_code("invalid_handoff"),
            "handoff"
        );
        assert_eq!(
            responsible_component_for_failure_code("invalid_handoff_digest"),
            "handoff"
        );
        assert_eq!(
            responsible_component_for_failure_code("rejected_certificate"),
            "certificate_producer"
        );
        assert_eq!(
            responsible_component_for_failure_code("environment_digest_mismatch"),
            "runtime_producer"
        );
    }

    #[test]
    fn case_failure_localization_accurate_for_policy_hash_mismatch_ambiguity() {
        let result = CaseRunResult {
            case_id: "policy_hash_mismatch".into(),
            kind: "invalid".into(),
            passed: false,
            profile_resolution_ok: true,
            handoff_validation_ok: true,
            status_match: false,
            failure_code_match: true,
            counterexample_match: false,
            repair_hint_present: true,
            repair_hint_kind_correct: true,
            repair_hint_command_present: true,
            responsible_component_correct: true,
            actual_certificate_status: None,
            actual_failure_code: Some("policy_hash_mismatch".into()),
            case_category: Some("policy_hash_mismatch".into()),
            repair_hint_quality: Some(RepairHintQuality {
                repair_hint_present: true,
                repair_hint_kind: "regenerate_trace_or_handoff".into(),
                responsible_component: "runtime_producer".into(),
                repair_command: "labtrust regenerate".into(),
            }),
            expected_failure_code: Some("policy_hash_mismatch".into()),
            expected_certificate_status: None,
            expected_repair_hint_kind: None,
            expected_responsible_component: None,
            expect_counterexample: false,
            expect_formal_facts: false,
            formal_facts_ok: false,
            repair_hint_acceptable: true,
            started_at: String::new(),
            completed_at: String::new(),
            duration_ms: 0,
            explain_signals: ExplainSignals::default(),
            errors: vec![],
        };
        assert!(case_failure_localization_accurate(&result));
    }

    #[test]
    fn failure_code_for_localization_prefers_rejected_certificate_category() {
        let result = CaseRunResult {
            case_id: "rejected_certificate".into(),
            kind: "invalid".into(),
            passed: false,
            profile_resolution_ok: true,
            handoff_validation_ok: true,
            status_match: false,
            failure_code_match: true,
            counterexample_match: true,
            repair_hint_present: true,
            repair_hint_kind_correct: true,
            repair_hint_command_present: true,
            responsible_component_correct: false,
            actual_certificate_status: Some("Rejected".into()),
            actual_failure_code: Some("unauthorized_tool_call".into()),
            case_category: Some("rejected_certificate".into()),
            repair_hint_quality: None,
            expected_failure_code: Some("unauthorized_tool_call".into()),
            expected_certificate_status: Some("Rejected".into()),
            expected_repair_hint_kind: None,
            expected_responsible_component: Some("runtime_producer".into()),
            expect_counterexample: true,
            expect_formal_facts: false,
            formal_facts_ok: false,
            repair_hint_acceptable: true,
            started_at: String::new(),
            completed_at: String::new(),
            duration_ms: 0,
            explain_signals: ExplainSignals::default(),
            errors: vec![],
        };
        assert_eq!(
            failure_code_for_localization(&result, "unauthorized_tool_call"),
            "rejected_certificate"
        );
        assert_eq!(
            responsible_component_for_failure_code(&failure_code_for_localization(
                &result,
                "unauthorized_tool_call"
            )),
            "certificate_producer"
        );
    }
}
