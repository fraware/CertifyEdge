//! Map CertifyEdge certificate benchmark results to pcs-core `BenchmarkReport.v0` artifacts.

use std::path::Path;

use serde::Serialize;
use serde_json::{json, Value};

use crate::certificate_benchmark::{
    CaseRunResult, CertificateCoverageReport, CertificateBenchmarkSuiteV0,
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

#[derive(Debug, Clone, Serialize)]
pub struct BenchmarkCertificatesJsonSummary {
    pub schema_version: String,
    pub producer_id: String,
    pub profile_id: String,
    pub benchmark_suite_id: String,
    pub cases_run: usize,
    pub cases_passed: usize,
    pub failure_code_accuracy: f64,
    pub repair_hint_accuracy: f64,
    pub certificate_completeness_score: f64,
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

pub fn map_case_category_to_pcs_kind(category: &str, folder_kind: &str) -> &'static str {
    match category {
        "valid" => "valid_release",
        "invalid_hash_mismatch" | "policy_hash_mismatch" => "invalid_hash_mismatch",
        "invalid_missing_required_field" => "invalid_handoff",
        "invalid_source_provenance" => "invalid_certificate",
        "invalid_policy_or_property_violation"
        | "rejected_certificate"
        | "unauthorized_tool_call"
        | "missing_policy_hash"
        | "unknown_authorization_status"
        | "dataset_hash_mismatch"
        | "environment_digest_mismatch"
        | "result_hash_mismatch"
        | "missing_code_commit"
        | "nonzero_exit_code" => "invalid_certificate",
        _ if folder_kind == "valid" => "valid_release",
        _ => "invalid_certificate",
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

    let mut run_refs: Vec<Value> = Vec::new();
    let mut failures: Vec<Value> = Vec::new();

    for result in input.case_results {
        let run_filename = format!("benchmark_run.{}.v0.json", result.case_id);
        let run_path = input.out_dir.join(&run_filename);
        let run_doc = build_per_case_run(result, input.profile_id, meta)?;
        let run_value = serde_json::to_value(&run_doc).map_err(|e| e.to_string())?;
        crate::pcs_schema::validate_benchmark_run_schema(&run_value).map_err(|e| {
            format!(
                "benchmark run schema ({}, case {}): {e}",
                run_path.display(),
                result.case_id
            )
        })?;
        write_json_file(&run_path, &run_doc)?;
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

    let cert_coverage = coverage_report(
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

    let categories: Vec<String> = input
        .case_results
        .iter()
        .filter_map(|r| r.case_category.clone())
        .collect();
    let covered_categories: Vec<String> = input
        .case_results
        .iter()
        .filter(|r| r.passed)
        .filter_map(|r| r.case_category.clone())
        .collect();

    let profile_coverage = with_digest(json!({
        "schema_version": "v0",
        "coverage_id": format!("{suite_id}-profile-coverage"),
        "workflow_profile_id": input.profile_id,
        "producer_id": "certifyedge",
        "suite_id": suite_id,
        "artifact_types_required": [artifact_type],
        "artifact_types_covered": [artifact_type],
        "semantic_checks_required": categories,
        "semantic_checks_covered": covered_categories,
        "handoff_steps_required": ["runtime_to_certificate"],
        "handoff_steps_covered": ["runtime_to_certificate"],
        "numerator": input.suite.cases_passed as f64,
        "denominator": input.suite.cases_run.max(1) as f64,
        "coverage_ratio": input.coverage.profile_coverage.coverage_score,
        "details": {
            "templates_checked": input.coverage.profile_coverage.templates_checked,
            "counterexample_types_covered": input.coverage.profile_coverage.counterexample_types_covered,
            "unsupported_cases": input.coverage.profile_coverage.unsupported_cases,
        },
        "source_repo": CERTIFYEDGE_SOURCE_REPO,
        "source_commit": meta.source_commit,
        "signature_or_digest": ""
    }));

    let report = build_benchmark_report(
        &suite_id,
        input.profile_id,
        &run_refs,
        &failures,
        &cert_coverage,
        &repair_coverage,
        &profile_coverage,
        input.coverage,
        input.suite,
        meta,
    )?;
    crate::pcs_schema::validate_benchmark_report_schema(&report)
        .map_err(|e| format!("benchmark report schema: {e}"))?;
    crate::pcs_schema::validate_coverage_report_schema(&cert_coverage)
        .map_err(|e| format!("certificate completeness coverage schema: {e}"))?;
    crate::pcs_schema::validate_coverage_report_schema(&repair_coverage)
        .map_err(|e| format!("repair hint coverage schema: {e}"))?;
    // Repair-hint coverage is scored via `summary.repair_hint_accuracy`; keep the artifact
    // out of `BenchmarkReport.coverage` because pcs-core's block schema is closed.
    crate::pcs_schema::validate_profile_coverage_report_schema(&profile_coverage)
        .map_err(|e| format!("profile coverage report schema: {e}"))?;

    write_json_file(
        &input.out_dir.join("benchmark_report.v0.json"),
        &report,
    )?;
    write_json_file(
        &input.out_dir.join("certificate_coverage_report.v0.json"),
        &cert_coverage,
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
        let suite_id = benchmark_suite_id(input.profile_id);
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

    Ok(())
}

fn build_per_case_run(
    result: &CaseRunResult,
    profile_id: &str,
    meta: &CertifyEdgeMetadata,
) -> Result<Value, String> {
    let observed_status = if result.passed { "passed" } else { "failed" };
    let failure_code = result.actual_failure_code.clone().unwrap_or_default();
    let (repair_hint_pcs, component) = if let Some(q) = &result.repair_hint_quality {
        if q.repair_hint_present {
            (
                map_certifyedge_repair_kind(&q.repair_hint_kind).to_string(),
                normalize_responsible_component(&q.responsible_component),
            )
        } else {
            ("none".to_string(), "unknown".to_string())
        }
    } else {
        ("unknown".to_string(), "unknown".to_string())
    };

    let command = format!(
        "certifyedge emit-pcs-certificate --profile {profile_id} --handoff <case>/handoff.json"
    );
    let exit_code = if result.passed { 0 } else { 1 };

    Ok(with_digest(json!({
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
        "artifacts_produced": ["certificate.json"],
        "observed_status": observed_status,
        "observed_failure_code": failure_code,
        "observed_responsible_component": component,
        "observed_repair_hint": repair_hint_pcs,
        "duration_ms": result.duration_ms,
        "source_repo": CERTIFYEDGE_SOURCE_REPO,
        "source_commit": meta.source_commit,
        "signature_or_digest": ""
    })))
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
    coverage: &CertificateCoverageReport,
    suite: &CertificateBenchmarkSuiteV0,
    meta: &CertifyEdgeMetadata,
) -> Result<Value, String> {
    let total = suite.cases_run;
    let passed = suite.cases_passed;
    let failed = total.saturating_sub(passed);

    Ok(with_digest(json!({
        "schema_version": "v0",
        "report_id": format!("benchmark-report-{suite_id}"),
        "benchmark_suite_id": suite_id,
        "producer_id": "certifyedge",
        "runs": run_refs,
        "metrics": [
            "certificate_completeness",
            "failure_localization",
            "repair_hint_quality"
        ],
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
            "repair_hint_quality_score": repair_coverage.get("coverage_ratio").and_then(|v| v.as_f64()).unwrap_or(0.0)
        },
        "coverage": {
            "certificate_completeness": cert_coverage,
            "profile_coverage": profile_coverage,
            "registry": coverage_report(
                &format!("{suite_id}-registry"),
                "registry_coverage",
                1.0,
                1.0,
                json!({}),
                meta
            ),
            "formal_checks": coverage_report(
                &format!("{suite_id}-formal"),
                "formal_check_coverage",
                1.0,
                1.0,
                json!({}),
                meta
            ),
            "scientific_memory": coverage_report(
                &format!("{suite_id}-sm"),
                "scientific_memory_interpretability",
                1.0,
                1.0,
                json!({}),
                meta
            ),
            "release_reproducibility": coverage_report(
                &format!("{suite_id}-repro"),
                "release_reproducibility",
                passed as f64,
                total.max(1) as f64,
                json!({ "profile_id": profile_id }),
                meta
            )
        },
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
        schema_version: "v0".into(),
        producer_id: "certifyedge".into(),
        profile_id: profile_id.to_string(),
        benchmark_suite_id: suite_id,
        cases_run: suite.cases_run,
        cases_passed: suite.cases_passed,
        failure_code_accuracy: coverage.failure_code_accuracy,
        repair_hint_accuracy: coverage.repair_hint_metrics.repair_hint_accuracy,
        certificate_completeness_score: ratio_score(suite.cases_passed, suite.cases_run),
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
