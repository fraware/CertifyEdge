//! pcs-core benchmark artifact validation after `benchmark certificates`.

#[path = "../common/support.rs"]
mod support;

use pcs_certificate::{
    validate_benchmark_report_schema, validate_benchmark_run_schema,
    validate_coverage_report_schema, validate_profile_coverage_report_schema,
};

use support::repo_root;

fn read_json(path: &std::path::Path) -> serde_json::Value {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| {
        panic!("read {}: {e}", path.display());
    });
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("parse {}: {e}", path.display()))
}

fn assert_pcs_outputs(out: &std::path::Path) {
    let report = read_json(&out.join("benchmark_report.v0.json"));
    validate_benchmark_report_schema(&report)
        .unwrap_or_else(|e| panic!("benchmark_report: {e}"));

    let cert_cov = read_json(&out.join("certificate_coverage_report.v0.json"));
    validate_coverage_report_schema(&cert_cov)
        .unwrap_or_else(|e| panic!("certificate_coverage_report: {e}"));
    assert_eq!(
        cert_cov.get("metric").and_then(|v| v.as_str()),
        Some("certificate_completeness")
    );

    let profile_cov = read_json(&out.join("profile_coverage_report.v0.json"));
    validate_profile_coverage_report_schema(&profile_cov)
        .unwrap_or_else(|e| panic!("profile_coverage_report: {e}"));

    let repair_cov = read_json(&out.join("repair_hint_quality_report.v0.json"));
    validate_coverage_report_schema(&repair_cov)
        .unwrap_or_else(|e| panic!("repair_hint_quality_report: {e}"));

    let runs = report
        .get("runs")
        .and_then(|v| v.as_array())
        .expect("benchmark_report.runs");
    assert!(!runs.is_empty(), "expected per-case run refs");
    for run_ref in runs {
        let path = run_ref
            .get("path")
            .and_then(|v| v.as_str())
            .expect("run path");
        let run_doc = read_json(&out.join(path));
        validate_benchmark_run_schema(&run_doc)
            .unwrap_or_else(|e| panic!("{path}: {e}"));
    }

    let manifest = out.join("repair_hint_manifest.v0.json");
    assert!(
        manifest.is_file(),
        "expected repair_hint_manifest.v0.json for pcs-bench scoring"
    );
}

#[test]
fn pcs_benchmark_outputs_validate_for_tool_use_suite() {
    let root = repo_root();
    let out = root
        .join("target")
        .join("certificate_benchmark")
        .join("tool_use_safety");
    pcs_certificate::run_certificate_benchmark(pcs_certificate::BenchmarkCertificatesOptions {
        profile_id: "agent_tool_use.safety_v0",
        cases_dir: &root.join("benchmarks/certificates/tool_use_safety"),
        out_dir: &out,
        certifyedge_root: &root,
        profile_registry: None,
        release_mode: true,
        json_summary: true,
    })
    .expect("run benchmark");
    assert_pcs_outputs(&out);
    assert!(
        out.join("benchmark_summary.v0.json").is_file(),
        "json-summary output missing"
    );
}
