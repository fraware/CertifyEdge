//! pcs-core benchmark artifact validation after `benchmark certificates`.

#[path = "../common/support.rs"]
mod support;

use pcs_certificate::{
    run_certificate_benchmark, validate_pcs_benchmark_output_dir, validate_pcs_bench_ingest_schema,
    BenchmarkCertificatesOptions,
};

use support::repo_root;

const PROFILE_SUITES: &[(&str, &str)] = &[
    ("hospital_lab.qc_release", "hospital_lab_qc_release"),
    ("agent_tool_use.safety_v0", "tool_use_safety"),
    (
        "scientific_computation.reproducibility_v0",
        "computation_reproducibility",
    ),
];

#[test]
fn pcs_benchmark_outputs_validate_for_all_profile_suites() {
    let root = repo_root();
    for (profile_id, suite_dir) in PROFILE_SUITES {
        let out = root
            .join("target")
            .join("certificate_benchmark")
            .join(suite_dir);
        let outcome = run_certificate_benchmark(BenchmarkCertificatesOptions {
            profile_id,
            cases_dir: &root.join("benchmarks/certificates").join(suite_dir),
            out_dir: &out,
            certifyedge_root: &root,
            profile_registry: None,
            release_mode: true,
            json_summary: true,
            validate_pcs_core_output: None,
        })
        .unwrap_or_else(|e| panic!("benchmark {profile_id}: {e}"));

        validate_pcs_benchmark_output_dir(&out)
            .unwrap_or_else(|e| panic!("pcs outputs {profile_id}: {e}"));

        let ingest_text = std::fs::read_to_string(out.join("pcs_bench_ingest.v0.json"))
            .unwrap_or_else(|e| panic!("read pcs_bench_ingest: {e}"));
        let ingest: serde_json::Value =
            serde_json::from_str(&ingest_text).unwrap_or_else(|e| panic!("parse ingest: {e}"));
        validate_pcs_bench_ingest_schema(&ingest)
            .unwrap_or_else(|e| panic!("pcs_bench_ingest {profile_id}: {e}"));
        assert_eq!(
            ingest.get("workflow_id").and_then(|v| v.as_str()),
            Some(*profile_id),
            "ingest.workflow_id must match profile for {profile_id}"
        );
        assert!(
            ingest.get("coverage_reports").and_then(|v| v.as_array()).map(|a| !a.is_empty())
                == Some(true),
            "ingest.coverage_reports empty for {profile_id}"
        );
        assert!(
            !ingest
                .get("benchmark_runs")
                .and_then(|v| v.as_array())
                .map(|a| a.is_empty())
                .unwrap_or(true),
            "ingest.benchmark_runs empty for {profile_id}"
        );
        let artifact_refs = ingest
            .get("artifact_refs")
            .and_then(|v| v.as_array())
            .unwrap_or_else(|| panic!("ingest.artifact_refs missing for {profile_id}"));
        assert!(
            !artifact_refs.is_empty(),
            "ingest.artifact_refs empty for {profile_id}"
        );
        for (idx, artifact_ref) in artifact_refs.iter().enumerate() {
            pcs_certificate::validate_benchmark_artifact_ref_schema(artifact_ref)
                .unwrap_or_else(|e| panic!("artifact_refs[{idx}] {profile_id}: {e}"));
        }
        let localizations = ingest
            .get("failure_localization_reports")
            .and_then(|v| v.as_array())
            .map(|a| a.len())
            .unwrap_or(0);
        let invalid_cases = outcome.suite.coverage.invalid_cases_total;
        assert!(
            localizations >= invalid_cases,
            "failure_localization_reports ({localizations}) < invalid cases ({invalid_cases}) for {profile_id}"
        );
        assert!(
            out.join("failure_localization").is_dir(),
            "failure_localization/ sidecar dir missing for {profile_id}"
        );
        assert!(
            out.join("explain_quality").is_dir(),
            "explain_quality/ sidecar dir missing for {profile_id}"
        );
        assert!(
            ingest
                .get("profile_coverage_reports")
                .and_then(|v| v.as_array())
                .map(|a| a.len() == 1)
                == Some(true),
            "ingest.profile_coverage_reports must have one entry for {profile_id}"
        );
        for run in ingest
            .get("benchmark_runs")
            .and_then(|v| v.as_array())
            .into_iter()
            .flatten()
        {
            if run.get("observed_status").and_then(|v| v.as_str()) == Some("passed") {
                assert!(
                    run.get("observed_failure_code").map(|v| v.is_null()).unwrap_or(true),
                    "passed ingest run must have null observed_failure_code ({profile_id})"
                );
            }
        }
        for run in ingest
            .get("benchmark_runs")
            .and_then(|v| v.as_array())
            .into_iter()
            .flatten()
        {
            pcs_certificate::validate_benchmark_run_schema(run)
                .unwrap_or_else(|e| panic!("ingest BenchmarkRun.v0 {profile_id}: {e}"));
        }

        let summary = outcome
            .json_summary
            .unwrap_or_else(|| panic!("json-summary missing for {profile_id}"));
        assert_eq!(summary.workflow_profile_id.as_str(), *profile_id);
        assert_eq!(summary.producer_id.as_str(), "certifyedge");
        assert!(
            out.join("benchmark_summary.v0.json").is_file(),
            "benchmark_summary.v0.json missing for {profile_id}"
        );
        let runs_dir = out.join("runs");
        let run_sidecars = std::fs::read_dir(&runs_dir)
            .unwrap_or_else(|e| panic!("read runs/ for {profile_id}: {e}"))
            .filter_map(|e| e.ok())
            .filter(|e| {
                e.path()
                    .file_name()
                    .and_then(|n| n.to_str())
                    .is_some_and(|n| n.ends_with(".benchmark_run.v0.json"))
            })
            .count();
        assert_eq!(
            run_sidecars,
            ingest
                .get("benchmark_runs")
                .and_then(|v| v.as_array())
                .map(|a| a.len())
                .unwrap_or(0),
            "runs/*.benchmark_run.v0.json count mismatch for {profile_id}"
        );
        let ref_paths: std::collections::BTreeSet<String> = artifact_refs
            .iter()
            .filter_map(|r| r.get("path").and_then(|v| v.as_str()).map(str::to_string))
            .collect();
        assert!(
            ref_paths.contains("profile_coverage_report.v0.json"),
            "artifact_refs missing profile_coverage_report for {profile_id}"
        );
        assert!(
            ref_paths.contains("repair_hint_quality_report.v0.json"),
            "artifact_refs missing repair_hint_quality_report for {profile_id}"
        );
        assert!(
            ref_paths.iter().any(|p| p.starts_with("runs/")),
            "artifact_refs missing runs/ entries for {profile_id}"
        );
    }
}

#[test]
fn pcs_core_schemas_validate_benchmark_outputs_when_checkout_present() {
    let pcs_core = std::env::var("PCS_CORE_PATH")
        .or_else(|_| std::env::var("PCS_CORE_ROOT"))
        .ok()
        .map(std::path::PathBuf::from);
    let Some(pcs_core) = pcs_core.filter(|p| p.join("schemas").is_dir()) else {
        eprintln!("skip: PCS_CORE_PATH / PCS_CORE_ROOT with schemas/ not set");
        return;
    };

    let root = repo_root();
    for (profile_id, suite_dir) in PROFILE_SUITES {
        let out = root
            .join("target")
            .join("certificate_benchmark")
            .join(format!("pcs_core_schema_{suite_dir}"));
        run_certificate_benchmark(BenchmarkCertificatesOptions {
            profile_id,
            cases_dir: &root.join("benchmarks/certificates").join(suite_dir),
            out_dir: &out,
            certifyedge_root: &root,
            profile_registry: None,
            release_mode: true,
            json_summary: true,
            validate_pcs_core_output: Some(pcs_core.clone()),
        })
        .unwrap_or_else(|e| panic!("benchmark with pcs-core validation {profile_id}: {e}"));

        pcs_certificate::validate_pcs_core_output_dir(&pcs_core, &out).unwrap_or_else(|e| {
            panic!("pcs-core schema validation of benchmark outputs {profile_id}: {e}")
        });
    }
}

#[test]
fn benchmark_validate_output_cli_matches_library_gate() {
    let root = repo_root();
    let out = root.join("target/certificate_benchmark/cli_validate_output_v2");
    run_certificate_benchmark(BenchmarkCertificatesOptions {
        profile_id: "agent_tool_use.safety_v0",
        cases_dir: &root.join("benchmarks/certificates/tool_use_safety"),
        out_dir: &out,
        certifyedge_root: &root,
        profile_registry: None,
        release_mode: true,
        json_summary: true,
        validate_pcs_core_output: None,
    })
    .expect("benchmark for validate-output CLI");

    validate_pcs_benchmark_output_dir(&out)
        .unwrap_or_else(|e| panic!("validate-output library gate: {e}"));
}

#[test]
fn pcs_bench_ingest_passes_pcs_core_consumer_semantics_when_checkout_present() {
    let pcs_core = std::env::var("PCS_CORE_PATH")
        .or_else(|_| std::env::var("PCS_CORE_ROOT"))
        .ok()
        .map(std::path::PathBuf::from);
    let Some(pcs_core) = pcs_core.filter(|p| p.join("python/pcs_core").is_dir()) else {
        eprintln!("skip: PCS_CORE_PATH with python/pcs_core not set");
        return;
    };

    let root = repo_root();
    for (profile_id, suite_dir) in PROFILE_SUITES {
        let out = root
            .join("target")
            .join("certificate_benchmark")
            .join(format!("consumer_semantics_{suite_dir}"));
        run_certificate_benchmark(BenchmarkCertificatesOptions {
            profile_id,
            cases_dir: &root.join("benchmarks/certificates").join(suite_dir),
            out_dir: &out,
            certifyedge_root: &root,
            profile_registry: None,
            release_mode: true,
            json_summary: true,
            validate_pcs_core_output: None,
        })
        .unwrap_or_else(|e| panic!("benchmark for consumer semantics {profile_id}: {e}"));

        validate_pcs_bench_ingest_with_pcs_core_python(
            &pcs_core,
            &out.join("pcs_bench_ingest.v0.json"),
        );
    }
}

fn validate_pcs_bench_ingest_with_pcs_core_python(pcs_core: &std::path::Path, ingest: &std::path::Path) {
    let python_pkg = pcs_core.join("python");
    if !python_pkg.join("pcs_core").is_dir() {
        panic!(
            "pcs-core python package missing at {}",
            python_pkg.display()
        );
    }
    let script = format!(
        r#"
import json
import sys
from pathlib import Path
sys.path.insert(0, r"{python_pkg}")
from pcs_core.benchmark_validate import validate_pcs_bench_ingest_semantics
from pcs_core.validate import ValidationError, validate_file
path = Path(r"{ingest}")
errors = []
try:
    validate_file(path)
except ValidationError as exc:
    errors.append(str(exc))
    errors.extend(exc.errors)
doc = json.loads(path.read_text(encoding="utf-8"))
errors.extend(validate_pcs_bench_ingest_semantics(doc))
if errors:
    for err in errors:
        print(f"error: {{err}}", file=sys.stderr)
    raise SystemExit(1)
print(f"OK pcs-core ingest validation: {{path}}")
"#,
        python_pkg = python_pkg.display(),
        ingest = ingest.display(),
    );
    let python = std::env::var("PYTHON")
        .ok()
        .or_else(|| {
            if std::process::Command::new("python")
                .arg("--version")
                .status()
                .map(|s| s.success())
                .unwrap_or(false)
            {
                Some("python".into())
            } else {
                None
            }
        })
        .unwrap_or_else(|| "python3".into());
    let status = std::process::Command::new(&python)
    .args(["-c", &script])
    .status()
    .unwrap_or_else(|e| panic!("spawn python for ingest consumer validation: {e}"));
    assert!(
        status.success(),
        "pcs-core consumer ingest validation failed for {}",
        ingest.display()
    );
}
