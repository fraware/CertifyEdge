//! pcs-core benchmark artifact validation after `benchmark certificates`.

#[path = "../common/support.rs"]
mod support;

use pcs_certificate::{
    run_certificate_benchmark, validate_pcs_benchmark_output_dir, validate_pcs_bench_ingest_schema,
    BenchmarkCertificatesOptions,
};

use support::{certifyedge_cmd, repo_root};

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
    let out = root.join("target/certificate_benchmark/tool_use_safety");
    run_certificate_benchmark(BenchmarkCertificatesOptions {
        profile_id: "agent_tool_use.safety_v0",
        cases_dir: &root.join("benchmarks/certificates/tool_use_safety"),
        out_dir: &out,
        certifyedge_root: &root,
        profile_registry: None,
        release_mode: true,
        json_summary: true,
        validate_pcs_core_output: Some(pcs_core.clone()),
    })
    .expect("benchmark with pcs-core validation");

    pcs_certificate::validate_pcs_core_output_dir(&pcs_core, &out)
        .expect("pcs-core schema validation of benchmark outputs");
}

#[test]
fn benchmark_validate_output_cli_matches_library_gate() {
    let root = repo_root();
    let out = root.join("target/certificate_benchmark/cli_validate_output");
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

    certifyedge_cmd()
        .args([
            "benchmark",
            "validate-output",
            "--out",
            out.to_str().expect("utf-8 out path"),
        ])
        .assert()
        .success();
}
