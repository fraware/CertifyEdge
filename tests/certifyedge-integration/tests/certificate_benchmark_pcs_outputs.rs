//! pcs-core benchmark artifact validation after `benchmark certificates`.

#[path = "../common/support.rs"]
mod support;

use pcs_certificate::{
    run_certificate_benchmark, validate_pcs_benchmark_output_dir, BenchmarkCertificatesOptions,
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
        })
        .unwrap_or_else(|e| panic!("benchmark {profile_id}: {e}"));

        validate_pcs_benchmark_output_dir(&out)
            .unwrap_or_else(|e| panic!("pcs outputs {profile_id}: {e}"));

        let summary = outcome
            .json_summary
            .unwrap_or_else(|| panic!("json-summary missing for {profile_id}"));
        assert_eq!(summary.workflow_profile_id.as_str(), profile_id);
        assert_eq!(summary.producer_id, "certifyedge");
        assert!(
            out.join("benchmark_summary.v0.json").is_file(),
            "benchmark_summary.v0.json missing for {profile_id}"
        );
    }
}
