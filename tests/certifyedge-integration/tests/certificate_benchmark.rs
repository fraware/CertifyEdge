//! Profile-driven certificate benchmark runner (all committed suites).

#[path = "../common/support.rs"]
mod support;

use pcs_certificate::{run_certificate_benchmark, BenchmarkCertificatesOptions};

use support::repo_root;

fn run_suite(profile_id: &str, cases_subdir: &str) {
    let root = repo_root();
    let cases = root.join("benchmarks/certificates").join(cases_subdir);
    assert!(
        cases.is_dir(),
        "missing benchmark cases at {}; run scripts/generate-certificate-benchmark-cases.py",
        cases.display()
    );
    let out = root
        .join("target")
        .join("certificate_benchmark")
        .join(cases_subdir);
    let run = run_certificate_benchmark(BenchmarkCertificatesOptions {
        profile_id,
        cases_dir: &cases,
        out_dir: &out,
        certifyedge_root: &root,
        profile_registry: None,
        release_mode: true,
    })
    .unwrap_or_else(|e| panic!("benchmark {profile_id}: {e}"));
    assert_eq!(
        run.cases_passed, run.cases_run,
        "benchmark {profile_id}: {}/{} passed; see {}/benchmark_run.v0.json",
        run.cases_passed,
        run.cases_run,
        out.display()
    );
}

#[test]
fn certificate_benchmark_hospital_lab_qc_release() {
    run_suite(
        "hospital_lab.qc_release",
        "hospital_lab_qc_release",
    );
}

#[test]
fn certificate_benchmark_tool_use_safety() {
    run_suite("agent_tool_use.safety_v0", "tool_use_safety");
}

#[test]
fn certificate_benchmark_computation_reproducibility() {
    run_suite(
        "scientific_computation.reproducibility_v0",
        "computation_reproducibility",
    );
}
