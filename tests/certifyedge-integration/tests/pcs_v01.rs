use labtrust_adapter::{
    check_property, parse_and_validate_json, validate_trace, PropertyId, PropertySpec, TraceView,
    workflow_sim::{run_workflow, WorkflowStep},
};
use pcs_certificate::{build_certificate, verify_certificate_document, CertifyEdgeMetadata};
use std::path::PathBuf;

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
}

fn spec_path(name: &str) -> PathBuf {
    repo_root().join("templates/hospital_lab").join(name)
}

fn step(action: &str, actor_id: &str, role: &str, ts: &str) -> WorkflowStep {
    WorkflowStep {
        action: action.into(),
        actor_id: actor_id.into(),
        actor_role: role.into(),
        timestamp: ts.into(),
    }
}

fn valid_trace() -> labtrust_adapter::LabTrustTrace {
    run_workflow(
        "qc-release",
        "PCS-SAMPLE-001",
        &[
            step("accession_sample", "acc-tech-01", "accession_tech", "2026-01-15T08:00:00+00:00"),
            step("perform_qc", "qc-tech-01", "qc_tech", "2026-01-15T09:00:00+00:00"),
            step("record_analysis", "analyst-01", "analyst", "2026-01-15T10:00:00+00:00"),
            step("release_sample", "rel-mgr-01", "release_manager", "2026-01-15T11:00:00+00:00"),
        ],
    )
}

fn missing_qc_trace() -> labtrust_adapter::LabTrustTrace {
    run_workflow(
        "qc-release-invalid-missing-qc",
        "PCS-SAMPLE-002",
        &[
            step("accession_sample", "acc-tech-01", "accession_tech", "2026-01-15T08:00:00+00:00"),
            step("release_sample", "rel-mgr-01", "release_manager", "2026-01-15T10:00:00+00:00"),
        ],
    )
}

fn unauthorized_trace() -> labtrust_adapter::LabTrustTrace {
    run_workflow(
        "qc-release-invalid-unauthorized",
        "PCS-SAMPLE-003",
        &[
            step("accession_sample", "acc-tech-01", "accession_tech", "2026-01-15T08:00:00+00:00"),
            step("perform_qc", "qc-tech-01", "qc_tech", "2026-01-15T09:00:00+00:00"),
            step("record_analysis", "analyst-01", "analyst", "2026-01-15T10:00:00+00:00"),
            step("release_sample", "intern-01", "unauthorized_user", "2026-01-15T11:00:00+00:00"),
        ],
    )
}

#[test]
fn valid_labtrust_trace_accepted() {
    let trace = valid_trace();
    validate_trace(&trace).unwrap();
    let spec = PropertySpec::load(&spec_path("qc_release.stl")).unwrap();
    let result = check_property(&TraceView::from(trace), &spec);
    assert!(result.passed, "{:?}", result.counterexample);
}

#[test]
fn missing_qc_trace_rejected() {
    let trace = missing_qc_trace();
    validate_trace(&trace).unwrap();
    let spec = PropertySpec::load(&spec_path("qc_release.stl")).unwrap();
    let result = check_property(&TraceView::from(trace), &spec);
    assert!(!result.passed);
    assert_eq!(
        result.counterexample.as_ref().unwrap().reason,
        "release_before_qc"
    );
}

#[test]
fn unauthorized_release_trace_rejected() {
    let trace = unauthorized_trace();
    validate_trace(&trace).unwrap();
    let spec = PropertySpec::load(&spec_path("qc_release.stl")).unwrap();
    let result = check_property(&TraceView::from(trace), &spec);
    assert!(!result.passed);
    assert_eq!(
        result.counterexample.as_ref().unwrap().reason,
        "unauthorized_release"
    );
}

#[test]
fn malformed_trace_rejected() {
    let mut trace = valid_trace();
    trace.trace_hash = "sha256:0000000000000000000000000000000000000000000000000000000000000000".into();
    assert!(validate_trace(&trace).is_err());
}

#[test]
fn trace_hash_stable() {
    let a = valid_trace();
    let b = valid_trace();
    assert_eq!(a.trace_hash, b.trace_hash);
}

#[test]
fn spec_hash_stable() {
    let spec = PropertySpec::load(&spec_path("qc_release.stl")).unwrap();
    let h1 = pcs_certificate::hash::spec_hash(&spec.raw_text, spec.property_id.as_str());
    let h2 = pcs_certificate::hash::spec_hash(&spec.raw_text, spec.property_id.as_str());
    assert_eq!(h1, h2);
}

#[test]
fn certificate_digest_verifies() {
    let trace = valid_trace();
    let spec = PropertySpec::load(&spec_path("qc_release.stl")).unwrap();
    let check = check_property(&TraceView::from(trace.clone()), &spec);
    let outcome = build_certificate(
        &trace.trace_hash,
        &spec,
        &check,
        &CertifyEdgeMetadata::default(),
        None,
    );
    let json = serde_json::to_string_pretty(&outcome.certificate).unwrap();
    verify_certificate_document(&json, Some(&trace.trace_hash)).unwrap();
}

#[test]
fn counterexample_emitted_for_rejected() {
    let trace = missing_qc_trace();
    let spec = PropertySpec::load(&spec_path("no_release_before_qc.stl")).unwrap();
    let result = check_property(&TraceView::from(trace), &spec);
    let cx = result.counterexample.expect("counterexample");
    assert!(!cx.counterexample_id.is_empty());
    assert_eq!(cx.property_id, PropertyId::NoReleaseBeforeQc.as_str());
}

#[test]
fn labtrust_trace_hash_matches_gym_export() {
    let rust = valid_trace();
    let gym_root = std::env::var("LABTRUST_GYM_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from(r"C:\Users\mateo\LabTrust-Gym"));
    let trace_path = gym_root.join("runs/qc-release/trace.json");
    if !trace_path.exists() {
        return;
    }
    let text = std::fs::read_to_string(trace_path).unwrap();
    let gym: labtrust_adapter::LabTrustTrace =
        labtrust_adapter::parse_and_validate_json(&text).unwrap();
    assert_eq!(
        rust.trace_hash, gym.trace_hash,
        "trace_hash must match LabTrust-Gym export"
    );
}

#[test]
fn fixture_traces_roundtrip_json() {
    let fixtures = repo_root().join("tests/labtrust");
    for name in [
        "valid_trace.json",
        "invalid_missing_qc_trace.json",
        "invalid_unauthorized_trace.json",
    ] {
        let path = fixtures.join(name);
        if !path.exists() {
            continue;
        }
        let text = std::fs::read_to_string(&path).unwrap();
        parse_and_validate_json(&text).unwrap();
    }
}
