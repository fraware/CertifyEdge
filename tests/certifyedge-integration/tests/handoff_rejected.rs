//! Phase 2: rejected-certificate outbound handoff conformance.

#[path = "../common/support.rs"]
mod support;

#[path = "../common/handoff_fixtures.rs"]
mod handoff_fixtures;

use pcs_certificate::{
    load_handoff_manifest, validate_handoff_manifest_schema, HANDOFF_KIND_CERTIFICATE_TO_BUNDLE,
};
use serde_json::Value;

use handoff_fixtures::{handoff_workdir, write_runtime_handoff_with_trace};
use support::{certifyedge_cmd, repo_root};

fn run_rejected_handoff_emit(work: &std::path::Path) {
    std::fs::create_dir_all(work).unwrap();
    let invalid = repo_root().join("tests/labtrust/invalid_missing_qc_trace.json");
    let handoff_path = write_runtime_handoff_with_trace(work, invalid, |_| {});
    certifyedge_cmd()
        .args([
            "emit-pcs-certificate",
            "--handoff",
            handoff_path.to_str().unwrap(),
            "--out",
            work.join("trace_certificate.json").to_str().unwrap(),
            "--counterexample-out",
            work.join("counterexample.json").to_str().unwrap(),
            "--handoff-out",
            work.join("certifyedge_to_labtrust_handoff.json")
                .to_str()
                .unwrap(),
        ])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .success();
}

#[test]
fn test_rejected_certificate_handoff_has_status_rejected() {
    let work = handoff_workdir("handoff_reject_status");
    run_rejected_handoff_emit(&work);
    let handoff =
        load_handoff_manifest(&work.join("certifyedge_to_labtrust_handoff.json")).unwrap();
    assert_eq!(handoff.invariants["status"], "Rejected");
    assert_eq!(handoff.handoff_kind, HANDOFF_KIND_CERTIFICATE_TO_BUNDLE);
}

#[test]
fn test_rejected_certificate_handoff_has_no_certified_bundle_expected_output() {
    let work = handoff_workdir("handoff_reject_no_bundle");
    run_rejected_handoff_emit(&work);
    let handoff =
        load_handoff_manifest(&work.join("certifyedge_to_labtrust_handoff.json")).unwrap();
    assert!(!handoff
        .expected_outputs
        .contains_key("science_claim_bundle.certified.json"));
}

#[test]
fn test_rejected_certificate_handoff_references_counterexample_when_available() {
    let work = handoff_workdir("handoff_reject_cx");
    run_rejected_handoff_emit(&work);
    assert!(work.join("counterexample.json").is_file());
    let handoff =
        load_handoff_manifest(&work.join("certifyedge_to_labtrust_handoff.json")).unwrap();
    assert!(handoff.expected_outputs.contains_key("counterexample.json"));
}

#[test]
fn test_rejected_certificate_handoff_validates_against_pcs_core() {
    let work = handoff_workdir("handoff_reject_validate");
    run_rejected_handoff_emit(&work);
    let path = work.join("certifyedge_to_labtrust_handoff.json");
    let value: Value = serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
    validate_handoff_manifest_schema(&value).unwrap();
    load_handoff_manifest(&path).unwrap();
}

#[test]
fn test_rejected_certificate_handoff_blocks_certified_bundle() {
    let work = handoff_workdir("handoff_reject_blocks_bundle");
    run_rejected_handoff_emit(&work);
    let handoff =
        load_handoff_manifest(&work.join("certifyedge_to_labtrust_handoff.json")).unwrap();
    assert_eq!(handoff.invariants["status"], "Rejected");
    assert!(
        !handoff
            .expected_outputs
            .contains_key("science_claim_bundle.certified.json"),
        "rejected handoff must block certified bundle promotion"
    );
}
