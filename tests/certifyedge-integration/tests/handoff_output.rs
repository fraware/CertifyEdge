//! Phase 2: outbound `HandoffManifest.v0` after certificate emission.

#[path = "../common/support.rs"]
mod support;

#[path = "../common/handoff_fixtures.rs"]
mod handoff_fixtures;

use pcs_certificate::{
    load_handoff_manifest, validate_handoff_manifest_schema, HANDOFF_KIND_CERTIFICATE_TO_BUNDLE,
};
use serde_json::Value;

use handoff_fixtures::{handoff_workdir, write_runtime_handoff};
use support::{certifyedge_cmd, pcs_core_rc_constants, repo_root, with_source_commit};

fn run_handoff_emit(work: &std::path::Path) -> std::path::PathBuf {
    std::fs::create_dir_all(work).unwrap();
    let handoff_in = write_runtime_handoff(work, |_| {});
    let cert_out = work.join("trace_certificate.json");
    let handoff_out = work.join("certifyedge_to_labtrust_handoff.json");

    with_source_commit(pcs_core_rc_constants().source_commit, || {
        certifyedge_cmd()
            .arg("--release-mode")
            .args([
                "emit-pcs-certificate",
                "--handoff",
                handoff_in.to_str().unwrap(),
                "--out",
                cert_out.to_str().unwrap(),
                "--handoff-out",
                handoff_out.to_str().unwrap(),
            ])
            .env("CERTIFYEDGE_ROOT", repo_root())
            .assert()
            .success();
    });
    handoff_out
}

#[test]
fn test_certificate_handoff_validates_against_pcs_core() {
    let work = handoff_workdir("handoff_out_validate");
    let handoff_out = run_handoff_emit(&work);
    let value: Value =
        serde_json::from_str(&std::fs::read_to_string(&handoff_out).unwrap()).unwrap();
    validate_handoff_manifest_schema(&value).unwrap();
    load_handoff_manifest(&handoff_out).unwrap();
}

#[test]
fn test_certificate_handoff_certificate_id_matches_certificate() {
    let work = handoff_workdir("handoff_out_cert_id");
    run_handoff_emit(&work);
    let cert: Value = serde_json::from_str(
        &std::fs::read_to_string(work.join("trace_certificate.json")).unwrap(),
    )
    .unwrap();
    let handoff =
        load_handoff_manifest(&work.join("certifyedge_to_labtrust_handoff.json")).unwrap();
    assert_eq!(
        handoff.invariants["certificate_id"],
        cert["certificate_id"].as_str().unwrap()
    );
}

#[test]
fn test_certificate_handoff_trace_hash_matches_certificate() {
    let work = handoff_workdir("handoff_out_trace_hash");
    run_handoff_emit(&work);
    let cert: Value = serde_json::from_str(
        &std::fs::read_to_string(work.join("trace_certificate.json")).unwrap(),
    )
    .unwrap();
    let handoff =
        load_handoff_manifest(&work.join("certifyedge_to_labtrust_handoff.json")).unwrap();
    assert_eq!(
        handoff.invariants["trace_hash"],
        cert["trace_hash"].as_str().unwrap()
    );
}

#[test]
fn test_certificate_handoff_status_certificate_checked() {
    let work = handoff_workdir("handoff_out_status");
    run_handoff_emit(&work);
    let handoff =
        load_handoff_manifest(&work.join("certifyedge_to_labtrust_handoff.json")).unwrap();
    assert_eq!(handoff.handoff_kind, HANDOFF_KIND_CERTIFICATE_TO_BUNDLE);
    assert_eq!(handoff.invariants["status"], "CertificateChecked");
}
