//! Phase 2: emit TraceCertificate.v0 from `HandoffManifest.v0` input.

#[path = "../common/support.rs"]
mod support;

#[path = "../common/handoff_fixtures.rs"]
mod handoff_fixtures;

use pcs_certificate::{
    load_handoff_manifest, plan_emit_from_handoff, validate_handoff_manifest_schema,
    ZERO_SOURCE_COMMIT,
};
use serde_json::Value;

use handoff_fixtures::{handoff_workdir, write_runtime_handoff, write_runtime_handoff_with_trace};
use support::{
    certifyedge_cmd, labtrust_release_fixture, pcs_core_rc_constants, repo_root,
    runbook_spec_authorized_release_only, runbook_spec_qc_release, with_source_commit,
};

#[test]
fn test_emit_certificate_from_valid_handoff_manifest() {
    let work = handoff_workdir("handoff_emit_ok");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_runtime_handoff(&work, |_| {});
    let cert_out = work.join("trace_certificate.json");

    with_source_commit(pcs_core_rc_constants().source_commit, || {
        certifyedge_cmd()
            .arg("--release-mode")
            .args([
                "emit-pcs-certificate",
                "--handoff",
                handoff_path.to_str().unwrap(),
                "--out",
                cert_out.to_str().unwrap(),
            ])
            .env("CERTIFYEDGE_ROOT", repo_root())
            .assert()
            .success();
    });

    let rc = pcs_core_rc_constants();
    let cert: Value = serde_json::from_str(&std::fs::read_to_string(&cert_out).unwrap()).unwrap();
    assert_eq!(cert["trace_hash"].as_str().unwrap(), rc.trace_hash);
    assert_eq!(cert["source_commit"].as_str().unwrap(), rc.source_commit);
    assert_eq!(cert["status"].as_str().unwrap(), "CertificateChecked");
}

#[test]
fn test_emit_certificate_rejects_wrong_to_component() {
    let work = handoff_workdir("handoff_emit_wrong_to");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_runtime_handoff(&work, |h| {
        h.to_component = "Provability Fabric".to_string();
    });

    certifyedge_cmd()
        .args([
            "emit-pcs-certificate",
            "--handoff",
            handoff_path.to_str().unwrap(),
            "--out",
            work.join("trace_certificate.json").to_str().unwrap(),
        ])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .failure();
}

#[test]
fn test_emit_certificate_rejects_missing_trace_artifact() {
    let work = handoff_workdir("handoff_emit_no_trace");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_runtime_handoff(&work, |h| {
        h.input_artifacts.remove("trace.json");
    });

    certifyedge_cmd()
        .args([
            "emit-pcs-certificate",
            "--handoff",
            handoff_path.to_str().unwrap(),
            "--out",
            work.join("trace_certificate.json").to_str().unwrap(),
        ])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .failure();
}

#[test]
fn test_emit_certificate_rejects_trace_hash_mismatch() {
    let work = handoff_workdir("handoff_emit_bad_hash");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_runtime_handoff(&work, |h| {
        h.invariants.insert(
            "trace_hash".to_string(),
            "sha256:1111111111111111111111111111111111111111111111111111111111111111".to_string(),
        );
    });

    certifyedge_cmd()
        .args([
            "emit-pcs-certificate",
            "--handoff",
            handoff_path.to_str().unwrap(),
            "--out",
            work.join("trace_certificate.json").to_str().unwrap(),
        ])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .failure();
}

#[test]
fn test_emit_certificate_rejects_property_id_mismatch() {
    let work = handoff_workdir("handoff_emit_property_mismatch");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_runtime_handoff(&work, |_| {});
    let handoff = load_handoff_manifest(&handoff_path).unwrap();
    let err = plan_emit_from_handoff(
        &handoff_path,
        &handoff,
        &repo_root(),
        Some(&runbook_spec_authorized_release_only()),
        None,
        None,
        false,
    );
    assert!(err.is_err(), "expected property_id mismatch: {err:?}");
    assert!(
        err.unwrap_err().contains("property_id mismatch"),
        "unexpected error"
    );
}

#[test]
fn test_emit_certificate_rejects_missing_property_id() {
    let work = handoff_workdir("handoff_emit_no_property");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_runtime_handoff(&work, |h| {
        h.invariants.remove("property_id");
    });

    certifyedge_cmd()
        .args([
            "emit-pcs-certificate",
            "--handoff",
            handoff_path.to_str().unwrap(),
            "--out",
            work.join("trace_certificate.json").to_str().unwrap(),
        ])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .failure();
}

#[test]
fn test_reject_handoff_placeholder_source_commit_in_release_mode() {
    let work = handoff_workdir("handoff_emit_placeholder");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_runtime_handoff(&work, |h| {
        h.source_commit = ZERO_SOURCE_COMMIT.to_string();
    });

    certifyedge_cmd()
        .arg("--release-mode")
        .args([
            "emit-pcs-certificate",
            "--handoff",
            handoff_path.to_str().unwrap(),
            "--out",
            work.join("trace_certificate.json").to_str().unwrap(),
        ])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .failure();
}

#[test]
fn test_emit_rejected_certificate_and_handoff_from_invalid_trace() {
    let work = handoff_workdir("handoff_emit_rejected");
    std::fs::create_dir_all(&work).unwrap();
    let invalid = repo_root().join("tests/labtrust/invalid_missing_qc_trace.json");
    let handoff_path = write_runtime_handoff_with_trace(&work, invalid, |_| {});
    let cert_out = work.join("trace_certificate.json");
    let handoff_out = work.join("certifyedge_to_labtrust_handoff.json");
    let cx_out = work.join("counterexample.json");

    certifyedge_cmd()
        .args([
            "emit-pcs-certificate",
            "--handoff",
            handoff_path.to_str().unwrap(),
            "--out",
            cert_out.to_str().unwrap(),
            "--counterexample-out",
            cx_out.to_str().unwrap(),
            "--handoff-out",
            handoff_out.to_str().unwrap(),
        ])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .success();

    let cert: Value = serde_json::from_str(&std::fs::read_to_string(&cert_out).unwrap()).unwrap();
    assert_eq!(cert["status"].as_str().unwrap(), "Rejected");
    assert!(cx_out.is_file(), "counterexample.json must be written");

    let outbound = load_handoff_manifest(&handoff_out).unwrap();
    assert_eq!(outbound.invariants["status"], "Rejected");
    assert!(
        !outbound
            .expected_outputs
            .contains_key("science_claim_bundle.certified.json"),
        "rejected handoff must not promise certified bundle"
    );
    assert!(outbound
        .expected_outputs
        .contains_key("counterexample.json"));
}

/// Regenerate `tests/fixtures/handoff/labtrust_to_certifyedge_handoff.json` from RC trace.
#[test]
#[ignore]
fn write_labtrust_handoff_fixture() {
    let dir = repo_root().join("tests/fixtures/handoff");
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::copy(
        labtrust_release_fixture("trace.json"),
        dir.join("trace.json"),
    )
    .unwrap();
    write_runtime_handoff(&dir, |_| {});
    eprintln!(
        "wrote {}",
        dir.join("labtrust_to_certifyedge_handoff.json").display()
    );
}

#[test]
fn test_emit_from_committed_handoff_fixture() {
    let handoff = repo_root().join("tests/fixtures/handoff/labtrust_to_certifyedge_handoff.json");
    assert!(
        handoff.is_file(),
        "missing committed handoff fixture; run: bash scripts/write-labtrust-handoff-fixture.sh"
    );
    let work = handoff_workdir("handoff_committed_fixture");
    std::fs::create_dir_all(&work).unwrap();
    std::fs::copy(
        labtrust_release_fixture("trace.json"),
        work.join("trace.json"),
    )
    .unwrap();
    std::fs::copy(&handoff, work.join("labtrust_to_certifyedge_handoff.json")).unwrap();
    let cert_out = work.join("trace_certificate.json");

    with_source_commit(pcs_core_rc_constants().source_commit, || {
        certifyedge_cmd()
            .arg("--release-mode")
            .args([
                "emit-pcs-certificate",
                "--handoff",
                work.join("labtrust_to_certifyedge_handoff.json")
                    .to_str()
                    .unwrap(),
                "--out",
                cert_out.to_str().unwrap(),
            ])
            .env("CERTIFYEDGE_ROOT", repo_root())
            .assert()
            .success();
    });

    certifyedge_cmd()
        .args([
            "verify-certificate",
            cert_out.to_str().unwrap(),
            "--trace",
            work.join("trace.json").to_str().unwrap(),
        ])
        .assert()
        .success();
}

#[test]
fn test_handoff_input_validates_against_pcs_core_schema() {
    let work = handoff_workdir("handoff_schema");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_runtime_handoff(&work, |_| {});
    let value: Value =
        serde_json::from_str(&std::fs::read_to_string(&handoff_path).unwrap()).unwrap();
    validate_handoff_manifest_schema(&value).unwrap();
    let handoff = load_handoff_manifest(&handoff_path).unwrap();
    plan_emit_from_handoff(
        &handoff_path,
        &handoff,
        &repo_root(),
        Some(&runbook_spec_qc_release()),
        None,
        None,
        false,
    )
    .unwrap();
}
