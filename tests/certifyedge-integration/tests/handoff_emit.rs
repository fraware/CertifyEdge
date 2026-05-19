//! Phase 2: emit TraceCertificate.v0 from `HandoffManifest.v0` input.

#[path = "../common/support.rs"]
mod support;

#[path = "../common/handoff_fixtures.rs"]
mod handoff_fixtures;

use pcs_certificate::{
    load_handoff_manifest, plan_emit_from_handoff, validate_handoff_manifest_schema,
    PropertyProfileRegistry, ZERO_SOURCE_COMMIT,
};
use serde_json::Value;

use handoff_fixtures::{handoff_workdir, write_runtime_handoff};
use support::{
    certifyedge_cmd, labtrust_release_fixture, pcs_core_rc_constants, repo_root,
    runbook_spec_authorized_release_only, runbook_spec_qc_release, with_source_commit,
};

#[test]
fn test_emit_handoff_release_mode_full_protocol_outputs() {
    let work = handoff_workdir("handoff_emit_full_protocol");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_runtime_handoff(&work, |_| {});
    let cert_out = work.join("trace_certificate.json");
    let summary_out = work.join("certificate_summary.json");
    let handoff_out = work.join("certifyedge_to_labtrust_handoff.json");
    let formal_facts_out = work.join("certificate_formal_facts.json");
    let profiles = repo_root().join("templates/profiles");

    with_source_commit(pcs_core_rc_constants().source_commit, || {
        certifyedge_cmd()
            .arg("--release-mode")
            .args([
                "emit-pcs-certificate",
                "--handoff",
                handoff_path.to_str().unwrap(),
                "--profile-registry",
                profiles.to_str().unwrap(),
                "--out",
                cert_out.to_str().unwrap(),
                "--summary-out",
                summary_out.to_str().unwrap(),
                "--handoff-out",
                handoff_out.to_str().unwrap(),
                "--formal-facts-out",
                formal_facts_out.to_str().unwrap(),
            ])
            .env("CERTIFYEDGE_ROOT", repo_root())
            .assert()
            .success();
    });

    let cert: Value = serde_json::from_str(&std::fs::read_to_string(&cert_out).unwrap()).unwrap();
    let summary: Value =
        serde_json::from_str(&std::fs::read_to_string(&summary_out).unwrap()).unwrap();
    let facts: Value =
        serde_json::from_str(&std::fs::read_to_string(&formal_facts_out).unwrap()).unwrap();
    assert_eq!(summary["certificate_id"], cert["certificate_id"]);
    assert_eq!(summary["property_id"], "hospital_lab.qc_release");
    assert_eq!(summary["status"], "CertificateChecked");
    assert_eq!(facts["certificate_id"], cert["certificate_id"]);
    assert_eq!(facts["trace_hash"], cert["trace_hash"]);
    assert_eq!(facts["status"], cert["status"]);
    assert_eq!(facts["formal_predicate"], "CertificateMatchesRuntime");
    assert_eq!(facts["admissible_for_release"], true);
    assert_eq!(facts["artifact"], "trace_certificate.json");

    let outbound = load_handoff_manifest(&handoff_out).expect("outbound handoff parses");
    assert_eq!(outbound.invariants["status"], "CertificateChecked");
    assert!(outbound
        .expected_outputs
        .contains_key("science_claim_bundle.certified.json"));
    assert_eq!(
        outbound.invariants["formal_predicate"],
        "CertificateMatchesRuntime"
    );
    assert_eq!(outbound.invariants["admissible_for_release"], "true");
    assert!(outbound
        .input_artifacts
        .contains_key("certificate_formal_facts.json"));
    assert_eq!(
        outbound.input_artifacts["certificate_formal_facts.json"].artifact_type,
        "CertificateFormalFacts.v0"
    );
}

#[test]
fn test_emit_certificate_from_handoff_release_mode() {
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
fn test_emit_certificate_rejects_trace_file_digest_mismatch() {
    let work = handoff_workdir("handoff_emit_file_digest");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_runtime_handoff(&work, |h| {
        if let Some(entry) = h.input_artifacts.get_mut("trace.json") {
            entry.sha256 = Some(
                "sha256:1111111111111111111111111111111111111111111111111111111111111111"
                    .to_string(),
            );
        }
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
fn test_property_template_mismatch_rejected() {
    let work = handoff_workdir("handoff_emit_property_mismatch");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_runtime_handoff(&work, |_| {});
    let registry = PropertyProfileRegistry::from_certifyedge_root(&repo_root());
    let handoff = load_handoff_manifest(&handoff_path).unwrap();
    let err = plan_emit_from_handoff(
        &handoff_path,
        &handoff,
        &registry,
        Some(&runbook_spec_authorized_release_only()),
        None,
        None,
        false,
    );
    assert!(err.is_err(), "expected property_id mismatch: {err:?}");
    assert!(
        err.unwrap_err().contains("property_template_mismatch"),
        "unexpected error"
    );
}

#[test]
fn test_emit_certificate_resolves_property_profile_from_handoff() {
    let work = handoff_workdir("handoff_profile_resolve");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_runtime_handoff(&work, |_| {});
    let registry = PropertyProfileRegistry::from_certifyedge_root(&repo_root());
    let handoff = load_handoff_manifest(&handoff_path).unwrap();
    let plan = plan_emit_from_handoff(&handoff_path, &handoff, &registry, None, None, None, false)
        .unwrap();
    assert_eq!(plan.property_profile.property_id, "hospital_lab.qc_release");
    assert!(plan.spec_path.ends_with("qc_release.stl"));
    assert_eq!(
        plan.property_profile.output_certificate_artifact,
        "TraceCertificate.v0"
    );
}

#[test]
fn test_unknown_property_id_rejected() {
    let work = handoff_workdir("handoff_unknown_property");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_runtime_handoff(&work, |h| {
        h.invariants.insert(
            "property_id".to_string(),
            "hospital_lab.unknown_domain".to_string(),
        );
    });

    let assert = certifyedge_cmd()
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
    let stderr = String::from_utf8_lossy(&assert.get_output().stderr);
    assert!(
        stderr.contains("unknown_property_id"),
        "expected repair-hint failure_code in stderr: {stderr}"
    );
    assert!(stderr.contains("repair_hint"));
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
    let registry = PropertyProfileRegistry::from_certifyedge_root(&repo_root());
    let handoff = load_handoff_manifest(&handoff_path).unwrap();
    plan_emit_from_handoff(
        &handoff_path,
        &handoff,
        &registry,
        Some(&runbook_spec_qc_release()),
        None,
        None,
        false,
    )
    .unwrap();
}
