//! Canonical PCS release-candidate fixtures synced from pcs-core/examples/labtrust-release/.

#[path = "../common/support.rs"]
mod support;

use predicates::prelude::*;

use pcs_certificate::ZERO_SOURCE_COMMIT;

use support::{
    certifyedge_cmd, labtrust_release_fixture, pcs_core_rc_constants, repo_root,
    validate_certificate_against_pcs_core,
};

const WRONG_SOURCE_REPO: &str = "https://github.com/example/wrong-repo";

const TAMPERED_DIGEST: &str =
    "sha256:0000000000000000000000000000000000000000000000000000000000000000";
const TAMPERED_TRACE_HASH: &str =
    "sha256:1111111111111111111111111111111111111111111111111111111111111111";
const TAMPERED_CERTIFICATE_ID: &str = "cert-trace-00000000-0000-0000-0000-000000000000";

#[test]
fn test_trace_certificate_matches_pcs_core_rc() {
    let rc = pcs_core_rc_constants();
    let cert: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(labtrust_release_fixture("trace_certificate.json")).unwrap(),
    )
    .unwrap();

    assert_eq!(cert["schema_version"].as_str().unwrap(), "v0");
    assert_eq!(cert["certificate_id"].as_str().unwrap(), rc.certificate_id);
    assert_eq!(cert["source_commit"].as_str().unwrap(), rc.source_commit);
    assert_eq!(cert["trace_hash"].as_str().unwrap(), rc.trace_hash);
    assert_eq!(cert["status"].as_str().unwrap(), "CertificateChecked");
    assert_eq!(
        cert["signature_or_digest"].as_str().unwrap(),
        rc.signature_or_digest
    );
    assert_eq!(
        cert["source_repo"].as_str().unwrap(),
        "https://github.com/fraware/CertifyEdge"
    );

    let manifest: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(labtrust_release_fixture("PCS_CORE_RC_MANIFEST.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(
        manifest["artifacts"]["science_claim_bundle.certified.json"]
            .as_str()
            .unwrap(),
        rc.certified_bundle_hash
    );
    assert_eq!(
        manifest["certifyedge_commit"].as_str().unwrap(),
        rc.source_commit
    );

    validate_certificate_against_pcs_core(&labtrust_release_fixture("trace_certificate.json"));
}

#[test]
fn test_verify_canonical_rc_certificate_against_trace() {
    certifyedge_cmd()
        .args([
            "verify-certificate",
            labtrust_release_fixture("trace_certificate.json")
                .to_str()
                .unwrap(),
            "--trace",
            labtrust_release_fixture("trace.json").to_str().unwrap(),
        ])
        .assert()
        .success();
}

#[test]
fn test_verify_canonical_rc_certificate_in_release_mode() {
    certifyedge_cmd()
        .arg("--release-mode")
        .args([
            "verify-certificate",
            labtrust_release_fixture("trace_certificate.json")
                .to_str()
                .unwrap(),
            "--trace",
            labtrust_release_fixture("trace.json").to_str().unwrap(),
        ])
        .assert()
        .success();
}

fn pcs_core_rc_source_dir() -> Option<std::path::PathBuf> {
    std::env::var("PCS_CORE_PATH")
        .or_else(|_| std::env::var("PCS_CORE_ROOT"))
        .ok()
        .map(|root| std::path::PathBuf::from(root).join("examples/labtrust-release"))
}

fn tampered_rc_certificate_path(suffix: &str) -> std::path::PathBuf {
    repo_root().join(format!("target/pcs_core_rc_tamper_{suffix}.json"))
}

/// When `PCS_CORE_PATH` or `PCS_CORE_ROOT` is set, committed fixtures must match pcs-core bytes.
#[test]
fn test_local_fixtures_match_pcs_core_rc_source() {
    let Some(src) = pcs_core_rc_source_dir() else {
        eprintln!("skip: PCS_CORE_PATH / PCS_CORE_ROOT not set");
        return;
    };
    for name in ["trace.json", "trace_certificate.json"] {
        let upstream = src.join(name);
        assert!(
            upstream.is_file(),
            "missing pcs-core fixture: {}",
            upstream.display()
        );
        let expected = std::fs::read(&upstream).unwrap();
        let local = std::fs::read(labtrust_release_fixture(name)).unwrap();
        assert_eq!(
            expected, local,
            "{name} drifted from {}",
            src.display()
        );
    }
}

#[test]
fn test_verify_certificate_rejects_modified_trace_hash() {
    let out = tampered_rc_certificate_path("trace_hash");
    let mut cert: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(labtrust_release_fixture("trace_certificate.json")).unwrap(),
    )
    .unwrap();
    cert["trace_hash"] = serde_json::json!(TAMPERED_TRACE_HASH);
    std::fs::write(&out, serde_json::to_string_pretty(&cert).unwrap()).unwrap();

    certifyedge_cmd()
        .args([
            "verify-certificate",
            out.to_str().unwrap(),
            "--trace",
            labtrust_release_fixture("trace.json").to_str().unwrap(),
        ])
        .assert()
        .failure();
}

#[test]
fn test_verify_certificate_rejects_modified_certificate_id() {
    let out = tampered_rc_certificate_path("certificate_id");
    let mut cert: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(labtrust_release_fixture("trace_certificate.json")).unwrap(),
    )
    .unwrap();
    cert["certificate_id"] = serde_json::json!(TAMPERED_CERTIFICATE_ID);
    std::fs::write(&out, serde_json::to_string_pretty(&cert).unwrap()).unwrap();

    certifyedge_cmd()
        .args([
            "verify-certificate",
            out.to_str().unwrap(),
            "--trace",
            labtrust_release_fixture("trace.json").to_str().unwrap(),
        ])
        .assert()
        .failure();
}

#[test]
fn test_verify_certificate_rejects_wrong_source_repo_in_release_mode() {
    let out = tampered_rc_certificate_path("source_repo");
    let mut cert: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(labtrust_release_fixture("trace_certificate.json")).unwrap(),
    )
    .unwrap();
    cert["source_repo"] = serde_json::json!(WRONG_SOURCE_REPO);
    std::fs::write(&out, serde_json::to_string_pretty(&cert).unwrap()).unwrap();

    certifyedge_cmd()
        .arg("--release-mode")
        .args([
            "verify-certificate",
            out.to_str().unwrap(),
            "--trace",
            labtrust_release_fixture("trace.json").to_str().unwrap(),
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("source_repo"));
}

#[test]
fn test_verify_certificate_rejects_placeholder_source_commit_in_release_mode() {
    let out = tampered_rc_certificate_path("source_commit");
    let mut cert: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(labtrust_release_fixture("trace_certificate.json")).unwrap(),
    )
    .unwrap();
    cert["source_commit"] = serde_json::json!(ZERO_SOURCE_COMMIT);
    std::fs::write(&out, serde_json::to_string_pretty(&cert).unwrap()).unwrap();

    certifyedge_cmd()
        .arg("--release-mode")
        .args([
            "verify-certificate",
            out.to_str().unwrap(),
            "--trace",
            labtrust_release_fixture("trace.json").to_str().unwrap(),
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("placeholder"));
}

#[test]
fn test_verify_certificate_rejects_modified_signature_or_digest() {
    let out = tampered_rc_certificate_path("signature_or_digest");
    let mut cert: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(labtrust_release_fixture("trace_certificate.json")).unwrap(),
    )
    .unwrap();
    cert["signature_or_digest"] = serde_json::json!(TAMPERED_DIGEST);
    std::fs::write(&out, serde_json::to_string_pretty(&cert).unwrap()).unwrap();

    certifyedge_cmd()
        .args([
            "verify-certificate",
            out.to_str().unwrap(),
            "--trace",
            labtrust_release_fixture("trace.json").to_str().unwrap(),
        ])
        .assert()
        .failure();
}
