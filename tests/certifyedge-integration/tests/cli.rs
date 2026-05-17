//! CLI runbook tests — `certifyedge check-trace`, `emit-pcs-certificate`, etc.

use std::path::PathBuf;

use assert_cmd::Command;
use predicates::prelude::*;
use pcs_certificate::{is_zero_source_commit, CertifyEdgeMetadata, ZERO_SOURCE_COMMIT};

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn spec_qc_release() -> PathBuf {
    repo_root().join("templates/hospital_lab/qc_release.stl")
}

fn valid_trace() -> PathBuf {
    repo_root().join("tests/labtrust/valid_trace.json")
}

fn missing_qc_trace() -> PathBuf {
    repo_root().join("tests/labtrust/invalid_missing_qc_trace.json")
}

fn unauthorized_trace() -> PathBuf {
    repo_root().join("tests/labtrust/invalid_unauthorized_trace.json")
}

fn certifyedge() -> Command {
    Command::cargo_bin("certifyedge").expect("certifyedge binary")
}

#[test]
fn test_cli_check_trace_malformed_trace_fails() {
    let dir = repo_root().join("target/cli_malformed");
    std::fs::create_dir_all(&dir).unwrap();
    let bad = dir.join("bad_trace.json");
    std::fs::write(&bad, r#"{"version":"0","trace_hash":"sha256:00"}"#).unwrap();
    certifyedge()
        .args([
            "check-trace",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            bad.to_str().unwrap(),
        ])
        .assert()
        .failure();
}

#[test]
fn test_cli_check_trace_valid_passes() {
    certifyedge()
        .args([
            "check-trace",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            valid_trace().to_str().unwrap(),
        ])
        .assert()
        .success()
        .stdout(predicate::str::contains("PASS"));
}

#[test]
fn test_cli_check_trace_missing_qc_fails() {
    certifyedge()
        .args([
            "check-trace",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            missing_qc_trace().to_str().unwrap(),
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("FAIL"));
}

#[test]
fn test_cli_check_trace_unauthorized_fails() {
    certifyedge()
        .args([
            "check-trace",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            unauthorized_trace().to_str().unwrap(),
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("FAIL"));
}

#[test]
fn test_emit_pcs_certificate_valid() {
    let out = repo_root().join("target/test_cert_valid.json");
    certifyedge()
        .args([
            "emit-pcs-certificate",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            valid_trace().to_str().unwrap(),
            "--out",
            out.to_str().unwrap(),
        ])
        .assert()
        .success()
        .stdout(predicate::str::contains("CertificateChecked"));

    let text = std::fs::read_to_string(&out).unwrap();
    let cert: serde_json::Value = serde_json::from_str(&text).unwrap();
    assert_eq!(cert["status"], "CertificateChecked");
    assert_eq!(cert["checker"], "CertifyEdge");
    assert_eq!(cert["property_id"], "hospital_lab.qc_release");
    assert!(cert["counterexample_ref"].is_null());
}

#[test]
fn test_emit_pcs_certificate_rejected_with_counterexample() {
    let out_dir = repo_root().join("target/cli_reject");
    std::fs::create_dir_all(&out_dir).unwrap();
    let cert_path = out_dir.join("trace_certificate.json");
    let cx_path = out_dir.join("counterexample.json");

    certifyedge()
        .args([
            "emit-pcs-certificate",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            missing_qc_trace().to_str().unwrap(),
            "--out",
            cert_path.to_str().unwrap(),
            "--counterexample-out",
            cx_path.to_str().unwrap(),
        ])
        .assert()
        .success()
        .stdout(predicate::str::contains("Rejected"));

    let cert: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&cert_path).unwrap()).unwrap();
    assert_eq!(cert["status"], "Rejected");
    assert!(cert["counterexample_ref"].is_string());
    assert!(cx_path.exists());
}

#[test]
fn test_certificate_trace_hash_matches_labtrust_trace_hash() {
    let out = repo_root().join("target/test_cert_hash.json");
    certifyedge()
        .args([
            "emit-pcs-certificate",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            valid_trace().to_str().unwrap(),
            "--out",
            out.to_str().unwrap(),
        ])
        .assert()
        .success();

    let trace: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(valid_trace()).unwrap()).unwrap();
    let cert: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&out).unwrap()).unwrap();
    assert_eq!(cert["trace_hash"], trace["trace_hash"]);
}

#[test]
fn test_verify_certificate_rejects_modified_digest() {
    let out = repo_root().join("target/test_cert_verify.json");
    certifyedge()
        .args([
            "emit-pcs-certificate",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            valid_trace().to_str().unwrap(),
            "--out",
            out.to_str().unwrap(),
        ])
        .assert()
        .success();

    let mut cert: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&out).unwrap()).unwrap();
    cert["signature_or_digest"] = serde_json::json!("sha256:0000000000000000000000000000000000000000000000000000000000000000");
    std::fs::write(&out, serde_json::to_string_pretty(&cert).unwrap()).unwrap();

    certifyedge()
        .arg("verify-certificate")
        .arg(&out)
        .assert()
        .failure();
}

#[test]
fn test_release_mode_never_emits_zero_source_commit() {
    let out = repo_root().join("target/test_cert_release.json");
    let commit = "abcdef0123456789abcdef0123456789abcdef01";
    certifyedge()
        .args([
            "--release-mode",
            "emit-pcs-certificate",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            valid_trace().to_str().unwrap(),
            "--out",
            out.to_str().unwrap(),
        ])
        .env("CERTIFYEDGE_SOURCE_COMMIT", commit)
        .assert()
        .success();

    let cert: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&out).unwrap()).unwrap();
    assert_eq!(cert["source_commit"], commit);
    assert!(!is_zero_source_commit(
        cert["source_commit"].as_str().unwrap()
    ));
}

#[test]
fn test_release_mode_rejects_zero_source_commit() {
    std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", ZERO_SOURCE_COMMIT);
    let result = CertifyEdgeMetadata::resolve(true);
    std::env::remove_var("CERTIFYEDGE_SOURCE_COMMIT");
    // With a real git checkout, resolve(true) may use HEAD instead of the zero env var.
    if result.is_ok() {
        assert!(!is_zero_source_commit(&result.unwrap().source_commit));
    } else {
        assert!(result.unwrap_err().contains("source_commit"));
    }
}

#[test]
fn test_release_mode_uses_nonzero_commit() {
    let commit = "abcdef0123456789abcdef0123456789abcdef01";
    std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", commit);
    let meta = CertifyEdgeMetadata::resolve(true).unwrap();
    assert_eq!(meta.source_commit, commit);
    assert!(!is_zero_source_commit(&meta.source_commit));
    std::env::remove_var("CERTIFYEDGE_SOURCE_COMMIT");
}

#[test]
fn test_certificate_validates_against_pcs_core() {
    if std::process::Command::new("pcs")
        .arg("--help")
        .output()
        .is_err()
    {
        eprintln!("skipping test_certificate_validates_against_pcs_core: pcs CLI not installed");
        return;
    }

    let out = repo_root().join("target/test_cert_pcs.json");
    certifyedge()
        .args([
            "--release-mode",
            "emit-pcs-certificate",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            valid_trace().to_str().unwrap(),
            "--out",
            out.to_str().unwrap(),
        ])
        .env(
            "CERTIFYEDGE_SOURCE_COMMIT",
            "abcdef0123456789abcdef0123456789abcdef01",
        )
        .assert()
        .success();

    Command::new("pcs")
        .arg("validate")
        .arg(&out)
        .assert()
        .success();
}
