//! CLI runbook tests — `certifyedge check-trace`, `emit-pcs-certificate`, etc.

use std::path::PathBuf;
use std::sync::Mutex;

use assert_cmd::Command;
use pcs_certificate::{is_zero_source_commit, CertifyEdgeMetadata, ZERO_SOURCE_COMMIT};
use predicates::prelude::*;

#[path = "support.rs"]
mod support;

use support::{labtrust_fixture, repo_root, spec_path};

/// `CERTIFYEDGE_SOURCE_COMMIT` is process-global; serialize env-mutating tests.
static ENV_LOCK: Mutex<()> = Mutex::new(());

fn spec_qc_release() -> PathBuf {
    spec_path("qc_release.stl")
}

fn spec_authorized_release_only() -> PathBuf {
    spec_path("authorized_release_only.stl")
}

fn valid_trace() -> PathBuf {
    labtrust_fixture("valid_trace.json")
}

fn missing_qc_trace() -> PathBuf {
    labtrust_fixture("invalid_missing_qc_trace.json")
}

fn unauthorized_trace() -> PathBuf {
    labtrust_fixture("invalid_unauthorized_trace.json")
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
fn test_authorized_release_only_template_exists() {
    let path = spec_authorized_release_only();
    assert!(path.is_file(), "missing {}", path.display());
    let spec = labtrust_adapter::PropertySpec::load(&path).unwrap();
    assert_eq!(
        spec.property_id.as_str(),
        "hospital_lab.authorized_release_only"
    );
    assert!(spec.allowed_release_roles.contains("release_manager"));
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
    let cert: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&out).unwrap()).unwrap();
    assert_eq!(cert["trace_hash"], trace["trace_hash"]);
}

#[test]
fn test_cli_verify_certificate_valid_passes() {
    let out = repo_root().join("target/test_cert_verify_runbook.json");
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

    certifyedge()
        .arg("verify-certificate")
        .arg(&out)
        .assert()
        .success()
        .stdout(predicate::str::contains("valid TraceCertificate.v0"))
        .stdout(predicate::str::contains("CertificateChecked"));
}

#[test]
fn test_cli_explain_counterexample() {
    let out_dir = repo_root().join("target/cli_explain_cx");
    std::fs::create_dir_all(&out_dir).unwrap();
    let cx_path = out_dir.join("counterexample.json");

    certifyedge()
        .args([
            "check-trace",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            missing_qc_trace().to_str().unwrap(),
            "--counterexample-out",
            cx_path.to_str().unwrap(),
        ])
        .assert()
        .failure();

    certifyedge()
        .arg("explain-counterexample")
        .arg(&cx_path)
        .assert()
        .success()
        .stdout(predicate::str::contains("release_before_qc"));
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
    cert["signature_or_digest"] = serde_json::json!(
        "sha256:0000000000000000000000000000000000000000000000000000000000000000"
    );
    std::fs::write(&out, serde_json::to_string_pretty(&cert).unwrap()).unwrap();

    certifyedge()
        .arg("verify-certificate")
        .arg(&out)
        .assert()
        .failure();
}

#[test]
fn test_emit_pcs_certificate_release_mode_flag_on_subcommand() {
    let _guard = ENV_LOCK.lock().unwrap();
    let out = repo_root().join("target/test_cert_release_subcmd.json");
    let commit = "abcdef0123456789abcdef0123456789abcdef01";
    std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", commit);
    certifyedge()
        .args([
            "emit-pcs-certificate",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            valid_trace().to_str().unwrap(),
            "--out",
            out.to_str().unwrap(),
            "--release-mode",
        ])
        .assert()
        .success();
    std::env::remove_var("CERTIFYEDGE_SOURCE_COMMIT");

    let cert: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&out).unwrap()).unwrap();
    assert_eq!(cert["source_commit"], commit);
    assert!(!is_zero_source_commit(
        cert["source_commit"].as_str().unwrap()
    ));
}

#[test]
fn test_release_mode_never_emits_zero_source_commit() {
    let _guard = ENV_LOCK.lock().unwrap();
    let out = repo_root().join("target/test_cert_release.json");
    let commit = "abcdef0123456789abcdef0123456789abcdef01";
    std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", commit);
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
        .assert()
        .success();
    std::env::remove_var("CERTIFYEDGE_SOURCE_COMMIT");

    let cert: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&out).unwrap()).unwrap();
    assert_eq!(cert["source_commit"], commit);
    assert!(!is_zero_source_commit(
        cert["source_commit"].as_str().unwrap()
    ));
}

#[test]
fn test_release_mode_rejects_zero_source_commit() {
    let _guard = ENV_LOCK.lock().unwrap();
    std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", ZERO_SOURCE_COMMIT);
    assert!(CertifyEdgeMetadata::resolve(true).is_err());

    let out = repo_root().join("target/test_cert_release_zero.json");
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
        .assert()
        .failure()
        .stderr(predicate::str::contains("non-zero"));

    std::env::remove_var("CERTIFYEDGE_SOURCE_COMMIT");
}

#[test]
fn test_release_mode_uses_nonzero_commit() {
    let _guard = ENV_LOCK.lock().unwrap();
    let commit = "abcdef0123456789abcdef0123456789abcdef01";
    std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", commit);
    let meta = CertifyEdgeMetadata::resolve(true).unwrap();
    assert_eq!(meta.source_commit, commit);
    assert!(!is_zero_source_commit(&meta.source_commit));
    std::env::remove_var("CERTIFYEDGE_SOURCE_COMMIT");
}

#[test]
fn test_emit_pcs_certificate_validates_against_pcs_core() {
    let out = repo_root().join("target/test_cert_pcs_schema.json");
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

    let text = std::fs::read_to_string(&out).unwrap();
    let value: serde_json::Value = serde_json::from_str(&text).unwrap();
    pcs_certificate::validate_trace_certificate_schema(&value).unwrap();

    if std::process::Command::new("pcs")
        .arg("--help")
        .output()
        .is_ok()
    {
        Command::new("pcs")
            .arg("validate")
            .arg(&out)
            .assert()
            .success();
    }
}

#[test]
fn test_trace_certificate_schema_version_is_v0() {
    let out = repo_root().join("target/test_cert_schema_v0.json");
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

    let cert: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&out).unwrap()).unwrap();
    assert_eq!(cert["schema_version"], "v0");
    assert_eq!(cert["checker"], "CertifyEdge");
}
