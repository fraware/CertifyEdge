//! PCS v0.1 runbook CLI smoke tests (LabTrust handoff command names).

use std::path::PathBuf;

use assert_cmd::Command;
use pcs_certificate::{is_zero_source_commit, ZERO_SOURCE_COMMIT};
use predicates::prelude::*;

#[path = "../common/support.rs"]
mod support;

use support::{
    assert_certificate_semantics_equal, certifyedge_cmd, env_lock, labtrust_fixture,
    labtrust_release_certificate_fixture, pcs_cli_available, repo_root, spec_path,
    validate_certificate_against_pcs_core, RELEASE_FIXTURE_SOURCE_COMMIT,
};

fn spec_qc_release() -> PathBuf {
    spec_path("qc_release.stl")
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
    certifyedge_cmd()
}

#[test]
fn test_cli_labtrust_release_certificate_e2e() {
    let out_dir = repo_root().join("target/cli_release_e2e");
    std::fs::create_dir_all(&out_dir).unwrap();
    let cert_path = out_dir.join("trace_certificate.json");

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

    let previous = std::env::var("CERTIFYEDGE_SOURCE_COMMIT").ok();
    std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", RELEASE_FIXTURE_SOURCE_COMMIT);

    certifyedge()
        .args([
            "emit-pcs-certificate",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            valid_trace().to_str().unwrap(),
            "--out",
            cert_path.to_str().unwrap(),
        ])
        .assert()
        .success()
        .stdout(predicate::str::contains("CertificateChecked"));

    if let Some(value) = previous {
        std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", value);
    } else {
        std::env::remove_var("CERTIFYEDGE_SOURCE_COMMIT");
    }

    validate_certificate_against_pcs_core(&cert_path);

    certifyedge()
        .arg("verify-certificate")
        .arg(&cert_path)
        .arg("--trace")
        .arg(valid_trace())
        .assert()
        .success();
}

#[test]
fn test_cli_invalid_trace_counterexample_missing_qc() {
    let cx_path = repo_root().join("target/cli_cx_missing_qc.json");
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

    let cx: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&cx_path).unwrap()).unwrap();
    assert_eq!(cx["reason"], "release_before_qc");
}

#[test]
fn test_cli_invalid_trace_counterexample_unauthorized() {
    let cx_path = repo_root().join("target/cli_cx_unauthorized.json");
    certifyedge()
        .args([
            "check-trace",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            unauthorized_trace().to_str().unwrap(),
            "--counterexample-out",
            cx_path.to_str().unwrap(),
        ])
        .assert()
        .failure();

    let cx: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&cx_path).unwrap()).unwrap();
    assert_eq!(cx["reason"], "unauthorized_release");
}

#[test]
fn test_release_certificate_fixture_validates() {
    let fixture = labtrust_release_certificate_fixture();
    assert!(
        fixture.is_file(),
        "missing {}; run write_fixtures with --ignored",
        fixture.display()
    );

    let fixture_value: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&fixture).unwrap()).unwrap();
    assert_eq!(fixture_value["status"], "CertificateChecked");
    assert_eq!(fixture_value["schema_version"], "v0");
    assert_eq!(
        fixture_value["source_commit"].as_str().unwrap(),
        RELEASE_FIXTURE_SOURCE_COMMIT
    );

    validate_certificate_against_pcs_core(&fixture);

    let trace: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(valid_trace()).unwrap()).unwrap();
    assert_eq!(fixture_value["trace_hash"], trace["trace_hash"]);

    certifyedge()
        .arg("verify-certificate")
        .arg(&fixture)
        .arg("--trace")
        .arg(valid_trace())
        .assert()
        .success();

    let out = repo_root().join("target/cli_fixture_reemit.json");
    let previous = std::env::var("CERTIFYEDGE_SOURCE_COMMIT").ok();
    std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", RELEASE_FIXTURE_SOURCE_COMMIT);
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
    if let Some(value) = previous {
        std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", value);
    } else {
        std::env::remove_var("CERTIFYEDGE_SOURCE_COMMIT");
    }

    let emitted: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&out).unwrap()).unwrap();
    assert_certificate_semantics_equal(&emitted, &fixture_value);
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
fn test_cli_emit_pcs_certificate_validates_against_pcs_core() {
    let out = repo_root().join("target/test_cli_pcs_validate.json");
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

    validate_certificate_against_pcs_core(&out);
    if !pcs_cli_available() {
        eprintln!("note: pcs CLI not on PATH; vendored schema validation ran");
    }
}

#[test]
fn test_cli_verify_certificate_detects_digest_tampering() {
    let out = repo_root().join("target/test_cli_digest_tamper.json");
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
fn test_cli_explain_counterexample_outputs_machine_readable_reason() {
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

    let cx: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&cx_path).unwrap()).unwrap();
    let reason = cx["reason"].as_str().expect("counterexample.reason");
    assert_eq!(reason, "release_before_qc");
    let property_id = cx["property_id"].as_str().expect("counterexample.property_id");
    assert!(property_id.starts_with("hospital_lab."));

    certifyedge()
        .arg("explain-counterexample")
        .arg(&cx_path)
        .assert()
        .success()
        .stdout(predicate::str::contains(reason))
        .stdout(predicate::str::contains(property_id));
}

#[test]
fn test_trace_hash_matches_labtrust_fixture() {
    let trace: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(valid_trace()).unwrap()).unwrap();

    let valid_out = repo_root().join("target/test_cli_valid_cert.json");
    certifyedge()
        .args([
            "emit-pcs-certificate",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            valid_trace().to_str().unwrap(),
            "--out",
            valid_out.to_str().unwrap(),
        ])
        .assert()
        .success();

    let valid_cert: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&valid_out).unwrap()).unwrap();
    assert_eq!(valid_cert["trace_hash"], trace["trace_hash"]);
    assert_eq!(valid_cert["status"], "CertificateChecked");
    assert!(valid_cert["counterexample_ref"].is_null());

    let invalid_out = repo_root().join("target/test_cli_invalid_cert.json");
    certifyedge()
        .args([
            "emit-pcs-certificate",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            missing_qc_trace().to_str().unwrap(),
            "--out",
            invalid_out.to_str().unwrap(),
        ])
        .assert()
        .success()
        .stdout(predicate::str::contains("Rejected"));

    let missing_trace: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(missing_qc_trace()).unwrap()).unwrap();
    let invalid_cert: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&invalid_out).unwrap()).unwrap();
    assert_eq!(invalid_cert["trace_hash"], missing_trace["trace_hash"]);
    assert_eq!(invalid_cert["status"], "Rejected");
    assert!(invalid_cert["counterexample_ref"].is_string());
}

#[test]
fn test_release_mode_rejects_zero_source_commit() {
    let _guard = env_lock();
    let out = repo_root().join("target/test_release_zero_commit.json");
    let previous = std::env::var("CERTIFYEDGE_SOURCE_COMMIT").ok();

    std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", ZERO_SOURCE_COMMIT);
    certifyedge()
        .args([
            "emit-pcs-certificate",
            "--release-mode",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            valid_trace().to_str().unwrap(),
            "--out",
            out.to_str().unwrap(),
        ])
        .assert()
        .failure()
        .stderr(predicate::str::contains("source_commit").or(predicate::str::contains("release")));

    if let Some(value) = previous {
        std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", value);
    } else {
        std::env::remove_var("CERTIFYEDGE_SOURCE_COMMIT");
    }
}

#[test]
fn test_release_mode_accepts_real_source_commit() {
    let _guard = env_lock();
    let out = repo_root().join("target/test_release_real_commit.json");
    let previous = std::env::var("CERTIFYEDGE_SOURCE_COMMIT").ok();
    let real_commit = "deadbeefdeadbeefdeadbeefdeadbeefdeadbeef";

    std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", real_commit);
    certifyedge()
        .args([
            "emit-pcs-certificate",
            "--release-mode",
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
    assert_eq!(cert["source_commit"], real_commit);
    assert!(!is_zero_source_commit(&cert["source_commit"].as_str().unwrap()));

    if let Some(value) = previous {
        std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", value);
    } else {
        std::env::remove_var("CERTIFYEDGE_SOURCE_COMMIT");
    }
}

#[test]
fn test_release_mode_global_flag_emit() {
    let _guard = env_lock();
    if !pcs_cli_available() {
        eprintln!("note: skipped global --release-mode pcs validate (pcs CLI not on PATH)");
        return;
    }

    let out = repo_root().join("target/test_release_global_flag.json");
    let previous = std::env::var("CERTIFYEDGE_SOURCE_COMMIT").ok();
    let real_commit = "cafebabecafebabecafebabecafebabecafebabe";
    std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", real_commit);

    certifyedge()
        .arg("--release-mode")
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

    validate_certificate_against_pcs_core(&out);
    let cert: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&out).unwrap()).unwrap();
    assert_eq!(cert["source_commit"], real_commit);
    assert!(!is_zero_source_commit(&cert["source_commit"].as_str().unwrap()));

    if let Some(value) = previous {
        std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", value);
    } else {
        std::env::remove_var("CERTIFYEDGE_SOURCE_COMMIT");
    }
}

#[test]
fn test_release_mode_global_flag_rejects_zero_commit() {
    let _guard = env_lock();
    let out = repo_root().join("target/test_release_global_zero.json");
    let previous = std::env::var("CERTIFYEDGE_SOURCE_COMMIT").ok();
    std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", ZERO_SOURCE_COMMIT);

    certifyedge()
        .arg("--release-mode")
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
        .failure();

    if let Some(value) = previous {
        std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", value);
    } else {
        std::env::remove_var("CERTIFYEDGE_SOURCE_COMMIT");
    }
}
