//! End-to-end PCS v0.1 runbook (mirrors `scripts/pcs-runbook.sh`).

use std::path::PathBuf;

use assert_cmd::Command;
use pcs_certificate::validate_trace_certificate_schema;
use predicates::prelude::*;

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn certifyedge() -> Command {
    Command::cargo_bin("certifyedge").expect("certifyedge binary")
}

fn spec(name: &str) -> PathBuf {
    repo_root().join("templates/hospital_lab").join(name)
}

#[test]
fn test_pcs_runbook_end_to_end() {
    let out_dir = repo_root().join("target/runbook_test");
    std::fs::create_dir_all(&out_dir).unwrap();
    let cert = out_dir.join("trace_certificate.json");
    let cx = out_dir.join("counterexample.json");

    let valid = repo_root().join("tests/labtrust/valid_trace.json");
    let missing_qc = repo_root().join("tests/labtrust/invalid_missing_qc_trace.json");
    let qc_release = spec("qc_release.stl");

    certifyedge()
        .args([
            "check-trace",
            "--spec",
            qc_release.to_str().unwrap(),
            "--trace",
            valid.to_str().unwrap(),
        ])
        .assert()
        .success()
        .stdout(predicate::str::contains("PASS"));

    certifyedge()
        .args([
            "emit-pcs-certificate",
            "--spec",
            qc_release.to_str().unwrap(),
            "--trace",
            valid.to_str().unwrap(),
            "--out",
            cert.to_str().unwrap(),
        ])
        .assert()
        .success()
        .stdout(predicate::str::contains("CertificateChecked"));

    let cert_value: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&cert).unwrap()).unwrap();
    validate_trace_certificate_schema(&cert_value).unwrap();

    certifyedge()
        .arg("verify-certificate")
        .arg(&cert)
        .assert()
        .success();

    certifyedge()
        .args([
            "check-trace",
            "--spec",
            qc_release.to_str().unwrap(),
            "--trace",
            missing_qc.to_str().unwrap(),
            "--counterexample-out",
            cx.to_str().unwrap(),
        ])
        .assert()
        .failure();

    assert!(cx.is_file());
    certifyedge()
        .arg("explain-counterexample")
        .arg(&cx)
        .assert()
        .success()
        .stdout(predicate::str::contains("release_before_qc"));

    for stl in [
        "qc_release.stl",
        "no_release_before_qc.stl",
        "authorized_release_only.stl",
    ] {
        certifyedge()
            .args([
                "check-trace",
                "--spec",
                spec(stl).to_str().unwrap(),
                "--trace",
                valid.to_str().unwrap(),
            ])
            .assert()
            .success();
    }
}

#[test]
fn test_golden_expected_certificate_validates() {
    let path = repo_root().join("tests/labtrust/expected_valid_certificate.json");
    let text = std::fs::read_to_string(&path).unwrap();
    let value: serde_json::Value = serde_json::from_str(&text).unwrap();
    validate_trace_certificate_schema(&value).unwrap();
    pcs_certificate::verify_certificate_document(
        &text,
        Some("sha256:c3e8a3dc4ad86d533de1dfa4ae7fe2a338c2cff3c945404c96a75216524d58cd"),
    )
    .unwrap();
    assert_eq!(value["schema_version"], "v0");
    assert_eq!(value["status"], "CertificateChecked");
}
