//! PCS v0.1 runbook CLI smoke tests (LabTrust handoff command names).

use std::path::PathBuf;

use assert_cmd::Command;
use predicates::prelude::*;

#[path = "../common/support.rs"]
mod support;

use support::{
    certifyedge_cmd, labtrust_release_fixture, pcs_cli_available, repo_root,
    runbook_labtrust_release_trace, runbook_spec_qc_release, validate_certificate_against_pcs_core,
};

fn spec_qc_release() -> PathBuf {
    runbook_spec_qc_release()
}

fn valid_trace() -> PathBuf {
    runbook_labtrust_release_trace()
}

fn missing_qc_trace() -> PathBuf {
    labtrust_release_fixture("invalid_missing_qc_trace.json")
}

fn unauthorized_trace() -> PathBuf {
    labtrust_release_fixture("invalid_unauthorized_trace.json")
}

fn certifyedge() -> Command {
    certifyedge_cmd()
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

    let cx: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&cx_path).unwrap()).unwrap();
    let reason = cx["reason"].as_str().expect("counterexample.reason");
    assert_eq!(reason, "release_before_qc");
    let property_id = cx["property_id"]
        .as_str()
        .expect("counterexample.property_id");
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
}

#[test]
fn test_profiles_list_includes_qc_release() {
    certifyedge()
        .args(["profiles", "list"])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .success()
        .stdout(predicate::str::contains("hospital_lab.qc_release"))
        .stdout(predicate::str::contains(
            "hospital_lab.no_release_before_qc",
        ))
        .stdout(predicate::str::contains("agent_tool_use.safety_v0"))
        .stdout(predicate::str::contains("scientific_computation.reproducibility_v0"));
}

#[test]
fn test_profiles_explain_qc_release() {
    certifyedge()
        .args(["profiles", "explain", "hospital_lab.qc_release"])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .success()
        .stdout(predicate::str::contains("TraceCertificate.v0"));
}

#[test]
fn test_profiles_explain_agent_tool_use() {
    certifyedge()
        .args(["profiles", "explain", "agent_tool_use.safety_v0"])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .success()
        .stdout(predicate::str::contains("ToolUseCertificate.v0"))
        .stdout(predicate::str::contains("ToolUseTrace.v0"));
}

#[test]
fn test_profiles_explain_scientific_computation() {
    certifyedge()
        .args([
            "profiles",
            "explain",
            "scientific_computation.reproducibility_v0",
        ])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .success()
        .stdout(predicate::str::contains("ComputationWitness.v0"))
        .stdout(predicate::str::contains("ComputationRunReceipt.v0"))
        .stdout(predicate::str::contains("DatasetReceipt.v0"))
        .stdout(predicate::str::contains("supporting_artifacts"));
}

#[test]
fn test_profiles_validate_qc_release_profile() {
    let path = repo_root().join("templates/profiles/hospital_lab.qc_release.json");
    certifyedge()
        .args(["profiles", "validate", path.to_str().unwrap()])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .success()
        .stdout(predicate::str::contains("OK property profile"));
}

#[test]
fn test_profiles_validate_agent_tool_use_profile() {
    let path = repo_root().join("templates/profiles/agent_tool_use.safety_v0.json");
    certifyedge()
        .args(["profiles", "validate", path.to_str().unwrap()])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .success()
        .stdout(predicate::str::contains("agent_tool_use.safety_v0"));
}

#[test]
fn test_profiles_validate_scientific_computation_profile() {
    let path = repo_root().join("templates/profiles/scientific_computation.reproducibility_v0.json");
    certifyedge()
        .args(["profiles", "validate", path.to_str().unwrap()])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .success()
        .stdout(predicate::str::contains("scientific_computation.reproducibility_v0"));
}

#[test]
fn test_cli_emit_rejected_certificate() {
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
