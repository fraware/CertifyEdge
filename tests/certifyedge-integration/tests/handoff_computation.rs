//! Handoff-driven emit for scientific_computation.reproducibility_v0 (ComputationWitness.v0).

#[path = "../common/support.rs"]
mod support;

#[path = "../common/handoff_fixtures.rs"]
mod handoff_fixtures;

use pcs_certificate::{
    load_handoff_manifest, validate_certificate_json_for_profile,
    validate_computation_witness_schema, PropertyProfileRegistry, ARTIFACT_COMPUTATION_WITNESS,
};
use serde_json::Value;

use handoff_fixtures::{handoff_workdir, write_computation_runtime_handoff};
use support::{certifyedge_cmd, repo_root, with_source_commit};

fn computation_fixtures() -> std::path::PathBuf {
    repo_root().join("tests/computation")
}

#[test]
fn test_handoff_emit_computation_witness_checked() {
    let work = handoff_workdir("handoff_computation_ok");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_computation_runtime_handoff(
        &work,
        &computation_fixtures(),
        "computation_run_receipt.json",
        |_| {},
    );
    let cert_out = work.join("certificate.json");
    let handoff_out = work.join("certifyedge_handoff.json");
    let summary_out = work.join("certificate_summary.json");
    let formal_facts_out = work.join("certificate_formal_facts.json");

    with_source_commit("abcdef0123456789abcdef0123456789abcdef01", || {
        certifyedge_cmd()
            .arg("--release-mode")
            .args([
                "emit-pcs-certificate",
                "--handoff",
                handoff_path.to_str().unwrap(),
                "--profile-registry",
                repo_root().join("templates/profiles").to_str().unwrap(),
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
    assert_eq!(cert["status"], "CertificateChecked");
    assert_eq!(
        cert["property_id"],
        "scientific_computation.reproducibility_v0"
    );
    validate_computation_witness_schema(&cert).unwrap();

    let registry = PropertyProfileRegistry::from_certifyedge_root(&repo_root());
    let profile = registry
        .load("scientific_computation.reproducibility_v0")
        .unwrap();
    validate_certificate_json_for_profile(&cert, &profile).unwrap();
    assert_eq!(
        profile.output_certificate_artifact,
        ARTIFACT_COMPUTATION_WITNESS
    );

    let summary: Value =
        serde_json::from_str(&std::fs::read_to_string(&summary_out).unwrap()).unwrap();
    assert_eq!(
        summary["output_certificate_artifact"],
        "ComputationWitness.v0"
    );
    assert_eq!(summary["status"], "CertificateChecked");
    assert_eq!(
        summary["formal_predicate"],
        "ComputationWitnessBindsResults"
    );
    assert_eq!(summary["admissible_for_release"], true);

    let facts: Value =
        serde_json::from_str(&std::fs::read_to_string(&formal_facts_out).unwrap()).unwrap();
    assert_eq!(facts["formal_predicate"], "ComputationWitnessBindsResults");
    assert_eq!(facts["witness_id"], cert["certificate_id"]);
    assert_eq!(facts["run_receipt_hash"], cert["run_hash"]);
    assert_eq!(facts["admissible_for_release"], true);

    let outbound = load_handoff_manifest(&handoff_out).unwrap();
    assert_eq!(outbound.invariants["status"], "CertificateChecked");
    assert_eq!(
        outbound.invariants["run_hash"],
        cert["run_hash"].as_str().unwrap()
    );
    assert_eq!(
        outbound.invariants["property_id"],
        "scientific_computation.reproducibility_v0"
    );
    assert!(outbound
        .expected_outputs
        .contains_key("computation_bundle.certified.json"));
}

#[test]
fn test_handoff_emit_computation_rejected_with_repair_invariants() {
    let work = handoff_workdir("handoff_computation_reject");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_computation_runtime_handoff(
        &work,
        &computation_fixtures(),
        "invalid_exit_code_run_receipt.json",
        |_| {},
    );
    let cert_out = work.join("certificate.json");
    let handoff_out = work.join("certifyedge_handoff.json");
    let cx_out = work.join("computation_counterexample.json");

    let assert = certifyedge_cmd()
        .args([
            "emit-pcs-certificate",
            "--handoff",
            handoff_path.to_str().unwrap(),
            "--profile-registry",
            repo_root().join("templates/profiles").to_str().unwrap(),
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

    let stderr = String::from_utf8_lossy(&assert.get_output().stderr);
    assert!(stderr.contains("nonzero_exit_code"));

    let cert: Value = serde_json::from_str(&std::fs::read_to_string(&cert_out).unwrap()).unwrap();
    assert_eq!(cert["status"], "Rejected");
    assert!(cert["violations"][0]["failure_code"].is_string());
    validate_computation_witness_schema(&cert).unwrap();

    let outbound = load_handoff_manifest(&handoff_out).unwrap();
    assert_eq!(outbound.invariants["status"], "Rejected");
    assert_eq!(outbound.invariants["no_bundle_admissible"], "true");
    assert_eq!(outbound.invariants["failure_code"], "nonzero_exit_code");
    assert!(outbound.invariants.contains_key("repair_hint_kind"));
    assert!(std::fs::metadata(&cx_out).is_ok());
    assert_eq!(
        outbound.invariants["run_hash"],
        cert["run_hash"].as_str().unwrap()
    );
}

#[test]
fn test_handoff_emit_computation_rejected_dataset_hash_mismatch() {
    let work = handoff_workdir("handoff_computation_dataset_mismatch");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_computation_runtime_handoff(
        &work,
        &computation_fixtures(),
        "dataset_hash_mismatch_run_receipt.json",
        |_| {},
    );
    let cert_out = work.join("certificate.json");
    let handoff_out = work.join("certifyedge_handoff.json");

    let assert = certifyedge_cmd()
        .args([
            "emit-pcs-certificate",
            "--handoff",
            handoff_path.to_str().unwrap(),
            "--profile-registry",
            repo_root().join("templates/profiles").to_str().unwrap(),
            "--out",
            cert_out.to_str().unwrap(),
            "--handoff-out",
            handoff_out.to_str().unwrap(),
        ])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .success();

    let stderr = String::from_utf8_lossy(&assert.get_output().stderr);
    assert!(stderr.contains("dataset_hash_mismatch"));

    let cert: Value = serde_json::from_str(&std::fs::read_to_string(&cert_out).unwrap()).unwrap();
    assert_eq!(cert["status"], "Rejected");
    validate_computation_witness_schema(&cert).unwrap();

    let outbound = load_handoff_manifest(&handoff_out).unwrap();
    assert_eq!(outbound.invariants["failure_code"], "dataset_hash_mismatch");
}

#[test]
fn test_handoff_emit_computation_rejected_missing_code_commit() {
    let work = handoff_workdir("handoff_computation_missing_commit");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_computation_runtime_handoff(
        &work,
        &computation_fixtures(),
        "missing_code_commit_run_receipt.json",
        |_| {},
    );
    let cert_out = work.join("certificate.json");
    let handoff_out = work.join("certifyedge_handoff.json");

    let assert = certifyedge_cmd()
        .args([
            "emit-pcs-certificate",
            "--handoff",
            handoff_path.to_str().unwrap(),
            "--profile-registry",
            repo_root().join("templates/profiles").to_str().unwrap(),
            "--out",
            cert_out.to_str().unwrap(),
            "--handoff-out",
            handoff_out.to_str().unwrap(),
        ])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .success();

    let stderr = String::from_utf8_lossy(&assert.get_output().stderr);
    assert!(stderr.contains("missing_code_commit"));

    let cert: Value = serde_json::from_str(&std::fs::read_to_string(&cert_out).unwrap()).unwrap();
    assert_eq!(cert["status"], "Rejected");
    let outbound = load_handoff_manifest(&handoff_out).unwrap();
    assert_eq!(outbound.invariants["failure_code"], "missing_code_commit");
}

#[test]
fn test_handoff_emit_computation_rejected_result_hash_mismatch() {
    let work = handoff_workdir("handoff_computation_result_mismatch");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_computation_runtime_handoff(
        &work,
        &computation_fixtures(),
        "result_hash_mismatch_run_receipt.json",
        |_| {},
    );
    let cert_out = work.join("certificate.json");

    let assert = certifyedge_cmd()
        .args([
            "emit-pcs-certificate",
            "--handoff",
            handoff_path.to_str().unwrap(),
            "--profile-registry",
            repo_root().join("templates/profiles").to_str().unwrap(),
            "--out",
            cert_out.to_str().unwrap(),
        ])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .success();

    assert!(String::from_utf8_lossy(&assert.get_output().stderr).contains("result_hash_mismatch"));
    let cert: Value = serde_json::from_str(&std::fs::read_to_string(&cert_out).unwrap()).unwrap();
    assert_eq!(cert["status"], "Rejected");
    validate_computation_witness_schema(&cert).unwrap();
}

#[test]
fn test_handoff_emit_computation_rejected_environment_hash_mismatch() {
    let work = handoff_workdir("handoff_computation_env_mismatch");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_computation_runtime_handoff(
        &work,
        &computation_fixtures(),
        "environment_hash_mismatch_run_receipt.json",
        |_| {},
    );
    let cert_out = work.join("certificate.json");

    let assert = certifyedge_cmd()
        .args([
            "emit-pcs-certificate",
            "--handoff",
            handoff_path.to_str().unwrap(),
            "--profile-registry",
            repo_root().join("templates/profiles").to_str().unwrap(),
            "--out",
            cert_out.to_str().unwrap(),
        ])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .success();

    let stderr = String::from_utf8_lossy(&assert.get_output().stderr);
    assert!(stderr.contains("environment_digest_mismatch"));
    let cert: Value = serde_json::from_str(&std::fs::read_to_string(&cert_out).unwrap()).unwrap();
    assert_eq!(cert["status"], "Rejected");
    validate_computation_witness_schema(&cert).unwrap();
}

#[test]
fn test_handoff_emit_computation_rejected_missing_result_artifact() {
    let work = handoff_workdir("handoff_computation_missing_results");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_computation_runtime_handoff(
        &work,
        &computation_fixtures(),
        "missing_results_run_receipt.json",
        |_| {},
    );
    let cert_out = work.join("certificate.json");
    let cx_out = work.join("computation_counterexample.json");

    let assert = certifyedge_cmd()
        .args([
            "emit-pcs-certificate",
            "--handoff",
            handoff_path.to_str().unwrap(),
            "--profile-registry",
            repo_root().join("templates/profiles").to_str().unwrap(),
            "--out",
            cert_out.to_str().unwrap(),
            "--counterexample-out",
            cx_out.to_str().unwrap(),
        ])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .success();

    assert!(
        String::from_utf8_lossy(&assert.get_output().stderr).contains("missing_result_artifact")
    );
    assert!(std::fs::metadata(&cx_out).is_ok());
}
