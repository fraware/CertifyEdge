//! PCS v0.1 clean-checkout chain — CertifyEdge segment and optional full handoff.

use assert_cmd::Command;
use predicates::prelude::*;

#[path = "../common/support.rs"]
mod support;

use support::{
    assert_certificate_semantics_equal, certifyedge_cmd, labtrust_fixture,
    labtrust_release_certificate_fixture, repo_root, spec_path,
    validate_certificate_against_pcs_core, RELEASE_FIXTURE_SOURCE_COMMIT,
};

fn spec_qc_release() -> std::path::PathBuf {
    spec_path("qc_release.stl")
}

fn certifyedge() -> Command {
    certifyedge_cmd()
}

/// LabTrust export + CertifyEdge emit + verify + attach (no PF / Scientific Memory).
/// Run when `PCS_RUN_CLEAN_CHECKOUT=1` and LabTrust-Gym is a sibling checkout.
#[test]
#[ignore]
fn test_pcs_v01_clean_checkout_through_certified() {
    let gym = std::env::var("LABTRUST_GYM_ROOT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| repo_root().join("../LabTrust-Gym"));
    if !gym.join("policy").is_dir() {
        eprintln!("skip: LabTrust-Gym not at {}", gym.display());
        return;
    }

    let script = repo_root().join("scripts/pcs-v01-clean-checkout.sh");
    let status = std::process::Command::new("bash")
        .arg(&script)
        .arg("--through-certified")
        .env("LABTRUST_GYM_ROOT", &gym)
        .env("CERTIFYEDGE_ROOT", repo_root())
        .env("PCS_DETERMINISTIC", "1")
        .status()
        .expect("spawn clean-checkout script");
    assert!(
        status.success(),
        "pcs-v01-clean-checkout --through-certified failed: {status:?}"
    );
}

/// CertifyEdge segment using committed traces (same hashes as LabTrust-Gym export).
#[test]
fn test_pcs_v01_clean_checkout_certifyedge_segment() {
    let work = repo_root().join("target/clean_checkout_segment");
    std::fs::create_dir_all(&work).unwrap();
    let cert_path = work.join("trace_certificate.json");
    let trace = labtrust_fixture("valid_trace.json");

    let previous = std::env::var("CERTIFYEDGE_SOURCE_COMMIT").ok();
    std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", RELEASE_FIXTURE_SOURCE_COMMIT);

    certifyedge()
        .args([
            "emit-pcs-certificate",
            "--spec",
            spec_qc_release().to_str().unwrap(),
            "--trace",
            trace.to_str().unwrap(),
            "--out",
            cert_path.to_str().unwrap(),
        ])
        .assert()
        .success()
        .stdout(predicate::str::contains("CertificateChecked"));

    certifyedge()
        .args([
            "verify-certificate",
            cert_path.to_str().unwrap(),
            "--trace",
            trace.to_str().unwrap(),
        ])
        .assert()
        .success();

    validate_certificate_against_pcs_core(&cert_path);

    let fixture_value: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(labtrust_release_certificate_fixture()).unwrap(),
    )
    .unwrap();
    let emitted: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&cert_path).unwrap()).unwrap();
    assert_certificate_semantics_equal(&emitted, &fixture_value);

    if let Some(value) = previous {
        std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", value);
    } else {
        std::env::remove_var("CERTIFYEDGE_SOURCE_COMMIT");
    }
}
