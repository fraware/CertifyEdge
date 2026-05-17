//! Certificate identity handoff across PCS release-run artifacts.

use predicates::prelude::*;

#[path = "../common/support.rs"]
mod support;

use support::{
    assert_certificate_id_handoff_through_pf_chain,
    assert_certificate_id_handoff_trace_to_certified_bundle,
    assert_release_run_manifest_provenance, certifyedge_cmd, release_manifest_certifyedge_commit,
    release_run_dir, release_run_fixture, repo_root, runbook_labtrust_release_trace,
    runbook_spec_qc_release, validate_release_run_fixture_tree, with_source_commit,
};

#[test]
fn test_emit_pcs_certificate_writes_summary_out() {
    let out = repo_root().join("target/emit_summary_out_test.json");
    let summary = repo_root().join("target/emit_summary_out_summary.json");

    with_source_commit(&release_manifest_certifyedge_commit(), || {
        certifyedge_cmd()
            .args([
                "--release-mode",
                "emit-pcs-certificate",
                "--spec",
                runbook_spec_qc_release().to_str().unwrap(),
                "--trace",
                runbook_labtrust_release_trace().to_str().unwrap(),
                "--out",
                out.to_str().unwrap(),
                "--summary-out",
                summary.to_str().unwrap(),
            ])
            .assert()
            .success()
            .stdout(predicate::str::contains("certificate_id"));
    });

    let cert: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&out).unwrap()).unwrap();
    let summary: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&summary).unwrap()).unwrap();
    for key in ["certificate_id", "trace_hash", "spec_hash", "source_commit"] {
        assert_eq!(summary[key], cert[key], "summary field {key}");
    }
}

#[test]
fn test_certificate_id_survives_labtrust_attachment() {
    let run = release_run_dir();
    assert_certificate_id_handoff_trace_to_certified_bundle(&run);
}

#[test]
fn test_certificate_id_survives_pf_verification_and_signing() {
    let run = release_run_dir();
    assert_certificate_id_handoff_through_pf_chain(&run);
}

#[test]
fn test_release_run_fixture_tree_and_manifest_provenance() {
    validate_release_run_fixture_tree();
    assert_release_run_manifest_provenance(&release_run_dir());
}

#[test]
fn test_trace_certificate_matches_committed_summary() {
    let cert: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(release_run_fixture("trace_certificate.json")).unwrap(),
    )
    .unwrap();
    let summary: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(release_run_fixture("certificate_summary.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(summary["certificate_id"], cert["certificate_id"]);
}
