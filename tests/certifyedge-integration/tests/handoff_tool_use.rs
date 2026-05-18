//! Handoff-driven emit for agent_tool_use.safety_v0 (ToolUseCertificate.v0).

#[path = "../common/support.rs"]
mod support;

#[path = "../common/handoff_fixtures.rs"]
mod handoff_fixtures;

use pcs_certificate::{
    load_handoff_manifest, validate_certificate_json_for_profile,
    validate_tool_use_certificate_schema, PropertyProfileRegistry, ARTIFACT_TOOL_USE_CERTIFICATE,
};
use serde_json::Value;

use handoff_fixtures::{handoff_workdir, write_tool_use_runtime_handoff};
use support::{certifyedge_cmd, repo_root, with_source_commit};

fn tool_use_trace(name: &str) -> std::path::PathBuf {
    repo_root().join("tests/tool_use").join(name)
}

#[test]
fn test_handoff_emit_tool_use_certificate_checked() {
    let work = handoff_workdir("handoff_tool_use_ok");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path =
        write_tool_use_runtime_handoff(&work, tool_use_trace("valid_tool_trace.json"), |_| {});
    let cert_out = work.join("certificate.json");
    let handoff_out = work.join("certifyedge_handoff.json");
    let summary_out = work.join("certificate_summary.json");

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
            ])
            .env("CERTIFYEDGE_ROOT", repo_root())
            .assert()
            .success();
    });

    let cert: Value = serde_json::from_str(&std::fs::read_to_string(&cert_out).unwrap()).unwrap();
    assert_eq!(cert["status"], "CertificateChecked");
    assert_eq!(cert["property_id"], "agent_tool_use.safety_v0");
    validate_tool_use_certificate_schema(&cert).unwrap();

    let registry = PropertyProfileRegistry::from_certifyedge_root(&repo_root());
    let profile = registry.load("agent_tool_use.safety_v0").unwrap();
    validate_certificate_json_for_profile(&cert, &profile).unwrap();
    assert_eq!(
        profile.output_certificate_artifact,
        ARTIFACT_TOOL_USE_CERTIFICATE
    );

    let summary: Value =
        serde_json::from_str(&std::fs::read_to_string(&summary_out).unwrap()).unwrap();
    assert_eq!(
        summary["output_certificate_artifact"],
        "ToolUseCertificate.v0"
    );
    assert_eq!(summary["status"], "CertificateChecked");

    let outbound = load_handoff_manifest(&handoff_out).unwrap();
    assert_eq!(outbound.invariants["status"], "CertificateChecked");
    assert!(outbound
        .expected_outputs
        .contains_key("tool_use_bundle.certified.json"));
}

#[test]
fn test_handoff_emit_tool_use_rejected_with_repair_invariants() {
    let work = handoff_workdir("handoff_tool_use_reject");
    std::fs::create_dir_all(&work).unwrap();
    let handoff_path = write_tool_use_runtime_handoff(
        &work,
        tool_use_trace("unauthorized_tool_trace.json"),
        |_| {},
    );
    let cert_out = work.join("certificate.json");
    let handoff_out = work.join("certifyedge_handoff.json");
    let cx_out = work.join("counterexample.json");

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
    assert!(stderr.contains("unauthorized_tool_call"));

    let cert: Value = serde_json::from_str(&std::fs::read_to_string(&cert_out).unwrap()).unwrap();
    assert_eq!(cert["status"], "Rejected");
    assert!(cert["violations"][0]["failure_code"].is_string());

    let outbound = load_handoff_manifest(&handoff_out).unwrap();
    assert_eq!(outbound.invariants["status"], "Rejected");
    assert_eq!(outbound.invariants["no_bundle_admissible"], "true");
    assert_eq!(
        outbound.invariants["failure_code"],
        "unauthorized_tool_call"
    );
    assert!(outbound.expected_outputs.is_empty());
}
