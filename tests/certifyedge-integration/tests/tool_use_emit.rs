//! Tool-use profile certificate emit (ToolUseCertificate.v0).

#[path = "../common/support.rs"]
mod support;

use pcs_certificate::{
    emit_certificate_for_profile, load_handoff_manifest, validate_certificate_json_for_profile,
    validate_tool_use_certificate_schema, CertifyEdgeMetadata, PropertyProfileRegistry,
    ARTIFACT_TOOL_USE_CERTIFICATE,
};
use serde_json::Value;

use support::{certifyedge_cmd, repo_root, with_source_commit};

fn tool_use_trace(path: &str) -> std::path::PathBuf {
    repo_root().join("tests/tool_use").join(path)
}

#[test]
fn test_agent_tool_use_profile_loads() {
    let registry = PropertyProfileRegistry::from_certifyedge_root(&repo_root());
    let profile = registry.load("agent_tool_use.safety_v0").expect("profile");
    assert_eq!(
        profile.output_certificate_artifact,
        ARTIFACT_TOOL_USE_CERTIFICATE
    );
}

#[test]
fn test_emit_tool_use_certificate_valid_trace() {
    let work = repo_root().join("target/tool_use_emit_ok");
    std::fs::create_dir_all(&work).unwrap();
    let trace_path = tool_use_trace("valid_tool_trace.json");
    let out = work.join("certificate.json");
    let spec = repo_root().join("templates/tool_use/no_unauthorized_tool.stl");

    with_source_commit("abcdef0123456789abcdef0123456789abcdef01", || {
        certifyedge_cmd()
            .arg("--release-mode")
            .args([
                "emit-pcs-certificate",
                "--spec",
                spec.to_str().unwrap(),
                "--trace",
                trace_path.to_str().unwrap(),
                "--profile-registry",
                repo_root().join("templates/profiles").to_str().unwrap(),
                "--out",
                out.to_str().unwrap(),
            ])
            .env("CERTIFYEDGE_ROOT", repo_root())
            .assert()
            .success();
    });

    let cert: Value = serde_json::from_str(&std::fs::read_to_string(&out).unwrap()).unwrap();
    assert_eq!(cert["status"], "CertificateChecked");
    assert_eq!(cert["property_id"], "agent_tool_use.safety_v0");
    validate_tool_use_certificate_schema(&cert).unwrap();
}

#[test]
fn test_emit_tool_use_certificate_rejected_with_repair_hint() {
    let work = repo_root().join("target/tool_use_emit_reject");
    std::fs::create_dir_all(&work).unwrap();
    let trace_path = tool_use_trace("unauthorized_tool_trace.json");
    let out = work.join("certificate.json");
    let cx_out = work.join("counterexample.json");
    let handoff_out = work.join("certificate_handoff.json");
    let spec = repo_root().join("templates/tool_use/no_unauthorized_tool.stl");

    let assert = certifyedge_cmd()
        .args([
            "emit-pcs-certificate",
            "--spec",
            spec.to_str().unwrap(),
            "--trace",
            trace_path.to_str().unwrap(),
            "--profile-registry",
            repo_root().join("templates/profiles").to_str().unwrap(),
            "--out",
            out.to_str().unwrap(),
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
    assert!(stderr.contains("responsible_component"));
    assert!(stderr.contains("fix_trace_or_policy"));

    let cert: Value = serde_json::from_str(&std::fs::read_to_string(&out).unwrap()).unwrap();
    assert_eq!(cert["status"], "Rejected");
    assert!(cert["violations"].as_array().unwrap().len() >= 1);
    assert!(cx_out.is_file());

    let handoff = load_handoff_manifest(&handoff_out).unwrap();
    assert_eq!(handoff.invariants["status"], "Rejected");
    assert_eq!(handoff.invariants["no_bundle_admissible"], "true");
    assert_eq!(handoff.invariants["failure_code"], "unauthorized_tool_call");
    assert_eq!(
        handoff.invariants["responsible_component"],
        "runtime_producer"
    );
    assert_eq!(
        handoff.invariants["repair_hint_kind"],
        "fix_trace_or_policy"
    );
    assert!(handoff.expected_outputs.is_empty());
}

#[test]
fn test_emit_tool_use_release_mode_rejects_missing_policy_hash() {
    let work = repo_root().join("target/tool_use_emit_no_policy_hash");
    std::fs::create_dir_all(&work).unwrap();
    let trace_path = tool_use_trace("missing_policy_hash_trace.json");
    let out = work.join("certificate.json");
    let spec = repo_root().join("templates/tool_use/no_unauthorized_tool.stl");

    with_source_commit("abcdef0123456789abcdef0123456789abcdef01", || {
        certifyedge_cmd()
            .arg("--release-mode")
            .args([
                "emit-pcs-certificate",
                "--spec",
                spec.to_str().unwrap(),
                "--trace",
                trace_path.to_str().unwrap(),
                "--profile-registry",
                repo_root().join("templates/profiles").to_str().unwrap(),
                "--out",
                out.to_str().unwrap(),
            ])
            .env("CERTIFYEDGE_ROOT", repo_root())
            .assert()
            .failure();
    });
}

#[test]
fn test_rejected_tool_use_summary_includes_repair_hint() {
    let work = repo_root().join("target/tool_use_emit_summary_repair");
    std::fs::create_dir_all(&work).unwrap();
    let trace_path = tool_use_trace("unauthorized_tool_trace.json");
    let out = work.join("certificate.json");
    let summary = work.join("certificate_summary.json");
    let spec = repo_root().join("templates/tool_use/no_unauthorized_tool.stl");

    certifyedge_cmd()
        .args([
            "emit-pcs-certificate",
            "--spec",
            spec.to_str().unwrap(),
            "--trace",
            trace_path.to_str().unwrap(),
            "--profile-registry",
            repo_root().join("templates/profiles").to_str().unwrap(),
            "--out",
            out.to_str().unwrap(),
            "--summary-out",
            summary.to_str().unwrap(),
        ])
        .env("CERTIFYEDGE_ROOT", repo_root())
        .assert()
        .success();

    let summary: Value = serde_json::from_str(&std::fs::read_to_string(&summary).unwrap()).unwrap();
    assert_eq!(summary["status"], "Rejected");
    assert_eq!(summary["failure_code"], "unauthorized_tool_call");
    assert_eq!(summary["responsible_component"], "runtime_producer");
    assert_eq!(summary["repair_hint"]["kind"], "fix_trace_or_policy");
    assert_eq!(
        summary["output_certificate_artifact"],
        "ToolUseCertificate.v0"
    );
}

#[test]
fn test_tool_use_certificate_in_process() {
    let registry = PropertyProfileRegistry::from_certifyedge_root(&repo_root());
    let profile = registry.load("agent_tool_use.safety_v0").unwrap();
    let trace_bytes = std::fs::read(tool_use_trace("valid_tool_trace.json")).unwrap();
    let meta = CertifyEdgeMetadata::dev_default();
    let outcome = emit_certificate_for_profile(
        &profile,
        &registry,
        &repo_root().join(&profile.template),
        &trace_bytes,
        &meta,
        None,
    )
    .unwrap();
    let value = outcome.certificate.as_value();
    validate_certificate_json_for_profile(&value, &profile).unwrap();
}
