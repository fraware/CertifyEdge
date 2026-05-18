use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use pcs_certificate::{
    file_digest, finalize_handoff_digest, write_handoff_manifest, HandoffArtifactRef,
    HandoffManifestV0, COMPONENT_CERTIFYEDGE, COMPONENT_LABTRUST,
    HANDOFF_KIND_RUNTIME_TO_CERTIFICATE,
};

use crate::support::{labtrust_release_fixture, pcs_core_rc_constants, repo_root};

pub fn write_runtime_handoff(dir: &Path, mutate: impl FnOnce(&mut HandoffManifestV0)) -> PathBuf {
    write_runtime_handoff_with_trace(dir, labtrust_release_fixture("trace.json"), mutate)
}

pub fn write_runtime_handoff_with_trace(
    dir: &Path,
    trace_src: PathBuf,
    mutate: impl FnOnce(&mut HandoffManifestV0),
) -> PathBuf {
    let trace_bytes = std::fs::read(&trace_src).unwrap();
    let trace_file_digest = file_digest(&trace_bytes);
    let trace_path = dir.join("trace.json");
    std::fs::write(&trace_path, &trace_bytes).unwrap();
    let trace: labtrust_adapter::LabTrustTrace =
        labtrust_adapter::parse_and_validate_json(&String::from_utf8(trace_bytes).unwrap())
            .expect("trace fixture parses");
    let trace_hash = trace.trace_hash.clone();
    let rc = pcs_core_rc_constants();

    let mut handoff = HandoffManifestV0 {
        schema_version: "v0".to_string(),
        handoff_id: "handoff-labtrust-to-certifyedge-test".to_string(),
        handoff_kind: HANDOFF_KIND_RUNTIME_TO_CERTIFICATE.to_string(),
        from_component: COMPONENT_LABTRUST.to_string(),
        to_component: COMPONENT_CERTIFYEDGE.to_string(),
        created_at: "2026-05-17T17:01:22Z".to_string(),
        source_repo: "https://github.com/fraware/LabTrust-Gym".to_string(),
        source_commit: "4c5439ae358733f9a4c4a58e33fdaed1ab0d29de".to_string(),
        input_artifacts: BTreeMap::from([(
            "trace.json".to_string(),
            HandoffArtifactRef {
                artifact_type: "Trace".to_string(),
                sha256: Some(trace_file_digest),
            },
        )]),
        expected_outputs: BTreeMap::from([(
            "trace_certificate.json".to_string(),
            HandoffArtifactRef {
                artifact_type: "TraceCertificate.v0".to_string(),
                sha256: None,
            },
        )]),
        invariants: BTreeMap::from([
            ("trace_hash".to_string(), trace_hash),
            (
                "property_id".to_string(),
                "hospital_lab.qc_release".to_string(),
            ),
        ]),
        status: "Validated".to_string(),
        signature_or_digest: String::new(),
    };
    mutate(&mut handoff);
    finalize_handoff_digest(&mut handoff);
    let path = dir.join("labtrust_to_certifyedge_handoff.json");
    write_handoff_manifest(&path, &handoff).unwrap();
    path
}

pub fn handoff_workdir(name: &str) -> PathBuf {
    repo_root().join(format!("target/{name}"))
}

/// Runtime handoff for `agent_tool_use.safety_v0` (ToolUseTrace.v0 → ToolUseCertificate.v0).
pub fn write_tool_use_runtime_handoff(
    dir: &Path,
    trace_src: PathBuf,
    mutate: impl FnOnce(&mut HandoffManifestV0),
) -> PathBuf {
    let trace_bytes = std::fs::read(&trace_src).unwrap();
    let trace_file_digest = file_digest(&trace_bytes);
    let trace_path = dir.join("trace.json");
    std::fs::write(&trace_path, &trace_bytes).unwrap();
    let trace: serde_json::Value =
        serde_json::from_slice(&trace_bytes).expect("tool-use trace JSON");
    let trace_hash = trace["trace_hash"]
        .as_str()
        .expect("trace_hash")
        .to_string();

    let mut handoff = HandoffManifestV0 {
        schema_version: "v0".to_string(),
        handoff_id: "handoff-tool-use-to-certifyedge-test".to_string(),
        handoff_kind: HANDOFF_KIND_RUNTIME_TO_CERTIFICATE.to_string(),
        from_component: COMPONENT_LABTRUST.to_string(),
        to_component: COMPONENT_CERTIFYEDGE.to_string(),
        created_at: "2026-05-17T17:01:22Z".to_string(),
        source_repo: "https://github.com/fraware/CertifyEdge".to_string(),
        source_commit: "abcdef0123456789abcdef0123456789abcdef01".to_string(),
        input_artifacts: BTreeMap::from([(
            "trace.json".to_string(),
            HandoffArtifactRef {
                artifact_type: "ToolUseTrace.v0".to_string(),
                sha256: Some(trace_file_digest),
            },
        )]),
        expected_outputs: BTreeMap::from([(
            "certificate.json".to_string(),
            HandoffArtifactRef {
                artifact_type: "ToolUseCertificate.v0".to_string(),
                sha256: None,
            },
        )]),
        invariants: BTreeMap::from([
            ("trace_hash".to_string(), trace_hash),
            (
                "property_id".to_string(),
                "agent_tool_use.safety_v0".to_string(),
            ),
        ]),
        status: "Validated".to_string(),
        signature_or_digest: String::new(),
    };
    mutate(&mut handoff);
    finalize_handoff_digest(&mut handoff);
    let path = dir.join("runtime_to_certifyedge_handoff.json");
    write_handoff_manifest(&path, &handoff).unwrap();
    path
}
