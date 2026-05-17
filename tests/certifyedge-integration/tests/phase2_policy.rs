//! Phase 2: canonical hash vectors and certificate status policy.

use labtrust_adapter::hash::pcs_digest;
use pcs_certificate::{
    validate_certificate_status_transition, STATUS_CERTIFICATE_CHECKED, STATUS_CERTIFICATE_PENDING,
    STATUS_REJECTED,
};
use serde_json::{json, Value};

#[test]
fn test_trace_certificate_hash_matches_pcs_core_vector() {
    let input: Value = serde_json::from_str(include_str!(
        "../../../tests/fixtures/pcs-hash-vectors/TraceCertificate.v0/input.json"
    ))
    .unwrap();
    let expected =
        include_str!("../../../tests/fixtures/pcs-hash-vectors/TraceCertificate.v0/digest.txt")
            .trim();
    assert_eq!(pcs_digest(&input), expected);
}

#[test]
fn test_handoff_manifest_hash_matches_pcs_core_vector() {
    let input: Value = serde_json::from_str(include_str!(
        "../../../tests/fixtures/pcs-hash-vectors/HandoffManifest.v0/input.json"
    ))
    .unwrap();
    let expected =
        include_str!("../../../tests/fixtures/pcs-hash-vectors/HandoffManifest.v0/digest.txt")
            .trim();
    assert_eq!(pcs_digest(&input), expected);
}

#[test]
fn test_hash_ignores_signature_or_digest() {
    let with_placeholder = json!({
        "schema_version": "v0",
        "handoff_id": "handoff-test",
        "handoff_kind": "runtime_to_certificate",
        "status": "Validated",
        "signature_or_digest": "sha256:0000000000000000000000000000000000000000000000000000000000000000"
    });
    let without = json!({
        "schema_version": "v0",
        "handoff_id": "handoff-test",
        "handoff_kind": "runtime_to_certificate",
        "status": "Validated",
    });
    assert_eq!(pcs_digest(&with_placeholder), pcs_digest(&without));
}

#[test]
fn test_certificate_status_transition_certificate_pending_to_checked() {
    validate_certificate_status_transition(
        STATUS_CERTIFICATE_PENDING,
        STATUS_CERTIFICATE_CHECKED,
        true,
    )
    .expect("pending -> checked");
}

#[test]
fn test_hash_vectors_match_pcs_core_when_path_set() {
    let pcs_core = std::env::var("PCS_CORE_PATH")
        .or_else(|_| std::env::var("PCS_CORE_ROOT"))
        .ok()
        .map(std::path::PathBuf::from);
    let Some(pcs_core) = pcs_core else {
        eprintln!("skip: PCS_CORE_PATH / PCS_CORE_ROOT not set");
        return;
    };
    let repo_root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let vectors = pcs_core.join("test_vectors/hash");
    for (artifact, vector_name) in [
        ("TraceCertificate.v0", "trace_certificate.vector.json"),
        ("HandoffManifest.v0", "handoff_manifest.vector.json"),
    ] {
        let vector_path = vectors.join(vector_name);
        let vector: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(&vector_path).unwrap()).unwrap();
        let expected = vector["expected_digest"].as_str().unwrap();
        let local_digest_path = repo_root
            .join("tests/fixtures/pcs-hash-vectors")
            .join(artifact)
            .join("digest.txt");
        let local_digest = std::fs::read_to_string(&local_digest_path)
            .unwrap()
            .trim()
            .to_string();
        assert_eq!(local_digest, expected, "{artifact} digest drift");
        let input_rel = vector["input"].as_str().unwrap();
        let upstream = pcs_core.join(input_rel);
        let local_input = repo_root
            .join("tests/fixtures/pcs-hash-vectors")
            .join(artifact)
            .join("input.json");
        let upstream_bytes = std::fs::read(&upstream).unwrap();
        let local_bytes = std::fs::read(&local_input).unwrap();
        assert_eq!(upstream_bytes, local_bytes, "{artifact} input drift");
    }
}

#[test]
fn test_rejected_certificate_is_terminal_in_release_mode() {
    assert!(
        validate_certificate_status_transition(STATUS_REJECTED, STATUS_CERTIFICATE_CHECKED, true)
            .is_err(),
        "release mode must not transition away from Rejected"
    );
    validate_certificate_status_transition(STATUS_REJECTED, STATUS_REJECTED, true)
        .expect("rejected is stable");
}
