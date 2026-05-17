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
fn test_rejected_certificate_is_terminal_in_release_mode() {
    assert!(
        validate_certificate_status_transition(STATUS_REJECTED, STATUS_CERTIFICATE_CHECKED, true)
            .is_err(),
        "release mode must not transition away from Rejected"
    );
    validate_certificate_status_transition(STATUS_REJECTED, STATUS_REJECTED, true)
        .expect("rejected is stable");
}
