//! Canonical PCS release-candidate fixtures synced from pcs-core/examples/labtrust-release/.

#[path = "../common/support.rs"]
mod support;

use support::{
    certifyedge_cmd, labtrust_release_fixture, pcs_core_rc_constants, validate_certificate_against_pcs_core,
};

#[test]
fn test_trace_certificate_matches_pcs_core_rc() {
    let rc = pcs_core_rc_constants();
    let cert: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(labtrust_release_fixture("trace_certificate.json")).unwrap(),
    )
    .unwrap();

    assert_eq!(cert["certificate_id"].as_str().unwrap(), rc.certificate_id);
    assert_eq!(cert["source_commit"].as_str().unwrap(), rc.source_commit);
    assert_eq!(cert["trace_hash"].as_str().unwrap(), rc.trace_hash);
    assert_eq!(cert["status"].as_str().unwrap(), "CertificateChecked");
    assert_eq!(
        cert["signature_or_digest"].as_str().unwrap(),
        rc.signature_or_digest
    );
    assert_eq!(
        cert["source_repo"].as_str().unwrap(),
        "https://github.com/fraware/CertifyEdge"
    );

    let manifest: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(labtrust_release_fixture("PCS_CORE_RC_MANIFEST.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(
        manifest["artifacts"]["science_claim_bundle.certified.json"]
            .as_str()
            .unwrap(),
        rc.certified_bundle_hash
    );
    assert_eq!(
        manifest["certifyedge_commit"].as_str().unwrap(),
        rc.source_commit
    );

    validate_certificate_against_pcs_core(&labtrust_release_fixture("trace_certificate.json"));
}

#[test]
fn test_verify_canonical_rc_certificate_against_trace() {
    certifyedge_cmd()
        .args([
            "verify-certificate",
            labtrust_release_fixture("trace_certificate.json")
                .to_str()
                .unwrap(),
            "--trace",
            labtrust_release_fixture("trace.json").to_str().unwrap(),
        ])
        .assert()
        .success();
}
