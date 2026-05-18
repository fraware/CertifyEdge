//! Phase 2: PCS artifact registry contribution and registry CLI gates.

#[path = "../common/support.rs"]
mod support;

use serde_json::Value;

use support::{
    labtrust_release_fixture, pcs_cli_available, pcs_registry_check_artifact, repo_root,
};

const REGISTRY_ENTRY_REQUIRED: &[&str] = &[
    "artifact_type",
    "schema",
    "producer",
    "allowed_statuses",
    "required_release_fields",
    "semantic_checks",
    "consumer_repos",
    "canonical_hash_required",
    "release_mode_required",
];

#[test]
fn test_registry_contribution_matches_pcs_core_registry_shape() {
    let path = repo_root().join("pcs_registry/TraceCertificate.v0.registry.json");
    let entry: Value = serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
    for key in REGISTRY_ENTRY_REQUIRED {
        assert!(
            entry.get(key).is_some(),
            "registry contribution missing required field {key}"
        );
    }
    assert_eq!(entry["artifact_type"], "TraceCertificate.v0");
    assert_eq!(entry["schema_owner"], "pcs-core");
    assert_eq!(entry["runtime_producer"], "CertifyEdge");
    assert!(entry["canonical_hash_required"].as_bool().unwrap());
    assert!(entry["release_mode_required"].as_bool().unwrap());
    let consumers = entry["consumer_repos"].as_array().unwrap();
    assert!(consumers.iter().any(|v| v.as_str() == Some("LabTrust-Gym")));
    assert!(consumers.iter().any(|v| v.as_str() == Some("CertifyEdge")));
}

#[test]
fn test_registry_check_artifact_passes_for_certificate() {
    if !pcs_cli_available() {
        eprintln!("skip: pcs CLI not on PATH");
        return;
    }
    pcs_registry_check_artifact(&labtrust_release_fixture("trace_certificate.json"));
}
