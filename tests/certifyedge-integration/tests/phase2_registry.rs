//! Phase 2: PCS artifact registry contribution and registry CLI gates.

#[path = "../common/support.rs"]
mod support;

use pcs_certificate::validate_registry_contribution_entry;
use serde_json::Value;

use support::{
    certifyedge_cmd, labtrust_release_fixture, pcs_cli_available, pcs_registry_check_artifact,
    repo_root, spec_path,
};

const REGISTRY_ENTRY_REQUIRED: &[&str] = &[
    "artifact_type",
    "schema",
    "schema_owner",
    "runtime_producer",
    "allowed_runtime_producers",
    "producer",
    "allowed_statuses",
    "required_release_fields",
    "semantic_checks",
    "consumer_repos",
    "canonical_hash_required",
    "release_mode_required",
];

const EXPECTED_SEMANTIC_CHECK_IDS: &[&str] = &[
    "trace_hash_matches_runtime_receipt",
    "status_is_certificate_checked_for_release",
    "source_commit_matches_release_manifest",
];

fn load_registry_contribution(artifact: &str) -> Value {
    let path = repo_root()
        .join("pcs_registry")
        .join(format!("{artifact}.registry.json"));
    serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap()
}

#[test]
fn test_trace_certificate_registry_contribution_matches_pcs_core_shape() {
    let entry = load_registry_contribution("TraceCertificate.v0");
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

    let producers = entry["allowed_runtime_producers"].as_array().unwrap();
    assert!(producers.iter().any(|v| v.as_str() == Some("CertifyEdge")));

    let consumers = entry["consumer_repos"].as_array().unwrap();
    assert!(consumers.iter().any(|v| v.as_str() == Some("LabTrust-Gym")));
    assert!(consumers.iter().any(|v| v.as_str() == Some("CertifyEdge")));

    let checks = entry["semantic_checks"].as_array().unwrap();
    assert_eq!(checks.len(), EXPECTED_SEMANTIC_CHECK_IDS.len());
    for (idx, expected_id) in EXPECTED_SEMANTIC_CHECK_IDS.iter().enumerate() {
        let check = &checks[idx];
        assert_eq!(check["check_id"], *expected_id);
        assert_eq!(check["severity"], "release_blocking");
        assert_eq!(check["responsible_component"], "CertifyEdge");
    }
}

#[test]
fn test_registry_contribution_validates_against_vendored_schema() {
    for artifact in ["TraceCertificate.v0", "ToolUseCertificate.v0"] {
        let entry = load_registry_contribution(artifact);
        validate_registry_contribution_entry(&entry)
            .unwrap_or_else(|e| panic!("{artifact} registry contribution schema: {e}"));
    }
}

#[test]
fn test_tool_use_certificate_registry_contribution_shape() {
    let entry = load_registry_contribution("ToolUseCertificate.v0");
    for key in REGISTRY_ENTRY_REQUIRED {
        assert!(
            entry.get(key).is_some(),
            "ToolUseCertificate registry missing {key}"
        );
    }
    assert_eq!(entry["artifact_type"], "ToolUseCertificate.v0");
    assert!(entry["required_release_fields"]
        .as_array()
        .unwrap()
        .iter()
        .any(|v| v.as_str() == Some("policy_hash")));
    let checks = entry["semantic_checks"].as_array().unwrap();
    assert!(checks
        .iter()
        .any(|c| c["check_id"] == "policy_hash_matches_runtime_policy"));
}

#[test]
fn test_registry_contribution_aligns_with_pcs_core_entry() {
    let pcs_core = std::env::var("PCS_CORE_PATH")
        .or_else(|_| std::env::var("PCS_CORE_ROOT"))
        .ok()
        .map(std::path::PathBuf::from);
    let Some(pcs_core) = pcs_core else {
        eprintln!("skip: PCS_CORE_PATH not set");
        return;
    };
    let upstream = pcs_core.join("examples/artifact_registry.valid.json");
    if !upstream.is_file() {
        eprintln!("skip: {}", upstream.display());
        return;
    }
    let upstream_registry: Value =
        serde_json::from_str(&std::fs::read_to_string(&upstream).unwrap()).unwrap();
    let pcs_entry = &upstream_registry["entries"]["TraceCertificate.v0"];
    let local = load_registry_contribution("TraceCertificate.v0");

    for key in [
        "artifact_type",
        "schema",
        "schema_owner",
        "runtime_producer",
        "allowed_runtime_producers",
        "allowed_statuses",
        "required_release_fields",
        "semantic_checks",
        "canonical_hash_required",
        "release_mode_required",
    ] {
        assert_eq!(
            local.get(key),
            pcs_entry.get(key),
            "registry contribution drift on {key}"
        );
    }
    for repo in pcs_entry["consumer_repos"].as_array().unwrap() {
        let consumers = local["consumer_repos"].as_array().unwrap();
        assert!(
            consumers.contains(repo),
            "local consumer_repos missing pcs-core entry {repo}"
        );
    }
}

#[test]
fn test_registry_check_artifact_passes_for_certificate() {
    if !pcs_cli_available() {
        eprintln!("skip: pcs CLI not on PATH");
        return;
    }
    pcs_registry_check_artifact(&labtrust_release_fixture("trace_certificate.json"));
}

#[test]
fn test_dev_emit_logs_registry_skip_when_pcs_unavailable() {
    if !cfg!(unix) {
        eprintln!("skip: PATH isolation test requires unix");
        return;
    }
    if pcs_cli_available() {
        eprintln!("skip: pcs CLI present; cannot assert dev registry skip warning");
        return;
    }

    let work = std::env::temp_dir().join("certifyedge-registry-skip-warning");
    std::fs::create_dir_all(&work).unwrap();
    let trace = repo_root().join("tests/labtrust/valid_trace.json");
    let out = work.join("trace_certificate.json");

    let output = certifyedge_cmd()
        .args([
            "emit-pcs-certificate",
            "--spec",
            spec_path("qc_release.stl").to_str().unwrap(),
            "--trace",
            trace.to_str().unwrap(),
            "--out",
            out.to_str().unwrap(),
        ])
        .env("PATH", "/usr/bin:/bin")
        .output()
        .expect("emit-pcs-certificate");

    assert!(
        output.status.success(),
        "emit failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("warning: pcs-core registry check skipped because pcs CLI unavailable"),
        "expected registry skip warning, got: {stderr}"
    );
}
