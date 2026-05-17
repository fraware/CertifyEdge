//! PCS `HandoffManifest.v0` — consume runtime handoffs and emit certificate handoffs.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use chrono::Utc;
use labtrust_adapter::hash::pcs_digest;
use labtrust_adapter::LabTrustTrace;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use uuid::Uuid;

use crate::pcs_schema::validate_handoff_manifest_schema;
use crate::source_commit::is_placeholder_source_commit;
use crate::status_policy::STATUS_REJECTED;
use crate::trace_certificate::TraceCertificateV0;

pub const HANDOFF_KIND_RUNTIME_TO_CERTIFICATE: &str = "runtime_to_certificate";
pub const HANDOFF_KIND_CERTIFICATE_TO_BUNDLE: &str = "certificate_to_bundle";
pub const COMPONENT_CERTIFYEDGE: &str = "CertifyEdge";
pub const COMPONENT_LABTRUST: &str = "LabTrust-Gym";
pub const TRACE_ARTIFACT_NAME: &str = "trace.json";
pub const TRACE_CERTIFICATE_ARTIFACT_NAME: &str = "trace_certificate.json";
pub const ARTIFACT_TYPE_TRACE: &str = "Trace";
pub const ARTIFACT_TYPE_TRACE_CERTIFICATE: &str = "TraceCertificate.v0";

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct HandoffArtifactRef {
    pub artifact_type: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sha256: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct HandoffManifestV0 {
    pub schema_version: String,
    pub handoff_id: String,
    pub handoff_kind: String,
    pub from_component: String,
    pub to_component: String,
    pub created_at: String,
    pub source_repo: String,
    pub source_commit: String,
    pub input_artifacts: BTreeMap<String, HandoffArtifactRef>,
    pub expected_outputs: BTreeMap<String, HandoffArtifactRef>,
    pub invariants: BTreeMap<String, String>,
    pub status: String,
    pub signature_or_digest: String,
}

#[derive(Debug, Clone)]
pub struct HandoffEmitPlan {
    pub trace_path: PathBuf,
    pub spec_path: PathBuf,
    pub out_path: PathBuf,
}

/// Raw SHA-256 of file bytes (`sha256:<hex>`), matching pcs-core `file_digest`.
pub fn file_digest(content: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    let digest = Sha256::digest(content);
    format!("sha256:{digest:x}")
}

pub fn load_handoff_manifest(path: &Path) -> Result<HandoffManifestV0, String> {
    let text = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    let value: Value = serde_json::from_str(&text).map_err(|e| e.to_string())?;
    validate_handoff_manifest_schema(&value)?;
    verify_handoff_digest(&value)?;
    serde_json::from_value(value).map_err(|e| e.to_string())
}

pub fn finalize_handoff_digest(manifest: &mut HandoffManifestV0) {
    let value = serde_json::to_value(&*manifest).expect("handoff serializes");
    manifest.signature_or_digest = pcs_digest(&value);
}

pub fn handoff_manifest_to_json(manifest: &HandoffManifestV0) -> Result<String, String> {
    let mut value = serde_json::to_value(manifest).map_err(|e| e.to_string())?;
    let digest = pcs_digest(&value);
    if let Some(obj) = value.as_object_mut() {
        obj.insert("signature_or_digest".to_string(), Value::String(digest));
    }
    serde_json::to_string_pretty(&value).map_err(|e| e.to_string())
}

pub fn verify_handoff_digest(value: &Value) -> Result<(), String> {
    let expected = value
        .get("signature_or_digest")
        .and_then(|v| v.as_str())
        .ok_or_else(|| "handoff missing signature_or_digest".to_string())?;
    let actual = pcs_digest(value);
    if actual != expected {
        return Err(format!(
            "handoff signature_or_digest mismatch (expected {expected}, got {actual})"
        ));
    }
    Ok(())
}

pub fn spec_path_for_property_id(
    property_id: &str,
    certifyedge_root: &Path,
) -> Result<PathBuf, String> {
    let rel = match property_id {
        "hospital_lab.qc_release" => "templates/hospital_lab/qc_release.stl",
        _ => {
            return Err(format!(
                "unknown property profile {property_id}; add mapping in handoff.rs"
            ));
        }
    };
    let path = certifyedge_root.join(rel);
    if !path.is_file() {
        return Err(format!("property spec not found: {}", path.display()));
    }
    Ok(path)
}

pub fn plan_emit_from_handoff(
    handoff_path: &Path,
    handoff: &HandoffManifestV0,
    certifyedge_root: &Path,
    spec_override: Option<&Path>,
    trace_override: Option<&Path>,
    out_override: Option<&Path>,
    release_mode: bool,
) -> Result<HandoffEmitPlan, String> {
    if handoff.schema_version != "v0" {
        return Err(format!(
            "unsupported handoff schema_version: {}",
            handoff.schema_version
        ));
    }
    if handoff.handoff_kind != HANDOFF_KIND_RUNTIME_TO_CERTIFICATE {
        return Err(format!(
            "handoff_kind must be {HANDOFF_KIND_RUNTIME_TO_CERTIFICATE}, got {}",
            handoff.handoff_kind
        ));
    }
    if handoff.to_component != COMPONENT_CERTIFYEDGE {
        return Err(format!(
            "to_component must be {COMPONENT_CERTIFYEDGE}, got {}",
            handoff.to_component
        ));
    }
    if release_mode && is_placeholder_source_commit(&handoff.source_commit) {
        return Err(format!(
            "release mode: handoff source_commit is placeholder ({})",
            handoff.source_commit
        ));
    }

    let trace_entry = handoff
        .input_artifacts
        .get(TRACE_ARTIFACT_NAME)
        .ok_or_else(|| format!("input_artifacts must include {TRACE_ARTIFACT_NAME}"))?;
    if trace_entry.artifact_type != ARTIFACT_TYPE_TRACE
        && trace_entry.artifact_type != "LabTrust.Trace.v0"
    {
        return Err(format!(
            "{TRACE_ARTIFACT_NAME} artifact_type must be {ARTIFACT_TYPE_TRACE}"
        ));
    }
    let expected_sha = trace_entry
        .sha256
        .as_deref()
        .ok_or_else(|| format!("input_artifacts[{TRACE_ARTIFACT_NAME}] missing sha256"))?;

    let cert_output = handoff
        .expected_outputs
        .get(TRACE_CERTIFICATE_ARTIFACT_NAME)
        .ok_or_else(|| {
            format!("expected_outputs must include {TRACE_CERTIFICATE_ARTIFACT_NAME}")
        })?;
    if cert_output.artifact_type != ARTIFACT_TYPE_TRACE_CERTIFICATE {
        return Err(format!(
            "expected_outputs[{TRACE_CERTIFICATE_ARTIFACT_NAME}] must be {ARTIFACT_TYPE_TRACE_CERTIFICATE}"
        ));
    }

    let invariant_trace_hash = handoff
        .invariants
        .get("trace_hash")
        .ok_or_else(|| "invariants must include trace_hash".to_string())?;
    let property_id = handoff
        .invariants
        .get("property_id")
        .ok_or_else(|| "invariants must include property_id".to_string())?;

    let handoff_dir = handoff_path
        .parent()
        .ok_or_else(|| "handoff path has no parent directory".to_string())?;

    let trace_path = trace_override
        .map(Path::to_path_buf)
        .unwrap_or_else(|| handoff_dir.join(TRACE_ARTIFACT_NAME));
    let trace_bytes = std::fs::read(&trace_path)
        .map_err(|e| format!("read trace {}: {e}", trace_path.display()))?;
    let actual_file_digest = file_digest(&trace_bytes);
    if actual_file_digest != expected_sha {
        return Err(format!(
            "trace file hash mismatch: handoff expects {expected_sha}, file has {actual_file_digest}"
        ));
    }

    let trace: LabTrustTrace = labtrust_adapter::parse_and_validate_json(
        &String::from_utf8(trace_bytes).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())?;
    if trace.trace_hash != *invariant_trace_hash {
        return Err(format!(
            "trace_hash invariant mismatch: handoff {invariant_trace_hash}, trace {}",
            trace.trace_hash
        ));
    }

    let spec_path = spec_override.map(Path::to_path_buf).unwrap_or_else(|| {
        spec_path_for_property_id(property_id, certifyedge_root)
            .unwrap_or_else(|_| handoff_dir.join("qc_release.stl"))
    });
    let spec = labtrust_adapter::PropertySpec::load(&spec_path)
        .map_err(|e| format!("load spec {}: {e}", spec_path.display()))?;
    if spec.property_id.as_str() != property_id {
        return Err(format!(
            "property_id mismatch: handoff {property_id}, spec {}",
            spec.property_id.as_str()
        ));
    }

    let out_path = out_override
        .map(Path::to_path_buf)
        .unwrap_or_else(|| handoff_dir.join(TRACE_CERTIFICATE_ARTIFACT_NAME));

    Ok(HandoffEmitPlan {
        trace_path,
        spec_path,
        out_path,
    })
}

pub fn build_certificate_to_bundle_handoff(
    cert: &TraceCertificateV0,
    cert_path: &Path,
) -> Result<HandoffManifestV0, String> {
    let cert_bytes = std::fs::read(cert_path)
        .map_err(|e| format!("read certificate {}: {e}", cert_path.display()))?;
    let cert_digest = file_digest(&cert_bytes);
    let cert_name = cert_path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or(TRACE_CERTIFICATE_ARTIFACT_NAME);

    let rejected = cert.status == STATUS_REJECTED;
    let expected_outputs = if rejected {
        let mut out = BTreeMap::new();
        if cert.counterexample_ref.is_some() {
            out.insert(
                "counterexample.json".to_string(),
                HandoffArtifactRef {
                    artifact_type: "LabTrust.Counterexample.v0".to_string(),
                    sha256: None,
                },
            );
        }
        out
    } else {
        BTreeMap::from([(
            "science_claim_bundle.certified.json".to_string(),
            HandoffArtifactRef {
                artifact_type: "ScienceClaimBundle.v0".to_string(),
                sha256: None,
            },
        )])
    };

    Ok(HandoffManifestV0 {
        schema_version: "v0".to_string(),
        handoff_id: format!("handoff-certifyedge-{}", Uuid::new_v4()),
        handoff_kind: HANDOFF_KIND_CERTIFICATE_TO_BUNDLE.to_string(),
        from_component: COMPONENT_CERTIFYEDGE.to_string(),
        to_component: COMPONENT_LABTRUST.to_string(),
        created_at: Utc::now().format("%Y-%m-%dT%H:%M:%SZ").to_string(),
        source_repo: cert.source_repo.clone(),
        source_commit: cert.source_commit.clone(),
        input_artifacts: BTreeMap::from([(
            cert_name.to_string(),
            HandoffArtifactRef {
                artifact_type: ARTIFACT_TYPE_TRACE_CERTIFICATE.to_string(),
                sha256: Some(cert_digest),
            },
        )]),
        expected_outputs,
        invariants: BTreeMap::from([
            ("certificate_id".to_string(), cert.certificate_id.clone()),
            ("trace_hash".to_string(), cert.trace_hash.clone()),
            ("status".to_string(), cert.status.clone()),
        ]),
        status: "Validated".to_string(),
        signature_or_digest: String::new(),
    })
}

pub fn write_handoff_manifest(path: &Path, manifest: &HandoffManifestV0) -> Result<(), String> {
    let json = handoff_manifest_to_json(manifest)?;
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent).map_err(|e| e.to_string())?;
        }
    }
    std::fs::write(path, format!("{json}\n")).map_err(|e| e.to_string())
}

/// Validate handoff JSON against vendored schema; optional `pcs validate` when installed.
pub fn validate_handoff_artifact(path: &Path, require_pcs_cli: bool) -> Result<(), String> {
    let text = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    let value: serde_json::Value = serde_json::from_str(&text).map_err(|e| e.to_string())?;
    validate_handoff_manifest_schema(&value)?;
    verify_handoff_digest(&value)?;
    crate::pcs_validate::validate_with_pcs_cli(path, require_pcs_cli)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn file_digest_is_raw_bytes() {
        assert_eq!(
            file_digest(b"{}"),
            "sha256:44136fa355b3678a1146ad16f7e8649e94fb4fc21fe77e8310c060f61caaff8a"
        );
    }

    #[test]
    fn output_handoff_invariants_use_certificate_fields() {
        let cert = TraceCertificateV0 {
            certificate_id: "cert-trace-test".into(),
            schema_version: "v0".into(),
            trace_hash: "sha256:c3e8a3dc4ad86d533de1dfa4ae7fe2a338c2cff3c945404c96a75216524d58cd"
                .into(),
            spec_hash: "sha256:7c66dfcf640d382653d8ce7c2c700371d72ff0d6fb59156d411cf2aa9a7dfe5e"
                .into(),
            property_id: "hospital_lab.qc_release".into(),
            checker: "CertifyEdge".into(),
            checker_version: "0.1.0".into(),
            status: "CertificateChecked".into(),
            counterexample_ref: None,
            created_at: "2026-05-17T15:37:01Z".into(),
            producer: "CertifyEdge".into(),
            producer_version: "0.1.0".into(),
            source_repo: crate::trace_certificate::SOURCE_REPO.to_string(),
            source_commit: "cb6848001e2e60a484e04eba5ad6be3fe2e4eccc".into(),
            signature_or_digest:
                "sha256:34dec7d507119b599c2e2611bff0f984359a64d12cee2600901cc73537fd6f2b".into(),
        };
        let dir = std::env::temp_dir().join(format!("ce-handoff-{}", Uuid::new_v4()));
        std::fs::create_dir_all(&dir).unwrap();
        let cert_path = dir.join("trace_certificate.json");
        std::fs::write(&cert_path, r#"{"certificate_id":"cert-trace-test"}"#).unwrap();
        let handoff = build_certificate_to_bundle_handoff(&cert, &cert_path).unwrap();
        assert_eq!(handoff.handoff_kind, HANDOFF_KIND_CERTIFICATE_TO_BUNDLE);
        assert_eq!(handoff.invariants["certificate_id"], cert.certificate_id);
        assert_eq!(handoff.invariants["status"], "CertificateChecked");
    }

    #[test]
    fn rejected_handoff_does_not_promise_certified_bundle() {
        let cert = TraceCertificateV0 {
            certificate_id: "cert-trace-rejected".into(),
            schema_version: "v0".into(),
            trace_hash: "sha256:c3e8a3dc4ad86d533de1dfa4ae7fe2a338c2cff3c945404c96a75216524d58cd"
                .into(),
            spec_hash: "sha256:7c66dfcf640d382653d8ce7c2c700371d72ff0d6fb59156d411cf2aa9a7dfe5e"
                .into(),
            property_id: "hospital_lab.qc_release".into(),
            checker: "CertifyEdge".into(),
            checker_version: "0.1.0".into(),
            status: STATUS_REJECTED.into(),
            counterexample_ref: Some("counterexample.json".into()),
            created_at: "2026-05-17T15:37:01Z".into(),
            producer: "CertifyEdge".into(),
            producer_version: "0.1.0".into(),
            source_repo: crate::trace_certificate::SOURCE_REPO.to_string(),
            source_commit: "cb6848001e2e60a484e04eba5ad6be3fe2e4eccc".into(),
            signature_or_digest:
                "sha256:34dec7d507119b599c2e2611bff0f984359a64d12cee2600901cc73537fd6f2b".into(),
        };
        let dir = std::env::temp_dir().join(format!("ce-handoff-reject-{}", Uuid::new_v4()));
        std::fs::create_dir_all(&dir).unwrap();
        let cert_path = dir.join("trace_certificate.json");
        std::fs::write(&cert_path, r#"{"certificate_id":"cert-trace-rejected"}"#).unwrap();
        let handoff = build_certificate_to_bundle_handoff(&cert, &cert_path).unwrap();
        assert_eq!(handoff.invariants["status"], STATUS_REJECTED);
        assert!(!handoff
            .expected_outputs
            .contains_key("science_claim_bundle.certified.json"));
        assert!(handoff.expected_outputs.contains_key("counterexample.json"));
    }
}
