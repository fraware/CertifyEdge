use crate::trace_certificate::{TraceCertificateV0, SOURCE_REPO};
use serde_json::Value;
use thiserror::Error;

use crate::pcs_schema::validate_trace_certificate_schema;
use crate::signing::verify_digest;

const TRACE_CERT_STATUSES: &[&str] = &[
    "CertificatePending",
    "CertificateChecked",
    "Rejected",
    "Stale",
];

#[derive(Debug, Error)]
pub enum CertificateValidationError {
    #[error("invalid certificate JSON: {0}")]
    Json(String),
    #[error("PCS validation failed: {0}")]
    Pcs(String),
    #[error("signature_or_digest mismatch")]
    DigestMismatch,
    #[error("trace hash mismatch: certificate {cert} != trace {trace}")]
    TraceHashMismatch { cert: String, trace: String },
    #[error("release mode: source_repo must be {expected}, got {got}")]
    ReleaseSourceRepoMismatch { expected: String, got: String },
}

pub fn verify_certificate_document(
    cert_text: &str,
    expected_trace_hash: Option<&str>,
    release_mode: bool,
) -> Result<TraceCertificateV0, CertificateValidationError> {
    let value: Value = serde_json::from_str(cert_text)
        .map_err(|e| CertificateValidationError::Json(e.to_string()))?;

    if !value.is_object() || value.get("certificate_id").is_none() {
        return Err(CertificateValidationError::Pcs(
            "not a TraceCertificate.v0 document".into(),
        ));
    }

    validate_trace_certificate_shape(&value)?;
    validate_trace_certificate_schema(&value).map_err(CertificateValidationError::Pcs)?;

    if release_mode {
        let repo = value
            .get("source_repo")
            .and_then(|v| v.as_str())
            .unwrap_or("");
        if repo != SOURCE_REPO {
            return Err(CertificateValidationError::ReleaseSourceRepoMismatch {
                expected: SOURCE_REPO.to_string(),
                got: repo.to_string(),
            });
        }
    }

    let cert: TraceCertificateV0 = serde_json::from_value(value)
        .map_err(|e| CertificateValidationError::Json(e.to_string()))?;

    if !verify_digest(&cert) {
        return Err(CertificateValidationError::DigestMismatch);
    }

    if let Some(trace_hash) = expected_trace_hash {
        if cert.trace_hash != trace_hash {
            return Err(CertificateValidationError::TraceHashMismatch {
                cert: cert.trace_hash.clone(),
                trace: trace_hash.to_string(),
            });
        }
    }

    Ok(cert)
}

fn validate_trace_certificate_shape(value: &Value) -> Result<(), CertificateValidationError> {
    let obj = value
        .as_object()
        .ok_or_else(|| CertificateValidationError::Pcs("root must be object".into()))?;

    let required = [
        "certificate_id",
        "schema_version",
        "trace_hash",
        "spec_hash",
        "property_id",
        "checker",
        "checker_version",
        "status",
        "counterexample_ref",
        "created_at",
        "producer",
        "producer_version",
        "source_repo",
        "source_commit",
        "signature_or_digest",
    ];

    for key in required {
        if !obj.contains_key(key) {
            return Err(CertificateValidationError::Pcs(format!(
                "missing field {key}"
            )));
        }
    }

    if obj.get("schema_version").and_then(|v| v.as_str()) != Some("v0") {
        return Err(CertificateValidationError::Pcs(
            "schema_version must be v0".into(),
        ));
    }

    let status = obj
        .get("status")
        .and_then(|v| v.as_str())
        .ok_or_else(|| CertificateValidationError::Pcs("status must be string".into()))?;

    if !TRACE_CERT_STATUSES.contains(&status) {
        return Err(CertificateValidationError::Pcs(format!(
            "invalid status: {status}"
        )));
    }

    for digest_field in ["trace_hash", "spec_hash", "signature_or_digest"] {
        let digest = obj
            .get(digest_field)
            .and_then(|v| v.as_str())
            .ok_or_else(|| {
                CertificateValidationError::Pcs(format!("{digest_field} must be string"))
            })?;
        if !digest.starts_with("sha256:") || digest.len() != 71 {
            return Err(CertificateValidationError::Pcs(format!(
                "{digest_field} must match sha256:<64 hex>"
            )));
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trace_certificate::SOURCE_REPO;
    use serde_json::json;

    fn sample_cert_json(source_repo: &str) -> String {
        serde_json::to_string(&json!({
            "certificate_id": "cert-trace-886c95f0-5d63-42d6-aa13-5891c12c5a6a",
            "schema_version": "v0",
            "trace_hash": "sha256:c3e8a3dc4ad86d533de1dfa4ae7fe2a338c2cff3c945404c96a75216524d58cd",
            "spec_hash": "sha256:7c66dfcf640d382653d8ce7c2c700371d72ff0d6fb59156d411cf2aa9a7dfe5e",
            "property_id": "hospital_lab.qc_release",
            "checker": "CertifyEdge",
            "checker_version": "0.1.0",
            "status": "CertificateChecked",
            "counterexample_ref": null,
            "created_at": "2026-05-17T15:37:01Z",
            "producer": "CertifyEdge",
            "producer_version": "0.1.0",
            "source_repo": source_repo,
            "source_commit": "cb6848001e2e60a484e04eba5ad6be3fe2e4eccc",
            "signature_or_digest": "sha256:34dec7d507119b599c2e2611bff0f984359a64d12cee2600901cc73537fd6f2b"
        }))
        .unwrap()
    }

    #[test]
    fn release_mode_rejects_wrong_source_repo_before_digest() {
        let json = sample_cert_json("https://github.com/example/wrong");
        let err = verify_certificate_document(&json, None, true).unwrap_err();
        assert!(matches!(
            err,
            CertificateValidationError::ReleaseSourceRepoMismatch { .. }
        ));
    }

    #[test]
    fn release_mode_accepts_canonical_source_repo() {
        let json = sample_cert_json(SOURCE_REPO);
        verify_certificate_document(&json, None, true).expect("canonical RC certificate");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::trace_certificate::SOURCE_REPO;
    use serde_json::json;

    fn sample_cert_json(source_repo: &str) -> String {
        serde_json::to_string(&json!({
            "certificate_id": "cert-trace-886c95f0-5d63-42d6-aa13-5891c12c5a6a",
            "schema_version": "v0",
            "trace_hash": "sha256:c3e8a3dc4ad86d533de1dfa4ae7fe2a338c2cff3c945404c96a75216524d58cd",
            "spec_hash": "sha256:7c66dfcf640d382653d8ce7c2c700371d72ff0d6fb59156d411cf2aa9a7dfe5e",
            "property_id": "hospital_lab.qc_release",
            "checker": "CertifyEdge",
            "checker_version": "0.1.0",
            "status": "CertificateChecked",
            "counterexample_ref": null,
            "created_at": "2026-05-17T15:37:01Z",
            "producer": "CertifyEdge",
            "producer_version": "0.1.0",
            "source_repo": source_repo,
            "source_commit": "cb6848001e2e60a484e04eba5ad6be3fe2e4eccc",
            "signature_or_digest": "sha256:34dec7d507119b599c2e2611bff0f984359a64d12cee2600901cc73537fd6f2b"
        }))
        .unwrap()
    }

    #[test]
    fn release_mode_rejects_wrong_source_repo_before_digest() {
        let json = sample_cert_json("https://github.com/example/wrong");
        let err = verify_certificate_document(&json, None, true).unwrap_err();
        assert!(matches!(
            err,
            CertificateValidationError::ReleaseSourceRepoMismatch { .. }
        ));
    }

    #[test]
    fn release_mode_accepts_canonical_source_repo() {
        let json = sample_cert_json(SOURCE_REPO);
        verify_certificate_document(&json, None, true).expect("canonical RC certificate");
    }
}
