use crate::trace_certificate::TraceCertificateV0;
use serde_json::Value;
use thiserror::Error;

use crate::signing::verify_digest;

const TRACE_CERT_STATUSES: &[&str] = &["CertificatePending", "CertificateChecked", "Rejected", "Stale"];

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
}

pub fn verify_certificate_document(
    cert_text: &str,
    expected_trace_hash: Option<&str>,
) -> Result<TraceCertificateV0, CertificateValidationError> {
    let value: Value =
        serde_json::from_str(cert_text).map_err(|e| CertificateValidationError::Json(e.to_string()))?;

    if !value.is_object() || value.get("certificate_id").is_none() {
        return Err(CertificateValidationError::Pcs(
            "not a TraceCertificate.v0 document".into(),
        ));
    }

    validate_trace_certificate_shape(&value)?;

    let cert: TraceCertificateV0 =
        serde_json::from_value(value).map_err(|e| CertificateValidationError::Json(e.to_string()))?;

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
            return Err(CertificateValidationError::Pcs(format!("missing field {key}")));
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
            .ok_or_else(|| CertificateValidationError::Pcs(format!("{digest_field} must be string")))?;
        if !digest.starts_with("sha256:") || digest.len() != 71 {
            return Err(CertificateValidationError::Pcs(format!(
                "{digest_field} must match sha256:<64 hex>"
            )));
        }
    }

    Ok(())
}
