use serde::Serialize;

use crate::trace_certificate::TraceCertificateV0;

/// Minimal certificate identity for downstream PCS handoff (`--summary-out`).
#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct CertificateEmitSummary {
    pub certificate_id: String,
    pub trace_hash: String,
    pub spec_hash: String,
    pub source_commit: String,
}

impl CertificateEmitSummary {
    pub fn from_certificate(cert: &TraceCertificateV0) -> Self {
        Self {
            certificate_id: cert.certificate_id.clone(),
            trace_hash: cert.trace_hash.clone(),
            spec_hash: cert.spec_hash.clone(),
            source_commit: cert.source_commit.clone(),
        }
    }
}

pub fn summary_to_json(summary: &CertificateEmitSummary) -> Result<String, serde_json::Error> {
    serde_json::to_string_pretty(summary)
}
