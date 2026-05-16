use crate::hash::canonical_hash;
use crate::trace_certificate::TraceCertificateV0;

/// Compute `signature_or_digest` as the PCS canonical hash of the certificate body.
pub fn digest_certificate(cert: &TraceCertificateV0) -> String {
    let value = serde_json::to_value(cert).expect("certificate serializes");
    canonical_hash(&value)
}

pub fn verify_digest(cert: &TraceCertificateV0) -> bool {
    cert.signature_or_digest == digest_certificate(cert)
}
