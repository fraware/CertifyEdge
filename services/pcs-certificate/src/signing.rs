use crate::hash::canonical_hash;
use crate::tool_use_certificate::ToolUseCertificateV0;
use crate::trace_certificate::TraceCertificateV0;

/// Compute `signature_or_digest` as the PCS canonical hash of the certificate body.
pub fn digest_certificate(cert: &TraceCertificateV0) -> String {
    let value = serde_json::to_value(cert).expect("certificate serializes");
    canonical_hash(&value)
}

pub fn digest_tool_use_certificate(cert: &ToolUseCertificateV0) -> String {
    let value = serde_json::to_value(cert).expect("tool-use certificate serializes");
    canonical_hash(&value)
}

pub fn verify_digest(cert: &TraceCertificateV0) -> bool {
    cert.signature_or_digest == digest_certificate(cert)
}

#[cfg(test)]
mod tests {
    use super::*;
    use labtrust_adapter::hash::pcs_digest;
    use serde_json::Value;

    #[test]
    fn certifyedge_hash_matches_pcs_core_trace_certificate_vector() {
        let input: Value = serde_json::from_str(include_str!(
            "../../../tests/fixtures/pcs-hash-vectors/TraceCertificate.v0/input.json"
        ))
        .unwrap();
        let expected =
            include_str!("../../../tests/fixtures/pcs-hash-vectors/TraceCertificate.v0/digest.txt")
                .trim();
        assert_eq!(pcs_digest(&input), expected);
        let cert: TraceCertificateV0 = serde_json::from_value(input).unwrap();
        assert_eq!(digest_certificate(&cert), expected);
    }
}
