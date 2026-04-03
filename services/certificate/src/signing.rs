//! Ed25519 signing for certificate payloads.

use ed25519_dalek::{Signature, Signer, SigningKey};
use rand::rngs::OsRng;

use crate::error::CertificateError;
use crate::format::CertificateFormat;

/// Signs certificate digests using Ed25519.
#[derive(Debug)]
pub struct CertificateSigner {
    signing_key: SigningKey,
}

impl CertificateSigner {
    pub fn new(_config: &crate::config::CertificateConfig) -> Result<Self, CertificateError> {
        let signing_key = SigningKey::generate(&mut OsRng);
        Ok(Self { signing_key })
    }

    pub async fn sign_certificate(
        &self,
        mut certificate: CertificateFormat,
    ) -> Result<CertificateFormat, CertificateError> {
        let digest = certificate_signing_digest(&certificate)?;
        let sig: Signature = self.signing_key.sign(&digest);
        certificate.ed25519_signature = Some(sig.to_bytes().to_vec());
        Ok(certificate)
    }

    pub fn verifying_key_bytes(&self) -> [u8; 32] {
        self.signing_key.verifying_key().to_bytes()
    }
}

/// Canonical byte sequence signed for Ed25519 (excludes signatures and volatile metadata).
pub fn certificate_signing_digest(cert: &CertificateFormat) -> Result<Vec<u8>, CertificateError> {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(cert.certificate_id.as_bytes());
    hasher.update(cert.version.as_bytes());
    hasher.update(&cert.spec_hash);
    hasher.update(&cert.lean_proof_hash);
    hasher.update(&cert.model_hash);
    hasher.update(cert.solver_version.as_bytes());
    hasher.update(cert.lean_version.as_bytes());
    for h in &cert.smt_proof_hashes {
        hasher.update(h);
    }
    for c in &cert.sbom_components {
        hasher.update(c.as_bytes());
    }
    Ok(hasher.finalize().to_vec())
}
