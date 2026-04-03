//! Certificate signature verification.

use ed25519_dalek::{Signature, Verifier, VerifyingKey};

use crate::error::CertificateError;
use crate::format::CertificateFormat;
use crate::signing::certificate_signing_digest;

#[derive(Debug, Clone)]
pub struct CertificateVerifier {
    verifying_key: VerifyingKey,
}

impl CertificateVerifier {
    pub fn new(config: &crate::config::CertificateConfig) -> Result<Self, CertificateError> {
        let bytes = config
            .ed25519_verifying_key
            .as_ref()
            .ok_or(CertificateError::MissingVerificationKey)?;
        if bytes.len() != 32 {
            return Err(CertificateError::InvalidVerificationKey);
        }
        let arr: [u8; 32] = bytes
            .as_slice()
            .try_into()
            .map_err(|_| CertificateError::InvalidVerificationKey)?;
        Ok(Self {
            verifying_key: VerifyingKey::from_bytes(&arr)
                .map_err(|_| CertificateError::InvalidVerificationKey)?,
        })
    }

    pub async fn verify_certificate(
        &self,
        certificate: &CertificateFormat,
    ) -> Result<crate::VerificationResult, CertificateError> {
        let digest = certificate_signing_digest(certificate)?;
        let Some(sig_bytes) = certificate.ed25519_signature.as_ref() else {
            return Ok(crate::VerificationResult::failure(
                certificate.certificate_id.clone(),
                vec!["Missing Ed25519 signature".to_string()],
            ));
        };
        if sig_bytes.len() != 64 {
            return Ok(crate::VerificationResult::failure(
                certificate.certificate_id.clone(),
                vec!["Invalid signature length".to_string()],
            ));
        }
        let signature = Signature::try_from(sig_bytes.as_slice())
            .map_err(|_| CertificateError::InvalidSignature)?;
        match self.verifying_key.verify(&digest, &signature) {
            Ok(()) => Ok(crate::VerificationResult::success(
                certificate.certificate_id.clone(),
            )),
            Err(_) => Ok(crate::VerificationResult::failure(
                certificate.certificate_id.clone(),
                vec!["Ed25519 verification failed".to_string()],
            )),
        }
    }
}
