//! Placeholder for future Sigstore / cosign integration.

use crate::error::CertificateError;
use crate::format::CertificateFormat;

/// Reserved for OIDC + Sigstore signing flows.
pub struct SigstoreIntegration {
    _enabled: bool,
}

impl SigstoreIntegration {
    pub fn from_config(config: &crate::config::CertificateConfig) -> Self {
        Self {
            _enabled: config.enable_sigstore,
        }
    }

    pub async fn attach_signature_if_enabled(
        &self,
        certificate: CertificateFormat,
    ) -> Result<CertificateFormat, CertificateError> {
        // Real Sigstore integration would run here; offline tests keep this as a no-op.
        Ok(certificate)
    }
}
