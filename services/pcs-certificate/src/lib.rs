//! PCS `TraceCertificate.v0` construction, digest signing, and validation.

pub mod hash;
pub mod metadata;
pub mod pcs_schema;
pub mod pcs_validate;
pub mod signing;
pub mod trace_certificate;
pub mod validation;

pub use metadata::{is_zero_source_commit, CertifyEdgeMetadata, ZERO_SOURCE_COMMIT};
pub use pcs_schema::validate_trace_certificate_schema;
pub use pcs_validate::validate_certificate_artifact;
pub use trace_certificate::{
    build_certificate, certificate_from_json, certificate_to_json, counterexample_from_json,
    counterexample_to_json, explain_counterexample, CertificateOutcome,
};
pub use validation::verify_certificate_document;
