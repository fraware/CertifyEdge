//! PCS `TraceCertificate.v0` construction, digest signing, and validation.

pub mod hash;
pub mod signing;
pub mod trace_certificate;
pub mod validation;

pub use trace_certificate::{
    build_certificate, certificate_from_json, certificate_to_json, counterexample_from_json,
    counterexample_to_json, explain_counterexample, CertificateOutcome, CertifyEdgeMetadata,
};
pub use validation::verify_certificate_document;
