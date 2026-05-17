//! PCS `TraceCertificate.v0` construction, digest signing, and validation.

pub mod emit_summary;
pub mod hash;
pub mod metadata;
pub mod pcs_schema;
pub mod pcs_validate;
pub mod signing;
pub mod source_commit;
pub mod trace_certificate;
pub mod validation;

pub use emit_summary::{summary_to_json, CertificateEmitSummary};
pub use metadata::CertifyEdgeMetadata;
pub use pcs_schema::validate_trace_certificate_schema;
pub use pcs_validate::validate_certificate_artifact;
pub use source_commit::{
    certifyedge_repo_root, is_placeholder_source_commit, is_zero_source_commit, labtrust_gym_root,
    SourceCommitResolution, ZERO_SOURCE_COMMIT,
};
pub use trace_certificate::{
    build_certificate, certificate_from_json, certificate_to_json, counterexample_from_json,
    counterexample_to_json, explain_counterexample, CertificateOutcome, SOURCE_REPO,
};
pub use validation::verify_certificate_document;
