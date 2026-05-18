//! PCS `TraceCertificate.v0` construction, digest signing, and validation.

pub mod emit_summary;
pub mod handoff;
pub mod hash;
pub mod metadata;
pub mod pcs_schema;
pub mod pcs_validate;
pub mod property_profile;
pub mod signing;
pub mod source_commit;
pub mod status_policy;
pub mod trace_certificate;
pub mod validation;

pub use emit_summary::{summary_to_json, CertificateEmitSummary};
pub use handoff::{
    build_certificate_to_bundle_handoff, file_digest, finalize_handoff_digest,
    load_handoff_manifest, plan_emit_from_handoff, validate_handoff_artifact,
    write_handoff_manifest, HandoffArtifactRef, HandoffEmitPlan, HandoffManifestV0,
    COMPONENT_CERTIFYEDGE, COMPONENT_LABTRUST, HANDOFF_KIND_CERTIFICATE_TO_BUNDLE,
    HANDOFF_KIND_RUNTIME_TO_CERTIFICATE,
};
pub use metadata::CertifyEdgeMetadata;
pub use pcs_schema::validate_handoff_manifest_schema;
pub use pcs_schema::validate_trace_certificate_schema;
pub use pcs_validate::{registry_check_artifact, validate_certificate_artifact};
pub use property_profile::{load_property_profile, PropertyProfile};
pub use source_commit::{
    certifyedge_repo_root, is_placeholder_source_commit, is_zero_source_commit, labtrust_gym_root,
    SourceCommitResolution, ZERO_SOURCE_COMMIT,
};
pub use status_policy::{
    is_terminal_certificate_status, validate_certificate_status_transition,
    STATUS_CERTIFICATE_CHECKED, STATUS_CERTIFICATE_PENDING, STATUS_REJECTED,
};
pub use trace_certificate::{
    build_certificate, certificate_from_json, certificate_to_json, counterexample_from_json,
    counterexample_to_json, explain_counterexample, CertificateOutcome, SOURCE_REPO,
};
pub use validation::verify_certificate_document;
