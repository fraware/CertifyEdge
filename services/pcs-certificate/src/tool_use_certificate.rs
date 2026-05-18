//! `ToolUseCertificate.v0` construction for tool-use profiles.

use serde::{Deserialize, Serialize};
use uuid::Uuid;

use crate::metadata::CertifyEdgeMetadata;
use crate::property_profile::PropertyProfile;
use crate::status_policy::STATUS_CERTIFICATE_PENDING;
use crate::tool_use_check::ToolUseCheckResult;
use crate::tool_use_trace::{policy_hash_from_trace, ToolUseTraceV0};
use crate::tool_use_violation::ToolUseViolationV0;
use crate::trace_certificate::{CHECKER, SCHEMA_VERSION, SOURCE_REPO};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct ToolUseCertificateV0 {
    pub schema_version: String,
    pub certificate_id: String,
    pub trace_hash: String,
    pub policy_hash: String,
    pub property_id: String,
    pub checker: String,
    pub checker_version: String,
    pub status: String,
    pub violations: Vec<ToolUseViolationV0>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub counterexample_ref: Option<String>,
    pub source_repo: String,
    pub source_commit: String,
    pub signature_or_digest: String,
}

pub fn build_tool_use_certificate(
    trace: &ToolUseTraceV0,
    profile: &PropertyProfile,
    check: &ToolUseCheckResult,
    meta: &CertifyEdgeMetadata,
    counterexample_ref: Option<String>,
) -> Result<ToolUseCertificateV0, String> {
    if profile.property_id != "agent_tool_use.safety_v0" {
        return Err(format!(
            "tool-use certificate build requires agent_tool_use.safety_v0 profile, got {}",
            profile.property_id
        ));
    }

    let status = crate::property_profile::status_for_check(profile, check.passed).to_string();
    crate::property_profile::validate_certificate_status_transition_for_profile(
        STATUS_CERTIFICATE_PENDING,
        &status,
        profile,
        meta.release_mode,
    )?;

    let mut certificate = ToolUseCertificateV0 {
        schema_version: SCHEMA_VERSION.to_string(),
        certificate_id: format!("cert-tool-{}", Uuid::new_v4()),
        trace_hash: trace.trace_hash.clone(),
        policy_hash: policy_hash_from_trace(trace),
        property_id: profile.property_id.clone(),
        checker: CHECKER.to_string(),
        checker_version: meta.checker_version.clone(),
        status,
        violations: if check.passed {
            vec![]
        } else {
            check.violations.clone()
        },
        counterexample_ref: if check.passed {
            None
        } else {
            counterexample_ref
        },
        source_repo: SOURCE_REPO.to_string(),
        source_commit: meta.source_commit.clone(),
        signature_or_digest: String::new(),
    };

    certificate.signature_or_digest = crate::signing::digest_tool_use_certificate(&certificate);
    Ok(certificate)
}

pub fn certificate_to_json(cert: &ToolUseCertificateV0) -> Result<String, serde_json::Error> {
    serde_json::to_string_pretty(cert)
}
