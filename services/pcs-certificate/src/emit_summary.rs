use serde::Serialize;

use crate::emitted_certificate::EmittedCertificate;
use crate::formal_facts::{admissible_for_release, ARTIFACT_CERTIFICATE_FORMAL_FACTS};
use crate::property_profile::PropertyProfile;
use crate::repair_hint::{repair_hint_from_profile, RepairHint};

/// Certificate emit summary for PCS release-run handoff (`--summary-out`).
#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct CertificateEmitSummary {
    pub certificate_id: String,
    pub trace_hash: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub spec_hash: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub policy_hash: Option<String>,
    pub property_id: String,
    pub status: String,
    pub output_certificate_artifact: String,
    pub source_commit: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub counterexample_ref: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub failure_code: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub responsible_component: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub repair_hint: Option<RepairHint>,
    pub formal_predicate: String,
    pub formal_fact_artifact: String,
    pub admissible_for_release: bool,
}

impl CertificateEmitSummary {
    pub fn from_emitted(cert: &EmittedCertificate) -> Self {
        Self::from_emitted_with_rejection(cert, None, None)
    }

    pub fn from_emitted_with_rejection(
        cert: &EmittedCertificate,
        failure_code: Option<&str>,
        profile: Option<&PropertyProfile>,
    ) -> Self {
        let (failure_code, responsible_component, repair_hint) =
            rejection_summary_fields(profile, failure_code);
        let (formal_predicate, admissible) = profile
            .map(|p| {
                (
                    p.formalization.certificate_predicate.clone(),
                    admissible_for_release(p, cert.status()),
                )
            })
            .unwrap_or_else(|| (String::new(), cert.status() == "CertificateChecked"));
        let base = |certificate_id: String,
                    trace_hash: String,
                    spec_hash: Option<String>,
                    policy_hash: Option<String>,
                    property_id: String,
                    status: String,
                    source_commit: String,
                    counterexample_ref: Option<String>| {
            Self {
                certificate_id,
                trace_hash,
                spec_hash,
                policy_hash,
                property_id,
                status,
                output_certificate_artifact: cert.output_artifact_type().to_string(),
                source_commit,
                counterexample_ref,
                failure_code: failure_code.clone(),
                responsible_component: responsible_component.clone(),
                repair_hint: repair_hint.clone(),
                formal_predicate: formal_predicate.clone(),
                formal_fact_artifact: ARTIFACT_CERTIFICATE_FORMAL_FACTS.to_string(),
                admissible_for_release: admissible,
            }
        };
        match cert {
            EmittedCertificate::Trace(c) => base(
                c.certificate_id.clone(),
                c.trace_hash.clone(),
                Some(c.spec_hash.clone()),
                None,
                c.property_id.clone(),
                c.status.clone(),
                c.source_commit.clone(),
                c.counterexample_ref.clone(),
            ),
            EmittedCertificate::ToolUse(c) => base(
                c.certificate_id.clone(),
                c.trace_hash.clone(),
                None,
                Some(c.policy_hash.clone()),
                c.property_id.clone(),
                c.status.clone(),
                c.source_commit.clone(),
                c.counterexample_ref.clone(),
            ),
            EmittedCertificate::Computation(c) => base(
                c.certificate_id.clone(),
                c.run_hash.clone(),
                None,
                None,
                c.property_id.clone(),
                c.status.clone(),
                c.source_commit.clone(),
                c.counterexample_ref.clone(),
            ),
        }
    }
}

fn rejection_summary_fields(
    profile: Option<&PropertyProfile>,
    failure_code: Option<&str>,
) -> (Option<String>, Option<String>, Option<RepairHint>) {
    let Some(code) = failure_code else {
        return (None, None, None);
    };
    let Some(profile) = profile else {
        return (Some(code.to_string()), None, None);
    };
    let Some(entry) = profile.repair_hint_for(code) else {
        return (Some(code.to_string()), None, None);
    };
    (
        Some(code.to_string()),
        entry.responsible_component.clone(),
        Some(repair_hint_from_profile(entry)),
    )
}

pub fn summary_to_json(summary: &CertificateEmitSummary) -> Result<String, serde_json::Error> {
    serde_json::to_string_pretty(summary)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::property_profile::{ProfileFormalization, PropertyProfile};
    use std::collections::BTreeMap;

    #[test]
    fn rejected_summary_includes_repair_hint() {
        let profile = PropertyProfile {
            property_id: "agent_tool_use.safety_v0".into(),
            template: "templates/tool_use/no_unauthorized_tool.stl".into(),
            input_trace_artifact: "ToolUseTrace.v0".into(),
            output_certificate_artifact: "ToolUseCertificate.v0".into(),
            counterexample_artifact: "ToolUseCounterexample.v0".into(),
            valid_success_status: "CertificateChecked".into(),
            valid_failure_status: "Rejected".into(),
            required_release_fields: vec!["trace_hash".into()],
            repair_hints: BTreeMap::from([(
                "unauthorized_tool_call".into(),
                crate::property_profile::ProfileRepairHint {
                    kind: "fix_trace_or_policy".into(),
                    command: "regenerate runtime trace after policy enforcement".into(),
                    responsible_component: Some("runtime_producer".into()),
                },
            )]),
            supporting_artifacts: vec![],
            formalization: ProfileFormalization {
                certificate_predicate: "CertificateMatchesRuntime".into(),
                required_fields: vec![
                    "certificate_id".into(),
                    "trace_hash".into(),
                    "status".into(),
                ],
                admissible_status: Some("CertificateChecked".into()),
                rejected_status: Some("Rejected".into()),
                stale_status: Some("Stale".into()),
            },
        };
        let summary = CertificateEmitSummary::from_emitted_with_rejection(
            &EmittedCertificate::ToolUse(crate::tool_use_certificate::ToolUseCertificateV0 {
                schema_version: "v0".into(),
                certificate_id: "cert-1".into(),
                trace_hash:
                    "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into(),
                policy_hash:
                    "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into(),
                property_id: "agent_tool_use.safety_v0".into(),
                checker: "CertifyEdge".into(),
                checker_version: "0.1.0".into(),
                status: "Rejected".into(),
                violations: vec![crate::tool_use_violation::ToolUseViolationV0::new(
                    "unauthorized_tool_call",
                    "x",
                )],
                counterexample_ref: Some("counterexample.json".into()),
                source_repo: "https://github.com/fraware/CertifyEdge".into(),
                source_commit: "abcdef0123456789abcdef0123456789abcdef01".into(),
                signature_or_digest:
                    "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc".into(),
            }),
            Some("unauthorized_tool_call"),
            Some(&profile),
        );
        assert_eq!(summary.formal_predicate, "CertificateMatchesRuntime");
        assert!(!summary.admissible_for_release);
        assert_eq!(
            summary.failure_code.as_deref(),
            Some("unauthorized_tool_call")
        );
        assert_eq!(
            summary.responsible_component.as_deref(),
            Some("runtime_producer")
        );
        assert_eq!(
            summary.repair_hint.as_ref().unwrap().kind,
            "fix_trace_or_policy"
        );
    }
}
