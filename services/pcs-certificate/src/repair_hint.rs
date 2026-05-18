//! Structured certificate failures with repair hints (PF explain / operator recovery).

use serde::Serialize;
use serde_json::Value;

use crate::property_profile::{ProfileRepairHint, PropertyProfile};

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct RepairHint {
    pub kind: String,
    pub command: String,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct CertificateFailure {
    pub failure_code: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub responsible_component: Option<String>,
    pub artifact: String,
    pub message: String,
    pub repair_hint: RepairHint,
}

impl CertificateFailure {
    pub fn to_error_string(&self) -> String {
        serde_json::to_string_pretty(self).unwrap_or_else(|_| self.message.clone())
    }
}

pub fn certificate_failure(
    failure_code: &str,
    artifact: &str,
    message: impl Into<String>,
    repair_hint: RepairHint,
) -> String {
    CertificateFailure {
        failure_code: failure_code.to_string(),
        responsible_component: None,
        artifact: artifact.to_string(),
        message: message.into(),
        repair_hint,
    }
    .to_error_string()
}

pub fn certificate_failure_with_component(
    failure_code: &str,
    responsible_component: &str,
    artifact: &str,
    message: impl Into<String>,
    repair_hint: RepairHint,
) -> String {
    CertificateFailure {
        failure_code: failure_code.to_string(),
        responsible_component: Some(responsible_component.to_string()),
        artifact: artifact.to_string(),
        message: message.into(),
        repair_hint,
    }
    .to_error_string()
}

pub fn repair_hint_from_profile(entry: &ProfileRepairHint) -> RepairHint {
    RepairHint {
        kind: entry.kind.clone(),
        command: entry.command.clone(),
    }
}

pub fn emit_certificate_failure(
    profile: &PropertyProfile,
    failure_code: &str,
    artifact: &str,
    message: impl Into<String>,
) -> String {
    let message = message.into();
    if let Some(entry) = profile.repair_hint_for(failure_code) {
        let repair_hint = repair_hint_from_profile(entry);
        let responsible = entry
            .responsible_component
            .as_deref()
            .unwrap_or("runtime_producer");
        return certificate_failure_with_component(
            failure_code,
            responsible,
            artifact,
            message,
            repair_hint,
        );
    }
    certificate_failure(
        failure_code,
        artifact,
        message,
        RepairHint {
            kind: "fix_trace_or_property".to_string(),
            command: "certifyedge emit-pcs-certificate --profile-registry templates/profiles --handoff <handoff> --out <certificate.json>".to_string(),
        },
    )
}

pub fn repair_regenerate_handoff(
    trace_path: &str,
    receipt_path: &str,
    out_path: &str,
) -> RepairHint {
    RepairHint {
        kind: "regenerate_trace_or_handoff".to_string(),
        command: format!(
            "labtrust emit-handoff-to-certifyedge --trace {trace_path} \
             --runtime-receipt {receipt_path} --out {out_path} --release-mode"
        ),
    }
}

pub fn repair_fix_trace_hash(trace_path: &str) -> RepairHint {
    RepairHint {
        kind: "regenerate_trace_or_handoff".to_string(),
        command: format!(
            "labtrust export-trace --run <run> --out {trace_path} && \
             labtrust emit-handoff-to-certifyedge --trace {trace_path} ..."
        ),
    }
}

pub fn repair_unknown_property_id(property_id: &str, registry_dir: &str) -> RepairHint {
    RepairHint {
        kind: "add_property_profile".to_string(),
        command: format!(
            "add templates/profiles/{property_id}.json under {registry_dir} and matching STL template"
        ),
    }
}

pub fn repair_property_template_mismatch(property_id: &str, template_path: &str) -> RepairHint {
    RepairHint {
        kind: "align_property_template".to_string(),
        command: format!(
            "ensure {template_path} declares property_id {property_id} or update handoff invariants"
        ),
    }
}

pub fn repair_temporal_check_failed(
    profile: &PropertyProfile,
    trace_path: &str,
    spec_path: &str,
) -> String {
    let message = format!(
        "temporal property check failed for property_id={}",
        profile.property_id
    );
    if let Some(entry) = profile.repair_hint_for("temporal_check_failed") {
        let mut hint = repair_hint_from_profile(entry);
        if hint.command.contains("<trace.json>") {
            hint.command = hint.command.replace("<trace.json>", trace_path);
        } else {
            hint.command =
                format!("certifyedge check-trace --spec {spec_path} --trace {trace_path}");
        }
        let responsible = entry
            .responsible_component
            .as_deref()
            .unwrap_or("runtime_producer");
        return certificate_failure_with_component(
            "temporal_check_failed",
            responsible,
            trace_path,
            message,
            hint,
        );
    }
    certificate_failure(
        "temporal_check_failed",
        trace_path,
        message,
        RepairHint {
            kind: "fix_trace_or_property".to_string(),
            command: format!("certifyedge check-trace --spec {spec_path} --trace {trace_path}"),
        },
    )
}

/// Stable JSON object for Provability Fabric explain mode (stdout/stderr/summary/handoff).
pub fn certificate_failure_value(
    profile: &PropertyProfile,
    failure_code: &str,
    artifact: &str,
    message: impl Into<String>,
) -> Result<CertificateFailure, String> {
    let message = message.into();
    if let Some(entry) = profile.repair_hint_for(failure_code) {
        let repair_hint = repair_hint_from_profile(entry);
        return Ok(CertificateFailure {
            failure_code: failure_code.to_string(),
            responsible_component: entry.responsible_component.clone(),
            artifact: artifact.to_string(),
            message,
            repair_hint,
        });
    }
    Ok(CertificateFailure {
        failure_code: failure_code.to_string(),
        responsible_component: None,
        artifact: artifact.to_string(),
        message,
        repair_hint: RepairHint {
            kind: "fix_trace_or_property".to_string(),
            command: "certifyedge emit-pcs-certificate --profile-registry templates/profiles --handoff <handoff> --out <certificate.json>".to_string(),
        },
    })
}

pub fn rejection_repair_context(
    profile: &PropertyProfile,
    failure_code: &str,
) -> Option<(String, Option<String>, RepairHint)> {
    let entry = profile.repair_hint_for(failure_code)?;
    let responsible = entry.responsible_component.clone();
    Some((
        failure_code.to_string(),
        responsible,
        repair_hint_from_profile(entry),
    ))
}

pub fn repair_tool_use_check_failed(
    profile: &PropertyProfile,
    failure_code: &str,
    artifact: &str,
) -> String {
    emit_certificate_failure(
        profile,
        failure_code,
        artifact,
        format!(
            "tool-use property check failed for property_id={}",
            profile.property_id
        ),
    )
}

pub fn validate_release_mode_fields(cert: &Value, profile: &PropertyProfile) -> Result<(), String> {
    let obj = cert
        .as_object()
        .ok_or_else(|| "certificate must be a JSON object".to_string())?;
    let mut missing = Vec::new();
    for field in profile.release_mode_required_fields() {
        if !obj.contains_key(field) {
            missing.push(field.as_str());
        }
    }
    if missing.is_empty() {
        Ok(())
    } else {
        Err(emit_certificate_failure(
            profile,
            "release_mode_required_fields_missing",
            "certificate.json",
            format!(
                "release mode: certificate missing profile-required fields: {}",
                missing.join(", ")
            ),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    fn sample_profile() -> PropertyProfile {
        PropertyProfile {
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
                ProfileRepairHint {
                    kind: "fix_trace_or_policy".into(),
                    command: "regenerate runtime trace after policy enforcement".into(),
                    responsible_component: Some("runtime_producer".into()),
                },
            )]),
            supporting_artifacts: vec![],
        }
    }

    #[test]
    fn profile_repair_hint_includes_responsible_component() {
        let err = emit_certificate_failure(
            &sample_profile(),
            "unauthorized_tool_call",
            "trace.json",
            "unauthorized tool call",
        );
        let value: Value = serde_json::from_str(&err).unwrap();
        assert_eq!(value["failure_code"], "unauthorized_tool_call");
        assert_eq!(value["responsible_component"], "runtime_producer");
        assert_eq!(value["repair_hint"]["kind"], "fix_trace_or_policy");
    }
}
