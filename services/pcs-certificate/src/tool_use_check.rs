//! Tool-use property checks (v0.1: no unauthorized tool calls).

use std::path::Path;

use serde::Serialize;
use serde_json::Value;

use crate::tool_use_trace::{
    tool_use_counterexample_json, trace_has_explicit_policy_hash, ToolUseTraceV0,
};
use crate::tool_use_violation::ToolUseViolationV0;

#[derive(Debug, Clone)]
pub struct ToolUsePropertySpec {
    pub property_id: String,
    pub raw_text: String,
}

impl ToolUsePropertySpec {
    pub fn load(path: &Path) -> Result<Self, String> {
        let raw_text = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
        let property_id = parse_property_id(&raw_text)
            .ok_or_else(|| format!("spec {} missing property: line", path.display()))?;
        Ok(Self {
            property_id,
            raw_text,
        })
    }
}

fn parse_property_id(text: &str) -> Option<String> {
    for line in text.lines() {
        let line = line.trim();
        if let Some(id) = line.strip_prefix("property:") {
            let id = id.trim();
            if !id.is_empty() {
                return Some(id.to_string());
            }
        }
    }
    None
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct ToolUseCheckResult {
    pub passed: bool,
    pub failure_code: Option<String>,
    pub violations: Vec<ToolUseViolationV0>,
    pub counterexample: Option<Value>,
}

pub fn is_unauthorized_status(status: &str) -> bool {
    matches!(
        status.to_ascii_lowercase().as_str(),
        "unauthorized" | "rejected"
    )
}

pub fn check_no_unauthorized_tool_call(
    trace: &ToolUseTraceV0,
    spec: &ToolUsePropertySpec,
) -> ToolUseCheckResult {
    if spec.property_id != "agent_tool_use.safety_v0" {
        return ToolUseCheckResult {
            passed: false,
            failure_code: Some("property_template_mismatch".to_string()),
            violations: vec![ToolUseViolationV0::new(
                "property_template_mismatch",
                format!(
                    "spec property_id {} does not match agent_tool_use.safety_v0",
                    spec.property_id
                ),
            )],
            counterexample: None,
        };
    }

    for call in &trace.tool_calls {
        let status_lower = call.authorization_status.to_ascii_lowercase();
        if status_lower != "authorized" && !is_unauthorized_status(&call.authorization_status) {
            let message = format!(
                "unknown authorization_status on {} ({}): {}",
                call.event_id, call.tool_name, call.authorization_status
            );
            return ToolUseCheckResult {
                passed: false,
                failure_code: Some("unknown_authorization_status".to_string()),
                violations: vec![ToolUseViolationV0::new(
                    "unknown_authorization_status",
                    message.clone(),
                )
                .with_tool_call(&call.event_id, &call.tool_name, &call.authorization_status)],
                counterexample: Some(tool_use_counterexample_json(
                    "unknown_authorization_status",
                    &call.event_id,
                    &call.tool_name,
                    &call.authorization_status,
                )),
            };
        }
        if is_unauthorized_status(&call.authorization_status) {
            let message = format!(
                "unauthorized tool call {} ({}) status={}",
                call.event_id, call.tool_name, call.authorization_status
            );
            return ToolUseCheckResult {
                passed: false,
                failure_code: Some("unauthorized_tool_call".to_string()),
                violations: vec![ToolUseViolationV0::new("unauthorized_tool_call", message)
                    .with_tool_call(&call.event_id, &call.tool_name, &call.authorization_status)],
                counterexample: Some(tool_use_counterexample_json(
                    "unauthorized_tool_call",
                    &call.event_id,
                    &call.tool_name,
                    &call.authorization_status,
                )),
            };
        }
    }

    ToolUseCheckResult {
        passed: true,
        failure_code: None,
        violations: vec![],
        counterexample: None,
    }
}

pub fn check_policy_hash_present(trace: &ToolUseTraceV0) -> ToolUseCheckResult {
    if trace_has_explicit_policy_hash(trace) {
        return ToolUseCheckResult {
            passed: true,
            failure_code: None,
            violations: vec![],
            counterexample: None,
        };
    }
    ToolUseCheckResult {
        passed: false,
        failure_code: Some("policy_hash_missing".to_string()),
        violations: vec![ToolUseViolationV0::new(
            "policy_hash_missing",
            "tool-use trace missing explicit policy_hash",
        )],
        counterexample: Some(serde_json::json!({
            "failure_code": "policy_hash_missing",
            "policy_id": trace.policy_id,
        })),
    }
}

pub fn check_tool_use_property(
    trace: &ToolUseTraceV0,
    spec: &ToolUsePropertySpec,
    release_mode: bool,
) -> ToolUseCheckResult {
    if release_mode {
        let policy = check_policy_hash_present(trace);
        if !policy.passed {
            return policy;
        }
    }
    check_no_unauthorized_tool_call(trace, spec)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tool_use_trace::ToolCall;

    fn sample_trace(status: &str) -> ToolUseTraceV0 {
        ToolUseTraceV0 {
            schema_version: "v0".into(),
            trace_id: "trace-tool-001".into(),
            trace_hash: "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                .into(),
            policy_id: "policy-demo".into(),
            tool_calls: vec![ToolCall {
                event_id: "evt-1".into(),
                authorization_status: status.into(),
                tool_name: "search".into(),
            }],
            policy_hash: Some(
                "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into(),
            ),
            signature_or_digest: String::new(),
        }
    }

    fn spec() -> ToolUsePropertySpec {
        ToolUsePropertySpec {
            property_id: "agent_tool_use.safety_v0".into(),
            raw_text: "property: agent_tool_use.safety_v0\n".into(),
        }
    }

    #[test]
    fn authorized_trace_passes() {
        let result = check_tool_use_property(&sample_trace("authorized"), &spec(), false);
        assert!(result.passed);
    }

    #[test]
    fn release_mode_requires_explicit_policy_hash() {
        let mut trace = sample_trace("authorized");
        trace.policy_hash = None;
        let result = check_tool_use_property(&trace, &spec(), true);
        assert!(!result.passed);
        assert_eq!(result.failure_code.as_deref(), Some("policy_hash_missing"));
    }

    #[test]
    fn rejected_tool_call_fails() {
        let result = check_tool_use_property(&sample_trace("rejected"), &spec(), false);
        assert!(!result.passed);
        assert_eq!(
            result.failure_code.as_deref(),
            Some("unauthorized_tool_call")
        );
    }

    #[test]
    fn unauthorized_string_fails() {
        let result = check_tool_use_property(&sample_trace("unauthorized"), &spec(), false);
        assert!(!result.passed);
    }
}
