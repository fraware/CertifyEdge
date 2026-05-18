//! Minimal `ToolUseTrace.v0` parsing for profile-driven certification.

use serde::Deserialize;
use serde_json::Value;

pub const PLACEHOLDER_POLICY_HASH: &str =
    "sha256:0000000000000000000000000000000000000000000000000000000000000000";

#[derive(Debug, Clone, Deserialize, PartialEq)]
pub struct ToolCall {
    pub event_id: String,
    pub authorization_status: String,
    #[serde(default)]
    pub tool_name: String,
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
pub struct ToolUseTraceV0 {
    pub schema_version: String,
    pub trace_id: String,
    pub trace_hash: String,
    #[serde(default)]
    pub policy_id: String,
    #[serde(default)]
    pub policy_hash: Option<String>,
    pub tool_calls: Vec<ToolCall>,
    #[serde(default)]
    pub signature_or_digest: String,
}

pub fn parse_tool_use_trace_json(text: &str) -> Result<ToolUseTraceV0, String> {
    serde_json::from_str(text).map_err(|e| format!("invalid ToolUseTrace.v0 JSON: {e}"))
}

pub fn trace_has_explicit_policy_hash(trace: &ToolUseTraceV0) -> bool {
    trace
        .policy_hash
        .as_ref()
        .map(|h| !h.trim().is_empty() && h != PLACEHOLDER_POLICY_HASH)
        .unwrap_or(false)
}

/// Policy digest for certificates: explicit trace field, or dev-only derivation from `policy_id`.
pub fn policy_hash_from_trace(trace: &ToolUseTraceV0) -> String {
    if let Some(hash) = trace.policy_hash.as_ref() {
        if !hash.trim().is_empty() {
            return hash.trim().to_string();
        }
    }
    if trace.policy_id.is_empty() {
        return PLACEHOLDER_POLICY_HASH.to_string();
    }
    use sha2::{Digest, Sha256};
    let digest = Sha256::digest(trace.policy_id.as_bytes());
    format!("sha256:{digest:x}")
}

pub fn tool_use_counterexample_json(
    failure_code: &str,
    event_id: &str,
    tool_name: &str,
    authorization_status: &str,
) -> Value {
    serde_json::json!({
        "failure_code": failure_code,
        "event_id": event_id,
        "tool_name": tool_name,
        "authorization_status": authorization_status,
    })
}
