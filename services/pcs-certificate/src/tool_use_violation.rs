//! Structured violations on `ToolUseCertificate.v0` (pcs-core registry compatible).

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ToolUseViolationV0 {
    pub failure_code: String,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub event_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tool_name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub authorization_status: Option<String>,
}

impl ToolUseViolationV0 {
    pub fn new(failure_code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            failure_code: failure_code.into(),
            message: message.into(),
            event_id: None,
            tool_name: None,
            authorization_status: None,
        }
    }

    pub fn with_tool_call(
        mut self,
        event_id: impl Into<String>,
        tool_name: impl Into<String>,
        authorization_status: impl Into<String>,
    ) -> Self {
        self.event_id = Some(event_id.into());
        self.tool_name = Some(tool_name.into());
        self.authorization_status = Some(authorization_status.into());
        self
    }
}
