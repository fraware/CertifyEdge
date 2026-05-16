use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::HashMap;

pub const TRACE_VERSION: &str = "0";
pub const ARTIFACT_KIND: &str = "Trace";

pub const REQUIRED_ACTIONS: &[&str] = &[
    "accession_sample",
    "perform_qc",
    "record_analysis",
    "release_sample",
];

pub const TRACE_EVENT_FIELDS: &[&str] = &[
    "event_id",
    "run_id",
    "sample_id",
    "timestamp",
    "actor_id",
    "actor_role",
    "action",
    "pre_state",
    "post_state",
    "policy_decision",
    "reason_code",
    "event_hash",
    "previous_event_hash",
];

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TraceEvent {
    pub event_id: String,
    pub run_id: String,
    pub sample_id: String,
    pub timestamp: String,
    pub actor_id: String,
    pub actor_role: String,
    pub action: String,
    pub pre_state: HashMap<String, Value>,
    pub post_state: HashMap<String, Value>,
    pub policy_decision: String,
    pub reason_code: String,
    pub event_hash: String,
    pub previous_event_hash: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct LabTrustTrace {
    pub version: String,
    pub artifact_kind: String,
    pub run_id: String,
    pub sample_id: String,
    pub events: Vec<TraceEvent>,
    pub trace_hash: String,
}

impl LabTrustTrace {
    pub fn from_json_value(value: &Value) -> Result<Self, serde_json::Error> {
        serde_json::from_value(value.clone())
    }
}
