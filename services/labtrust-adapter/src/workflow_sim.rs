//! Minimal QC-release workflow simulator aligned with LabTrust-Gym `workflow.py`.

use crate::hash::{compute_event_hash, compute_trace_hash, GENESIS_EVENT_HASH};
use crate::labtrust_trace::{LabTrustTrace, TraceEvent};
use serde_json::{json, Map, Value};
use std::collections::HashMap;

#[derive(Clone)]
pub struct WorkflowStep {
    pub action: String,
    pub actor_id: String,
    pub actor_role: String,
    pub timestamp: String,
}

pub fn role_can_release(role: &str) -> bool {
    role == "release_manager"
}

pub fn evaluate_action(
    action: &str,
    state: &HashMap<String, Value>,
    actor_role: &str,
) -> (String, String, HashMap<String, Value>) {
    let mut post = state.clone();
    match action {
        "accession_sample" => {
            if state.get("lifecycle").and_then(|v| v.as_str()) != Some("registered") {
                return ("deny".into(), "invalid_transition".into(), post);
            }
            post.insert("lifecycle".into(), json!("accessioned"));
            ("allow".into(), "ok".into(), post)
        }
        "perform_qc" => {
            if state.get("lifecycle").and_then(|v| v.as_str()) != Some("accessioned") {
                return ("deny".into(), "invalid_transition".into(), post);
            }
            post.insert("qc_complete".into(), json!(true));
            post.insert("lifecycle".into(), json!("qc_complete"));
            ("allow".into(), "ok".into(), post)
        }
        "record_analysis" => {
            if state.get("lifecycle").and_then(|v| v.as_str()) != Some("qc_complete") {
                return ("deny".into(), "invalid_transition".into(), post);
            }
            post.insert("analysis_complete".into(), json!(true));
            post.insert("lifecycle".into(), json!("analyzed"));
            ("allow".into(), "ok".into(), post)
        }
        "release_sample" => {
            if !state.get("qc_complete").and_then(|v| v.as_bool()).unwrap_or(false) {
                return ("deny".into(), "missing_qc".into(), post);
            }
            if state.get("lifecycle").and_then(|v| v.as_str()) != Some("analyzed") {
                return ("deny".into(), "invalid_transition".into(), post);
            }
            if !role_can_release(actor_role) {
                return ("deny".into(), "unauthorized_release".into(), post);
            }
            post.insert("released".into(), json!(true));
            post.insert("lifecycle".into(), json!("released"));
            ("allow".into(), "ok".into(), post)
        }
        _ => ("deny".into(), "invalid_transition".into(), post),
    }
}

pub fn run_workflow(run_id: &str, sample_id: &str, steps: &[WorkflowStep]) -> LabTrustTrace {
    let mut state = HashMap::from([
        ("lifecycle".into(), json!("registered")),
        ("qc_complete".into(), json!(false)),
        ("analysis_complete".into(), json!(false)),
        ("released".into(), json!(false)),
    ]);

    let mut events = Vec::new();
    let mut prev_hash = GENESIS_EVENT_HASH.to_string();

    for (idx, step) in steps.iter().enumerate() {
        let pre_state = state.clone();
        let (decision, reason, mut post_state) =
            evaluate_action(&step.action, &state, &step.actor_role);
        if decision == "allow" {
            state = post_state.clone();
        } else {
            post_state = pre_state.clone();
        }

        let mut body = Map::new();
        body.insert("event_id".into(), json!(format!("{run_id}-evt-{idx:03}")));
        body.insert("run_id".into(), json!(run_id));
        body.insert("sample_id".into(), json!(sample_id));
        body.insert("timestamp".into(), json!(step.timestamp));
        body.insert("actor_id".into(), json!(step.actor_id));
        body.insert("actor_role".into(), json!(step.actor_role));
        body.insert("action".into(), json!(step.action));
        body.insert("pre_state".into(), json!(pre_state));
        body.insert("post_state".into(), json!(post_state));
        body.insert("policy_decision".into(), json!(decision));
        body.insert("reason_code".into(), json!(reason));
        body.insert("previous_event_hash".into(), json!(prev_hash));

        let event_hash = compute_event_hash(&body);
        body.insert("event_hash".into(), json!(event_hash));
        prev_hash = event_hash.clone();

        let event: TraceEvent = serde_json::from_value(Value::Object(body)).expect("event shape");
        events.push(event);
    }

    let events_json: Vec<Value> = events
        .iter()
        .map(|e| serde_json::to_value(e).unwrap())
        .collect();
    let trace_hash = compute_trace_hash(&events_json, run_id, sample_id);

    LabTrustTrace {
        version: "0".into(),
        artifact_kind: "Trace".into(),
        run_id: run_id.into(),
        sample_id: sample_id.into(),
        events,
        trace_hash,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn step(action: &str, actor_id: &str, role: &str, ts: &str) -> WorkflowStep {
        WorkflowStep {
            action: action.into(),
            actor_id: actor_id.into(),
            actor_role: role.into(),
            timestamp: ts.into(),
        }
    }

    #[test]
    fn valid_workflow_produces_four_events() {
        let steps = vec![
            step("accession_sample", "acc-tech-01", "accession_tech", "2026-01-15T08:00:00+00:00"),
            step("perform_qc", "qc-tech-01", "qc_tech", "2026-01-15T09:00:00+00:00"),
            step("record_analysis", "analyst-01", "analyst", "2026-01-15T10:00:00+00:00"),
            step("release_sample", "rel-mgr-01", "release_manager", "2026-01-15T11:00:00+00:00"),
        ];
        let trace = run_workflow("qc-release", "PCS-SAMPLE-001", &steps);
        assert_eq!(trace.events.len(), 4);
        assert!(trace.trace_hash.starts_with("sha256:"));
    }
}
