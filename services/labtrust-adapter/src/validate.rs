use crate::hash::{compute_event_hash, compute_trace_hash, GENESIS_EVENT_HASH};
use crate::labtrust_trace::{LabTrustTrace, TRACE_EVENT_FIELDS, TRACE_VERSION};
use serde_json::{Map, Value};
use thiserror::Error;

#[derive(Debug, Error, PartialEq)]
pub enum TraceValidationError {
    #[error("malformed trace: {0}")]
    Malformed(String),
    #[error("trace hash mismatch: expected {expected}, found {found}")]
    TraceHashMismatch { expected: String, found: String },
}

pub fn validate_trace(trace: &LabTrustTrace) -> Result<(), TraceValidationError> {
    if trace.version != TRACE_VERSION {
        return Err(TraceValidationError::Malformed(format!(
            "unsupported trace version: {}",
            trace.version
        )));
    }
    if trace.artifact_kind != "Trace" {
        return Err(TraceValidationError::Malformed(format!(
            "unexpected artifact_kind: {}",
            trace.artifact_kind
        )));
    }
    if trace.run_id.is_empty() || trace.sample_id.is_empty() {
        return Err(TraceValidationError::Malformed(
            "run_id and sample_id are required".into(),
        ));
    }

    let events_json: Vec<Value> = trace
        .events
        .iter()
        .map(|e| serde_json::to_value(e).expect("event serializes"))
        .collect();

    let chain_errors = verify_event_hash_chain(&events_json);
    if !chain_errors.is_empty() {
        return Err(TraceValidationError::Malformed(chain_errors.join("; ")));
    }

    let expected = compute_trace_hash(&events_json, &trace.run_id, &trace.sample_id);
    if trace.trace_hash != expected {
        return Err(TraceValidationError::TraceHashMismatch {
            expected,
            found: trace.trace_hash.clone(),
        });
    }

    Ok(())
}

pub fn verify_event_hash_chain(events: &[Value]) -> Vec<String> {
    let mut errors = Vec::new();
    let mut prev = GENESIS_EVENT_HASH.to_string();

    for (i, event) in events.iter().enumerate() {
        let obj = match event.as_object() {
            Some(o) => o,
            None => {
                errors.push(format!("event[{i}]: not an object"));
                continue;
            }
        };

        for key in TRACE_EVENT_FIELDS {
            if !obj.contains_key(*key) {
                errors.push(format!("event[{i}]: missing field {key}"));
            }
        }

        if obj
            .get("previous_event_hash")
            .and_then(|v| v.as_str())
            != Some(prev.as_str())
        {
            errors.push(format!("event[{i}]: previous_event_hash mismatch"));
        }

        let mut body = Map::new();
        for (k, v) in obj {
            if k != "event_hash" {
                body.insert(k.clone(), v.clone());
            }
        }
        let expected = compute_event_hash(&body);
        if obj.get("event_hash").and_then(|v| v.as_str()) != Some(expected.as_str()) {
            errors.push(format!("event[{i}]: event_hash mismatch"));
        }

        prev = obj
            .get("event_hash")
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string();
    }

    errors
}

pub fn parse_and_validate_json(text: &str) -> Result<LabTrustTrace, TraceValidationError> {
    let value: Value = serde_json::from_str(text)
        .map_err(|e| TraceValidationError::Malformed(e.to_string()))?;
    let trace = LabTrustTrace::from_json_value(&value)
        .map_err(|e| TraceValidationError::Malformed(e.to_string()))?;
    validate_trace(&trace)?;
    Ok(trace)
}
