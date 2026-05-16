use serde_json::{json, Map, Value};
use sha2::{Digest, Sha256};

const SIGNATURE_FIELD: &str = "signature_or_digest";

pub const GENESIS_EVENT_HASH: &str = "0000000000000000000000000000000000000000000000000000000000000000";

/// Canonical JSON matching LabTrust `canonical_json` (sorted keys, compact separators).
pub fn canonical_json(value: &Value) -> String {
    let sorted = sort_json_value(value.clone());
    serde_json::to_string(&sorted).expect("canonical json serialization")
}

pub fn sha256_hex(data: &str) -> String {
    let digest = Sha256::digest(data.as_bytes());
    format!("{digest:x}")
}

pub fn hash_object(value: &Value) -> String {
    sha256_hex(&canonical_json(value))
}

/// PCS-core canonical digest (`sha256:...`), matching `pcs_core::canonical_hash`.
pub fn pcs_digest(doc: &Value) -> String {
    let canonical = canonicalize_for_hash(doc);
    let bytes = serde_json::to_vec(&canonical).expect("serialize canonical json");
    let digest = Sha256::digest(bytes);
    format!("sha256:{digest:x}")
}

fn canonicalize_for_hash(data: &Value) -> Value {
    let mut obj = data
        .as_object()
        .expect("digest root must be object")
        .clone();
    obj.remove(SIGNATURE_FIELD);
    sort_json_value(Value::Object(obj))
}

pub fn compute_event_hash(body: &Map<String, Value>) -> String {
    sha256_hex(&canonical_json(&Value::Object(body.clone())))
}

pub fn compute_trace_hash(events: &[Value], run_id: &str, sample_id: &str) -> String {
    let event_hashes: Vec<&str> = events
        .iter()
        .filter_map(|e| e.get("event_hash").and_then(|v| v.as_str()))
        .collect();
    pcs_digest(&json!({
        "version": "0",
        "run_id": run_id,
        "sample_id": sample_id,
        "event_hashes": event_hashes,
    }))
}

pub fn spec_hash(spec_text: &str, property_id: &str) -> String {
    pcs_digest(&json!({
        "property_id": property_id,
        "spec": spec_text,
    }))
}

fn sort_json_value(value: Value) -> Value {
    match value {
        Value::Object(map) => {
            let mut keys: Vec<_> = map.keys().cloned().collect();
            keys.sort();
            let mut sorted = Map::new();
            for key in keys {
                if let Some(v) = map.get(&key) {
                    sorted.insert(key, sort_json_value(v.clone()));
                }
            }
            Value::Object(sorted)
        }
        Value::Array(items) => Value::Array(items.into_iter().map(sort_json_value).collect()),
        other => other,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_json_sorted_keys() {
        let v = json!({"b": 1, "a": 2});
        assert_eq!(canonical_json(&v), r#"{"a":2,"b":1}"#);
    }
}
