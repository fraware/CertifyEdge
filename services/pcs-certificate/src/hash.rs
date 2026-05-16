use labtrust_adapter::hash::pcs_digest;
use serde_json::json;
use serde_json::Value;

pub fn spec_hash(spec_text: &str, property_id: &str) -> String {
    pcs_digest(&json!({
        "property_id": property_id,
        "spec": spec_text,
    }))
}

/// PCS canonical artifact hash (`sha256:...`), excluding `signature_or_digest`.
pub fn canonical_hash(data: &Value) -> String {
    pcs_digest(data)
}
