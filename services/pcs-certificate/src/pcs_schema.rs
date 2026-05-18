use serde_json::Value;
use std::sync::OnceLock;

use jsonschema::Validator;

static TRACE_CERTIFICATE_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static TOOL_USE_CERTIFICATE_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static HANDOFF_MANIFEST_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static TOOL_USE_TRACE_VALIDATOR: OnceLock<Validator> = OnceLock::new();

/// Merged TraceCertificate.v0 + common defs for self-contained JSON Schema validation.
fn merged_trace_certificate_schema() -> Value {
    let common: Value = serde_json::from_str(include_str!("../../../schemas/pcs/common.defs.json"))
        .expect("common.defs.json");
    let mut cert: Value = serde_json::from_str(include_str!(
        "../../../schemas/pcs/TraceCertificate.v0.schema.json"
    ))
    .expect("TraceCertificate.v0.schema.json");

    if let (Some(common_defs), Some(cert_obj)) = (common.get("$defs"), cert.as_object_mut()) {
        cert_obj.insert("$defs".to_string(), common_defs.clone());
    }
    rewrite_common_defs_refs(&mut cert);
    cert
}

fn trace_certificate_validator() -> &'static Validator {
    TRACE_CERTIFICATE_VALIDATOR.get_or_init(|| {
        let schema = merged_trace_certificate_schema();
        Validator::new(&schema).expect("TraceCertificate.v0 schema compiles")
    })
}

fn rewrite_common_defs_refs(value: &mut Value) {
    match value {
        Value::Object(map) => {
            if let Some(Value::String(reference)) = map.get("$ref") {
                if let Some(suffix) = reference.strip_prefix("common.defs.json#/") {
                    map.insert("$ref".to_string(), Value::String(format!("#/{suffix}")));
                }
            }
            for child in map.values_mut() {
                rewrite_common_defs_refs(child);
            }
        }
        Value::Array(items) => {
            for child in items {
                rewrite_common_defs_refs(child);
            }
        }
        _ => {}
    }
}

fn merged_handoff_manifest_schema() -> Value {
    let common: Value = serde_json::from_str(include_str!("../../../schemas/pcs/common.defs.json"))
        .expect("common.defs.json");
    let mut handoff: Value = serde_json::from_str(include_str!(
        "../../../schemas/pcs/HandoffManifest.v0.schema.json"
    ))
    .expect("HandoffManifest.v0.schema.json");

    if let (Some(common_defs), Some(obj)) = (common.get("$defs"), handoff.as_object_mut()) {
        obj.insert("$defs".to_string(), common_defs.clone());
    }
    rewrite_common_defs_refs(&mut handoff);
    handoff
}

fn handoff_manifest_validator() -> &'static Validator {
    HANDOFF_MANIFEST_VALIDATOR.get_or_init(|| {
        let schema = merged_handoff_manifest_schema();
        Validator::new(&schema).expect("HandoffManifest.v0 schema compiles")
    })
}

pub fn validate_handoff_manifest_schema(value: &Value) -> Result<(), String> {
    let validator = handoff_manifest_validator();
    let errors: Vec<String> = validator
        .iter_errors(value)
        .map(|e| e.to_string())
        .collect();
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors.join("; "))
    }
}

fn merged_tool_use_certificate_schema() -> Value {
    let common: Value = serde_json::from_str(include_str!("../../../schemas/pcs/common.defs.json"))
        .expect("common.defs.json");
    let mut cert: Value = serde_json::from_str(include_str!(
        "../../../schemas/pcs/ToolUseCertificate.v0.schema.json"
    ))
    .expect("ToolUseCertificate.v0.schema.json");

    if let Some(cert_obj) = cert.as_object_mut() {
        let mut merged_defs = serde_json::Map::new();
        if let Some(common_defs) = common.get("$defs").and_then(|v| v.as_object()) {
            for (k, v) in common_defs {
                merged_defs.insert(k.clone(), v.clone());
            }
        }
        if let Some(local_defs) = cert_obj.get("$defs").and_then(|v| v.as_object()) {
            for (k, v) in local_defs {
                merged_defs.insert(k.clone(), v.clone());
            }
        }
        cert_obj.insert("$defs".to_string(), Value::Object(merged_defs));
    }
    rewrite_common_defs_refs(&mut cert);
    cert
}

fn tool_use_certificate_validator() -> &'static Validator {
    TOOL_USE_CERTIFICATE_VALIDATOR.get_or_init(|| {
        let schema = merged_tool_use_certificate_schema();
        Validator::new(&schema).expect("ToolUseCertificate.v0 schema compiles")
    })
}

pub fn validate_trace_certificate_schema(value: &Value) -> Result<(), String> {
    let validator = trace_certificate_validator();
    let errors: Vec<String> = validator
        .iter_errors(value)
        .map(|e| e.to_string())
        .collect();
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors.join("; "))
    }
}

fn merged_tool_use_trace_schema() -> Value {
    let common: Value = serde_json::from_str(include_str!("../../../schemas/pcs/common.defs.json"))
        .expect("common.defs.json");
    let mut trace: Value = serde_json::from_str(include_str!(
        "../../../schemas/pcs/ToolUseTrace.v0.schema.json"
    ))
    .expect("ToolUseTrace.v0.schema.json");

    if let (Some(common_defs), Some(trace_obj)) = (common.get("$defs"), trace.as_object_mut()) {
        let mut merged_defs = serde_json::Map::new();
        for (k, v) in common_defs.as_object().expect("common $defs object") {
            merged_defs.insert(k.clone(), v.clone());
        }
        if let Some(local_defs) = trace_obj.get("$defs").and_then(|v| v.as_object()) {
            for (k, v) in local_defs {
                merged_defs.insert(k.clone(), v.clone());
            }
        }
        trace_obj.insert("$defs".to_string(), Value::Object(merged_defs));
    }
    rewrite_common_defs_refs(&mut trace);
    trace
}

fn tool_use_trace_validator() -> &'static Validator {
    TOOL_USE_TRACE_VALIDATOR.get_or_init(|| {
        let schema = merged_tool_use_trace_schema();
        Validator::new(&schema).expect("ToolUseTrace.v0 schema compiles")
    })
}

pub fn validate_tool_use_trace_schema(value: &Value) -> Result<(), String> {
    let validator = tool_use_trace_validator();
    let errors: Vec<String> = validator
        .iter_errors(value)
        .map(|e| e.to_string())
        .collect();
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors.join("; "))
    }
}

pub fn validate_tool_use_certificate_schema(value: &Value) -> Result<(), String> {
    let validator = tool_use_certificate_validator();
    let errors: Vec<String> = validator
        .iter_errors(value)
        .map(|e| e.to_string())
        .collect();
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors.join("; "))
    }
}

pub fn detect_certificate_artifact_type(value: &Value) -> Option<&'static str> {
    if value.get("violations").is_some() && value.get("policy_hash").is_some() {
        Some(crate::property_profile::ARTIFACT_TOOL_USE_CERTIFICATE)
    } else if value.get("spec_hash").is_some() && value.get("counterexample_ref").is_some() {
        Some(crate::property_profile::ARTIFACT_TRACE_CERTIFICATE)
    } else if value.get("policy_hash").is_some() {
        Some(crate::property_profile::ARTIFACT_TOOL_USE_CERTIFICATE)
    } else if value.get("spec_hash").is_some() {
        Some(crate::property_profile::ARTIFACT_TRACE_CERTIFICATE)
    } else {
        None
    }
}

pub fn validate_certificate_schema_for_type(
    value: &Value,
    artifact_type: &str,
) -> Result<(), String> {
    match artifact_type {
        crate::property_profile::ARTIFACT_TRACE_CERTIFICATE => {
            validate_trace_certificate_schema(value)
        }
        crate::property_profile::ARTIFACT_TOOL_USE_CERTIFICATE => {
            validate_tool_use_certificate_schema(value)
        }
        other => Err(format!("unsupported certificate artifact type: {other}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn rejects_unknown_field() {
        let mut doc = minimal_valid_cert();
        doc["extra"] = json!("x");
        assert!(validate_trace_certificate_schema(&doc).is_err());
    }

    #[test]
    fn accepts_minimal_valid_shape() {
        let doc = minimal_valid_cert();
        validate_trace_certificate_schema(&doc).unwrap();
    }

    fn minimal_valid_cert() -> Value {
        json!({
            "certificate_id": "cert-trace-test",
            "schema_version": "v0",
            "trace_hash": "sha256:1111111111111111111111111111111111111111111111111111111111111111",
            "spec_hash": "sha256:2222222222222222222222222222222222222222222222222222222222222222",
            "property_id": "hospital_lab.qc_release",
            "checker": "CertifyEdge",
            "checker_version": "0.1.0",
            "status": "CertificateChecked",
            "counterexample_ref": null,
            "created_at": "2026-05-16T12:00:00Z",
            "producer": "CertifyEdge",
            "producer_version": "0.1.0",
            "source_repo": "https://github.com/fraware/CertifyEdge",
            "source_commit": "abcdef0123456789abcdef0123456789abcdef01",
            "signature_or_digest": "sha256:3333333333333333333333333333333333333333333333333333333333333333"
        })
    }
}
