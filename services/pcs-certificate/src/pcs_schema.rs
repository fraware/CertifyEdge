use serde_json::Value;
use std::sync::OnceLock;

use jsonschema::Validator;

static TRACE_CERTIFICATE_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static TOOL_USE_CERTIFICATE_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static HANDOFF_MANIFEST_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static TOOL_USE_TRACE_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static COMPUTATION_WITNESS_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static BENCHMARK_CASE_SPEC_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static BENCHMARK_RUN_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static CERTIFICATE_COVERAGE_REPORT_VALIDATOR: OnceLock<Validator> = OnceLock::new();

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
                let rewritten = if let Some(suffix) = reference.strip_prefix("common.defs.json#/") {
                    Some(format!("#/{suffix}"))
                } else if reference == "ProfileCoverageReport.v0.schema.json" {
                    Some("#/$defs/profile_coverage_report_v0".to_string())
                } else if reference == "CertificateCoverageReport.v0.schema.json" {
                    Some("#/$defs/certificate_coverage_report_v0".to_string())
                } else {
                    None
                };
                if let Some(r) = rewritten {
                    map.insert("$ref".to_string(), Value::String(r));
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

fn strip_schema_metadata(value: &mut Value) {
    if let Some(obj) = value.as_object_mut() {
        obj.remove("$schema");
        obj.remove("$id");
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

fn merged_computation_witness_schema() -> Value {
    let common: Value = serde_json::from_str(include_str!("../../../schemas/pcs/common.defs.json"))
        .expect("common.defs.json");
    let mut cert: Value = serde_json::from_str(include_str!(
        "../../../schemas/pcs/ComputationWitness.v0.schema.json"
    ))
    .expect("ComputationWitness.v0.schema.json");

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

fn computation_witness_validator() -> &'static Validator {
    COMPUTATION_WITNESS_VALIDATOR.get_or_init(|| {
        let schema = merged_computation_witness_schema();
        Validator::new(&schema).expect("ComputationWitness.v0 schema compiles")
    })
}

fn merged_certificate_formal_facts_schema() -> Value {
    let common: Value = serde_json::from_str(include_str!("../../../schemas/pcs/common.defs.json"))
        .expect("common.defs.json");
    let mut cert: Value = serde_json::from_str(include_str!(
        "../../../schemas/pcs/CertificateFormalFacts.v0.schema.json"
    ))
    .expect("CertificateFormalFacts.v0.schema.json");

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

static CERTIFICATE_FORMAL_FACTS_VALIDATOR: OnceLock<Validator> = OnceLock::new();

fn certificate_formal_facts_validator() -> &'static Validator {
    CERTIFICATE_FORMAL_FACTS_VALIDATOR.get_or_init(|| {
        let schema = merged_certificate_formal_facts_schema();
        Validator::new(&schema).expect("CertificateFormalFacts.v0 schema compiles")
    })
}

pub fn validate_certificate_formal_facts_schema(value: &Value) -> Result<(), String> {
    let validator = certificate_formal_facts_validator();
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

pub fn validate_computation_witness_schema(value: &Value) -> Result<(), String> {
    let validator = computation_witness_validator();
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
    if value.get("run_hash").is_some() && value.get("dataset_receipt_hash").is_some() {
        Some(crate::property_profile::ARTIFACT_COMPUTATION_WITNESS)
    } else if value.get("violations").is_some() && value.get("policy_hash").is_some() {
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

fn merged_benchmark_case_spec_schema() -> Value {
    let common: Value = serde_json::from_str(include_str!("../../../schemas/pcs/common.defs.json"))
        .expect("common.defs.json");
    let mut spec: Value = serde_json::from_str(include_str!(
        "../../../schemas/pcs/BenchmarkCaseSpec.v0.schema.json"
    ))
    .expect("BenchmarkCaseSpec.v0.schema.json");
    if let (Some(common_defs), Some(obj)) = (common.get("$defs"), spec.as_object_mut()) {
        obj.insert("$defs".to_string(), common_defs.clone());
    }
    rewrite_common_defs_refs(&mut spec);
    spec
}

fn benchmark_case_spec_validator() -> &'static Validator {
    BENCHMARK_CASE_SPEC_VALIDATOR.get_or_init(|| {
        Validator::new(&merged_benchmark_case_spec_schema())
            .expect("BenchmarkCaseSpec.v0 schema compiles")
    })
}

fn merged_certificate_coverage_report_schema() -> Value {
    let common: Value = serde_json::from_str(include_str!("../../../schemas/pcs/common.defs.json"))
        .expect("common.defs.json");
    let mut coverage: Value = serde_json::from_str(include_str!(
        "../../../schemas/pcs/CertificateCoverageReport.v0.schema.json"
    ))
    .expect("CertificateCoverageReport.v0.schema.json");
    strip_schema_metadata(&mut coverage);
    if let (Some(common_defs), Some(obj)) = (common.get("$defs"), coverage.as_object_mut()) {
        obj.insert("$defs".to_string(), common_defs.clone());
    }
    rewrite_common_defs_refs(&mut coverage);
    coverage
}

fn certificate_coverage_report_validator() -> &'static Validator {
    CERTIFICATE_COVERAGE_REPORT_VALIDATOR.get_or_init(|| {
        Validator::new(&merged_certificate_coverage_report_schema())
            .expect("CertificateCoverageReport.v0 schema compiles")
    })
}

fn merged_benchmark_run_schema() -> Value {
    let common: Value = serde_json::from_str(include_str!("../../../schemas/pcs/common.defs.json"))
        .expect("common.defs.json");
    let mut coverage: Value = serde_json::from_str(include_str!(
        "../../../schemas/pcs/CertificateCoverageReport.v0.schema.json"
    ))
    .expect("CertificateCoverageReport.v0.schema.json");
    let mut run: Value = serde_json::from_str(include_str!(
        "../../../schemas/pcs/BenchmarkRun.v0.schema.json"
    ))
    .expect("BenchmarkRun.v0.schema.json");
    strip_schema_metadata(&mut coverage);
    strip_schema_metadata(&mut run);
    rewrite_common_defs_refs(&mut coverage);
    if let Some(obj) = run.as_object_mut() {
        let mut defs_map = serde_json::Map::new();
        if let Some(common_defs) = common.get("$defs").and_then(|v| v.as_object()) {
            for (k, v) in common_defs {
                defs_map.insert(k.clone(), v.clone());
            }
        }
        defs_map.insert(
            "certificate_coverage_report_v0".to_string(),
            coverage,
        );
        obj.insert("$defs".to_string(), Value::Object(defs_map));
    }
    rewrite_common_defs_refs(&mut run);
    run
}

fn benchmark_run_validator() -> &'static Validator {
    BENCHMARK_RUN_VALIDATOR.get_or_init(|| {
        Validator::new(&merged_benchmark_run_schema()).expect("BenchmarkRun.v0 schema compiles")
    })
}

fn validate_with(validator: &Validator, value: &Value) -> Result<(), String> {
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

pub fn validate_benchmark_case_spec_schema(value: &Value) -> Result<(), String> {
    validate_with(benchmark_case_spec_validator(), value)
}

pub fn validate_certificate_coverage_report_schema(value: &Value) -> Result<(), String> {
    validate_with(certificate_coverage_report_validator(), value)
}

pub fn validate_benchmark_run_schema(value: &Value) -> Result<(), String> {
    validate_with(benchmark_run_validator(), value)
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
        crate::property_profile::ARTIFACT_COMPUTATION_WITNESS => {
            validate_computation_witness_schema(value)
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

    #[test]
    fn benchmark_case_spec_schema_accepts_minimal() {
        let doc = json!({
            "schema_version": "v0",
            "case_id": "ok",
            "profile_id": "hospital_lab.qc_release",
            "kind": "valid",
            "handoff_file": "handoff.json"
        });
        validate_benchmark_case_spec_schema(&doc).unwrap();
    }

    #[test]
    fn benchmark_run_schema_accepts_sample_shape() {
        let doc = json!({
            "schema_version": "v0",
            "artifact": "BenchmarkRun.v0",
            "profile_id": "hospital_lab.qc_release",
            "cases_dir": "benchmarks/certificates/hospital_lab_qc_release",
            "out_dir": "benchmark_runs/hospital_lab_qc_release",
            "started_at": "2026-05-19T12:00:00Z",
            "finished_at": "2026-05-19T12:00:01Z",
            "cases_run": 1,
            "cases_passed": 1,
            "coverage": sample_coverage_report()
        });
        validate_benchmark_run_schema(&doc).unwrap();
    }

    fn sample_coverage_report() -> Value {
        json!({
            "schema_version": "v0",
            "artifact": "CertificateCoverageReport.v0",
            "profile_id": "hospital_lab.qc_release",
            "cases_dir": "benchmarks/certificates/hospital_lab_qc_release",
            "valid_certificates_accepted": 1,
            "valid_cases_total": 1,
            "invalid_certificates_rejected": 0,
            "invalid_cases_total": 0,
            "failure_code_accuracy": 1.0,
            "counterexample_completeness": 1.0,
            "profile_resolution_accuracy": 1.0,
            "handoff_validation_accuracy": 1.0,
            "repair_hint_metrics": {
                "repair_hint_accuracy": 1.0,
                "cases_with_expected_repair_hint": 0,
                "repair_hint_matches": 0,
                "missing_repair_hints": []
            },
            "profile_coverage": {
                "schema_version": "v0",
                "artifact": "ProfileCoverageReport.v0",
                "profile_id": "hospital_lab.qc_release",
                "templates_checked": true,
                "valid_cases": 1,
                "invalid_cases": 0,
                "properties_covered": ["hospital_lab.qc_release"],
                "counterexample_types_covered": [],
                "unsupported_cases": [],
                "coverage_score": 1.0
            },
            "case_results": [{
                "case_id": "ok",
                "kind": "valid",
                "passed": true,
                "profile_resolution_ok": true,
                "handoff_validation_ok": true,
                "status_match": true,
                "failure_code_match": true,
                "counterexample_match": true,
                "repair_hint_present": true,
                "repair_hint_kind_correct": true,
                "repair_hint_command_present": true,
                "responsible_component_correct": true,
                "errors": []
            }]
        })
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
