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
static CERTIFICATE_BENCHMARK_RUN_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static BENCHMARK_REPORT_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static COVERAGE_REPORT_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static PROFILE_COVERAGE_REPORT_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static CERTIFICATE_COVERAGE_REPORT_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static CERTIFICATE_BENCHMARK_SUITE_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static PCS_BENCH_INGEST_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static FAILURE_LOCALIZATION_VALIDATOR: OnceLock<Validator> = OnceLock::new();
static EXPLAIN_QUALITY_REPORT_VALIDATOR: OnceLock<Validator> = OnceLock::new();

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
                } else if reference == "CoverageReport.v0.schema.json" {
                    Some("#/$defs/coverage_report_v0".to_string())
                } else if reference == "ExplainQualityReport.v0.schema.json" {
                    Some("#/$defs/explain_quality_report_v0".to_string())
                } else if reference == "FailureLocalizationResult.v0.schema.json" {
                    Some("#/$defs/failure_localization_result_v0".to_string())
                } else if reference == "BenchmarkRun.v0.schema.json" {
                    Some("#/$defs/benchmark_run_v0".to_string())
                } else if reference == "BenchmarkArtifactRef.v0.schema.json" {
                    Some("#/$defs/benchmark_artifact_ref_v0".to_string())
                } else if reference == "CertificateCoverageReport.v0.schema.json" {
                    Some("#/$defs/certificate_coverage_report_v0".to_string())
                } else if reference == "CertificateBenchmarkSuite.v0.schema.json" {
                    Some("#/$defs/certificate_benchmark_suite_v0".to_string())
                } else if reference == "CertificateBenchmarkRun.v0.schema.json" {
                    Some("#/$defs/certificate_benchmark_run_v0".to_string())
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

fn merged_schema_with_common_defs(schema_json: &str) -> Value {
    let common: Value = serde_json::from_str(include_str!("../../../schemas/pcs/common.defs.json"))
        .expect("common.defs.json");
    let mut schema: Value = serde_json::from_str(schema_json).expect("schema json");
    strip_schema_metadata(&mut schema);
    if let (Some(common_defs), Some(obj)) = (common.get("$defs"), schema.as_object_mut()) {
        obj.insert("$defs".to_string(), common_defs.clone());
    }
    rewrite_common_defs_refs(&mut schema);
    schema
}

fn merged_benchmark_run_schema() -> Value {
    merged_schema_with_common_defs(include_str!(
        "../../../schemas/pcs/BenchmarkRun.v0.schema.json"
    ))
}

fn merged_benchmark_report_schema() -> Value {
    let common: Value = serde_json::from_str(include_str!("../../../schemas/pcs/common.defs.json"))
        .expect("common.defs.json");
    let mut report: Value = serde_json::from_str(include_str!(
        "../../../schemas/pcs/BenchmarkReport.v0.schema.json"
    ))
    .expect("BenchmarkReport.v0.schema.json");
    let coverage: Value = serde_json::from_str(include_str!(
        "../../../schemas/pcs/CoverageReport.v0.schema.json"
    ))
    .expect("CoverageReport.v0.schema.json");
    let profile: Value = serde_json::from_str(include_str!(
        "../../../schemas/pcs/ProfileCoverageReport.v0.schema.json"
    ))
    .expect("ProfileCoverageReport.v0.schema.json");
    let mut explain = read_nested_schema("ExplainQualityReport.v0.schema.json");
    let explain_nested_defs = explain.get("$defs").cloned();
    strip_schema_metadata(&mut report);
    let mut coverage = coverage;
    let mut profile = profile;
    strip_schema_metadata(&mut coverage);
    strip_schema_metadata(&mut profile);
    strip_schema_metadata(&mut explain);
    rewrite_common_defs_refs(&mut coverage);
    rewrite_common_defs_refs(&mut profile);
    rewrite_common_defs_refs(&mut explain);
    if let Some(obj) = explain.as_object_mut() {
        obj.remove("$defs");
    }
    let report_defs = report
        .as_object()
        .and_then(|obj| obj.get("$defs"))
        .and_then(|v| v.as_object())
        .cloned()
        .unwrap_or_default();
    if let Some(obj) = report.as_object_mut() {
        let mut defs_map = serde_json::Map::new();
        if let Some(common_defs) = common.get("$defs").and_then(|v| v.as_object()) {
            for (k, v) in common_defs {
                defs_map.insert(k.clone(), v.clone());
            }
        }
        for (k, v) in report_defs {
            defs_map.insert(k, v);
        }
        if let Some(Value::Object(nested)) = explain_nested_defs {
            for (k, v) in nested {
                defs_map.insert(k.clone(), v.clone());
            }
        }
        defs_map.insert("coverage_report_v0".to_string(), coverage);
        defs_map.insert("profile_coverage_report_v0".to_string(), profile);
        defs_map.insert("explain_quality_report_v0".to_string(), explain);
        obj.insert("$defs".to_string(), Value::Object(defs_map));
    }
    rewrite_common_defs_refs(&mut report);
    report
}

fn merged_certificate_benchmark_suite_schema() -> Value {
    let common: Value = serde_json::from_str(include_str!("../../../schemas/pcs/common.defs.json"))
        .expect("common.defs.json");
    let mut suite: Value = serde_json::from_str(include_str!(
        "../../../schemas/pcs/CertificateBenchmarkSuite.v0.schema.json"
    ))
    .expect("CertificateBenchmarkSuite.v0.schema.json");
    let coverage: Value = serde_json::from_str(include_str!(
        "../../../schemas/pcs/CertificateCoverageReport.v0.schema.json"
    ))
    .expect("CertificateCoverageReport.v0.schema.json");
    strip_schema_metadata(&mut suite);
    let mut coverage = coverage;
    strip_schema_metadata(&mut coverage);
    rewrite_common_defs_refs(&mut coverage);
    if let Some(obj) = suite.as_object_mut() {
        let mut defs_map = serde_json::Map::new();
        if let Some(common_defs) = common.get("$defs").and_then(|v| v.as_object()) {
            for (k, v) in common_defs {
                defs_map.insert(k.clone(), v.clone());
            }
        }
        defs_map.insert("certificate_coverage_report_v0".to_string(), coverage);
        obj.insert("$defs".to_string(), Value::Object(defs_map));
    }
    rewrite_common_defs_refs(&mut suite);
    suite
}

fn benchmark_run_validator() -> &'static Validator {
    BENCHMARK_RUN_VALIDATOR.get_or_init(|| {
        Validator::new(&merged_benchmark_run_schema()).expect("BenchmarkRun.v0 schema compiles")
    })
}

fn certificate_benchmark_run_validator() -> &'static Validator {
    CERTIFICATE_BENCHMARK_RUN_VALIDATOR.get_or_init(|| {
        Validator::new(&merged_schema_with_common_defs(include_str!(
            "../../../schemas/pcs/CertificateBenchmarkRun.v0.schema.json"
        )))
        .expect("CertificateBenchmarkRun.v0 schema compiles")
    })
}

fn benchmark_report_validator() -> &'static Validator {
    BENCHMARK_REPORT_VALIDATOR.get_or_init(|| {
        Validator::new(&merged_benchmark_report_schema())
            .expect("BenchmarkReport.v0 schema compiles")
    })
}

fn coverage_report_validator() -> &'static Validator {
    COVERAGE_REPORT_VALIDATOR.get_or_init(|| {
        Validator::new(&merged_schema_with_common_defs(include_str!(
            "../../../schemas/pcs/CoverageReport.v0.schema.json"
        )))
        .expect("CoverageReport.v0 schema compiles")
    })
}

fn profile_coverage_report_validator() -> &'static Validator {
    PROFILE_COVERAGE_REPORT_VALIDATOR.get_or_init(|| {
        Validator::new(&merged_schema_with_common_defs(include_str!(
            "../../../schemas/pcs/ProfileCoverageReport.v0.schema.json"
        )))
        .expect("ProfileCoverageReport.v0 schema compiles")
    })
}

fn certificate_benchmark_suite_validator() -> &'static Validator {
    CERTIFICATE_BENCHMARK_SUITE_VALIDATOR.get_or_init(|| {
        Validator::new(&merged_certificate_benchmark_suite_schema())
            .expect("CertificateBenchmarkSuite.v0 schema compiles")
    })
}

fn read_nested_schema(relative: &str) -> Value {
    match relative {
        "BenchmarkRun.v0.schema.json" => serde_json::from_str(include_str!(
            "../../../schemas/pcs/BenchmarkRun.v0.schema.json"
        ))
        .expect("BenchmarkRun.v0.schema.json"),
        "CoverageReport.v0.schema.json" => serde_json::from_str(include_str!(
            "../../../schemas/pcs/CoverageReport.v0.schema.json"
        ))
        .expect("CoverageReport.v0.schema.json"),
        "ProfileCoverageReport.v0.schema.json" => serde_json::from_str(include_str!(
            "../../../schemas/pcs/ProfileCoverageReport.v0.schema.json"
        ))
        .expect("ProfileCoverageReport.v0.schema.json"),
        "FailureLocalizationResult.v0.schema.json" => serde_json::from_str(include_str!(
            "../../../schemas/pcs/FailureLocalizationResult.v0.schema.json"
        ))
        .expect("FailureLocalizationResult.v0.schema.json"),
        "ExplainQualityReport.v0.schema.json" => serde_json::from_str(include_str!(
            "../../../schemas/pcs/ExplainQualityReport.v0.schema.json"
        ))
        .expect("ExplainQualityReport.v0.schema.json"),
        "BenchmarkArtifactRef.v0.schema.json" => serde_json::from_str(include_str!(
            "../../../schemas/pcs/BenchmarkArtifactRef.v0.schema.json"
        ))
        .expect("BenchmarkArtifactRef.v0.schema.json"),
        other => panic!("unsupported nested schema: {other}"),
    }
}

fn merged_pcs_bench_ingest_schema() -> Value {
    let common: Value = serde_json::from_str(include_str!("../../../schemas/pcs/common.defs.json"))
        .expect("common.defs.json");
    let mut ingest: Value = serde_json::from_str(include_str!(
        "../../../schemas/pcs/PcsBenchIngest.v0.schema.json"
    ))
    .expect("PcsBenchIngest.v0.schema.json");
    let mut benchmark_run = read_nested_schema("BenchmarkRun.v0.schema.json");
    let mut coverage = read_nested_schema("CoverageReport.v0.schema.json");
    let mut profile_cov = read_nested_schema("ProfileCoverageReport.v0.schema.json");
    let mut failure_loc = read_nested_schema("FailureLocalizationResult.v0.schema.json");
    let mut explain = read_nested_schema("ExplainQualityReport.v0.schema.json");
    let mut artifact_ref = read_nested_schema("BenchmarkArtifactRef.v0.schema.json");
    let explain_nested_defs = explain.get("$defs").cloned();
    strip_schema_metadata(&mut ingest);
    for doc in [
        &mut benchmark_run,
        &mut coverage,
        &mut profile_cov,
        &mut failure_loc,
        &mut explain,
        &mut artifact_ref,
    ] {
        strip_schema_metadata(doc);
        rewrite_common_defs_refs(doc);
    }
    if let Some(obj) = explain.as_object_mut() {
        obj.remove("$defs");
    }
    rewrite_common_defs_refs(&mut ingest);
    if let Some(obj) = ingest.as_object_mut() {
        let mut defs_map = serde_json::Map::new();
        if let Some(common_defs) = common.get("$defs").and_then(|v| v.as_object()) {
            for (k, v) in common_defs {
                defs_map.insert(k.clone(), v.clone());
            }
        }
        if let Some(Value::Object(nested)) = explain_nested_defs {
            for (k, v) in nested {
                defs_map.insert(k.clone(), v.clone());
            }
        }
        defs_map.insert("benchmark_run_v0".to_string(), benchmark_run);
        defs_map.insert("coverage_report_v0".to_string(), coverage);
        defs_map.insert("profile_coverage_report_v0".to_string(), profile_cov);
        defs_map.insert(
            "failure_localization_result_v0".to_string(),
            failure_loc,
        );
        defs_map.insert("explain_quality_report_v0".to_string(), explain);
        defs_map.insert("benchmark_artifact_ref_v0".to_string(), artifact_ref);
        obj.insert("$defs".to_string(), Value::Object(defs_map));
    }
    rewrite_common_defs_refs(&mut ingest);
    ingest
}

fn failure_localization_validator() -> &'static Validator {
    FAILURE_LOCALIZATION_VALIDATOR.get_or_init(|| {
        let common: Value = serde_json::from_str(include_str!("../../../schemas/pcs/common.defs.json"))
            .expect("common.defs.json");
        let mut doc = read_nested_schema("FailureLocalizationResult.v0.schema.json");
        strip_schema_metadata(&mut doc);
        rewrite_common_defs_refs(&mut doc);
        if let Some(obj) = doc.as_object_mut() {
            if let Some(common_defs) = common.get("$defs") {
                obj.insert("$defs".to_string(), common_defs.clone());
            }
        }
        rewrite_common_defs_refs(&mut doc);
        Validator::new(&doc).expect("FailureLocalizationResult.v0 schema compiles")
    })
}

fn explain_quality_report_validator() -> &'static Validator {
    EXPLAIN_QUALITY_REPORT_VALIDATOR.get_or_init(|| {
        let common: Value = serde_json::from_str(include_str!("../../../schemas/pcs/common.defs.json"))
            .expect("common.defs.json");
        let mut doc = read_nested_schema("ExplainQualityReport.v0.schema.json");
        let nested_defs = doc.get("$defs").cloned();
        strip_schema_metadata(&mut doc);
        rewrite_common_defs_refs(&mut doc);
        if let Some(obj) = doc.as_object_mut() {
            let mut defs_map = serde_json::Map::new();
            if let Some(common_defs) = common.get("$defs").and_then(|v| v.as_object()) {
                for (k, v) in common_defs {
                    defs_map.insert(k.clone(), v.clone());
                }
            }
            if let Some(Value::Object(nested)) = nested_defs {
                for (k, v) in nested {
                    defs_map.insert(k.clone(), v.clone());
                }
            }
            obj.insert("$defs".to_string(), Value::Object(defs_map));
        }
        rewrite_common_defs_refs(&mut doc);
        Validator::new(&doc).expect("ExplainQualityReport.v0 schema compiles")
    })
}

fn pcs_bench_ingest_validator() -> &'static Validator {
    PCS_BENCH_INGEST_VALIDATOR.get_or_init(|| {
        Validator::new(&merged_pcs_bench_ingest_schema()).expect("PcsBenchIngest.v0 schema compiles")
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

pub fn validate_certificate_benchmark_run_schema(value: &Value) -> Result<(), String> {
    validate_with(certificate_benchmark_run_validator(), value)
}

/// Project a `CertificateBenchmarkRun.v0` document to pcs-core `BenchmarkRun.v0` fields.
pub fn benchmark_run_core_from_certificate_run(value: &Value) -> Value {
    const CORE_FIELDS: &[&str] = &[
        "schema_version",
        "run_id",
        "task_id",
        "case_id",
        "started_at",
        "completed_at",
        "commands",
        "artifacts_produced",
        "observed_status",
        "observed_failure_code",
        "observed_responsible_component",
        "observed_repair_hint",
        "system_admission_outcome",
        "release_chain_status",
        "certificate_status",
        "scientific_memory_import_status",
        "scientific_memory_render_status",
        "duration_ms",
        "source_repo",
        "source_commit",
        "signature_or_digest",
    ];
    let mut out = serde_json::Map::new();
    if let Some(obj) = value.as_object() {
        for key in CORE_FIELDS {
            if let Some(v) = obj.get(*key) {
                out.insert((*key).to_string(), v.clone());
            }
        }
    }
    if !out.contains_key("system_admission_outcome") {
        if let Some(Value::String(outcome)) = value.get("observed_system_outcome") {
            out.insert(
                "system_admission_outcome".to_string(),
                Value::String(outcome.clone()),
            );
        }
    }
    Value::Object(out)
}

pub fn validate_benchmark_report_schema(value: &Value) -> Result<(), String> {
    validate_with(benchmark_report_validator(), value)
}

pub fn validate_coverage_report_schema(value: &Value) -> Result<(), String> {
    validate_with(coverage_report_validator(), value)
}

pub fn validate_profile_coverage_report_schema(value: &Value) -> Result<(), String> {
    validate_with(profile_coverage_report_validator(), value)
}

pub fn validate_certificate_benchmark_suite_schema(value: &Value) -> Result<(), String> {
    validate_with(certificate_benchmark_suite_validator(), value)
}

pub fn validate_pcs_bench_ingest_schema(value: &Value) -> Result<(), String> {
    validate_with(pcs_bench_ingest_validator(), value)
}

pub fn validate_failure_localization_result_schema(value: &Value) -> Result<(), String> {
    validate_with(failure_localization_validator(), value)
}

pub fn validate_explain_quality_report_schema(value: &Value) -> Result<(), String> {
    validate_with(explain_quality_report_validator(), value)
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
    fn benchmark_run_schema_accepts_per_case_shape() {
        let doc = json!({
            "schema_version": "v0",
            "run_id": "bench-run-ok",
            "task_id": "hospital_lab.qc_release",
            "case_id": "ok",
            "started_at": "2026-05-19T12:00:00Z",
            "completed_at": "2026-05-19T12:00:01Z",
            "commands": [{"command": "certifyedge emit-pcs-certificate", "exit_code": 0}],
            "artifacts_produced": ["certificate.json"],
            "observed_status": "passed",
            "observed_failure_code": null,
            "observed_responsible_component": null,
            "observed_repair_hint": null,
            "certificate_status": "CertificateChecked",
            "duration_ms": 1,
            "source_repo": "https://github.com/fraware/CertifyEdge",
            "source_commit": "abcdef0123456789abcdef0123456789abcdef01",
            "signature_or_digest": "sha256:1111111111111111111111111111111111111111111111111111111111111111"
        });
        validate_benchmark_run_schema(&doc).unwrap();
    }

    #[test]
    fn certificate_benchmark_run_core_projection_validates() {
        let doc = json!({
            "schema_version": "v0",
            "run_id": "bench-run-ok",
            "task_id": "agent_tool_use.safety_v0",
            "case_id": "ok",
            "started_at": "2026-05-19T12:00:00Z",
            "completed_at": "2026-05-19T12:00:01Z",
            "commands": [{"command": "certifyedge emit-pcs-certificate", "exit_code": 0}],
            "artifacts_produced": ["certificate.json"],
            "observed_status": "passed",
            "observed_failure_code": null,
            "observed_responsible_component": null,
            "observed_repair_hint": null,
            "duration_ms": 1,
            "source_repo": "https://github.com/fraware/CertifyEdge",
            "source_commit": "abcdef0123456789abcdef0123456789abcdef01",
            "signature_or_digest": "sha256:1111111111111111111111111111111111111111111111111111111111111111",
            "suite_id": "certifyedge-tool-use-safety-v0",
            "workflow_id": "agent_tool_use.safety_v0",
            "workflow_profile_id": "agent_tool_use.safety_v0",
            "repair_hint_acceptable": true,
            "formal_facts_emitted": false,
            "expected_benchmark_status": "passed",
            "observed_benchmark_status": "passed",
            "expected_system_outcome": "admitted",
            "observed_system_outcome": "admitted",
            "repair_hint_quality": null,
            "logs": []
        });
        validate_certificate_benchmark_run_schema(&doc).unwrap();
        let core = benchmark_run_core_from_certificate_run(&doc);
        validate_benchmark_run_schema(&core).unwrap();
    }

    #[test]
    fn pcs_bench_ingest_schema_accepts_canonical_pcs_core_shape() {
        let run = json!({
            "schema_version": "v0",
            "run_id": "bench-run-ok",
            "task_id": "agent_tool_use.safety_v0",
            "case_id": "ok",
            "started_at": "2026-05-19T12:00:00Z",
            "completed_at": "2026-05-19T12:00:01Z",
            "commands": [{"command": "certifyedge emit-pcs-certificate", "exit_code": 0}],
            "artifacts_produced": ["certificate.json"],
            "observed_status": "passed",
            "observed_failure_code": null,
            "observed_responsible_component": null,
            "observed_repair_hint": null,
            "duration_ms": 1,
            "source_repo": "https://github.com/fraware/CertifyEdge",
            "source_commit": "abcdef0123456789abcdef0123456789abcdef01",
            "signature_or_digest": "sha256:1111111111111111111111111111111111111111111111111111111111111111"
        });
        let coverage = json!({
            "schema_version": "v0",
            "coverage_id": "suite-cert",
            "metric": "certificate_completeness",
            "numerator": 1.0,
            "denominator": 1.0,
            "coverage_ratio": 1.0,
            "details": { "profile_id": "agent_tool_use.safety_v0" },
            "source_repo": "https://github.com/fraware/CertifyEdge",
            "source_commit": "abcdef0123456789abcdef0123456789abcdef01",
            "signature_or_digest": "sha256:1111111111111111111111111111111111111111111111111111111111111111"
        });
        let profile_cov = json!({
            "schema_version": "v0",
            "coverage_id": "suite-profile",
            "workflow_profile_id": "agent_tool_use.safety_v0",
            "producer_id": "certifyedge",
            "artifact_types_required": ["ToolUseCertificate.v0"],
            "artifact_types_covered": ["ToolUseCertificate.v0"],
            "semantic_checks_required": ["unauthorized_tool_call"],
            "semantic_checks_covered": ["unauthorized_tool_call"],
            "handoff_steps_required": ["runtime_to_certificate"],
            "handoff_steps_covered": ["runtime_to_certificate"],
            "numerator": 1.0,
            "denominator": 1.0,
            "coverage_ratio": 1.0,
            "details": {
                "templates_checked": true,
                "release_mode_required_fields": ["policy_hash"],
                "counterexample_types_covered": []
            },
            "source_repo": "https://github.com/fraware/CertifyEdge",
            "source_commit": "abcdef0123456789abcdef0123456789abcdef01",
            "signature_or_digest": "sha256:1111111111111111111111111111111111111111111111111111111111111111"
        });
        let doc = json!({
            "schema_version": "v0",
            "producer_id": "certifyedge",
            "suite_id": "certifyedge-tool-use-safety-v0",
            "workflow_id": "agent_tool_use.safety_v0",
            "benchmark_runs": [run],
            "coverage_reports": [coverage],
            "failure_localization_reports": [],
            "explain_quality_reports": [],
            "profile_coverage_reports": [profile_cov],
            "commands": [{"command": "certifyedge benchmark certificates", "exit_code": 0}],
            "logs": [],
            "source_repo": "https://github.com/fraware/CertifyEdge",
            "source_commit": "abcdef0123456789abcdef0123456789abcdef01",
            "signature_or_digest": "sha256:1111111111111111111111111111111111111111111111111111111111111111"
        });
        validate_pcs_bench_ingest_schema(&doc).unwrap();
    }

    #[test]
    fn certificate_coverage_report_accepts_repair_hint_quality() {
        let mut doc = sample_coverage_report();
        doc["case_results"][0]["repair_hint_quality"] = json!({
            "repair_hint_present": true,
            "repair_hint_kind": "fix_trace_or_property",
            "responsible_component": "runtime_producer",
            "repair_command": "certifyedge check-trace"
        });
        validate_certificate_coverage_report_schema(&doc).unwrap();
    }

    #[test]
    fn certificate_benchmark_suite_schema_accepts_sample_shape() {
        let mut coverage = sample_coverage_report();
        coverage["case_results"][0]["repair_hint_quality"] = json!({
            "repair_hint_present": true,
            "repair_hint_kind": "fix_trace_or_property",
            "responsible_component": "runtime_producer",
            "repair_command": "certifyedge check-trace"
        });
        let doc = json!({
            "schema_version": "v0",
            "artifact": "CertificateBenchmarkSuite.v0",
            "profile_id": "hospital_lab.qc_release",
            "cases_dir": "benchmarks/certificates/hospital_lab_qc_release",
            "out_dir": "benchmark_runs/hospital_lab_qc_release",
            "started_at": "2026-05-19T12:00:00Z",
            "finished_at": "2026-05-19T12:00:01Z",
            "cases_run": 1,
            "cases_passed": 1,
            "coverage": coverage
        });
        validate_certificate_benchmark_suite_schema(&doc).unwrap();
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
