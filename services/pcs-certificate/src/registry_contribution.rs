//! Validate CertifyEdge `ArtifactRegistry.v0` contribution entries in-process.

use jsonschema::Validator;
use serde_json::Value;
use std::path::Path;
use std::sync::OnceLock;

static REGISTRY_ENTRY_VALIDATOR: OnceLock<Validator> = OnceLock::new();

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

fn merged_registry_entry_schema() -> Value {
    let common: Value = serde_json::from_str(include_str!("../../../schemas/pcs/common.defs.json"))
        .expect("common.defs.json");
    let registry: Value = serde_json::from_str(include_str!(
        "../../../schemas/pcs/ArtifactRegistry.v0.schema.json"
    ))
    .expect("ArtifactRegistry.v0.schema.json");

    let entry = registry
        .pointer("/$defs/registry_entry")
        .expect("registry_entry def")
        .clone();

    let mut schema = serde_json::json!({
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$defs": {}
    });
    if let Some(common_defs) = common.get("$defs") {
        schema["$defs"] = common_defs.clone();
    }
    if let Some(entry_defs) = registry.pointer("/$defs") {
        if let (Some(target), Some(source)) =
            (schema["$defs"].as_object_mut(), entry_defs.as_object())
        {
            for (key, value) in source {
                if key != "registry_entry" {
                    target.insert(key.clone(), value.clone());
                }
            }
        }
    }
    schema["allOf"] = serde_json::json!([entry]);
    rewrite_common_defs_refs(&mut schema);
    schema
}

fn registry_entry_validator() -> &'static Validator {
    REGISTRY_ENTRY_VALIDATOR.get_or_init(|| {
        let schema = merged_registry_entry_schema();
        Validator::new(&schema).expect("ArtifactRegistry registry_entry schema compiles")
    })
}

/// Validate a single registry contribution object against vendored `registry_entry` schema.
pub fn validate_registry_contribution_entry(value: &Value) -> Result<(), String> {
    let validator = registry_entry_validator();
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

fn validate_registry_contribution_file(repo_root: &Path, relative: &str) -> Result<(), String> {
    let path = repo_root.join(relative);
    let text =
        std::fs::read_to_string(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
    let value: Value = serde_json::from_str(&text).map_err(|e| e.to_string())?;
    validate_registry_contribution_entry(&value)
}

/// Load and validate `pcs_registry/TraceCertificate.v0.registry.json` under `repo_root`.
pub fn validate_default_trace_certificate_registry_contribution(
    repo_root: &Path,
) -> Result<(), String> {
    validate_registry_contribution_file(repo_root, "pcs_registry/TraceCertificate.v0.registry.json")
}

/// Load and validate `pcs_registry/ToolUseCertificate.v0.registry.json` under `repo_root`.
pub fn validate_default_tool_use_certificate_registry_contribution(
    repo_root: &Path,
) -> Result<(), String> {
    validate_registry_contribution_file(
        repo_root,
        "pcs_registry/ToolUseCertificate.v0.registry.json",
    )
}

/// Load and validate `pcs_registry/ComputationWitness.v0.registry.json` under `repo_root`.
pub fn validate_default_computation_witness_registry_contribution(
    repo_root: &Path,
) -> Result<(), String> {
    validate_registry_contribution_file(
        repo_root,
        "pcs_registry/ComputationWitness.v0.registry.json",
    )
}

/// Load and validate `pcs_registry/CertificateFormalFacts.v0.registry.json` under `repo_root`.
pub fn validate_default_certificate_formal_facts_registry_contribution(
    repo_root: &Path,
) -> Result<(), String> {
    validate_registry_contribution_file(
        repo_root,
        "pcs_registry/CertificateFormalFacts.v0.registry.json",
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn repo_root() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    #[test]
    fn trace_certificate_contribution_validates() {
        validate_default_trace_certificate_registry_contribution(&repo_root()).unwrap();
    }

    #[test]
    fn tool_use_certificate_contribution_validates() {
        validate_default_tool_use_certificate_registry_contribution(&repo_root()).unwrap();
    }

    #[test]
    fn computation_witness_contribution_validates() {
        validate_default_computation_witness_registry_contribution(&repo_root()).unwrap();
    }

    #[test]
    fn certificate_formal_facts_contribution_validates() {
        validate_default_certificate_formal_facts_registry_contribution(&repo_root()).unwrap();
    }

    #[test]
    fn benchmark_run_contribution_validates() {
        validate_registry_contribution_file(
            &repo_root(),
            "pcs_registry/BenchmarkRun.v0.registry.json",
        )
        .unwrap();
    }

    #[test]
    fn certificate_benchmark_run_contribution_validates() {
        validate_registry_contribution_file(
            &repo_root(),
            "pcs_registry/CertificateBenchmarkRun.v0.registry.json",
        )
        .unwrap();
    }

    #[test]
    fn pcs_bench_ingest_contribution_validates() {
        validate_registry_contribution_file(
            &repo_root(),
            "pcs_registry/PcsBenchIngest.v0.registry.json",
        )
        .unwrap();
    }

    #[test]
    fn benchmark_artifact_ref_contribution_validates() {
        validate_registry_contribution_file(
            &repo_root(),
            "pcs_registry/BenchmarkArtifactRef.v0.registry.json",
        )
        .unwrap();
    }

    #[test]
    fn certificate_coverage_report_contribution_validates() {
        validate_registry_contribution_file(
            &repo_root(),
            "pcs_registry/CertificateCoverageReport.v0.registry.json",
        )
        .unwrap();
    }

    #[test]
    fn benchmark_report_contribution_validates() {
        validate_registry_contribution_file(
            &repo_root(),
            "pcs_registry/BenchmarkReport.v0.registry.json",
        )
        .unwrap();
    }

    #[test]
    fn coverage_report_contribution_validates() {
        validate_registry_contribution_file(
            &repo_root(),
            "pcs_registry/CoverageReport.v0.registry.json",
        )
        .unwrap();
    }

    #[test]
    fn profile_coverage_report_contribution_validates() {
        validate_registry_contribution_file(
            &repo_root(),
            "pcs_registry/ProfileCoverageReport.v0.registry.json",
        )
        .unwrap();
    }

    #[test]
    fn certificate_benchmark_suite_contribution_validates() {
        validate_registry_contribution_file(
            &repo_root(),
            "pcs_registry/CertificateBenchmarkSuite.v0.registry.json",
        )
        .unwrap();
    }

    #[test]
    fn failure_localization_result_contribution_validates() {
        validate_registry_contribution_file(
            &repo_root(),
            "pcs_registry/FailureLocalizationResult.v0.registry.json",
        )
        .unwrap();
    }

    #[test]
    fn explain_quality_report_contribution_validates() {
        validate_registry_contribution_file(
            &repo_root(),
            "pcs_registry/ExplainQualityReport.v0.registry.json",
        )
        .unwrap();
    }
}
