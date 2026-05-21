//! Validate benchmark outputs against schemas from an external pcs-core checkout.

use std::path::{Path, PathBuf};

use jsonschema::Validator;
use serde_json::Value;

use crate::pcs_schema::{
    benchmark_run_core_from_certificate_run, validate_certificate_coverage_report_schema,
    validate_pcs_bench_ingest_schema,
};

fn pcs_core_schemas_dir(pcs_core_root: &Path) -> PathBuf {
    pcs_core_root.join("schemas")
}

fn load_merged_pcs_core_schema(schemas_dir: &Path, name: &str) -> Result<Value, String> {
    let common_path = schemas_dir.join("common.defs.json");
    let schema_path = schemas_dir.join(name);
    let common: Value =
        serde_json::from_str(&std::fs::read_to_string(&common_path).map_err(|e| e.to_string())?)
            .map_err(|e| format!("parse {}: {e}", common_path.display()))?;
    let mut schema: Value =
        serde_json::from_str(&std::fs::read_to_string(&schema_path).map_err(|e| e.to_string())?)
            .map_err(|e| format!("parse {}: {e}", schema_path.display()))?;
    if let (Some(common_defs), Some(obj)) = (common.get("$defs"), schema.as_object_mut()) {
        obj.insert("$defs".to_string(), common_defs.clone());
    }
    rewrite_external_refs(&mut schema);
    Ok(schema)
}

fn rewrite_external_refs(value: &mut Value) {
    match value {
        Value::Object(map) => {
            if let Some(Value::String(reference)) = map.get("$ref") {
                if let Some(suffix) = reference.strip_prefix("common.defs.json#/") {
                    map.insert("$ref".to_string(), Value::String(format!("#/{suffix}")));
                }
            }
            for child in map.values_mut() {
                rewrite_external_refs(child);
            }
        }
        Value::Array(items) => {
            for child in items {
                rewrite_external_refs(child);
            }
        }
        _ => {}
    }
}

fn validator_for(schemas_dir: &Path, name: &str) -> Result<Validator, String> {
    let schema = load_merged_pcs_core_schema(schemas_dir, name)?;
    Validator::new(&schema).map_err(|e| format!("compile pcs-core {name}: {e}"))
}

fn validate_with(validator: &Validator, value: &Value, label: &str) -> Result<(), String> {
    let errors: Vec<String> = validator
        .iter_errors(value)
        .map(|e| e.to_string())
        .collect();
    if errors.is_empty() {
        Ok(())
    } else {
        Err(format!("{label}: {}", errors.join("; ")))
    }
}

/// Validate normalized benchmark artifacts under `out_dir` using schemas from `pcs_core_root`.
pub fn validate_pcs_core_output_dir(pcs_core_root: &Path, out_dir: &Path) -> Result<(), String> {
    let schemas_dir = pcs_core_schemas_dir(pcs_core_root);
    if !schemas_dir.is_dir() {
        return Err(format!(
            "pcs-core schemas not found at {}",
            schemas_dir.display()
        ));
    }

    let report_path = out_dir.join("benchmark_report.v0.json");
    let report: Value = read_json(&report_path)?;
    validate_with(
        &validator_for(&schemas_dir, "BenchmarkReport.v0.schema.json")?,
        &report,
        "benchmark_report (pcs-core)",
    )?;

    let profile_cov: Value = read_json(&out_dir.join("profile_coverage_report.v0.json"))?;
    validate_with(
        &validator_for(&schemas_dir, "ProfileCoverageReport.v0.schema.json")?,
        &profile_cov,
        "profile_coverage_report (pcs-core)",
    )?;

    let repair_cov: Value = read_json(&out_dir.join("repair_hint_quality_report.v0.json"))?;
    validate_with(
        &validator_for(&schemas_dir, "CoverageReport.v0.schema.json")?,
        &repair_cov,
        "repair_hint_quality_report (pcs-core)",
    )?;

    let cert_cov: Value = read_json(&out_dir.join("certificate_coverage_report.v0.json"))?;
    validate_certificate_coverage_report_schema(&cert_cov)?;

    let run_validator = validator_for(&schemas_dir, "BenchmarkRun.v0.schema.json")?;

    let ingest_path = out_dir.join("pcs_bench_ingest.v0.json");
    if ingest_path.is_file() {
        let ingest: Value = read_json(&ingest_path)?;
        validate_pcs_bench_ingest_schema(&ingest)?;
        if let Some(ingest_runs) = ingest.get("benchmark_runs").and_then(|v| v.as_array()) {
            for (idx, run) in ingest_runs.iter().enumerate() {
                let core = benchmark_run_core_from_certificate_run(run);
                validate_with(
                    &run_validator,
                    &core,
                    &format!("pcs_bench_ingest.benchmark_runs[{idx}] (pcs-core BenchmarkRun.v0)"),
                )?;
            }
        }
    }
    let runs = report
        .get("runs")
        .and_then(|v| v.as_array())
        .ok_or_else(|| "benchmark_report.runs missing".to_string())?;
    for run_ref in runs {
        let rel = run_ref
            .get("path")
            .and_then(|v| v.as_str())
            .ok_or_else(|| "run ref missing path".to_string())?;
        let run_doc = read_json(&out_dir.join(rel))?;
        let core = benchmark_run_core_from_certificate_run(&run_doc);
        validate_with(
            &run_validator,
            &core,
            &format!("{rel} (pcs-core BenchmarkRun.v0)"),
        )?;
    }

    Ok(())
}

fn read_json(path: &Path) -> Result<Value, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("read {}: {e}", path.display()))?;
    serde_json::from_str(&text).map_err(|e| format!("parse {}: {e}", path.display()))
}
