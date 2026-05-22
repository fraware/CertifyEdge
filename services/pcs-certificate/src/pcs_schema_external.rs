//! Validate benchmark outputs against schemas from an external pcs-core checkout.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use jsonschema::Validator;
use serde_json::Value;

use crate::pcs_schema::{
    benchmark_run_core_from_certificate_run, validate_certificate_coverage_report_schema,
    validate_pcs_bench_ingest_schema,
};

static PCS_CORE_INGEST_VALIDATOR: OnceLock<Result<Validator, String>> = OnceLock::new();

fn pcs_core_schemas_dir(pcs_core_root: &Path) -> PathBuf {
    pcs_core_root.join("schemas")
}

fn rewrite_external_refs(value: &mut Value) {
    match value {
        Value::Object(map) => {
            if let Some(Value::String(reference)) = map.get("$ref") {
                let rewritten = if let Some(suffix) = reference.strip_prefix("common.defs.json#/") {
                    Some(format!("#/{suffix}"))
                } else if reference == "BenchmarkRun.v0.schema.json" {
                    Some("#/$defs/benchmark_run_v0".to_string())
                } else if reference == "CoverageReport.v0.schema.json" {
                    Some("#/$defs/coverage_report_v0".to_string())
                } else if reference == "ProfileCoverageReport.v0.schema.json" {
                    Some("#/$defs/profile_coverage_report_v0".to_string())
                } else if reference == "FailureLocalizationResult.v0.schema.json" {
                    Some("#/$defs/failure_localization_result_v0".to_string())
                } else if reference == "ExplainQualityReport.v0.schema.json" {
                    Some("#/$defs/explain_quality_report_v0".to_string())
                } else if reference == "BenchmarkArtifactRef.v0.schema.json" {
                    Some("#/$defs/benchmark_artifact_ref_v0".to_string())
                } else if reference == "MetricSummary.v0.schema.json" {
                    Some("#/$defs/metric_summary_v0".to_string())
                } else {
                    None
                };
                if let Some(r) = rewritten {
                    map.insert("$ref".to_string(), Value::String(r));
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

fn strip_schema_metadata(value: &mut Value) {
    if let Some(obj) = value.as_object_mut() {
        for key in ["$schema", "$id", "title", "description"] {
            obj.remove(key);
        }
    }
}

fn read_schema_file(schemas_dir: &Path, name: &str) -> Result<Value, String> {
    let path = schemas_dir.join(name);
    let text = std::fs::read_to_string(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
    serde_json::from_str(&text).map_err(|e| format!("parse {}: {e}", path.display()))
}

fn load_merged_pcs_core_schema(schemas_dir: &Path, name: &str) -> Result<Value, String> {
    let common = read_schema_file(schemas_dir, "common.defs.json")?;
    let mut schema = read_schema_file(schemas_dir, name)?;
    if let (Some(common_defs), Some(obj)) = (common.get("$defs"), schema.as_object_mut()) {
        obj.insert("$defs".to_string(), common_defs.clone());
    }
    rewrite_external_refs(&mut schema);
    Ok(schema)
}

fn load_pcs_core_merged_ingest_schema(schemas_dir: &Path) -> Result<Value, String> {
    let common = read_schema_file(schemas_dir, "common.defs.json")?;
    let mut ingest = read_schema_file(schemas_dir, "PcsBenchIngest.v0.schema.json")?;
    let mut benchmark_run = read_schema_file(schemas_dir, "BenchmarkRun.v0.schema.json")?;
    let mut coverage = read_schema_file(schemas_dir, "CoverageReport.v0.schema.json")?;
    let mut profile_cov = read_schema_file(schemas_dir, "ProfileCoverageReport.v0.schema.json")?;
    let mut failure_loc = read_schema_file(schemas_dir, "FailureLocalizationResult.v0.schema.json")?;
    let mut explain = read_schema_file(schemas_dir, "ExplainQualityReport.v0.schema.json")?;
    let mut artifact_ref = read_schema_file(schemas_dir, "BenchmarkArtifactRef.v0.schema.json")?;
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
        rewrite_external_refs(doc);
    }
    if let Some(obj) = explain.as_object_mut() {
        obj.remove("$defs");
    }
    rewrite_external_refs(&mut ingest);
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
    rewrite_external_refs(&mut ingest);
    Ok(ingest)
}

fn pcs_core_ingest_validator(schemas_dir: &Path) -> Result<&Validator, String> {
    PCS_CORE_INGEST_VALIDATOR
        .get_or_init(|| {
            let schema = load_pcs_core_merged_ingest_schema(schemas_dir)?;
            Validator::new(&schema).map_err(|e| format!("compile pcs-core PcsBenchIngest.v0: {e}"))
        })
        .as_ref()
        .map_err(|e| e.clone())
}

fn validator_for_explain_quality(schemas_dir: &Path) -> Result<Validator, String> {
    let common = read_schema_file(schemas_dir, "common.defs.json")?;
    let mut doc = read_schema_file(schemas_dir, "ExplainQualityReport.v0.schema.json")?;
    let nested_defs = doc.get("$defs").cloned();
    strip_schema_metadata(&mut doc);
    rewrite_external_refs(&mut doc);
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
    rewrite_external_refs(&mut doc);
    Validator::new(&doc).map_err(|e| format!("compile pcs-core ExplainQualityReport.v0: {e}"))
}

fn load_merged_benchmark_report_schema(schemas_dir: &Path) -> Result<Value, String> {
    let common = read_schema_file(schemas_dir, "common.defs.json")?;
    let mut report = read_schema_file(schemas_dir, "BenchmarkReport.v0.schema.json")?;
    let mut coverage = read_schema_file(schemas_dir, "CoverageReport.v0.schema.json")?;
    let mut profile = read_schema_file(schemas_dir, "ProfileCoverageReport.v0.schema.json")?;
    let mut metric_summary = read_schema_file(schemas_dir, "MetricSummary.v0.schema.json")?;
    let mut explain = read_schema_file(schemas_dir, "ExplainQualityReport.v0.schema.json")?;
    let explain_nested_defs = explain.get("$defs").cloned();
    strip_schema_metadata(&mut report);
    strip_schema_metadata(&mut coverage);
    strip_schema_metadata(&mut profile);
    strip_schema_metadata(&mut metric_summary);
    strip_schema_metadata(&mut explain);
    rewrite_external_refs(&mut report);
    rewrite_external_refs(&mut coverage);
    rewrite_external_refs(&mut profile);
    rewrite_external_refs(&mut metric_summary);
    rewrite_external_refs(&mut explain);
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
        defs_map.insert("coverage_report_v0".to_string(), coverage);
        defs_map.insert("profile_coverage_report_v0".to_string(), profile);
        defs_map.insert("metric_summary_v0".to_string(), metric_summary);
        if let Some(Value::Object(nested)) = explain_nested_defs {
            for (k, v) in nested {
                defs_map.insert(k.clone(), v.clone());
            }
        }
        defs_map.insert("explain_quality_report_v0".to_string(), explain);
        obj.insert("$defs".to_string(), Value::Object(defs_map));
    }
    rewrite_external_refs(&mut report);
    Ok(report)
}

fn validator_for(schemas_dir: &Path, name: &str) -> Result<Validator, String> {
    if name == "ExplainQualityReport.v0.schema.json" {
        return validator_for_explain_quality(schemas_dir);
    }
    if name == "BenchmarkReport.v0.schema.json" {
        let schema = load_merged_benchmark_report_schema(schemas_dir)?;
        return Validator::new(&schema).map_err(|e| format!("compile pcs-core {name}: {e}"));
    }
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
    let coverage_validator = validator_for(&schemas_dir, "CoverageReport.v0.schema.json")?;
    let failure_validator =
        validator_for(&schemas_dir, "FailureLocalizationResult.v0.schema.json")?;
    let explain_validator = validator_for(&schemas_dir, "ExplainQualityReport.v0.schema.json")?;

    let ingest_path = out_dir.join("pcs_bench_ingest.v0.json");
    if ingest_path.is_file() {
        let ingest: Value = read_json(&ingest_path)?;
        validate_pcs_bench_ingest_schema(&ingest)?;
        validate_with(
            pcs_core_ingest_validator(&schemas_dir)?,
            &ingest,
            "pcs_bench_ingest (pcs-core PcsBenchIngest.v0)",
        )?;
        if let Some(ingest_runs) = ingest.get("benchmark_runs").and_then(|v| v.as_array()) {
            for (idx, run) in ingest_runs.iter().enumerate() {
                validate_with(
                    &run_validator,
                    run,
                    &format!("pcs_bench_ingest.benchmark_runs[{idx}] (pcs-core BenchmarkRun.v0)"),
                )?;
            }
        }
        if let Some(reports) = ingest.get("coverage_reports").and_then(|v| v.as_array()) {
            for (idx, cov) in reports.iter().enumerate() {
                validate_with(
                    &coverage_validator,
                    cov,
                    &format!("pcs_bench_ingest.coverage_reports[{idx}] (pcs-core)"),
                )?;
            }
            let ingest_repair = reports
                .iter()
                .find(|r| r.get("metric").and_then(|v| v.as_str()) == Some("repair_hint_quality"));
            if ingest_repair != Some(&repair_cov) {
                return Err(
                    "pcs_bench_ingest.coverage_reports repair_hint_quality != repair_hint_quality_report.v0.json (pcs-core gate)"
                        .into(),
                );
            }
        }
        if let Some(reports) = ingest
            .get("profile_coverage_reports")
            .and_then(|v| v.as_array())
        {
            if reports.first() != Some(&profile_cov) {
                return Err(
                    "pcs_bench_ingest.profile_coverage_reports[0] != profile_coverage_report.v0.json (pcs-core gate)"
                        .into(),
                );
            }
        }
        if let Some(items) = ingest
            .get("failure_localization_reports")
            .and_then(|v| v.as_array())
        {
            for (idx, loc) in items.iter().enumerate() {
                validate_with(
                    &failure_validator,
                    loc,
                    &format!("pcs_bench_ingest.failure_localization_reports[{idx}] (pcs-core)"),
                )?;
            }
        }
        if let Some(items) = ingest
            .get("explain_quality_reports")
            .and_then(|v| v.as_array())
        {
            for (idx, exp) in items.iter().enumerate() {
                validate_with(
                    &explain_validator,
                    exp,
                    &format!("pcs_bench_ingest.explain_quality_reports[{idx}] (pcs-core)"),
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
