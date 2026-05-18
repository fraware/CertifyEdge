//! Computation handoff receipts (`ComputationRunReceipt.v0` and supporting artifacts).

use serde::Deserialize;
use serde_json::Value;

pub const ARTIFACT_COMPUTATION_RUN_RECEIPT: &str = "ComputationRunReceipt.v0";
pub const ARTIFACT_DATASET_RECEIPT: &str = "DatasetReceipt.v0";
pub const ARTIFACT_ENVIRONMENT_RECEIPT: &str = "EnvironmentReceipt.v0";
pub const ARTIFACT_RESULT_ARTIFACT: &str = "ResultArtifact.v0";

pub const COMPUTATION_RUN_RECEIPT_FILE: &str = "computation_run_receipt.json";
pub const DATASET_RECEIPT_FILE: &str = "dataset_receipt.json";
pub const ENVIRONMENT_RECEIPT_FILE: &str = "environment_receipt.json";
pub const RESULT_ARTIFACT_FILE: &str = "result_artifact.json";

#[derive(Debug, Clone, Deserialize, PartialEq)]
pub struct ComputationRunReceiptV0 {
    pub schema_version: String,
    pub run_id: String,
    pub run_hash: String,
    pub dataset_receipt_hash: String,
    pub environment_receipt_hash: String,
    pub code_commit: String,
    pub exit_code: i64,
    pub result_artifact_hashes: Vec<String>,
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
pub struct DatasetReceiptV0 {
    pub schema_version: String,
    pub receipt_hash: String,
    #[serde(default)]
    pub dataset_id: String,
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
pub struct EnvironmentReceiptV0 {
    pub schema_version: String,
    pub receipt_hash: String,
    pub environment_digest: String,
}

#[derive(Debug, Clone, Deserialize, PartialEq)]
pub struct ResultArtifactV0 {
    pub schema_version: String,
    pub artifact_hash: String,
    #[serde(default)]
    pub artifact_id: String,
}

#[derive(Debug, Clone)]
pub struct ComputationEmitInputs {
    pub run_receipt: ComputationRunReceiptV0,
    pub dataset_receipt: DatasetReceiptV0,
    pub environment_receipt: EnvironmentReceiptV0,
    pub result_artifact: ResultArtifactV0,
}

pub fn parse_computation_run_receipt(text: &str) -> Result<ComputationRunReceiptV0, String> {
    serde_json::from_str(text).map_err(|e| format!("invalid ComputationRunReceipt.v0 JSON: {e}"))
}

pub fn parse_dataset_receipt(text: &str) -> Result<DatasetReceiptV0, String> {
    serde_json::from_str(text).map_err(|e| format!("invalid DatasetReceipt.v0 JSON: {e}"))
}

pub fn parse_environment_receipt(text: &str) -> Result<EnvironmentReceiptV0, String> {
    serde_json::from_str(text).map_err(|e| format!("invalid EnvironmentReceipt.v0 JSON: {e}"))
}

pub fn parse_result_artifact(text: &str) -> Result<ResultArtifactV0, String> {
    serde_json::from_str(text).map_err(|e| format!("invalid ResultArtifact.v0 JSON: {e}"))
}

pub fn load_computation_inputs_from_dir(
    dir: &std::path::Path,
) -> Result<ComputationEmitInputs, String> {
    let run_text = std::fs::read_to_string(dir.join(COMPUTATION_RUN_RECEIPT_FILE))
        .map_err(|e| format!("read {COMPUTATION_RUN_RECEIPT_FILE}: {e}"))?;
    let dataset_text = std::fs::read_to_string(dir.join(DATASET_RECEIPT_FILE))
        .map_err(|e| format!("read {DATASET_RECEIPT_FILE}: {e}"))?;
    let environment_text = std::fs::read_to_string(dir.join(ENVIRONMENT_RECEIPT_FILE))
        .map_err(|e| format!("read {ENVIRONMENT_RECEIPT_FILE}: {e}"))?;
    let result_text = std::fs::read_to_string(dir.join(RESULT_ARTIFACT_FILE))
        .map_err(|e| format!("read {RESULT_ARTIFACT_FILE}: {e}"))?;
    load_computation_inputs_from_json(&run_text, &dataset_text, &environment_text, &result_text)
}

pub fn load_computation_inputs_from_json(
    run_text: &str,
    dataset_text: &str,
    environment_text: &str,
    result_text: &str,
) -> Result<ComputationEmitInputs, String> {
    Ok(ComputationEmitInputs {
        run_receipt: parse_computation_run_receipt(run_text)?,
        dataset_receipt: parse_dataset_receipt(dataset_text)?,
        environment_receipt: parse_environment_receipt(environment_text)?,
        result_artifact: parse_result_artifact(result_text)?,
    })
}

pub fn computation_counterexample_json(failure_code: &str, detail: &str) -> Value {
    serde_json::json!({
        "failure_code": failure_code,
        "detail": detail,
    })
}
