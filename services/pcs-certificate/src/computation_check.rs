//! Computation reproducibility checks for `scientific_computation.reproducibility_v0`.

use std::path::Path;

use serde::Serialize;
use serde_json::Value;

use crate::computation_receipt::ComputationEmitInputs;
use crate::computation_violation::ComputationViolationV0;

#[derive(Debug, Clone)]
pub struct ComputationPropertySpec {
    pub property_id: String,
}

impl ComputationPropertySpec {
    pub fn load(path: &Path) -> Result<Self, String> {
        let raw_text = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
        let property_id = parse_property_id(&raw_text)
            .ok_or_else(|| format!("spec {} missing property: line", path.display()))?;
        Ok(Self { property_id })
    }
}

fn parse_property_id(text: &str) -> Option<String> {
    for line in text.lines() {
        let line = line.trim();
        if let Some(id) = line.strip_prefix("property:") {
            let id = id.trim();
            if !id.is_empty() {
                return Some(id.to_string());
            }
        }
    }
    None
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct ComputationCheckResult {
    pub passed: bool,
    pub failure_code: Option<String>,
    pub violations: Vec<ComputationViolationV0>,
    pub counterexample: Option<Value>,
}

impl ComputationCheckResult {
    fn fail(failure_code: &str, message: impl Into<String>, detail: impl Into<String>) -> Self {
        let message = message.into();
        Self {
            passed: false,
            failure_code: Some(failure_code.to_string()),
            violations: vec![ComputationViolationV0::new(failure_code, message)],
            counterexample: Some(crate::computation_receipt::computation_counterexample_json(
                failure_code,
                &detail.into(),
            )),
        }
    }
}

pub fn check_computation_reproducibility(inputs: &ComputationEmitInputs) -> ComputationCheckResult {
    let run = &inputs.run_receipt;
    let dataset = &inputs.dataset_receipt;
    let environment = &inputs.environment_receipt;
    let result = &inputs.result_artifact;

    if run.dataset_receipt_hash != dataset.receipt_hash {
        return ComputationCheckResult::fail(
            "dataset_hash_mismatch",
            format!(
                "dataset receipt hash mismatch: run expects {}, dataset receipt has {}",
                run.dataset_receipt_hash, dataset.receipt_hash
            ),
            format!(
                "run.dataset_receipt_hash={} dataset.receipt_hash={}",
                run.dataset_receipt_hash, dataset.receipt_hash
            ),
        );
    }

    if run.environment_receipt_hash != environment.receipt_hash {
        return ComputationCheckResult::fail(
            "environment_digest_mismatch",
            format!(
                "environment receipt hash mismatch: run expects {}, environment receipt has {}",
                run.environment_receipt_hash, environment.receipt_hash
            ),
            format!(
                "run.environment_receipt_hash={} environment.receipt_hash={} digest={}",
                run.environment_receipt_hash,
                environment.receipt_hash,
                environment.environment_digest
            ),
        );
    }

    if environment.environment_digest.trim().is_empty() {
        return ComputationCheckResult::fail(
            "environment_digest_mismatch",
            "environment receipt missing environment_digest",
            "environment.environment_digest is empty",
        );
    }

    if run.code_commit.trim().is_empty() {
        return ComputationCheckResult::fail(
            "missing_code_commit",
            "computation run receipt missing code_commit",
            "run.code_commit is empty",
        );
    }

    if run.exit_code != 0 {
        return ComputationCheckResult::fail(
            "nonzero_exit_code",
            format!("computation run exit_code={} (expected 0)", run.exit_code),
            format!("run.exit_code={}", run.exit_code),
        );
    }

    if run.result_artifact_hashes.is_empty() {
        return ComputationCheckResult::fail(
            "missing_result_artifact",
            "computation run receipt has no result_artifact_hashes",
            "run.result_artifact_hashes is empty",
        );
    }

    if !run
        .result_artifact_hashes
        .iter()
        .any(|h| h == &result.artifact_hash)
    {
        return ComputationCheckResult::fail(
            "result_hash_mismatch",
            format!(
                "result artifact hash {} not listed on run receipt {:?}",
                result.artifact_hash, run.result_artifact_hashes
            ),
            format!(
                "result.artifact_hash={} run.result_artifact_hashes={:?}",
                result.artifact_hash, run.result_artifact_hashes
            ),
        );
    }

    ComputationCheckResult {
        passed: true,
        failure_code: None,
        violations: vec![],
        counterexample: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::computation_receipt::{
        ComputationRunReceiptV0, DatasetReceiptV0, EnvironmentReceiptV0, ResultArtifactV0,
    };

    fn valid_inputs() -> ComputationEmitInputs {
        ComputationEmitInputs {
            run_receipt: ComputationRunReceiptV0 {
                schema_version: "v0".into(),
                run_id: "run-001".into(),
                run_hash: "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                    .into(),
                dataset_receipt_hash:
                    "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into(),
                environment_receipt_hash:
                    "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc".into(),
                code_commit: "abcdef0123456789abcdef0123456789abcdef01".into(),
                exit_code: 0,
                result_artifact_hashes: vec![
                    "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd"
                        .into(),
                ],
            },
            dataset_receipt: DatasetReceiptV0 {
                schema_version: "v0".into(),
                receipt_hash:
                    "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into(),
                dataset_id: "dataset-001".into(),
            },
            environment_receipt: EnvironmentReceiptV0 {
                schema_version: "v0".into(),
                receipt_hash:
                    "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc".into(),
                environment_digest:
                    "sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee".into(),
            },
            result_artifact: ResultArtifactV0 {
                schema_version: "v0".into(),
                artifact_hash:
                    "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd".into(),
                artifact_id: "result-001".into(),
            },
        }
    }

    #[test]
    fn valid_computation_inputs_pass() {
        assert!(check_computation_reproducibility(&valid_inputs()).passed);
    }

    #[test]
    fn dataset_mismatch_fails() {
        let mut inputs = valid_inputs();
        inputs.dataset_receipt.receipt_hash =
            "sha256:0000000000000000000000000000000000000000000000000000000000000000".into();
        let result = check_computation_reproducibility(&inputs);
        assert!(!result.passed);
        assert_eq!(
            result.failure_code.as_deref(),
            Some("dataset_hash_mismatch")
        );
    }

    #[test]
    fn environment_mismatch_fails() {
        let mut inputs = valid_inputs();
        inputs.environment_receipt.receipt_hash =
            "sha256:0000000000000000000000000000000000000000000000000000000000000000".into();
        let result = check_computation_reproducibility(&inputs);
        assert_eq!(
            result.failure_code.as_deref(),
            Some("environment_digest_mismatch")
        );
    }

    #[test]
    fn missing_code_commit_fails() {
        let mut inputs = valid_inputs();
        inputs.run_receipt.code_commit = String::new();
        let result = check_computation_reproducibility(&inputs);
        assert_eq!(result.failure_code.as_deref(), Some("missing_code_commit"));
    }

    #[test]
    fn nonzero_exit_code_fails() {
        let mut inputs = valid_inputs();
        inputs.run_receipt.exit_code = 2;
        let result = check_computation_reproducibility(&inputs);
        assert_eq!(result.failure_code.as_deref(), Some("nonzero_exit_code"));
    }

    #[test]
    fn result_hash_mismatch_fails() {
        let mut inputs = valid_inputs();
        inputs.result_artifact.artifact_hash =
            "sha256:0000000000000000000000000000000000000000000000000000000000000000".into();
        let result = check_computation_reproducibility(&inputs);
        assert_eq!(result.failure_code.as_deref(), Some("result_hash_mismatch"));
    }

    #[test]
    fn missing_result_artifact_list_fails() {
        let mut inputs = valid_inputs();
        inputs.run_receipt.result_artifact_hashes.clear();
        let result = check_computation_reproducibility(&inputs);
        assert_eq!(
            result.failure_code.as_deref(),
            Some("missing_result_artifact")
        );
    }
}
