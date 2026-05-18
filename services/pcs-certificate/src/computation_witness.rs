//! `ComputationWitness.v0` construction for computation profiles.

use serde::{Deserialize, Serialize};
use uuid::Uuid;

use crate::computation_check::ComputationCheckResult;
use crate::computation_receipt::ComputationEmitInputs;
use crate::computation_violation::ComputationViolationV0;
use crate::metadata::CertifyEdgeMetadata;
use crate::property_profile::PropertyProfile;
use crate::source_commit::ZERO_SOURCE_COMMIT;
use crate::status_policy::STATUS_CERTIFICATE_PENDING;
use crate::trace_certificate::{CHECKER, SCHEMA_VERSION, SOURCE_REPO};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct ComputationWitnessV0 {
    pub schema_version: String,
    pub certificate_id: String,
    pub run_hash: String,
    pub dataset_receipt_hash: String,
    pub environment_receipt_hash: String,
    pub code_commit: String,
    pub property_id: String,
    pub checker: String,
    pub checker_version: String,
    pub status: String,
    pub violations: Vec<ComputationViolationV0>,
    pub result_artifact_hashes: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub counterexample_ref: Option<String>,
    pub source_repo: String,
    pub source_commit: String,
    pub signature_or_digest: String,
}

pub fn build_computation_witness(
    inputs: &ComputationEmitInputs,
    profile: &PropertyProfile,
    check: &ComputationCheckResult,
    meta: &CertifyEdgeMetadata,
    counterexample_ref: Option<String>,
) -> Result<ComputationWitnessV0, String> {
    let status = crate::property_profile::status_for_check(profile, check.passed).to_string();
    crate::property_profile::validate_certificate_status_transition_for_profile(
        STATUS_CERTIFICATE_PENDING,
        &status,
        profile,
        meta.release_mode,
    )?;

    let run = &inputs.run_receipt;
    let code_commit = if run.code_commit.trim().is_empty() {
        // Schema requires a 40-hex git commit; violations carry `missing_code_commit`.
        ZERO_SOURCE_COMMIT.to_string()
    } else {
        run.code_commit.clone()
    };
    let mut witness = ComputationWitnessV0 {
        schema_version: SCHEMA_VERSION.to_string(),
        certificate_id: format!("cert-computation-{}", Uuid::new_v4()),
        run_hash: run.run_hash.clone(),
        dataset_receipt_hash: run.dataset_receipt_hash.clone(),
        environment_receipt_hash: run.environment_receipt_hash.clone(),
        code_commit,
        property_id: profile.property_id.clone(),
        checker: CHECKER.to_string(),
        checker_version: meta.checker_version.clone(),
        status,
        violations: if check.passed {
            vec![]
        } else {
            check.violations.clone()
        },
        result_artifact_hashes: run.result_artifact_hashes.clone(),
        counterexample_ref: if check.passed {
            None
        } else {
            counterexample_ref
        },
        source_repo: SOURCE_REPO.to_string(),
        source_commit: meta.source_commit.clone(),
        signature_or_digest: String::new(),
    };

    witness.signature_or_digest = crate::signing::digest_computation_witness(&witness);
    Ok(witness)
}

pub fn witness_to_json(witness: &ComputationWitnessV0) -> Result<String, serde_json::Error> {
    serde_json::to_string_pretty(witness)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::computation_check::check_computation_reproducibility;
    use crate::computation_receipt::{
        ComputationEmitInputs, ComputationRunReceiptV0, DatasetReceiptV0, EnvironmentReceiptV0,
        ResultArtifactV0,
    };
    use crate::metadata::CertifyEdgeMetadata;
    use crate::pcs_schema::validate_computation_witness_schema;
    use crate::property_profile::PropertyProfileRegistry;

    fn repo_root() -> std::path::PathBuf {
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    fn missing_commit_inputs() -> ComputationEmitInputs {
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
                code_commit: String::new(),
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
    fn rejected_witness_with_missing_code_commit_is_schema_valid() {
        let registry = PropertyProfileRegistry::from_certifyedge_root(&repo_root());
        let profile = registry
            .load("scientific_computation.reproducibility_v0")
            .unwrap();
        let inputs = missing_commit_inputs();
        let check = check_computation_reproducibility(&inputs);
        assert_eq!(check.failure_code.as_deref(), Some("missing_code_commit"));
        let meta = CertifyEdgeMetadata::dev_default();
        let witness = build_computation_witness(&inputs, &profile, &check, &meta, None).unwrap();
        assert_eq!(witness.status, "Rejected");
        assert_eq!(
            witness.code_commit,
            crate::source_commit::ZERO_SOURCE_COMMIT
        );
        let value = serde_json::to_value(&witness).unwrap();
        validate_computation_witness_schema(&value).unwrap();
    }
}
