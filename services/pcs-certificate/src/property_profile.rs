//! Property profile registry (`templates/profiles/<property_id>.json`).

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use jsonschema::Validator;
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::repair_hint::{
    certificate_failure, repair_property_template_mismatch, repair_unknown_property_id,
};
use crate::status_policy::{STATUS_CERTIFICATE_CHECKED, STATUS_REJECTED};

pub const ARTIFACT_TRACE_CERTIFICATE: &str = "TraceCertificate.v0";
pub const ARTIFACT_TOOL_USE_CERTIFICATE: &str = "ToolUseCertificate.v0";
pub const ARTIFACT_LABTRUST_TRACE: &str = "LabTrust.Trace.v0";
pub const ARTIFACT_TOOL_USE_TRACE: &str = "ToolUseTrace.v0";
pub const ARTIFACT_COMPUTATION_WITNESS: &str = "ComputationWitness.v0";
pub const ARTIFACT_COMPUTATION_RUN_RECEIPT: &str = "ComputationRunReceipt.v0";

/// Legacy alias for the default LabTrust output artifact.
pub const RUNTIME_TO_CERTIFICATE_OUTPUT_ARTIFACT: &str = ARTIFACT_TRACE_CERTIFICATE;

pub const SUPPORTED_OUTPUT_ARTIFACTS: &[&str] = &[
    ARTIFACT_TRACE_CERTIFICATE,
    ARTIFACT_TOOL_USE_CERTIFICATE,
    ARTIFACT_COMPUTATION_WITNESS,
];

static PROFILE_SCHEMA_VALIDATOR: OnceLock<Validator> = OnceLock::new();

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct ProfileFormalization {
    pub certificate_predicate: String,
    pub required_fields: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub admissible_status: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rejected_status: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stale_status: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct ProfileRepairHint {
    pub kind: String,
    pub command: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub responsible_component: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct PropertyProfile {
    pub property_id: String,
    pub template: String,
    pub input_trace_artifact: String,
    pub output_certificate_artifact: String,
    pub counterexample_artifact: String,
    pub valid_success_status: String,
    pub valid_failure_status: String,
    #[serde(
        rename = "release_mode_required_fields",
        alias = "required_release_fields"
    )]
    pub required_release_fields: Vec<String>,
    pub repair_hints: BTreeMap<String, ProfileRepairHint>,
    #[serde(default)]
    pub supporting_artifacts: Vec<String>,
    pub formalization: ProfileFormalization,
}

impl PropertyProfile {
    pub fn release_mode_required_fields(&self) -> &[String] {
        &self.required_release_fields
    }

    pub fn repair_hint_for(&self, failure_code: &str) -> Option<&ProfileRepairHint> {
        self.repair_hints.get(failure_code)
    }

    pub fn is_computation_profile(&self) -> bool {
        self.input_trace_artifact == ARTIFACT_COMPUTATION_RUN_RECEIPT
    }

    pub fn primary_hash_invariant_key(&self) -> &'static str {
        if self.is_computation_profile() {
            "run_hash"
        } else {
            "trace_hash"
        }
    }
}

/// Loaded property profile registry (directory of `<property_id>.json` files).
#[derive(Debug, Clone)]
pub struct PropertyProfileRegistry {
    pub registry_dir: PathBuf,
    pub certifyedge_root: PathBuf,
}

impl PropertyProfileRegistry {
    pub fn from_certifyedge_root(certifyedge_root: &Path) -> Self {
        Self {
            registry_dir: certifyedge_root.join("templates/profiles"),
            certifyedge_root: certifyedge_root.to_path_buf(),
        }
    }

    pub fn with_registry_dir(registry_dir: PathBuf, certifyedge_root: PathBuf) -> Self {
        Self {
            registry_dir,
            certifyedge_root,
        }
    }

    pub fn resolve(certifyedge_root: &Path, registry_override: Option<&Path>) -> Self {
        if let Some(dir) = registry_override {
            Self::with_registry_dir(dir.to_path_buf(), certifyedge_root.to_path_buf())
        } else {
            Self::from_certifyedge_root(certifyedge_root)
        }
    }

    pub fn profile_path(&self, property_id: &str) -> PathBuf {
        self.registry_dir.join(format!("{property_id}.json"))
    }

    pub fn load(&self, property_id: &str) -> Result<PropertyProfile, String> {
        let path = self.profile_path(property_id);
        let text = std::fs::read_to_string(&path).map_err(|e| {
            certificate_failure(
                "unknown_property_id",
                "HandoffManifest.v0",
                format!(
                    "unknown property_id {property_id:?}: profile not found ({}): {e}",
                    path.display()
                ),
                repair_unknown_property_id(property_id, &self.registry_dir.display().to_string()),
            )
        })?;
        let value: Value = serde_json::from_str(&text)
            .map_err(|e| format!("invalid property profile JSON: {e}"))?;
        validate_property_profile_value(&value)?;
        let profile: PropertyProfile = serde_json::from_value(value)
            .map_err(|e| format!("invalid property profile {}: {e}", path.display()))?;
        if profile.property_id != property_id {
            return Err(format!(
                "property profile {} declares property_id {}, expected {}",
                path.display(),
                profile.property_id,
                property_id
            ));
        }
        validate_runtime_to_certificate_profile(&profile)?;
        let template_path = self.certifyedge_root.join(&profile.template);
        if !template_path.is_file() {
            return Err(format!(
                "property profile {}: template not found: {}",
                property_id,
                template_path.display()
            ));
        }
        Ok(profile)
    }

    pub fn validate_file(&self, path: &Path) -> Result<PropertyProfile, String> {
        let text =
            std::fs::read_to_string(path).map_err(|e| format!("read {}: {e}", path.display()))?;
        let value: Value = serde_json::from_str(&text)
            .map_err(|e| format!("invalid property profile JSON: {e}"))?;
        validate_property_profile_value(&value)?;
        let profile: PropertyProfile = serde_json::from_value(value)
            .map_err(|e| format!("invalid property profile {}: {e}", path.display()))?;
        validate_runtime_to_certificate_profile(&profile)?;
        let template_path = self.certifyedge_root.join(&profile.template);
        if !template_path.is_file() {
            return Err(format!(
                "property profile {}: template not found: {}",
                profile.property_id,
                template_path.display()
            ));
        }
        Ok(profile)
    }

    pub fn list(&self) -> Result<Vec<String>, String> {
        let mut ids = Vec::new();
        let entries = std::fs::read_dir(&self.registry_dir)
            .map_err(|e| format!("read profiles dir {}: {e}", self.registry_dir.display()))?;
        for entry in entries {
            let entry = entry.map_err(|e| e.to_string())?;
            let path = entry.path();
            if path.extension().and_then(|s| s.to_str()) != Some("json") {
                continue;
            }
            if path.file_name().and_then(|s| s.to_str()) == Some("schema.json") {
                continue;
            }
            if let Some(stem) = path.file_stem().and_then(|s| s.to_str()) {
                ids.push(stem.to_string());
            }
        }
        ids.sort();
        Ok(ids)
    }

    pub fn explain_json(&self, property_id: &str) -> Result<String, String> {
        let profile = self.load(property_id)?;
        let path = self.profile_path(property_id);
        let mut value = profile_document_value(&profile);
        if let Some(obj) = value.as_object_mut() {
            obj.insert(
                "_registry".to_string(),
                Value::String(self.registry_dir.display().to_string()),
            );
            obj.insert(
                "_template_path".to_string(),
                Value::String(
                    self.certifyedge_root
                        .join(&profile.template)
                        .display()
                        .to_string(),
                ),
            );
            obj.insert(
                "_profile_path".to_string(),
                Value::String(path.display().to_string()),
            );
        }
        serde_json::to_string_pretty(&value).map_err(|e| e.to_string())
    }

    pub fn spec_path(&self, profile: &PropertyProfile) -> PathBuf {
        self.certifyedge_root.join(&profile.template)
    }

    pub fn assert_template_matches(
        &self,
        property_id: &str,
        spec_property_id: &str,
        template_path: &Path,
    ) -> Result<(), String> {
        if spec_property_id == property_id {
            Ok(())
        } else {
            Err(certificate_failure(
                "property_template_mismatch",
                &template_path.display().to_string(),
                format!(
                    "property template mismatch: handoff property_id {property_id}, spec template declares {spec_property_id}"
                ),
                repair_property_template_mismatch(
                    property_id,
                    &template_path.display().to_string(),
                ),
            ))
        }
    }
}

fn profile_schema_validator() -> &'static Validator {
    PROFILE_SCHEMA_VALIDATOR.get_or_init(|| {
        let schema: Value =
            serde_json::from_str(include_str!("../../../templates/profiles/schema.json"))
                .expect("templates/profiles/schema.json");
        Validator::new(&schema).expect("property profile schema compiles")
    })
}

/// Canonical profile document shape for CLI `profiles explain` (schema field names).
pub fn profile_document_value(profile: &PropertyProfile) -> Value {
    serde_json::json!({
        "property_id": profile.property_id,
        "template": profile.template,
        "input_trace_artifact": profile.input_trace_artifact,
        "output_certificate_artifact": profile.output_certificate_artifact,
        "counterexample_artifact": profile.counterexample_artifact,
        "valid_success_status": profile.valid_success_status,
        "valid_failure_status": profile.valid_failure_status,
        "release_mode_required_fields": profile.required_release_fields,
        "supporting_artifacts": profile.supporting_artifacts,
        "repair_hints": profile.repair_hints,
        "formalization": profile.formalization,
    })
}

pub fn validate_property_profile_value(value: &Value) -> Result<(), String> {
    let validator = profile_schema_validator();
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

const COMPUTATION_SUPPORTING_ARTIFACTS: &[&str] = &[
    "DatasetReceipt.v0",
    "EnvironmentReceipt.v0",
    "ResultArtifact.v0",
];

const COMPUTATION_REPAIR_HINT_CODES: &[&str] = &[
    "dataset_hash_mismatch",
    "environment_digest_mismatch",
    "result_hash_mismatch",
    "missing_code_commit",
    "nonzero_exit_code",
    "missing_result_artifact",
];

pub fn validate_runtime_to_certificate_profile(profile: &PropertyProfile) -> Result<(), String> {
    if !SUPPORTED_OUTPUT_ARTIFACTS.contains(&profile.output_certificate_artifact.as_str()) {
        return Err(format!(
            "property profile {}: unsupported output_certificate_artifact {} (supported: {:?})",
            profile.property_id, profile.output_certificate_artifact, SUPPORTED_OUTPUT_ARTIFACTS
        ));
    }
    if profile.valid_success_status != STATUS_CERTIFICATE_CHECKED {
        return Err(format!(
            "property profile {}: valid_success_status must be {STATUS_CERTIFICATE_CHECKED}, got {}",
            profile.property_id, profile.valid_success_status
        ));
    }
    if profile.valid_failure_status != STATUS_REJECTED {
        return Err(format!(
            "property profile {}: valid_failure_status must be {STATUS_REJECTED}, got {}",
            profile.property_id, profile.valid_failure_status
        ));
    }

    if profile.is_computation_profile() {
        if profile.output_certificate_artifact != ARTIFACT_COMPUTATION_WITNESS {
            return Err(format!(
                "property profile {}: ComputationRunReceipt.v0 input requires output {}",
                profile.property_id, ARTIFACT_COMPUTATION_WITNESS
            ));
        }
        for artifact in COMPUTATION_SUPPORTING_ARTIFACTS {
            if !profile.supporting_artifacts.iter().any(|a| a == artifact) {
                return Err(format!(
                    "property profile {}: supporting_artifacts must include {artifact}",
                    profile.property_id
                ));
            }
        }
        if !profile
            .required_release_fields
            .iter()
            .any(|f| f == "run_hash")
        {
            return Err(format!(
                "property profile {}: release_mode_required_fields must include run_hash",
                profile.property_id
            ));
        }
        for code in COMPUTATION_REPAIR_HINT_CODES {
            if !profile.repair_hints.contains_key(*code) {
                return Err(format!(
                    "property profile {}: repair_hints missing failure_code {code}",
                    profile.property_id
                ));
            }
        }
    } else if !profile.supporting_artifacts.is_empty() {
        return Err(format!(
            "property profile {}: supporting_artifacts is only valid for computation profiles",
            profile.property_id
        ));
    }

    crate::formal_facts::validate_profile_formalization(profile)?;

    Ok(())
}

pub fn load_property_profile(
    property_id: &str,
    certifyedge_root: &Path,
) -> Result<PropertyProfile, String> {
    PropertyProfileRegistry::from_certifyedge_root(certifyedge_root).load(property_id)
}

pub fn resolve_property_profile(
    property_id: &str,
    certifyedge_root: &Path,
) -> Result<PropertyProfile, String> {
    load_property_profile(property_id, certifyedge_root)
}

pub fn spec_path_for_property_id(
    property_id: &str,
    certifyedge_root: &Path,
) -> Result<PathBuf, String> {
    let registry = PropertyProfileRegistry::from_certifyedge_root(certifyedge_root);
    let profile = registry.load(property_id)?;
    Ok(registry.spec_path(&profile))
}

pub fn list_registered_property_ids(certifyedge_root: &Path) -> Result<Vec<String>, String> {
    PropertyProfileRegistry::from_certifyedge_root(certifyedge_root).list()
}

pub fn status_for_check(profile: &PropertyProfile, passed: bool) -> &str {
    if passed {
        &profile.valid_success_status
    } else {
        &profile.valid_failure_status
    }
}

pub fn validate_emitted_certificate_status(
    status: &str,
    profile: &PropertyProfile,
) -> Result<(), String> {
    if status == profile.valid_success_status || status == profile.valid_failure_status {
        Ok(())
    } else {
        Err(format!(
            "certificate status {status} is not valid for property profile {} \
             (expected {} or {})",
            profile.property_id, profile.valid_success_status, profile.valid_failure_status
        ))
    }
}

pub fn validate_certificate_status_transition_for_profile(
    from: &str,
    to: &str,
    profile: &PropertyProfile,
    release_mode: bool,
) -> Result<(), String> {
    validate_emitted_certificate_status(to, profile)?;
    crate::status_policy::validate_certificate_status_transition(from, to, release_mode)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn repo_root() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    #[test]
    fn test_property_profile_registry_loads_qc_release() {
        let root = repo_root();
        let registry = PropertyProfileRegistry::from_certifyedge_root(&root);
        let profile = registry
            .load("hospital_lab.qc_release")
            .expect("profile loads");
        assert_eq!(profile.input_trace_artifact, ARTIFACT_LABTRUST_TRACE);
        assert_eq!(
            profile.output_certificate_artifact,
            ARTIFACT_TRACE_CERTIFICATE
        );
        assert!(profile.repair_hints.contains_key("temporal_check_failed"));
        assert_eq!(
            profile.formalization.certificate_predicate,
            "CertificateMatchesRuntime"
        );
        assert!(registry
            .list()
            .unwrap()
            .contains(&"hospital_lab.qc_release".to_string()));
    }

    #[test]
    fn test_property_profile_registry_loads_agent_tool_use() {
        let root = repo_root();
        let registry = PropertyProfileRegistry::from_certifyedge_root(&root);
        let profile = registry
            .load("agent_tool_use.safety_v0")
            .expect("profile loads");
        assert_eq!(profile.input_trace_artifact, ARTIFACT_TOOL_USE_TRACE);
        assert_eq!(
            profile.output_certificate_artifact,
            ARTIFACT_TOOL_USE_CERTIFICATE
        );
        assert!(profile.repair_hints.contains_key("unauthorized_tool_call"));
    }

    #[test]
    fn computation_profile_loads_with_supporting_artifacts() {
        let root = repo_root();
        let registry = PropertyProfileRegistry::from_certifyedge_root(&root);
        let profile = registry
            .load("scientific_computation.reproducibility_v0")
            .expect("computation profile loads");
        assert!(profile.is_computation_profile());
        assert_eq!(
            profile.output_certificate_artifact,
            ARTIFACT_COMPUTATION_WITNESS
        );
        assert_eq!(profile.supporting_artifacts.len(), 3);
        assert!(profile.repair_hints.contains_key("dataset_hash_mismatch"));
        assert_eq!(
            profile.formalization.certificate_predicate,
            "ComputationWitnessBindsResults"
        );
    }

    #[test]
    fn unknown_property_id_is_rejected() {
        let root = repo_root();
        let err = PropertyProfileRegistry::from_certifyedge_root(&root)
            .load("hospital_lab.unknown_property")
            .unwrap_err();
        assert!(err.contains("unknown_property_id"));
    }

    #[test]
    fn computation_explain_json_includes_supporting_artifacts() {
        let root = repo_root();
        let registry = PropertyProfileRegistry::from_certifyedge_root(&root);
        let text = registry
            .explain_json("scientific_computation.reproducibility_v0")
            .unwrap();
        let value: Value = serde_json::from_str(&text).unwrap();
        let supporting = value["supporting_artifacts"].as_array().unwrap();
        assert_eq!(supporting.len(), 3);
        assert!(supporting
            .iter()
            .any(|v| v.as_str() == Some("DatasetReceipt.v0")));
    }

    #[test]
    fn explain_json_uses_release_mode_required_fields_key() {
        let root = repo_root();
        let registry = PropertyProfileRegistry::from_certifyedge_root(&root);
        let text = registry.explain_json("hospital_lab.qc_release").unwrap();
        let value: Value = serde_json::from_str(&text).unwrap();
        assert!(value.get("release_mode_required_fields").is_some());
        assert!(value.get("repair_hints").is_some());
    }

    #[test]
    fn profile_schema_rejects_extra_fields() {
        let root = repo_root();
        let registry = PropertyProfileRegistry::from_certifyedge_root(&root);
        let path = registry.profile_path("hospital_lab.qc_release");
        let mut value: Value =
            serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
        value
            .as_object_mut()
            .unwrap()
            .insert("extra".to_string(), Value::String("x".into()));
        assert!(validate_property_profile_value(&value).is_err());
    }
}
