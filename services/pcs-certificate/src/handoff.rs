//! PCS `HandoffManifest.v0` — consume runtime handoffs and emit certificate handoffs.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use chrono::Utc;
use labtrust_adapter::hash::pcs_digest;
use labtrust_adapter::LabTrustTrace;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use uuid::Uuid;

use crate::computation_receipt::{
    load_computation_inputs_from_json, ComputationEmitInputs, ARTIFACT_COMPUTATION_RUN_RECEIPT,
    ARTIFACT_DATASET_RECEIPT, ARTIFACT_ENVIRONMENT_RECEIPT, ARTIFACT_RESULT_ARTIFACT,
    COMPUTATION_RUN_RECEIPT_FILE, DATASET_RECEIPT_FILE, ENVIRONMENT_RECEIPT_FILE,
    RESULT_ARTIFACT_FILE,
};
use crate::emitted_certificate::{default_certificate_output_name, EmittedCertificate};
use crate::formal_facts::{
    admissible_for_release, ARTIFACT_CERTIFICATE_FORMAL_FACTS, DEFAULT_FORMAL_FACTS_FILENAME,
};
use crate::pcs_schema::validate_handoff_manifest_schema;
use crate::property_profile::{
    validate_runtime_to_certificate_profile, PropertyProfile, PropertyProfileRegistry,
    ARTIFACT_COMPUTATION_WITNESS, ARTIFACT_LABTRUST_TRACE, ARTIFACT_TOOL_USE_TRACE,
};
use crate::repair_hint::{
    certificate_failure, repair_fix_trace_hash, repair_regenerate_handoff, RepairHint,
};
use crate::source_commit::is_placeholder_source_commit;
use crate::tool_use_check::ToolUsePropertySpec;
use crate::tool_use_trace::parse_tool_use_trace_json;

pub const HANDOFF_KIND_RUNTIME_TO_CERTIFICATE: &str = "runtime_to_certificate";
pub const HANDOFF_KIND_CERTIFICATE_TO_BUNDLE: &str = "certificate_to_bundle";
pub const COMPONENT_CERTIFYEDGE: &str = "CertifyEdge";
pub const COMPONENT_LABTRUST: &str = "LabTrust-Gym";
pub const TRACE_ARTIFACT_NAME: &str = "trace.json";
pub const TRACE_CERTIFICATE_ARTIFACT_NAME: &str = "trace_certificate.json";
pub const ARTIFACT_TYPE_TRACE: &str = "Trace";
pub const ARTIFACT_TYPE_TRACE_CERTIFICATE: &str = "TraceCertificate.v0";
pub const ARTIFACT_TYPE_TOOL_USE_CERTIFICATE: &str = "ToolUseCertificate.v0";
pub const ARTIFACT_TYPE_TOOL_USE_TRACE: &str = "ToolUseTrace.v0";
pub const ARTIFACT_TYPE_COMPUTATION_WITNESS: &str = "ComputationWitness.v0";

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct HandoffArtifactRef {
    pub artifact_type: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sha256: Option<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct HandoffManifestV0 {
    pub schema_version: String,
    pub handoff_id: String,
    pub handoff_kind: String,
    pub from_component: String,
    pub to_component: String,
    pub created_at: String,
    pub source_repo: String,
    pub source_commit: String,
    pub input_artifacts: BTreeMap<String, HandoffArtifactRef>,
    pub expected_outputs: BTreeMap<String, HandoffArtifactRef>,
    pub invariants: BTreeMap<String, String>,
    pub status: String,
    pub signature_or_digest: String,
}

#[derive(Debug, Clone)]
pub struct HandoffEmitPlan {
    pub trace_path: PathBuf,
    pub spec_path: PathBuf,
    pub out_path: PathBuf,
    pub property_profile: PropertyProfile,
    pub computation_inputs: Option<ComputationEmitInputs>,
}

/// Raw SHA-256 of file bytes (`sha256:<hex>`), matching pcs-core `file_digest`.
pub fn file_digest(content: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    let digest = Sha256::digest(content);
    format!("sha256:{digest:x}")
}

fn io_error_path(context: &str, path: &Path, err: std::io::Error) -> String {
    if err.kind() == std::io::ErrorKind::NotFound {
        format!("{context}: file not found: {}", path.display())
    } else {
        format!("{context}: {}: {err}", path.display())
    }
}

pub fn load_handoff_manifest(path: &Path) -> Result<HandoffManifestV0, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| io_error_path("handoff manifest", path, e))?;
    let value: Value = serde_json::from_str(&text).map_err(|e| e.to_string())?;
    validate_handoff_manifest_schema(&value)?;
    verify_handoff_digest(&value)?;
    serde_json::from_value(value).map_err(|e| e.to_string())
}

/// Recompute `signature_or_digest` from manifest content and rewrite the file (benchmark fixtures).
pub fn refresh_handoff_digest_file(path: &Path) -> Result<(), String> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| io_error_path("handoff manifest", path, e))?;
    let value: Value = serde_json::from_str(&text).map_err(|e| e.to_string())?;
    validate_handoff_manifest_schema(&value)?;
    let mut manifest: HandoffManifestV0 =
        serde_json::from_value(value).map_err(|e| e.to_string())?;
    finalize_handoff_digest(&mut manifest);
    write_handoff_manifest(path, &manifest)
}

pub fn finalize_handoff_digest(manifest: &mut HandoffManifestV0) {
    let value = serde_json::to_value(&*manifest).expect("handoff serializes");
    manifest.signature_or_digest = pcs_digest(&value);
}

pub fn handoff_manifest_to_json(manifest: &HandoffManifestV0) -> Result<String, String> {
    let mut value = serde_json::to_value(manifest).map_err(|e| e.to_string())?;
    let digest = pcs_digest(&value);
    if let Some(obj) = value.as_object_mut() {
        obj.insert("signature_or_digest".to_string(), Value::String(digest));
    }
    serde_json::to_string_pretty(&value).map_err(|e| e.to_string())
}

pub fn verify_handoff_digest(value: &Value) -> Result<(), String> {
    let expected = value
        .get("signature_or_digest")
        .and_then(|v| v.as_str())
        .ok_or_else(|| "handoff missing signature_or_digest".to_string())?;
    let actual = pcs_digest(value);
    if actual != expected {
        return Err(format!(
            "handoff signature_or_digest mismatch (expected {expected}, got {actual})"
        ));
    }
    Ok(())
}

pub fn spec_path_for_property_id(
    property_id: &str,
    certifyedge_root: &Path,
) -> Result<PathBuf, String> {
    crate::property_profile::spec_path_for_property_id(property_id, certifyedge_root)
}

pub fn plan_emit_from_handoff(
    handoff_path: &Path,
    handoff: &HandoffManifestV0,
    registry: &PropertyProfileRegistry,
    spec_override: Option<&Path>,
    trace_override: Option<&Path>,
    out_override: Option<&Path>,
    release_mode: bool,
) -> Result<HandoffEmitPlan, String> {
    if handoff.schema_version != "v0" {
        return Err(format!(
            "unsupported handoff schema_version: {}",
            handoff.schema_version
        ));
    }
    if handoff.handoff_kind != HANDOFF_KIND_RUNTIME_TO_CERTIFICATE {
        return Err(format!(
            "handoff_kind must be {HANDOFF_KIND_RUNTIME_TO_CERTIFICATE}, got {}",
            handoff.handoff_kind
        ));
    }
    if handoff.to_component != COMPONENT_CERTIFYEDGE {
        return Err(format!(
            "to_component must be {COMPONENT_CERTIFYEDGE}, got {}",
            handoff.to_component
        ));
    }
    if release_mode && is_placeholder_source_commit(&handoff.source_commit) {
        return Err(format!(
            "release mode: handoff source_commit is placeholder ({})",
            handoff.source_commit
        ));
    }

    let property_id = handoff
        .invariants
        .get("property_id")
        .ok_or_else(|| "invariants must include property_id".to_string())?;
    let profile = registry.load(property_id)?;

    if profile.is_computation_profile() {
        return plan_emit_computation_from_handoff(
            handoff_path,
            handoff,
            registry,
            &profile,
            spec_override,
            out_override,
        );
    }

    let handoff_dir = handoff_path
        .parent()
        .ok_or_else(|| "handoff path has no parent directory".to_string())?;

    let trace_entry = handoff
        .input_artifacts
        .get(TRACE_ARTIFACT_NAME)
        .ok_or_else(|| format!("input_artifacts must include {TRACE_ARTIFACT_NAME}"))?;
    let trace_type_ok = trace_entry.artifact_type == profile.input_trace_artifact
        || (profile.input_trace_artifact == ARTIFACT_LABTRUST_TRACE
            && trace_entry.artifact_type == ARTIFACT_TYPE_TRACE)
        || (profile.input_trace_artifact == ARTIFACT_TOOL_USE_TRACE
            && trace_entry.artifact_type == ARTIFACT_TYPE_TOOL_USE_TRACE);
    if !trace_type_ok {
        return Err(certificate_failure(
            "input_trace_artifact_mismatch",
            TRACE_ARTIFACT_NAME,
            format!(
                "{TRACE_ARTIFACT_NAME} artifact_type must be {} (profile {})",
                profile.input_trace_artifact, profile.property_id
            ),
            repair_regenerate_handoff(
                &handoff_dir.join(TRACE_ARTIFACT_NAME).display().to_string(),
                &handoff_dir
                    .join("runtime_receipt.json")
                    .display()
                    .to_string(),
                &handoff_path.display().to_string(),
            ),
        ));
    }
    let expected_sha = trace_entry
        .sha256
        .as_deref()
        .ok_or_else(|| format!("input_artifacts[{TRACE_ARTIFACT_NAME}] missing sha256"))?;

    let expected_cert_name = default_certificate_output_name(&profile);
    let cert_output = handoff
        .expected_outputs
        .get(expected_cert_name)
        .or_else(|| {
            handoff
                .expected_outputs
                .get(TRACE_CERTIFICATE_ARTIFACT_NAME)
        })
        .ok_or_else(|| {
            format!(
                "expected_outputs must include {expected_cert_name} (profile {})",
                profile.property_id
            )
        })?;
    let cert_type_ok = cert_output.artifact_type == profile.output_certificate_artifact
        || (profile.output_certificate_artifact
            == crate::property_profile::ARTIFACT_TOOL_USE_CERTIFICATE
            && cert_output.artifact_type == ARTIFACT_TYPE_TOOL_USE_CERTIFICATE)
        || (profile.output_certificate_artifact
            == crate::property_profile::ARTIFACT_TRACE_CERTIFICATE
            && cert_output.artifact_type == ARTIFACT_TYPE_TRACE_CERTIFICATE)
        || (profile.output_certificate_artifact == ARTIFACT_COMPUTATION_WITNESS
            && cert_output.artifact_type == ARTIFACT_TYPE_COMPUTATION_WITNESS);
    if !cert_type_ok {
        return Err(certificate_failure(
            "output_certificate_artifact_mismatch",
            expected_cert_name,
            format!(
                "expected_outputs[{expected_cert_name}] artifact_type must be {} (profile {})",
                profile.output_certificate_artifact, profile.property_id
            ),
            repair_regenerate_handoff(
                &handoff_dir.join(TRACE_ARTIFACT_NAME).display().to_string(),
                &handoff_dir
                    .join("runtime_receipt.json")
                    .display()
                    .to_string(),
                &handoff_path.display().to_string(),
            ),
        ));
    }
    let hash_key = profile.primary_hash_invariant_key();
    let invariant_trace_hash = handoff
        .invariants
        .get(hash_key)
        .ok_or_else(|| format!("invariants must include {hash_key}").to_string())?;

    let trace_path = trace_override
        .map(Path::to_path_buf)
        .unwrap_or_else(|| handoff_dir.join(TRACE_ARTIFACT_NAME));
    let trace_bytes = std::fs::read(&trace_path)
        .map_err(|e| format!("read trace {}: {e}", trace_path.display()))?;
    let actual_file_digest = file_digest(&trace_bytes);
    if actual_file_digest != expected_sha {
        return Err(certificate_failure(
            "trace_file_digest_mismatch",
            TRACE_ARTIFACT_NAME,
            format!(
                "trace file hash mismatch: handoff expects {expected_sha}, file has {actual_file_digest}"
            ),
            repair_regenerate_handoff(
                &trace_path.display().to_string(),
                &handoff_dir
                    .join("runtime_receipt.json")
                    .display()
                    .to_string(),
                &handoff_path.display().to_string(),
            ),
        ));
    }

    let spec_path = spec_override
        .map(Path::to_path_buf)
        .unwrap_or_else(|| registry.spec_path(&profile));

    if profile.input_trace_artifact == ARTIFACT_TOOL_USE_TRACE {
        let text = String::from_utf8(trace_bytes).map_err(|e| e.to_string())?;
        let trace_value: Value = serde_json::from_str(&text).map_err(|e| e.to_string())?;
        crate::pcs_schema::validate_tool_use_trace_schema(&trace_value)?;
        let trace = parse_tool_use_trace_json(&text)?;
        if trace.trace_hash != *invariant_trace_hash {
            return Err(certificate_failure(
                "trace_hash_mismatch",
                TRACE_ARTIFACT_NAME,
                format!(
                    "trace_hash invariant mismatch: handoff {invariant_trace_hash}, trace {}",
                    trace.trace_hash
                ),
                repair_fix_trace_hash(&trace_path.display().to_string()),
            ));
        }
        if let Some(invariant_policy) = handoff.invariants.get("policy_hash") {
            let trace_policy = crate::tool_use_trace::policy_hash_from_trace(&trace);
            if invariant_policy != &trace_policy {
                return Err(certificate_failure(
                    "policy_hash_mismatch",
                    TRACE_ARTIFACT_NAME,
                    format!(
                        "policy_hash invariant mismatch: handoff {invariant_policy}, trace {trace_policy}"
                    ),
                    repair_fix_trace_hash(&trace_path.display().to_string()),
                ));
            }
        }
        let spec = ToolUsePropertySpec::load(&spec_path)
            .map_err(|e| format!("load spec {}: {e}", spec_path.display()))?;
        registry.assert_template_matches(property_id, &spec.property_id, &spec_path)?;
    } else {
        let trace: LabTrustTrace = labtrust_adapter::parse_and_validate_json(
            &String::from_utf8(trace_bytes).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
        if trace.trace_hash != *invariant_trace_hash {
            return Err(certificate_failure(
                "trace_hash_mismatch",
                TRACE_ARTIFACT_NAME,
                format!(
                    "trace_hash invariant mismatch: handoff {invariant_trace_hash}, trace {}",
                    trace.trace_hash
                ),
                repair_fix_trace_hash(&trace_path.display().to_string()),
            ));
        }
        let spec = labtrust_adapter::PropertySpec::load(&spec_path)
            .map_err(|e| format!("load spec {}: {e}", spec_path.display()))?;
        registry.assert_template_matches(property_id, spec.property_id.as_str(), &spec_path)?;
    }

    let out_path = out_override
        .map(Path::to_path_buf)
        .unwrap_or_else(|| handoff_dir.join(default_certificate_output_name(&profile)));

    Ok(HandoffEmitPlan {
        trace_path: trace_path.clone(),
        spec_path,
        out_path,
        property_profile: profile,
        computation_inputs: None,
    })
}

fn read_validated_handoff_input(
    handoff: &HandoffManifestV0,
    handoff_dir: &Path,
    file_name: &str,
    artifact_type: &str,
    handoff_path: &Path,
) -> Result<Vec<u8>, String> {
    let entry = handoff
        .input_artifacts
        .get(file_name)
        .ok_or_else(|| format!("input_artifacts must include {file_name} ({artifact_type})"))?;
    if entry.artifact_type != artifact_type {
        return Err(certificate_failure(
            "input_artifact_type_mismatch",
            file_name,
            format!(
                "input_artifacts[{file_name}] artifact_type must be {artifact_type}, got {}",
                entry.artifact_type
            ),
            repair_regenerate_handoff(
                &handoff_dir.join(file_name).display().to_string(),
                &handoff_dir
                    .join("runtime_receipt.json")
                    .display()
                    .to_string(),
                &handoff_path.display().to_string(),
            ),
        ));
    }
    let expected_sha = entry
        .sha256
        .as_deref()
        .ok_or_else(|| format!("input_artifacts[{file_name}] missing sha256"))?;
    let path = handoff_dir.join(file_name);
    let bytes = std::fs::read(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
    let actual = file_digest(&bytes);
    if actual != expected_sha {
        return Err(certificate_failure(
            "input_file_digest_mismatch",
            file_name,
            format!(
                "file hash mismatch for {file_name}: handoff expects {expected_sha}, file has {actual}"
            ),
            RepairHint {
                kind: "regenerate_handoff_inputs".into(),
                command: format!("re-emit handoff with sha256 digest for {file_name}"),
            },
        ));
    }
    Ok(bytes)
}

fn plan_emit_computation_from_handoff(
    handoff_path: &Path,
    handoff: &HandoffManifestV0,
    registry: &PropertyProfileRegistry,
    profile: &PropertyProfile,
    spec_override: Option<&Path>,
    out_override: Option<&Path>,
) -> Result<HandoffEmitPlan, String> {
    let handoff_dir = handoff_path
        .parent()
        .ok_or_else(|| "handoff path has no parent directory".to_string())?;

    let expected_cert_name = default_certificate_output_name(profile);
    let cert_output = handoff
        .expected_outputs
        .get(expected_cert_name)
        .ok_or_else(|| {
            format!(
                "expected_outputs must include {expected_cert_name} (profile {})",
                profile.property_id
            )
        })?;
    let cert_type_ok = cert_output.artifact_type == profile.output_certificate_artifact
        || cert_output.artifact_type == ARTIFACT_TYPE_COMPUTATION_WITNESS;
    if !cert_type_ok {
        return Err(certificate_failure(
            "output_certificate_artifact_mismatch",
            expected_cert_name,
            format!(
                "expected_outputs[{expected_cert_name}] artifact_type must be {} (profile {})",
                profile.output_certificate_artifact, profile.property_id
            ),
            repair_regenerate_handoff(
                &handoff_dir
                    .join(COMPUTATION_RUN_RECEIPT_FILE)
                    .display()
                    .to_string(),
                &handoff_dir
                    .join("runtime_receipt.json")
                    .display()
                    .to_string(),
                &handoff_path.display().to_string(),
            ),
        ));
    }

    let run_hash = handoff
        .invariants
        .get("run_hash")
        .ok_or_else(|| "invariants must include run_hash".to_string())?;

    let run_bytes = read_validated_handoff_input(
        handoff,
        handoff_dir,
        COMPUTATION_RUN_RECEIPT_FILE,
        ARTIFACT_COMPUTATION_RUN_RECEIPT,
        handoff_path,
    )?;
    let dataset_bytes = read_validated_handoff_input(
        handoff,
        handoff_dir,
        DATASET_RECEIPT_FILE,
        ARTIFACT_DATASET_RECEIPT,
        handoff_path,
    )?;
    let environment_bytes = read_validated_handoff_input(
        handoff,
        handoff_dir,
        ENVIRONMENT_RECEIPT_FILE,
        ARTIFACT_ENVIRONMENT_RECEIPT,
        handoff_path,
    )?;
    let result_bytes = read_validated_handoff_input(
        handoff,
        handoff_dir,
        RESULT_ARTIFACT_FILE,
        ARTIFACT_RESULT_ARTIFACT,
        handoff_path,
    )?;

    let inputs = load_computation_inputs_from_json(
        &String::from_utf8(run_bytes).map_err(|e| e.to_string())?,
        &String::from_utf8(dataset_bytes).map_err(|e| e.to_string())?,
        &String::from_utf8(environment_bytes).map_err(|e| e.to_string())?,
        &String::from_utf8(result_bytes).map_err(|e| e.to_string())?,
    )?;
    if inputs.run_receipt.run_hash != *run_hash {
        return Err(certificate_failure(
            "run_hash_mismatch",
            COMPUTATION_RUN_RECEIPT_FILE,
            format!(
                "run_hash invariant mismatch: handoff {run_hash}, receipt {}",
                inputs.run_receipt.run_hash
            ),
            repair_fix_trace_hash(
                &handoff_dir
                    .join(COMPUTATION_RUN_RECEIPT_FILE)
                    .display()
                    .to_string(),
            ),
        ));
    }

    let spec_path = spec_override
        .map(Path::to_path_buf)
        .unwrap_or_else(|| registry.spec_path(profile));
    let out_path = out_override
        .map(Path::to_path_buf)
        .unwrap_or_else(|| handoff_dir.join(expected_cert_name));
    let primary_path = handoff_dir.join(COMPUTATION_RUN_RECEIPT_FILE);

    Ok(HandoffEmitPlan {
        trace_path: primary_path.clone(),
        spec_path,
        out_path,
        property_profile: profile.clone(),
        computation_inputs: Some(inputs),
    })
}

fn build_outbound_invariants(
    cert: &EmittedCertificate,
    profile: &PropertyProfile,
    rejected: bool,
    counterexample_ref: Option<&str>,
    rejection: Option<(&str, Option<&str>, &RepairHint)>,
) -> BTreeMap<String, String> {
    let hash_key = profile.primary_hash_invariant_key();
    let primary_hash = cert.trace_hash().to_string();
    let admissible = admissible_for_release(profile, cert.status());
    let mut invariants = BTreeMap::from([
        (
            "certificate_id".to_string(),
            cert.certificate_id().to_string(),
        ),
        (hash_key.to_string(), primary_hash.clone()),
        ("status".to_string(), cert.status().to_string()),
        ("property_id".to_string(), cert.property_id().to_string()),
        (
            "formal_predicate".to_string(),
            profile.formalization.certificate_predicate.clone(),
        ),
        ("admissible_for_release".to_string(), admissible.to_string()),
    ]);
    if hash_key != "trace_hash" {
        invariants.insert("trace_hash".to_string(), primary_hash);
    }
    if rejected {
        invariants.insert("no_bundle_admissible".to_string(), "true".to_string());
        if let Some(cx_ref) = counterexample_ref.or(cert.counterexample_ref()) {
            invariants.insert("counterexample_ref".to_string(), cx_ref.to_string());
        }
        if let Some((failure_code, responsible_component, repair_hint)) = rejection {
            invariants.insert("failure_code".to_string(), failure_code.to_string());
            if let Some(component) = responsible_component {
                invariants.insert("responsible_component".to_string(), component.to_string());
            }
            invariants.insert("repair_hint_kind".to_string(), repair_hint.kind.clone());
            invariants.insert(
                "repair_hint_command".to_string(),
                repair_hint.command.clone(),
            );
        }
    }
    invariants
}

fn success_expected_outputs(profile: &PropertyProfile) -> BTreeMap<String, HandoffArtifactRef> {
    if profile.output_certificate_artifact == crate::property_profile::ARTIFACT_COMPUTATION_WITNESS
    {
        BTreeMap::from([(
            "computation_bundle.certified.json".to_string(),
            HandoffArtifactRef {
                artifact_type: "ComputationBundle.v0".to_string(),
                sha256: None,
            },
        )])
    } else if profile.output_certificate_artifact
        == crate::property_profile::ARTIFACT_TOOL_USE_CERTIFICATE
    {
        BTreeMap::from([(
            "tool_use_bundle.certified.json".to_string(),
            HandoffArtifactRef {
                artifact_type: "ToolUseBundle.v0".to_string(),
                sha256: None,
            },
        )])
    } else {
        BTreeMap::from([(
            "science_claim_bundle.certified.json".to_string(),
            HandoffArtifactRef {
                artifact_type: "ScienceClaimBundle.v0".to_string(),
                sha256: None,
            },
        )])
    }
}

pub fn build_certificate_to_bundle_handoff(
    cert: &EmittedCertificate,
    cert_path: &Path,
    registry: &PropertyProfileRegistry,
    counterexample_ref: Option<&str>,
    rejection_failure_code: Option<&str>,
    formal_facts_path: Option<&Path>,
) -> Result<HandoffManifestV0, String> {
    let cert_bytes = std::fs::read(cert_path)
        .map_err(|e| format!("read certificate {}: {e}", cert_path.display()))?;
    let cert_digest = file_digest(&cert_bytes);
    let cert_name = cert_path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or(TRACE_CERTIFICATE_ARTIFACT_NAME);

    let profile = registry.load(cert.property_id())?;
    validate_runtime_to_certificate_profile(&profile)?;
    if cert.status() != profile.valid_success_status
        && cert.status() != profile.valid_failure_status
    {
        return Err(format!(
            "certificate status {} is not valid for property profile {}",
            cert.status(),
            profile.property_id
        ));
    }
    let rejected = cert.status() == profile.valid_failure_status;
    let expected_outputs = if rejected {
        BTreeMap::new()
    } else {
        success_expected_outputs(&profile)
    };

    let rejection = if rejected {
        rejection_failure_code
            .and_then(|code| crate::repair_hint::rejection_repair_context(&profile, code))
    } else {
        None
    };

    let input_artifact_type = profile.output_certificate_artifact.clone();

    let mut input_artifacts = BTreeMap::from([(
        cert_name.to_string(),
        HandoffArtifactRef {
            artifact_type: input_artifact_type,
            sha256: Some(cert_digest),
        },
    )]);
    if let Some(facts_path) = formal_facts_path {
        let facts_bytes = std::fs::read(facts_path)
            .map_err(|e| format!("read formal facts {}: {e}", facts_path.display()))?;
        let facts_name = facts_path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or(DEFAULT_FORMAL_FACTS_FILENAME);
        input_artifacts.insert(
            facts_name.to_string(),
            HandoffArtifactRef {
                artifact_type: ARTIFACT_CERTIFICATE_FORMAL_FACTS.to_string(),
                sha256: Some(file_digest(&facts_bytes)),
            },
        );
    }

    Ok(HandoffManifestV0 {
        schema_version: "v0".to_string(),
        handoff_id: format!("handoff-certifyedge-{}", Uuid::new_v4()),
        handoff_kind: HANDOFF_KIND_CERTIFICATE_TO_BUNDLE.to_string(),
        from_component: COMPONENT_CERTIFYEDGE.to_string(),
        to_component: COMPONENT_LABTRUST.to_string(),
        created_at: Utc::now().format("%Y-%m-%dT%H:%M:%SZ").to_string(),
        source_repo: match cert {
            EmittedCertificate::Trace(c) => c.source_repo.clone(),
            EmittedCertificate::ToolUse(c) => c.source_repo.clone(),
            EmittedCertificate::Computation(c) => c.source_repo.clone(),
        },
        source_commit: cert.source_commit().to_string(),
        input_artifacts,
        expected_outputs,
        invariants: build_outbound_invariants(
            cert,
            &profile,
            rejected,
            counterexample_ref,
            rejection
                .as_ref()
                .map(|(code, responsible, hint)| (code.as_str(), responsible.as_deref(), hint)),
        ),
        status: "Validated".to_string(),
        signature_or_digest: String::new(),
    })
}

pub fn write_handoff_manifest(path: &Path, manifest: &HandoffManifestV0) -> Result<(), String> {
    let json = handoff_manifest_to_json(manifest)?;
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent).map_err(|e| e.to_string())?;
        }
    }
    std::fs::write(path, format!("{json}\n")).map_err(|e| e.to_string())
}

/// Validate handoff JSON against vendored schema; optional `pcs validate` when installed.
pub fn validate_handoff_artifact(path: &Path, require_pcs_cli: bool) -> Result<(), String> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| io_error_path("handoff manifest", path, e))?;
    let value: serde_json::Value = serde_json::from_str(&text).map_err(|e| e.to_string())?;
    validate_handoff_manifest_schema(&value)?;
    verify_handoff_digest(&value)?;
    crate::pcs_validate::validate_with_pcs_cli(path, require_pcs_cli)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::status_policy::STATUS_REJECTED;
    use crate::trace_certificate::TraceCertificateV0;
    #[test]
    fn file_digest_is_raw_bytes() {
        assert_eq!(
            file_digest(b"{}"),
            "sha256:44136fa355b3678a1146ad16f7e8649e94fb4fc21fe77e8310c060f61caaff8a"
        );
    }

    #[test]
    fn output_handoff_invariants_use_certificate_fields() {
        let cert = TraceCertificateV0 {
            certificate_id: "cert-trace-test".into(),
            schema_version: "v0".into(),
            trace_hash: "sha256:c3e8a3dc4ad86d533de1dfa4ae7fe2a338c2cff3c945404c96a75216524d58cd"
                .into(),
            spec_hash: "sha256:7c66dfcf640d382653d8ce7c2c700371d72ff0d6fb59156d411cf2aa9a7dfe5e"
                .into(),
            property_id: "hospital_lab.qc_release".into(),
            checker: "CertifyEdge".into(),
            checker_version: "0.1.0".into(),
            status: "CertificateChecked".into(),
            counterexample_ref: None,
            created_at: "2026-05-17T15:37:01Z".into(),
            producer: "CertifyEdge".into(),
            producer_version: "0.1.0".into(),
            source_repo: crate::trace_certificate::SOURCE_REPO.to_string(),
            source_commit: "cb6848001e2e60a484e04eba5ad6be3fe2e4eccc".into(),
            signature_or_digest:
                "sha256:34dec7d507119b599c2e2611bff0f984359a64d12cee2600901cc73537fd6f2b".into(),
        };
        let dir = std::env::temp_dir().join(format!("ce-handoff-{}", Uuid::new_v4()));
        std::fs::create_dir_all(&dir).unwrap();
        let cert_path = dir.join("trace_certificate.json");
        std::fs::write(&cert_path, r#"{"certificate_id":"cert-trace-test"}"#).unwrap();
        let registry = PropertyProfileRegistry::from_certifyedge_root(
            &PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../.."),
        );
        let certificate_id = cert.certificate_id.clone();
        let emitted = EmittedCertificate::Trace(cert);
        let handoff =
            build_certificate_to_bundle_handoff(&emitted, &cert_path, &registry, None, None, None)
                .unwrap();
        assert_eq!(handoff.handoff_kind, HANDOFF_KIND_CERTIFICATE_TO_BUNDLE);
        assert_eq!(handoff.invariants["certificate_id"], certificate_id);
        assert_eq!(handoff.invariants["status"], "CertificateChecked");
        assert_eq!(
            handoff.invariants["formal_predicate"],
            "CertificateMatchesRuntime"
        );
        assert_eq!(handoff.invariants["admissible_for_release"], "true");
    }

    #[test]
    fn certificate_to_bundle_handoff_hash_vector_is_stable() {
        let mut handoff = HandoffManifestV0 {
            schema_version: "v0".into(),
            handoff_id: "handoff-certifyedge-to-labtrust-hash-vector".into(),
            handoff_kind: HANDOFF_KIND_CERTIFICATE_TO_BUNDLE.into(),
            from_component: COMPONENT_CERTIFYEDGE.into(),
            to_component: COMPONENT_LABTRUST.into(),
            created_at: "2026-05-17T17:01:22Z".into(),
            source_repo: crate::trace_certificate::SOURCE_REPO.to_string(),
            source_commit: "cb6848001e2e60a484e04eba5ad6be3fe2e4eccc".into(),
            input_artifacts: BTreeMap::from([(
                TRACE_CERTIFICATE_ARTIFACT_NAME.into(),
                HandoffArtifactRef {
                    artifact_type: ARTIFACT_TYPE_TRACE_CERTIFICATE.into(),
                    sha256: Some(
                        "sha256:44136fa355b3678a1146ad16f7e8649e94fb4fc21fe77e8310c060f61caaff8a"
                            .into(),
                    ),
                },
            )]),
            expected_outputs: BTreeMap::from([(
                "science_claim_bundle.certified.json".into(),
                HandoffArtifactRef {
                    artifact_type: "ScienceClaimBundle.v0".into(),
                    sha256: None,
                },
            )]),
            invariants: BTreeMap::from([
                ("certificate_id".into(), "cert-trace-hash-vector".into()),
                (
                    "trace_hash".into(),
                    "sha256:c3e8a3dc4ad86d533de1dfa4ae7fe2a338c2cff3c945404c96a75216524d58cd"
                        .into(),
                ),
                ("status".into(), "CertificateChecked".into()),
            ]),
            status: "Validated".into(),
            signature_or_digest: String::new(),
        };
        finalize_handoff_digest(&mut handoff);
        let value = serde_json::to_value(&handoff).unwrap();
        let digest = pcs_digest(&value);
        let expected = include_str!(
            "../../../tests/fixtures/pcs-hash-vectors/HandoffManifest.certificate_to_bundle/digest.txt"
        )
        .trim();
        assert_eq!(digest, expected);
    }

    #[test]
    fn rejected_handoff_does_not_promise_certified_bundle() {
        let cert = TraceCertificateV0 {
            certificate_id: "cert-trace-rejected".into(),
            schema_version: "v0".into(),
            trace_hash: "sha256:c3e8a3dc4ad86d533de1dfa4ae7fe2a338c2cff3c945404c96a75216524d58cd"
                .into(),
            spec_hash: "sha256:7c66dfcf640d382653d8ce7c2c700371d72ff0d6fb59156d411cf2aa9a7dfe5e"
                .into(),
            property_id: "hospital_lab.qc_release".into(),
            checker: "CertifyEdge".into(),
            checker_version: "0.1.0".into(),
            status: STATUS_REJECTED.into(),
            counterexample_ref: Some("counterexample.json".into()),
            created_at: "2026-05-17T15:37:01Z".into(),
            producer: "CertifyEdge".into(),
            producer_version: "0.1.0".into(),
            source_repo: crate::trace_certificate::SOURCE_REPO.to_string(),
            source_commit: "cb6848001e2e60a484e04eba5ad6be3fe2e4eccc".into(),
            signature_or_digest:
                "sha256:34dec7d507119b599c2e2611bff0f984359a64d12cee2600901cc73537fd6f2b".into(),
        };
        let dir = std::env::temp_dir().join(format!("ce-handoff-reject-{}", Uuid::new_v4()));
        std::fs::create_dir_all(&dir).unwrap();
        let cert_path = dir.join("trace_certificate.json");
        std::fs::write(&cert_path, r#"{"certificate_id":"cert-trace-rejected"}"#).unwrap();
        let registry = PropertyProfileRegistry::from_certifyedge_root(
            &PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../.."),
        );
        let emitted = EmittedCertificate::Trace(cert);
        let handoff = build_certificate_to_bundle_handoff(
            &emitted,
            &cert_path,
            &registry,
            Some("counterexample.json"),
            Some("temporal_check_failed"),
            None,
        )
        .unwrap();
        assert_eq!(handoff.invariants["status"], STATUS_REJECTED);
        assert_eq!(handoff.invariants["admissible_for_release"], "false");
        assert_eq!(handoff.invariants["no_bundle_admissible"], "true");
        assert_eq!(handoff.invariants["failure_code"], "temporal_check_failed");
        assert_eq!(
            handoff.invariants["counterexample_ref"],
            "counterexample.json"
        );
        assert!(!handoff
            .expected_outputs
            .contains_key("science_claim_bundle.certified.json"));
        assert!(handoff.expected_outputs.is_empty());
    }

    #[test]
    fn plan_emit_accepts_tool_use_expected_certificate_output() {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let registry = PropertyProfileRegistry::from_certifyedge_root(&root);
        let work = std::env::temp_dir().join(format!("ce-tool-handoff-{}", Uuid::new_v4()));
        std::fs::create_dir_all(&work).unwrap();
        let trace_src = root.join("tests/tool_use/valid_tool_trace.json");
        let trace_bytes = std::fs::read(&trace_src).unwrap();
        let trace_digest = file_digest(&trace_bytes);
        let trace: Value = serde_json::from_slice(&trace_bytes).unwrap();
        let trace_hash = trace["trace_hash"].as_str().unwrap();
        std::fs::write(work.join("trace.json"), &trace_bytes).unwrap();

        let mut handoff = HandoffManifestV0 {
            schema_version: "v0".into(),
            handoff_id: "handoff-tool-use-plan".into(),
            handoff_kind: HANDOFF_KIND_RUNTIME_TO_CERTIFICATE.into(),
            from_component: COMPONENT_LABTRUST.into(),
            to_component: COMPONENT_CERTIFYEDGE.into(),
            created_at: "2026-05-17T17:01:22Z".into(),
            source_repo: "https://github.com/fraware/CertifyEdge".into(),
            source_commit: "abcdef0123456789abcdef0123456789abcdef01".into(),
            input_artifacts: BTreeMap::from([(
                TRACE_ARTIFACT_NAME.into(),
                HandoffArtifactRef {
                    artifact_type: ARTIFACT_TYPE_TOOL_USE_TRACE.into(),
                    sha256: Some(trace_digest),
                },
            )]),
            expected_outputs: BTreeMap::from([(
                "certificate.json".into(),
                HandoffArtifactRef {
                    artifact_type: ARTIFACT_TYPE_TOOL_USE_CERTIFICATE.into(),
                    sha256: None,
                },
            )]),
            invariants: BTreeMap::from([
                ("trace_hash".into(), trace_hash.into()),
                ("property_id".into(), "agent_tool_use.safety_v0".into()),
            ]),
            status: "Validated".into(),
            signature_or_digest: String::new(),
        };
        finalize_handoff_digest(&mut handoff);
        let handoff_path = work.join("runtime_handoff.json");
        write_handoff_manifest(&handoff_path, &handoff).unwrap();

        let plan =
            plan_emit_from_handoff(&handoff_path, &handoff, &registry, None, None, None, false)
                .unwrap();
        assert_eq!(
            plan.property_profile.property_id,
            "agent_tool_use.safety_v0"
        );
        assert!(plan.out_path.ends_with("certificate.json"));
    }
}
