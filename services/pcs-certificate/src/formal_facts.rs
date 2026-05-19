//! `CertificateFormalFacts.v0` — Lean-fact sources derived from emitted certificates.

use serde_json::{json, Value};

use crate::emitted_certificate::EmittedCertificate;
use crate::property_profile::{ProfileRepairHint, PropertyProfile};
use crate::status_policy::{STATUS_CERTIFICATE_CHECKED, STATUS_STALE};

pub const ARTIFACT_CERTIFICATE_FORMAL_FACTS: &str = "CertificateFormalFacts.v0";
pub const DEFAULT_FORMAL_FACTS_FILENAME: &str = "certificate_formal_facts.json";

pub const PREDICATE_CERTIFICATE_MATCHES_RUNTIME: &str = "CertificateMatchesRuntime";
pub const PREDICATE_COMPUTATION_WITNESS_BINDS_RESULTS: &str = "ComputationWitnessBindsResults";

/// Whether `status` is admissible for downstream bundle release per profile formalization.
pub fn admissible_for_release(profile: &PropertyProfile, status: &str) -> bool {
    let admissible_status = profile
        .formalization
        .admissible_status
        .as_deref()
        .unwrap_or(&profile.valid_success_status);
    status == admissible_status
}

/// Allowed `formalization.required_fields` names per certificate family.
pub fn allowed_formal_fields_for_profile(profile: &PropertyProfile) -> &'static [&'static str] {
    if profile.is_computation_profile() {
        &[
            "witness_id",
            "dataset_hash",
            "environment_hash",
            "run_receipt_hash",
            "result_hashes",
            "status",
        ]
    } else {
        &[
            "certificate_id",
            "trace_hash",
            "policy_hash",
            "status",
            "source_repo",
            "source_commit",
            "signature_or_digest",
        ]
    }
}

/// Validate profile `formalization` matches output artifact family and field names.
pub fn validate_profile_formalization(profile: &PropertyProfile) -> Result<(), String> {
    let predicate = profile.formalization.certificate_predicate.trim();
    if predicate.is_empty() {
        return Err(format!(
            "property profile {}: formalization.certificate_predicate must be non-empty",
            profile.property_id
        ));
    }
    if profile.formalization.required_fields.is_empty() {
        return Err(format!(
            "property profile {}: formalization.required_fields must be non-empty",
            profile.property_id
        ));
    }

    let expected_predicate = if profile.is_computation_profile() {
        PREDICATE_COMPUTATION_WITNESS_BINDS_RESULTS
    } else {
        PREDICATE_CERTIFICATE_MATCHES_RUNTIME
    };
    if predicate != expected_predicate {
        return Err(format!(
            "property profile {}: formalization.certificate_predicate must be {expected_predicate} \
             for output {}, got {predicate}",
            profile.property_id, profile.output_certificate_artifact
        ));
    }

    let allowed = allowed_formal_fields_for_profile(profile);
    for field in &profile.formalization.required_fields {
        if !allowed.contains(&field.as_str()) {
            return Err(format!(
                "property profile {}: formalization.required_fields contains unknown field \
                 `{field}` (allowed: {})",
                profile.property_id,
                allowed.join(", ")
            ));
        }
    }

    let admissible = profile
        .formalization
        .admissible_status
        .as_deref()
        .unwrap_or(&profile.valid_success_status);
    if admissible != profile.valid_success_status {
        return Err(format!(
            "property profile {}: formalization.admissible_status must match valid_success_status",
            profile.property_id
        ));
    }

    Ok(())
}

/// Build formalization facts JSON for pcs-core / Provability Fabric consumption.
pub fn build_certificate_formal_facts(
    cert: &EmittedCertificate,
    profile: &PropertyProfile,
    artifact_name: &str,
    failure_code: Option<&str>,
    repair_hint: Option<&ProfileRepairHint>,
) -> Result<Value, String> {
    let formal = &profile.formalization;
    let status = cert.status().to_string();
    let admissible_status = formal
        .admissible_status
        .as_deref()
        .unwrap_or(&profile.valid_success_status);
    let rejected_status = formal
        .rejected_status
        .as_deref()
        .unwrap_or(&profile.valid_failure_status);
    let stale_status = formal.stale_status.as_deref().unwrap_or(STATUS_STALE);

    let admissible_for_release = admissible_for_release(profile, &status);
    if status == rejected_status || status == stale_status {
        if admissible_for_release {
            return Err(format!(
                "formal facts: admissible_for_release cannot be true when status is {status}"
            ));
        }
    } else if status == admissible_status && !admissible_for_release {
        return Err(
            "formal facts: admissible_for_release must be true for admissible status".into(),
        );
    }

    let mut obj = serde_json::Map::new();
    obj.insert("schema_version".into(), json!("v0"));
    obj.insert("artifact".into(), json!(artifact_name));
    obj.insert(
        "certificate_id".into(),
        json!(cert.certificate_id().to_string()),
    );
    obj.insert(
        "certificate_type".into(),
        json!(cert.output_artifact_type()),
    );
    obj.insert(
        "formal_predicate".into(),
        json!(formal.certificate_predicate.clone()),
    );
    obj.insert("status".into(), json!(status.clone()));
    obj.insert(
        "admissible_for_release".into(),
        json!(admissible_for_release),
    );

    for field in &formal.required_fields {
        if let Some(value) = formal_field_value(cert, field) {
            obj.insert(field.clone(), value);
        }
    }

    if !admissible_for_release {
        if let Some(code) = failure_code {
            obj.insert("failure_code".into(), json!(code));
            obj.insert(
                "formal_implication".into(),
                json!(format!(
                    "{} cannot be established",
                    formal.certificate_predicate
                )),
            );
        }
        if let Some(hint) = repair_hint {
            let mut hint_obj = serde_json::Map::new();
            hint_obj.insert("kind".into(), json!(hint.kind));
            hint_obj.insert("command".into(), json!(hint.command));
            if let Some(component) = &hint.responsible_component {
                hint_obj.insert("responsible_component".into(), json!(component));
            }
            obj.insert("repair_hint".into(), Value::Object(hint_obj));
        }
    }

    let facts = Value::Object(obj);
    validate_formal_facts_consistency(&facts, cert, profile)?;
    Ok(facts)
}

fn formal_field_value(cert: &EmittedCertificate, field: &str) -> Option<Value> {
    match field {
        "certificate_id" | "witness_id" => Some(json!(cert.certificate_id())),
        "trace_hash" | "run_receipt_hash" => Some(json!(cert.trace_hash())),
        "status" => Some(json!(cert.status())),
        "source_repo" => cert_source_repo(cert).map(|s| json!(s)),
        "source_commit" => Some(json!(cert.source_commit())),
        "signature_or_digest" => cert_signature(cert).map(|s| json!(s)),
        "policy_hash" => cert_policy_hash(cert).map(|s| json!(s)),
        "dataset_hash" => cert_dataset_hash(cert).map(|s| json!(s)),
        "environment_hash" => cert_environment_hash(cert).map(|s| json!(s)),
        "result_hashes" => cert_result_hashes(cert),
        _ => None,
    }
}

fn cert_source_repo(cert: &EmittedCertificate) -> Option<&str> {
    match cert {
        EmittedCertificate::Trace(c) => Some(&c.source_repo),
        EmittedCertificate::ToolUse(c) => Some(&c.source_repo),
        EmittedCertificate::Computation(c) => Some(&c.source_repo),
    }
}

fn cert_signature(cert: &EmittedCertificate) -> Option<&str> {
    match cert {
        EmittedCertificate::Trace(c) => Some(&c.signature_or_digest),
        EmittedCertificate::ToolUse(c) => Some(&c.signature_or_digest),
        EmittedCertificate::Computation(c) => Some(&c.signature_or_digest),
    }
}

fn cert_policy_hash(cert: &EmittedCertificate) -> Option<&str> {
    match cert {
        EmittedCertificate::ToolUse(c) => Some(&c.policy_hash),
        _ => None,
    }
}

fn cert_dataset_hash(cert: &EmittedCertificate) -> Option<&str> {
    match cert {
        EmittedCertificate::Computation(c) => Some(&c.dataset_receipt_hash),
        _ => None,
    }
}

fn cert_environment_hash(cert: &EmittedCertificate) -> Option<&str> {
    match cert {
        EmittedCertificate::Computation(c) => Some(&c.environment_receipt_hash),
        _ => None,
    }
}

fn cert_result_hashes(cert: &EmittedCertificate) -> Option<Value> {
    match cert {
        EmittedCertificate::Computation(c) => Some(json!(c.result_artifact_hashes)),
        _ => None,
    }
}

/// Consistency between formal facts and the emitted certificate document.
pub fn validate_formal_facts_consistency(
    facts: &Value,
    cert: &EmittedCertificate,
    profile: &PropertyProfile,
) -> Result<(), String> {
    let obj = facts
        .as_object()
        .ok_or_else(|| "formal facts must be a JSON object".to_string())?;

    let cert_id = obj
        .get("certificate_id")
        .and_then(|v| v.as_str())
        .ok_or_else(|| "formal facts missing certificate_id".to_string())?;
    if cert_id != cert.certificate_id() {
        return Err(format!(
            "formal facts certificate_id mismatch: facts {cert_id}, certificate {}",
            cert.certificate_id()
        ));
    }

    let status = obj
        .get("status")
        .and_then(|v| v.as_str())
        .ok_or_else(|| "formal facts missing status".to_string())?;
    if status != cert.status() {
        return Err(format!(
            "formal facts status mismatch: facts {status}, certificate {}",
            cert.status()
        ));
    }

    if let Some(trace_hash) = obj.get("trace_hash").and_then(|v| v.as_str()) {
        if trace_hash != cert.trace_hash() {
            return Err(format!(
                "formal facts trace_hash mismatch: facts {trace_hash}, certificate {}",
                cert.trace_hash()
            ));
        }
    }

    if let Some(run_hash) = obj.get("run_receipt_hash").and_then(|v| v.as_str()) {
        if run_hash != cert.trace_hash() {
            return Err(format!(
                "formal facts run_receipt_hash mismatch: facts {run_hash}, certificate {}",
                cert.trace_hash()
            ));
        }
    }

    if let Some(witness_id) = obj.get("witness_id").and_then(|v| v.as_str()) {
        if witness_id != cert.certificate_id() {
            return Err("formal facts witness_id must equal certificate_id".into());
        }
    }

    let admissible = obj
        .get("admissible_for_release")
        .and_then(|v| v.as_bool())
        .ok_or_else(|| "formal facts missing admissible_for_release".to_string())?;

    let formal = &profile.formalization;
    let admissible_status = formal
        .admissible_status
        .as_deref()
        .unwrap_or(&profile.valid_success_status);
    let rejected_status = formal
        .rejected_status
        .as_deref()
        .unwrap_or(&profile.valid_failure_status);
    let stale_status = formal.stale_status.as_deref().unwrap_or(STATUS_STALE);

    if admissible && status != admissible_status {
        return Err(format!(
            "admissible_for_release true requires status {admissible_status}, got {status}"
        ));
    }
    if !admissible && status == admissible_status {
        return Err(format!(
            "admissible_for_release false incompatible with status {admissible_status}"
        ));
    }
    if (status == rejected_status || status == stale_status) && admissible {
        return Err(format!(
            "admissible_for_release must be false when status is {status}"
        ));
    }

    if status == STATUS_CERTIFICATE_CHECKED && !admissible {
        return Err("admissible_for_release must be true when status is CertificateChecked".into());
    }

    if (status == rejected_status || status == STATUS_STALE) && admissible {
        return Err(format!(
            "admissible_for_release must be false when status is {status}"
        ));
    }

    Ok(())
}

pub fn formal_facts_to_json_pretty(facts: &Value) -> Result<String, String> {
    serde_json::to_string_pretty(facts).map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::property_profile::{ProfileFormalization, PropertyProfile, PropertyProfileRegistry};
    use crate::trace_certificate::TraceCertificateV0;
    use std::collections::BTreeMap;
    fn repo_root() -> std::path::PathBuf {
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    fn trace_cert(status: &str) -> EmittedCertificate {
        EmittedCertificate::Trace(TraceCertificateV0 {
            certificate_id: "cert-trace-formal".into(),
            schema_version: "v0".into(),
            trace_hash: "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                .into(),
            spec_hash: "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
                .into(),
            property_id: "hospital_lab.qc_release".into(),
            checker: "CertifyEdge".into(),
            checker_version: "0.1.0".into(),
            status: status.into(),
            counterexample_ref: None,
            created_at: "2026-05-17T15:37:01Z".into(),
            producer: "CertifyEdge".into(),
            producer_version: "0.1.0".into(),
            source_repo: crate::trace_certificate::SOURCE_REPO.to_string(),
            source_commit: "abcdef0123456789abcdef0123456789abcdef01".into(),
            signature_or_digest:
                "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc".into(),
        })
    }

    #[test]
    fn validate_profile_formalization_rejects_wrong_predicate() {
        let profile = PropertyProfile {
            property_id: "scientific_computation.reproducibility_v0".into(),
            template: "templates/computation/result_hashes_match.stl".into(),
            input_trace_artifact: "ComputationRunReceipt.v0".into(),
            output_certificate_artifact: "ComputationWitness.v0".into(),
            counterexample_artifact: "ComputationCounterexample.v0".into(),
            valid_success_status: "CertificateChecked".into(),
            valid_failure_status: "Rejected".into(),
            required_release_fields: vec!["run_hash".into()],
            repair_hints: BTreeMap::new(),
            supporting_artifacts: vec!["DatasetReceipt.v0".into()],
            formalization: ProfileFormalization {
                certificate_predicate: PREDICATE_CERTIFICATE_MATCHES_RUNTIME.into(),
                required_fields: vec!["witness_id".into(), "status".into()],
                admissible_status: Some("CertificateChecked".into()),
                rejected_status: Some("Rejected".into()),
                stale_status: Some("Stale".into()),
            },
        };
        let err = validate_profile_formalization(&profile).unwrap_err();
        assert!(err.contains("ComputationWitnessBindsResults"));
    }

    #[test]
    fn checked_trace_formal_facts_are_admissible() {
        let registry = PropertyProfileRegistry::from_certifyedge_root(&repo_root());
        let profile = registry.load("hospital_lab.qc_release").unwrap();
        let cert = trace_cert("CertificateChecked");
        let facts = build_certificate_formal_facts(&cert, &profile, "certificate.json", None, None)
            .unwrap();
        assert_eq!(facts["admissible_for_release"], true);
        assert_eq!(facts["formal_predicate"], "CertificateMatchesRuntime");
        assert_eq!(
            facts["trace_hash"],
            "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
        );
    }

    #[test]
    fn rejected_trace_formal_facts_include_implication() {
        let registry = PropertyProfileRegistry::from_certifyedge_root(&repo_root());
        let profile = registry.load("hospital_lab.qc_release").unwrap();
        let cert = trace_cert("Rejected");
        let hint = crate::property_profile::ProfileRepairHint {
            kind: "fix_trace".into(),
            command: "fix".into(),
            responsible_component: None,
        };
        let facts = build_certificate_formal_facts(
            &cert,
            &profile,
            "certificate.json",
            Some("temporal_check_failed"),
            Some(&hint),
        )
        .unwrap();
        assert_eq!(facts["admissible_for_release"], false);
        assert!(facts["formal_implication"]
            .as_str()
            .unwrap()
            .contains("cannot be established"));
        assert_eq!(facts["failure_code"], "temporal_check_failed");
    }
}
