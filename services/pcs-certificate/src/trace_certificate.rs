use chrono::Utc;
use labtrust_adapter::{Counterexample, PropertySpec, TemporalCheckResult};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TraceCertificateV0 {
    pub certificate_id: String,
    pub schema_version: String,
    pub trace_hash: String,
    pub spec_hash: String,
    pub property_id: String,
    pub checker: String,
    pub checker_version: String,
    pub status: String,
    pub counterexample_ref: Option<String>,
    pub created_at: String,
    pub producer: String,
    pub producer_version: String,
    pub source_repo: String,
    pub source_commit: String,
    pub signature_or_digest: String,
}

pub const CHECKER: &str = "CertifyEdge";
pub const PRODUCER: &str = "CertifyEdge";
pub const SCHEMA_VERSION: &str = "v0";
pub const SOURCE_REPO: &str = "https://github.com/fraware/CertifyEdge";

pub use crate::metadata::CertifyEdgeMetadata;
use crate::property_profile::{
    validate_certificate_status_transition_for_profile, PropertyProfile, PropertyProfileRegistry,
};
use crate::status_policy::STATUS_CERTIFICATE_PENDING;

#[derive(Debug, Clone)]
pub struct CertificateOutcome {
    pub certificate: TraceCertificateV0,
    pub counterexample: Option<Counterexample>,
}

fn resolve_profile_for_spec(
    spec: &PropertySpec,
    registry: &PropertyProfileRegistry,
) -> Result<PropertyProfile, String> {
    registry.load(spec.property_id.as_str())
}

pub fn resolve_profile_registry(
    certifyedge_root: &std::path::Path,
    registry_override: Option<&std::path::Path>,
) -> Result<PropertyProfileRegistry, String> {
    Ok(PropertyProfileRegistry::resolve(
        certifyedge_root,
        registry_override,
    ))
}

pub fn build_certificate(
    trace_hash: &str,
    spec: &PropertySpec,
    check: &TemporalCheckResult,
    meta: &CertifyEdgeMetadata,
    counterexample_path: Option<String>,
    registry: &PropertyProfileRegistry,
) -> Result<CertificateOutcome, String> {
    let profile = resolve_profile_for_spec(spec, registry)?;
    build_certificate_with_profile(trace_hash, spec, &profile, check, meta, counterexample_path)
}

pub fn build_certificate_with_profile(
    trace_hash: &str,
    spec: &PropertySpec,
    profile: &PropertyProfile,
    check: &TemporalCheckResult,
    meta: &CertifyEdgeMetadata,
    counterexample_path: Option<String>,
) -> Result<CertificateOutcome, String> {
    if spec.property_id.as_str() != profile.property_id {
        return Err(crate::repair_hint::certificate_failure(
            "property_template_mismatch",
            &profile.template,
            format!(
                "property template mismatch: spec declares {}, profile {}",
                spec.property_id.as_str(),
                profile.property_id
            ),
            crate::repair_hint::repair_property_template_mismatch(
                &profile.property_id,
                &profile.template,
            ),
        ));
    }

    let spec_hash = crate::hash::spec_hash(&spec.raw_text, spec.property_id.as_str());
    let property_id = profile.property_id.clone();

    let status = crate::property_profile::status_for_check(profile, check.passed).to_string();
    let counterexample_ref = if check.passed {
        None
    } else {
        counterexample_path.or_else(|| {
            check
                .counterexample
                .as_ref()
                .map(|_| "inline:counterexample.json".to_string())
        })
    };

    validate_certificate_status_transition_for_profile(
        STATUS_CERTIFICATE_PENDING,
        &status,
        profile,
        meta.release_mode,
    )?;

    let mut certificate = TraceCertificateV0 {
        certificate_id: format!("cert-trace-{}", Uuid::new_v4()),
        schema_version: SCHEMA_VERSION.to_string(),
        trace_hash: trace_hash.to_string(),
        spec_hash,
        property_id,
        checker: CHECKER.to_string(),
        checker_version: meta.checker_version.clone(),
        status,
        counterexample_ref,
        created_at: Utc::now().format("%Y-%m-%dT%H:%M:%SZ").to_string(),
        producer: PRODUCER.to_string(),
        producer_version: meta.producer_version.clone(),
        source_repo: SOURCE_REPO.to_string(),
        source_commit: meta.source_commit.clone(),
        signature_or_digest: String::new(),
    };

    certificate.signature_or_digest = crate::signing::digest_certificate(&certificate);

    Ok(CertificateOutcome {
        certificate,
        counterexample: check.counterexample.clone(),
    })
}

pub fn certificate_to_json(cert: &TraceCertificateV0) -> Result<String, serde_json::Error> {
    serde_json::to_string_pretty(cert)
}

pub fn certificate_from_json(text: &str) -> Result<TraceCertificateV0, serde_json::Error> {
    serde_json::from_str(text)
}

pub fn counterexample_to_json(cx: &Counterexample) -> Result<String, serde_json::Error> {
    serde_json::to_string_pretty(cx)
}

pub fn counterexample_from_json(text: &str) -> Result<Counterexample, serde_json::Error> {
    serde_json::from_str(text)
}

pub fn explain_counterexample(cx: &Counterexample) -> String {
    let sample = cx.sample_id.as_deref().unwrap_or("(unknown sample)");
    format!(
        "Property {} violated for sample {} at event {}.\nReason: {}\nExpected: {}\nFragment: {} event(s) attached.",
        cx.property_id,
        sample,
        cx.violating_event_id,
        cx.reason,
        cx.expected_precondition,
        cx.actual_trace_fragment.len()
    )
}

pub fn certificate_as_value(cert: &TraceCertificateV0) -> Value {
    serde_json::to_value(cert).expect("certificate serializes")
}
