//! Profile-selected certificate artifacts (`TraceCertificate.v0` | `ToolUseCertificate.v0` | `ComputationWitness.v0`).

use labtrust_adapter::{Counterexample, PropertySpec, TemporalCheckResult};
use serde_json::Value;

use crate::computation_check::{check_computation_reproducibility, ComputationCheckResult};
use crate::computation_receipt::{ComputationEmitInputs, ARTIFACT_COMPUTATION_RUN_RECEIPT};
use crate::computation_witness::{build_computation_witness, ComputationWitnessV0};
use crate::metadata::CertifyEdgeMetadata;
use crate::property_profile::{
    PropertyProfile, PropertyProfileRegistry, ARTIFACT_COMPUTATION_WITNESS,
    ARTIFACT_TOOL_USE_CERTIFICATE, ARTIFACT_TOOL_USE_TRACE, ARTIFACT_TRACE_CERTIFICATE,
};
use crate::repair_hint::emit_certificate_failure;
use crate::tool_use_certificate::{build_tool_use_certificate, ToolUseCertificateV0};
use crate::tool_use_check::{check_tool_use_property, ToolUseCheckResult, ToolUsePropertySpec};
use crate::tool_use_trace::ToolUseTraceV0;
use crate::trace_certificate::{build_certificate_with_profile, TraceCertificateV0};

#[derive(Debug, Clone)]
pub enum EmittedCertificate {
    Trace(TraceCertificateV0),
    ToolUse(ToolUseCertificateV0),
    Computation(ComputationWitnessV0),
}

#[derive(Debug, Clone)]
pub struct CertificateEmitOutcome {
    pub certificate: EmittedCertificate,
    pub labtrust_counterexample: Option<Counterexample>,
    pub tool_use_counterexample: Option<Value>,
    pub computation_counterexample: Option<Value>,
    pub failure_code: Option<String>,
}

impl EmittedCertificate {
    pub fn output_artifact_type(&self) -> &'static str {
        match self {
            Self::Trace(_) => ARTIFACT_TRACE_CERTIFICATE,
            Self::ToolUse(_) => ARTIFACT_TOOL_USE_CERTIFICATE,
            Self::Computation(_) => ARTIFACT_COMPUTATION_WITNESS,
        }
    }

    pub fn certificate_id(&self) -> &str {
        match self {
            Self::Trace(c) => &c.certificate_id,
            Self::ToolUse(c) => &c.certificate_id,
            Self::Computation(c) => &c.certificate_id,
        }
    }

    /// Primary receipt hash (`trace_hash` for LabTrust/tool-use, `run_hash` for computation).
    pub fn trace_hash(&self) -> &str {
        match self {
            Self::Trace(c) => &c.trace_hash,
            Self::ToolUse(c) => &c.trace_hash,
            Self::Computation(c) => &c.run_hash,
        }
    }

    pub fn property_id(&self) -> &str {
        match self {
            Self::Trace(c) => &c.property_id,
            Self::ToolUse(c) => &c.property_id,
            Self::Computation(c) => &c.property_id,
        }
    }

    pub fn status(&self) -> &str {
        match self {
            Self::Trace(c) => &c.status,
            Self::ToolUse(c) => &c.status,
            Self::Computation(c) => &c.status,
        }
    }

    pub fn source_commit(&self) -> &str {
        match self {
            Self::Trace(c) => &c.source_commit,
            Self::ToolUse(c) => &c.source_commit,
            Self::Computation(c) => &c.source_commit,
        }
    }

    pub fn counterexample_ref(&self) -> Option<&str> {
        match self {
            Self::Trace(c) => c.counterexample_ref.as_deref(),
            Self::ToolUse(c) => c.counterexample_ref.as_deref(),
            Self::Computation(c) => c.counterexample_ref.as_deref(),
        }
    }

    pub fn to_json_pretty(&self) -> Result<String, String> {
        match self {
            Self::Trace(c) => {
                crate::trace_certificate::certificate_to_json(c).map_err(|e| e.to_string())
            }
            Self::ToolUse(c) => {
                crate::tool_use_certificate::certificate_to_json(c).map_err(|e| e.to_string())
            }
            Self::Computation(c) => {
                crate::computation_witness::witness_to_json(c).map_err(|e| e.to_string())
            }
        }
    }

    pub fn as_value(&self) -> Value {
        match self {
            Self::Trace(c) => serde_json::to_value(c).expect("trace certificate serializes"),
            Self::ToolUse(c) => serde_json::to_value(c).expect("tool-use certificate serializes"),
            Self::Computation(c) => {
                serde_json::to_value(c).expect("computation witness serializes")
            }
        }
    }
}

pub fn emit_from_labtrust(
    trace_hash: &str,
    spec: &PropertySpec,
    profile: &PropertyProfile,
    check: &TemporalCheckResult,
    meta: &CertifyEdgeMetadata,
    counterexample_path: Option<String>,
) -> Result<CertificateEmitOutcome, String> {
    let outcome = build_certificate_with_profile(
        trace_hash,
        spec,
        profile,
        check,
        meta,
        counterexample_path,
    )?;
    Ok(CertificateEmitOutcome {
        certificate: EmittedCertificate::Trace(outcome.certificate),
        labtrust_counterexample: outcome.counterexample,
        tool_use_counterexample: None,
        computation_counterexample: None,
        failure_code: if check.passed {
            None
        } else {
            Some("temporal_check_failed".to_string())
        },
    })
}

pub fn emit_from_tool_use(
    trace: &ToolUseTraceV0,
    spec: &ToolUsePropertySpec,
    profile: &PropertyProfile,
    check: &ToolUseCheckResult,
    meta: &CertifyEdgeMetadata,
    counterexample_ref: Option<String>,
) -> Result<CertificateEmitOutcome, String> {
    if spec.property_id != profile.property_id {
        return Err(crate::repair_hint::certificate_failure(
            "property_template_mismatch",
            &profile.template,
            format!(
                "property template mismatch: spec declares {}, profile {}",
                spec.property_id, profile.property_id
            ),
            crate::repair_hint::repair_property_template_mismatch(
                &profile.property_id,
                &profile.template,
            ),
        ));
    }
    let certificate = build_tool_use_certificate(trace, profile, check, meta, counterexample_ref)?;
    Ok(CertificateEmitOutcome {
        certificate: EmittedCertificate::ToolUse(certificate),
        labtrust_counterexample: None,
        tool_use_counterexample: check.counterexample.clone(),
        computation_counterexample: None,
        failure_code: check.failure_code.clone(),
    })
}

pub fn emit_from_computation(
    inputs: &ComputationEmitInputs,
    profile: &PropertyProfile,
    check: &ComputationCheckResult,
    meta: &CertifyEdgeMetadata,
    counterexample_ref: Option<String>,
) -> Result<CertificateEmitOutcome, String> {
    let witness = build_computation_witness(inputs, profile, check, meta, counterexample_ref)?;
    Ok(CertificateEmitOutcome {
        certificate: EmittedCertificate::Computation(witness),
        labtrust_counterexample: None,
        tool_use_counterexample: None,
        computation_counterexample: check.counterexample.clone(),
        failure_code: check.failure_code.clone(),
    })
}

pub fn emit_certificate_for_profile(
    profile: &PropertyProfile,
    registry: &PropertyProfileRegistry,
    spec_path: &std::path::Path,
    primary_bytes: &[u8],
    meta: &CertifyEdgeMetadata,
    counterexample_path: Option<String>,
    computation_inputs: Option<ComputationEmitInputs>,
) -> Result<CertificateEmitOutcome, String> {
    if let Some(inputs) = computation_inputs {
        let check = check_computation_reproducibility(&inputs);
        return emit_from_computation(&inputs, profile, &check, meta, counterexample_path);
    }

    if profile.input_trace_artifact == ARTIFACT_COMPUTATION_RUN_RECEIPT {
        let parent = spec_path
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .ok_or_else(|| {
                "computation emit requires handoff directory with receipt JSON files".to_string()
            })?;
        let inputs = crate::computation_receipt::load_computation_inputs_from_dir(parent)?;
        let check = check_computation_reproducibility(&inputs);
        return emit_from_computation(&inputs, profile, &check, meta, counterexample_path);
    }

    match profile.input_trace_artifact.as_str() {
        ARTIFACT_TOOL_USE_TRACE => {
            let text = std::str::from_utf8(primary_bytes)
                .map_err(|e| format!("tool-use trace must be UTF-8 JSON: {e}"))?;
            let trace = crate::tool_use_trace::parse_tool_use_trace_json(text)?;
            let trace_value: Value =
                serde_json::from_str(text).map_err(|e| format!("tool-use trace JSON: {e}"))?;
            crate::pcs_schema::validate_tool_use_trace_schema(&trace_value)?;
            let spec = ToolUsePropertySpec::load(spec_path)?;
            let check = check_tool_use_property(&trace, &spec, meta.release_mode);
            emit_from_tool_use(&trace, &spec, profile, &check, meta, counterexample_path)
        }
        _ => {
            let text = std::str::from_utf8(primary_bytes)
                .map_err(|e| format!("trace must be UTF-8 JSON: {e}"))?;
            let trace =
                labtrust_adapter::parse_and_validate_json(text).map_err(|e| e.to_string())?;
            let trace_hash = trace.trace_hash.clone();
            let spec = labtrust_adapter::PropertySpec::load(spec_path)?;
            registry.assert_template_matches(
                &profile.property_id,
                spec.property_id.as_str(),
                spec_path,
            )?;
            let view = labtrust_adapter::TraceView::from(trace);
            let check = labtrust_adapter::check_property(&view, &spec);
            emit_from_labtrust(
                &trace_hash,
                &spec,
                profile,
                &check,
                meta,
                counterexample_path,
            )
        }
    }
}

pub fn emit_check_failure_stderr(
    profile: &PropertyProfile,
    failure_code: &str,
    artifact: &str,
    message: impl Into<String>,
) -> String {
    emit_certificate_failure(profile, failure_code, artifact, message)
}

pub const DEFAULT_CERTIFICATE_FILENAME: &str = "certificate.json";

pub fn default_certificate_output_name(profile: &PropertyProfile) -> &'static str {
    if profile.output_certificate_artifact == ARTIFACT_TOOL_USE_CERTIFICATE
        || profile.output_certificate_artifact == ARTIFACT_COMPUTATION_WITNESS
    {
        DEFAULT_CERTIFICATE_FILENAME
    } else {
        crate::handoff::TRACE_CERTIFICATE_ARTIFACT_NAME
    }
}

pub fn default_counterexample_filename(profile: &PropertyProfile) -> &'static str {
    if profile.is_computation_profile() {
        "computation_counterexample.json"
    } else {
        "counterexample.json"
    }
}
