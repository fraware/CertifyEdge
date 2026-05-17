use crate::convert::TraceView;
use crate::labtrust_trace::TraceEvent;
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::path::Path;
use uuid::Uuid;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PropertyId {
    NoReleaseBeforeQc,
    AuthorizedReleaseOnly,
    QcRelease,
}

impl PropertyId {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::NoReleaseBeforeQc => "hospital_lab.no_release_before_qc",
            Self::AuthorizedReleaseOnly => "hospital_lab.authorized_release_only",
            Self::QcRelease => "hospital_lab.qc_release",
        }
    }

    pub fn from_spec_filename(path: &Path) -> Option<Self> {
        let stem = path.file_stem()?.to_str()?;
        match stem {
            "no_release_before_qc" => Some(Self::NoReleaseBeforeQc),
            "authorized_release_only" => Some(Self::AuthorizedReleaseOnly),
            "qc_release" => Some(Self::QcRelease),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct PropertySpec {
    pub property_id: PropertyId,
    pub allowed_release_roles: HashSet<String>,
    pub raw_text: String,
}

impl PropertySpec {
    pub fn load(path: &Path) -> Result<Self, String> {
        let raw_text = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
        let property_id = PropertyId::from_spec_filename(path)
            .ok_or_else(|| format!("unknown spec file: {}", path.display()))?;
        let allowed_release_roles = parse_allowed_release_roles(&raw_text);
        Ok(Self {
            property_id,
            allowed_release_roles,
            raw_text,
        })
    }
}

fn parse_allowed_release_roles(text: &str) -> HashSet<String> {
    let mut roles = HashSet::new();
    for line in text.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("allowed_release_roles:") {
            for role in rest.split(',').map(str::trim).filter(|s| !s.is_empty()) {
                roles.insert(role.to_string());
            }
        }
    }
    if roles.is_empty() {
        roles.insert("release_manager".to_string());
    }
    roles
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Counterexample {
    pub counterexample_id: String,
    pub property_id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sample_id: Option<String>,
    pub violating_event_id: String,
    pub reason: String,
    pub expected_precondition: String,
    pub actual_trace_fragment: Vec<serde_json::Value>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TemporalCheckResult {
    pub passed: bool,
    pub counterexample: Option<Counterexample>,
}

pub fn check_property(view: &TraceView, spec: &PropertySpec) -> TemporalCheckResult {
    for sample_id in view.sample_ids() {
        let events: Vec<&TraceEvent> = view.events_for_sample(&sample_id);
        if let Some(cx) = check_sample(&events, spec, &sample_id) {
            return TemporalCheckResult {
                passed: false,
                counterexample: Some(cx),
            };
        }
    }
    TemporalCheckResult {
        passed: true,
        counterexample: None,
    }
}

fn check_sample(
    events: &[&TraceEvent],
    spec: &PropertySpec,
    sample_id: &str,
) -> Option<Counterexample> {
    match spec.property_id {
        PropertyId::NoReleaseBeforeQc => check_no_release_before_qc(events, spec, sample_id),
        PropertyId::AuthorizedReleaseOnly => check_authorized_release_only(events, spec, sample_id),
        PropertyId::QcRelease => check_qc_release(events, spec, sample_id),
    }
}

fn successful_qc_indices(events: &[&TraceEvent]) -> Vec<usize> {
    events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.action == "perform_qc" && e.policy_decision == "allow" && e.reason_code == "ok"
        })
        .map(|(i, _)| i)
        .collect()
}

fn check_no_release_before_qc(
    events: &[&TraceEvent],
    spec: &PropertySpec,
    sample_id: &str,
) -> Option<Counterexample> {
    let qc_ok = successful_qc_indices(events);
    let first_qc = qc_ok.first().copied();

    for (idx, event) in events.iter().enumerate() {
        if event.action != "release_sample" {
            continue;
        }
        let release_before_qc = match first_qc {
            None => true,
            Some(qc_idx) => idx < qc_idx,
        };
        if release_before_qc {
            return Some(build_counterexample(
                spec,
                sample_id,
                event,
                "release_before_qc",
                "perform_qc with successful outcome must precede release_sample",
                fragment_around(events, idx),
            ));
        }
    }
    None
}

fn check_authorized_release_only(
    events: &[&TraceEvent],
    spec: &PropertySpec,
    sample_id: &str,
) -> Option<Counterexample> {
    for (idx, event) in events.iter().enumerate() {
        if event.action != "release_sample" {
            continue;
        }
        if !spec.allowed_release_roles.contains(&event.actor_role) {
            return Some(build_counterexample(
                spec,
                sample_id,
                event,
                "unauthorized_release",
                format!(
                    "release_sample requires actor_role in {:?}",
                    spec.allowed_release_roles
                ),
                fragment_around(events, idx),
            ));
        }
    }
    None
}

fn check_qc_release(
    events: &[&TraceEvent],
    spec: &PropertySpec,
    sample_id: &str,
) -> Option<Counterexample> {
    if let Some(cx) = check_event_order(events, spec, sample_id) {
        return Some(cx);
    }
    check_authorized_release_only(events, spec, sample_id)
}

fn check_event_order(
    events: &[&TraceEvent],
    spec: &PropertySpec,
    sample_id: &str,
) -> Option<Counterexample> {
    let order = [
        "accession_sample",
        "perform_qc",
        "record_analysis",
        "release_sample",
    ];
    let mut last_index: Option<usize> = None;
    let mut last_action = "";

    for (idx, event) in events.iter().enumerate() {
        let pos = order.iter().position(|a| *a == event.action.as_str());
        let Some(pos) = pos else {
            continue;
        };

        if let Some(last) = last_index {
            if pos < last {
                return Some(build_counterexample(
                    spec,
                    sample_id,
                    event,
                    "invalid_event_order",
                    format!("{last_action} must precede {}", event.action),
                    fragment_around(events, idx),
                ));
            }
        }
        last_index = Some(pos);
        last_action = event.action.as_str();
    }

    // Require successful QC before release in composite property
    if let Some(cx) = check_no_release_before_qc(events, spec, sample_id) {
        return Some(cx);
    }

    None
}

fn build_counterexample(
    spec: &PropertySpec,
    sample_id: &str,
    event: &TraceEvent,
    reason: &str,
    expected_precondition: impl Into<String>,
    fragment: Vec<serde_json::Value>,
) -> Counterexample {
    Counterexample {
        counterexample_id: format!("cx-{}", Uuid::new_v4()),
        property_id: spec.property_id.as_str().to_string(),
        sample_id: Some(sample_id.to_string()),
        violating_event_id: event.event_id.clone(),
        reason: reason.to_string(),
        expected_precondition: expected_precondition.into(),
        actual_trace_fragment: fragment,
    }
}

fn fragment_around(events: &[&TraceEvent], idx: usize) -> Vec<serde_json::Value> {
    let start = idx.saturating_sub(1);
    let end = (idx + 2).min(events.len());
    events[start..end]
        .iter()
        .map(|e| serde_json::to_value(e).expect("event json"))
        .collect()
}
