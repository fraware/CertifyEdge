use crate::labtrust_trace::{LabTrustTrace, TraceEvent};
use std::collections::HashMap;

/// Normalized trace view for temporal checking.
#[derive(Debug, Clone)]
pub struct TraceView {
    pub run_id: String,
    pub sample_id: String,
    pub events: Vec<TraceEvent>,
}

impl From<LabTrustTrace> for TraceView {
    fn from(trace: LabTrustTrace) -> Self {
        Self {
            run_id: trace.run_id,
            sample_id: trace.sample_id,
            events: trace.events,
        }
    }
}

impl TraceView {
    pub fn events_for_sample(&self, sample_id: &str) -> Vec<&TraceEvent> {
        self.events
            .iter()
            .filter(|e| e.sample_id == sample_id)
            .collect()
    }

    pub fn sample_ids(&self) -> Vec<String> {
        let mut ids: Vec<String> = self.events.iter().map(|e| e.sample_id.clone()).collect();
        ids.sort();
        ids.dedup();
        ids
    }

    pub fn index_by_action<'a>(
        &self,
        events: &'a [TraceEvent],
    ) -> HashMap<&'a str, Vec<&'a TraceEvent>> {
        let mut map: HashMap<&str, Vec<&TraceEvent>> = HashMap::new();
        for event in events {
            map.entry(event.action.as_str()).or_default().push(event);
        }
        map
    }
}
