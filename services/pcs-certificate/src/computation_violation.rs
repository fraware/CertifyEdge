//! Structured violations on `ComputationWitness.v0`.

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ComputationViolationV0 {
    pub failure_code: String,
    pub message: String,
}

impl ComputationViolationV0 {
    pub fn new(failure_code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            failure_code: failure_code.into(),
            message: message.into(),
        }
    }
}
