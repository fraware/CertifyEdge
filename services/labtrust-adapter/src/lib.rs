//! LabTrust `trace.json` adapter: parse, validate schema and hash chain, compute trace digests.

pub mod convert;
pub mod hash;
pub mod labtrust_trace;
pub mod temporal;
pub mod validate;
pub mod workflow_sim;

pub use convert::TraceView;
pub use labtrust_trace::{LabTrustTrace, TraceEvent};
pub use temporal::{check_property, Counterexample, PropertyId, PropertySpec, TemporalCheckResult};
pub use validate::{parse_and_validate_json, validate_trace, TraceValidationError};
