use std::path::Path;
use std::process::Command;

use serde_json::Value;

use crate::pcs_schema::validate_trace_certificate_schema;

/// Validate JSON against vendored pcs-core TraceCertificate.v0 schema (in-process).
pub fn validate_certificate_json(value: &Value) -> Result<(), String> {
    validate_trace_certificate_schema(value)
}

/// Run `pcs validate <path>` when the pcs-core CLI is installed.
pub fn validate_with_pcs_cli(path: &Path, required: bool) -> Result<(), String> {
    let output = match Command::new("pcs").arg("validate").arg(path).output() {
        Ok(o) => o,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            if required {
                return Err(
                    "pcs CLI not found; install pcs-core (pip install -e pcs-core/python)".into(),
                );
            }
            eprintln!(
                "warning: pcs CLI not found; skipped external pcs validate for {}",
                path.display()
            );
            return Ok(());
        }
        Err(e) => return Err(format!("failed to run pcs validate: {e}")),
    };

    if output.status.success() {
        return Ok(());
    }

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    Err(format!(
        "pcs validate failed for {}:\n{stdout}{stderr}",
        path.display()
    ))
}

/// Full artifact validation: embedded pcs-core JSON Schema + optional `pcs` CLI cross-check.
pub fn validate_certificate_artifact(path: &Path, require_pcs_cli: bool) -> Result<(), String> {
    let text = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    let value: Value = serde_json::from_str(&text).map_err(|e| e.to_string())?;
    validate_certificate_json(&value)?;
    validate_with_pcs_cli(path, require_pcs_cli)
}
