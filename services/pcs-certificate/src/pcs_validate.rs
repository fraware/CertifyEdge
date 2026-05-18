use std::path::Path;
use std::process::Command;

use serde_json::Value;

use crate::pcs_schema::validate_trace_certificate_schema;

/// Validate JSON against vendored pcs-core TraceCertificate.v0 schema (in-process).
pub fn validate_certificate_json(value: &Value) -> Result<(), String> {
    validate_trace_certificate_schema(value)
}

/// Run `pcs validate <path>` when `required` is true (release-mode gates).
pub fn validate_with_pcs_cli(path: &Path, required: bool) -> Result<(), String> {
    if !required {
        return Ok(());
    }
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

/// Run `pcs registry check-artifact` in release mode; warn and skip when pcs is absent in dev.
pub fn registry_check_artifact(path: &Path, release_mode: bool) -> Result<(), String> {
    let output = match Command::new("pcs")
        .args(["registry", "check-artifact"])
        .arg(path)
        .output()
    {
        Ok(o) => o,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            if release_mode {
                return Err(
                    "pcs CLI not found; install pcs-core (pip install -e pcs-core/python)".into(),
                );
            }
            eprintln!("warning: pcs-core registry check skipped because pcs CLI unavailable");
            return Ok(());
        }
        Err(e) => return Err(format!("failed to run pcs registry check-artifact: {e}")),
    };

    if output.status.success() {
        return Ok(());
    }

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    Err(format!(
        "pcs registry check-artifact failed for {}:\n{stdout}{stderr}",
        path.display()
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    #[test]
    fn dev_registry_check_skips_when_pcs_missing() {
        let dir = tempfile::tempdir().expect("tempdir");
        let cert = dir.path().join("trace_certificate.json");
        std::fs::File::create(&cert)
            .and_then(|mut f| f.write_all(b"{}"))
            .expect("write cert stub");

        let old_path = std::env::var("PATH").ok();
        // Isolate PATH so `pcs` cannot be resolved.
        std::env::set_var("PATH", dir.path().as_os_str());

        let result = registry_check_artifact(&cert, false);
        if let Some(path) = old_path {
            std::env::set_var("PATH", path);
        } else {
            std::env::remove_var("PATH");
        }

        assert!(result.is_ok(), "dev mode should skip registry check when pcs missing");
    }
}

/// Full artifact validation: embedded pcs-core JSON Schema + optional `pcs` CLI cross-check.
pub fn validate_certificate_artifact(path: &Path, require_pcs_cli: bool) -> Result<(), String> {
    let text = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    let value: Value = serde_json::from_str(&text).map_err(|e| e.to_string())?;
    validate_certificate_json(&value)?;
    validate_with_pcs_cli(path, require_pcs_cli)
}
