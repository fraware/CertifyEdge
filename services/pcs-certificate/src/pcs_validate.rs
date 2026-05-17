use std::path::Path;
use std::process::Command;

/// Run `pcs validate <path>` from pcs-core. When `required` is true, a missing `pcs` binary is an error.
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
                "warning: pcs CLI not found; skipped pcs-core schema validation for {}",
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
