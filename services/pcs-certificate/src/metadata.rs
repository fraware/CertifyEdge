use std::process::Command;

pub const ZERO_SOURCE_COMMIT: &str = "0000000000000000000000000000000000000000";

#[derive(Debug, Clone)]
pub struct CertifyEdgeMetadata {
    pub checker_version: String,
    pub producer_version: String,
    pub source_commit: String,
}

impl CertifyEdgeMetadata {
    /// Resolve producer metadata. In release mode, `source_commit` must be a real git SHA
    /// (from `CERTIFYEDGE_SOURCE_COMMIT` or `git rev-parse HEAD`), never the zero placeholder.
    pub fn resolve(release_mode: bool) -> Result<Self, String> {
        let source_commit = resolve_source_commit(release_mode)?;
        Ok(Self {
            checker_version: env!("CARGO_PKG_VERSION").to_string(),
            producer_version: env!("CARGO_PKG_VERSION").to_string(),
            source_commit,
        })
    }

    pub fn dev_default() -> Self {
        Self::resolve(false).unwrap_or_else(|_| Self {
            checker_version: env!("CARGO_PKG_VERSION").to_string(),
            producer_version: env!("CARGO_PKG_VERSION").to_string(),
            source_commit: ZERO_SOURCE_COMMIT.to_string(),
        })
    }
}

pub fn is_zero_source_commit(commit: &str) -> bool {
    let trimmed = commit.trim();
    trimmed.is_empty()
        || trimmed == ZERO_SOURCE_COMMIT
        || trimmed.chars().all(|c| c == '0')
}

fn resolve_source_commit(release_mode: bool) -> Result<String, String> {
    if let Ok(value) = std::env::var("CERTIFYEDGE_SOURCE_COMMIT") {
        let commit = value.trim().to_string();
        if !is_zero_source_commit(&commit) {
            if commit.len() < 7 {
                return Err(format!(
                    "CERTIFYEDGE_SOURCE_COMMIT too short ({commit}); need at least 7 characters"
                ));
            }
            return Ok(commit);
        }
    }

    if let Some(commit) = git_head_commit() {
        if !is_zero_source_commit(&commit) {
            return Ok(commit);
        }
    }

    if release_mode {
        return Err(
            "could not resolve source_commit: set CERTIFYEDGE_SOURCE_COMMIT or run inside a git repo"
                .into(),
        );
    }

    Ok(ZERO_SOURCE_COMMIT.to_string())
}

fn git_head_commit() -> Option<String> {
    let output = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let commit = String::from_utf8_lossy(&output.stdout).trim().to_string();
    if commit.len() >= 7 {
        Some(commit)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_zero_commit() {
        assert!(is_zero_source_commit(ZERO_SOURCE_COMMIT));
        assert!(is_zero_source_commit("0000000"));
    }

    #[test]
    fn release_mode_never_returns_placeholder_commit() {
        std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", ZERO_SOURCE_COMMIT);
        let meta = CertifyEdgeMetadata::resolve(true).unwrap();
        assert!(!is_zero_source_commit(&meta.source_commit));
        std::env::remove_var("CERTIFYEDGE_SOURCE_COMMIT");
    }
}
