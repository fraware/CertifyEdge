use std::path::{Path, PathBuf};
use std::process::Command;

pub const ZERO_SOURCE_COMMIT: &str = "0000000000000000000000000000000000000000";

/// How `source_commit` was chosen for the certificate (CLI diagnostics only).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceCommitResolution {
    Env,
    Git,
    LocalDev,
}

impl SourceCommitResolution {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Env => "env",
            Self::Git => "git",
            Self::LocalDev => "local_dev",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedSourceCommit {
    pub commit: String,
    pub resolution: SourceCommitResolution,
}

const PLACEHOLDER_COMMITS: &[&str] = &[
    "local-dev",
    ZERO_SOURCE_COMMIT,
    "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
    "cccccccccccccccccccccccccccccccccccccccc",
];

pub fn is_zero_source_commit(commit: &str) -> bool {
    let trimmed = commit.trim();
    trimmed.is_empty() || trimmed == ZERO_SOURCE_COMMIT || trimmed.chars().all(|c| c == '0')
}

pub fn is_placeholder_source_commit(commit: &str) -> bool {
    let trimmed = commit.trim();
    if trimmed.eq_ignore_ascii_case("local-dev") {
        return true;
    }
    if is_zero_source_commit(trimmed) {
        return true;
    }
    PLACEHOLDER_COMMITS.contains(&trimmed)
}

pub fn resolve_source_commit(release_mode: bool) -> Result<ResolvedSourceCommit, String> {
    if let Ok(value) = std::env::var("CERTIFYEDGE_SOURCE_COMMIT") {
        let commit = value.trim().to_string();
        if !commit.is_empty() {
            return finish_resolve(commit, SourceCommitResolution::Env, release_mode);
        }
    }

    if let Some(commit) = git_head_in_certifyedge_repo() {
        return finish_resolve(commit, SourceCommitResolution::Git, release_mode);
    }

    if release_mode {
        return Err(
            "release mode: set CERTIFYEDGE_SOURCE_COMMIT to a real CertifyEdge git SHA or run inside the CertifyEdge repository"
                .into(),
        );
    }

    Ok(ResolvedSourceCommit {
        commit: ZERO_SOURCE_COMMIT.to_string(),
        resolution: SourceCommitResolution::LocalDev,
    })
}

fn finish_resolve(
    commit: String,
    resolution: SourceCommitResolution,
    release_mode: bool,
) -> Result<ResolvedSourceCommit, String> {
    if commit.len() < 7 {
        return Err(format!(
            "source_commit too short ({commit}); need at least 7 characters"
        ));
    }

    if release_mode {
        if is_placeholder_source_commit(&commit) {
            return Err(format!(
                "release mode: rejected placeholder source_commit ({commit})"
            ));
        }
        verify_release_source_commit_not_foreign(&commit)?;
    } else if is_zero_source_commit(&commit) {
        if let Some(git_commit) = git_head_in_certifyedge_repo() {
            if !is_zero_source_commit(&git_commit) {
                return Ok(ResolvedSourceCommit {
                    commit: git_commit,
                    resolution: SourceCommitResolution::Git,
                });
            }
        }
        return Ok(ResolvedSourceCommit {
            commit: ZERO_SOURCE_COMMIT.to_string(),
            resolution: SourceCommitResolution::LocalDev,
        });
    }

    Ok(ResolvedSourceCommit { commit, resolution })
}

/// Reject commits that match LabTrust-Gym `HEAD` when both repos are discoverable.
fn verify_release_source_commit_not_foreign(commit: &str) -> Result<(), String> {
    let ce_root = match certifyedge_repo_root() {
        Some(root) => root,
        None => return Ok(()),
    };
    let ce_head = match git_rev_parse(&ce_root, "HEAD") {
        Some(head) => head,
        None => return Ok(()),
    };

    let Some(lt_root) = labtrust_gym_root() else {
        return Ok(());
    };
    let Some(lt_head) = git_rev_parse(&lt_root, "HEAD") else {
        return Ok(());
    };

    if commit == lt_head && commit != ce_head {
        return Err(format!(
            "release mode: source_commit matches LabTrust-Gym HEAD ({lt_head}); use CertifyEdge HEAD ({ce_head}) or another CertifyEdge commit"
        ));
    }

    Ok(())
}

pub fn certifyedge_repo_root() -> Option<PathBuf> {
    if let Ok(root) = std::env::var("CERTIFYEDGE_ROOT") {
        let path = PathBuf::from(root);
        if is_certifyedge_repo(&path) {
            return Some(path);
        }
    }

    let mut dir = std::env::current_dir().ok()?;
    loop {
        if is_certifyedge_repo(&dir) {
            return Some(dir);
        }
        if !dir.pop() {
            break;
        }
    }
    None
}

pub fn labtrust_gym_root() -> Option<PathBuf> {
    if let Ok(root) = std::env::var("LABTRUST_GYM_ROOT") {
        let path = PathBuf::from(root);
        if is_git_checkout(&path) {
            return Some(path);
        }
    }
    if let Ok(root) = std::env::var("LABTRUST_ROOT") {
        let path = PathBuf::from(root);
        if is_git_checkout(&path) {
            return Some(path);
        }
    }
    let candidate = certifyedge_repo_root()?.join("../LabTrust-Gym");
    is_git_checkout(&candidate).then_some(candidate)
}

fn is_certifyedge_repo(path: &Path) -> bool {
    path.join("Cargo.toml").is_file()
        && path.join("cli").is_dir()
        && path.join("services/pcs-certificate").is_dir()
}

fn is_git_checkout(path: &Path) -> bool {
    path.join(".git").exists()
}

fn git_head_in_certifyedge_repo() -> Option<String> {
    let root = certifyedge_repo_root()?;
    git_rev_parse(&root, "HEAD")
}

fn git_rev_parse(repo: &Path, rev: &str) -> Option<String> {
    let output = Command::new("git")
        .args(["-C"])
        .arg(repo)
        .args(["rev-parse", rev])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let commit = String::from_utf8_lossy(&output.stdout).trim().to_string();
    if commit.len() >= 7 && !is_placeholder_source_commit(&commit) {
        Some(commit)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_placeholder_commits() {
        assert!(is_placeholder_source_commit("local-dev"));
        assert!(is_placeholder_source_commit(ZERO_SOURCE_COMMIT));
        assert!(is_placeholder_source_commit(
            "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
        ));
        assert!(!is_placeholder_source_commit(
            "deadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
        ));
    }

    #[test]
    fn release_mode_rejects_placeholder_env() {
        std::env::set_var(
            "CERTIFYEDGE_SOURCE_COMMIT",
            "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
        );
        let err = resolve_source_commit(true).unwrap_err();
        assert!(err.contains("placeholder"));
        std::env::remove_var("CERTIFYEDGE_SOURCE_COMMIT");
    }
}
