//! Shared paths for Cargo and Bazel (`RUNFILES_DIR/_main`).

use std::path::{Path, PathBuf};

/// Repository root (contains `Cargo.toml` and `templates/`).
pub fn repo_root() -> PathBuf {
    if let Some(root) = bazel_workspace_root() {
        return root;
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn bazel_workspace_root() -> Option<PathBuf> {
    let runfiles = std::env::var("RUNFILES_DIR").ok()?;
    for sub in ["_main", "CertifyEdge", "certifyedge"] {
        let candidate = PathBuf::from(&runfiles).join(sub);
        if candidate.join("Cargo.toml").is_file() {
            return Some(candidate);
        }
    }
    None
}

pub fn spec_path(name: &str) -> PathBuf {
    repo_root().join("templates/hospital_lab").join(name)
}

pub fn labtrust_fixture(name: &str) -> PathBuf {
    repo_root().join("tests/labtrust").join(name)
}

pub fn ensure_parent(path: &Path) -> std::io::Result<()> {
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent)?;
        }
    }
    Ok(())
}
