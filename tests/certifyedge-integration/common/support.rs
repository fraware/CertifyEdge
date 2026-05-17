//! Shared paths for Cargo and Bazel (`RUNFILES_DIR/_main`).

use assert_cmd::Command;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, MutexGuard};

/// Serialize tests that mutate `CERTIFYEDGE_SOURCE_COMMIT`.
pub static ENV_LOCK: Mutex<()> = Mutex::new(());

pub fn env_lock() -> MutexGuard<'static, ()> {
    ENV_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

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

/// Resolve `certifyedge` for integration tests (Cargo `cargo_bin` or Bazel `CERTIFYEDGE_BIN` / runfiles).
pub fn certifyedge_cmd() -> Command {
    if let Some(path) = resolve_certifyedge_bin() {
        return Command::new(path);
    }
    #[cfg(not(bazel))]
    {
        return Command::cargo_bin("certifyedge").expect(
            "certifyedge binary (run `cargo build -p certifyedge` before integration tests)",
        );
    }
    #[cfg(bazel)]
    {
        let hint = std::env::var("CERTIFYEDGE_BIN")
            .map(|p| format!("CERTIFYEDGE_BIN={p}"))
            .unwrap_or_else(|_| "CERTIFYEDGE_BIN unset".into());
        panic!(
            "certifyedge binary not found ({hint}); use `cargo test -p certifyedge-integration` on Windows or fix Bazel runfiles"
        );
    }
}

fn resolve_certifyedge_bin() -> Option<PathBuf> {
    for key in ["CERTIFYEDGE_BIN", "CARGO_BIN_EXE_certifyedge"] {
        if let Ok(path) = std::env::var(key) {
            if let Some(resolved) = resolve_bin_path(PathBuf::from(path)) {
                return Some(resolved);
            }
        }
    }
    bazel_certifyedge_bin()
}

fn resolve_bin_path(path: PathBuf) -> Option<PathBuf> {
    if path.is_file() {
        return Some(path);
    }
    if let Ok(canonical) = path.canonicalize() {
        if canonical.is_file() {
            return Some(canonical);
        }
    }
    if !path.is_relative() {
        return None;
    }
    for var in ["RUNFILES_DIR", "TEST_SRCDIR"] {
        let Ok(root) = std::env::var(var) else {
            continue;
        };
        for base in runfiles_roots(Path::new(&root)) {
            let candidate = base.join(&path);
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }
    None
}

fn bazel_certifyedge_bin() -> Option<PathBuf> {
    for var in ["RUNFILES_DIR", "TEST_SRCDIR"] {
        let Ok(root) = std::env::var(var) else {
            continue;
        };
        if let Some(path) = find_certifyedge_under(Path::new(&root)) {
            return Some(path);
        }
    }
    None
}

fn find_certifyedge_under(root: &Path) -> Option<PathBuf> {
    let names: [&str; 2] = ["cli/certifyedge.exe", "cli/certifyedge"];
    for base in runfiles_roots(root) {
        for name in names {
            let candidate = base.join(name);
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }
    None
}

fn runfiles_roots(root: &Path) -> Vec<PathBuf> {
    [
        root.join("_main"),
        root.join("CertifyEdge"),
        root.join("certifyedge"),
        root.to_path_buf(),
    ]
    .into_iter()
    .filter(|p| p.is_dir())
    .collect()
}
