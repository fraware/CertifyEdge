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

/// PCS v0.1 LabTrust release certificate (`certifyedge emit-pcs-certificate` output).
pub fn labtrust_release_certificate_fixture() -> PathBuf {
    repo_root()
        .join("tests/fixtures/labtrust")
        .join("trace_certificate.valid.json")
}

/// Pinned provenance for regenerating `trace_certificate.valid.json` (see `write_fixtures`).
pub const RELEASE_FIXTURE_SOURCE_COMMIT: &str =
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

/// Compare certificate fields that must be stable for a given trace, spec, and pinned `source_commit`.
pub fn assert_certificate_semantics_equal(
    emitted: &serde_json::Value,
    expected: &serde_json::Value,
) {
    for key in [
        "schema_version",
        "trace_hash",
        "spec_hash",
        "property_id",
        "checker",
        "checker_version",
        "status",
        "producer",
        "producer_version",
        "source_repo",
        "source_commit",
    ] {
        assert_eq!(
            emitted.get(key),
            expected.get(key),
            "certificate field {key}"
        );
    }
    assert!(emitted["counterexample_ref"].is_null());
    pcs_certificate::verify_certificate_document(
        &serde_json::to_string(emitted).unwrap(),
        Some(emitted["trace_hash"].as_str().unwrap()),
    )
    .expect("emitted certificate digest");
}

/// Validate emitted certificate: vendored pcs-core schema always; `pcs validate` when CLI is on PATH.
pub fn validate_certificate_against_pcs_core(path: &Path) {
    let text = std::fs::read_to_string(path).expect("read certificate");
    let value: serde_json::Value = serde_json::from_str(&text).expect("parse certificate JSON");
    pcs_certificate::validate_trace_certificate_schema(&value)
        .expect("TraceCertificate.v0 vendored schema (pcs-core)");
    if pcs_cli_available() {
        Command::new("pcs")
            .arg("validate")
            .arg(path)
            .assert()
            .success();
    }
}

/// `emit-pcs-certificate --release-mode` requires the pcs-core CLI (`pip install -e pcs-core/python`).
pub fn pcs_cli_available() -> bool {
    std::process::Command::new("pcs")
        .arg("--help")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
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
    for runfile_key in [
        "_main/cli/certifyedge.exe",
        "_main/cli/certifyedge",
        "cli/certifyedge.exe",
        "cli/certifyedge",
    ] {
        if let Some(path) = path_from_runfiles_manifest(runfile_key) {
            return Some(path);
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
    if path.is_relative() {
        let rel = path.to_string_lossy();
        for runfile_key in [rel.to_string(), format!("_main/{rel}")] {
            if let Some(abs) = path_from_runfiles_manifest(&runfile_key) {
                return Some(abs);
            }
        }
    } else {
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

/// Manifest-only runfiles (common on Windows): map `_main/cli/certifyedge.exe` → execroot path.
fn path_from_runfiles_manifest(runfile_key: &str) -> Option<PathBuf> {
    let manifest = runfiles_manifest_path()?;
    let content = std::fs::read_to_string(&manifest).ok()?;
    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let (key, value) = line.split_once(' ')?;
        if key == runfile_key {
            let path = PathBuf::from(value);
            if path.is_file() {
                return Some(path);
            }
        }
    }
    None
}

fn runfiles_manifest_path() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("RUNFILES_MANIFEST_FILE") {
        return Some(PathBuf::from(path));
    }
    let runfiles = std::env::var("RUNFILES_DIR").ok()?;
    let manifest = PathBuf::from(runfiles).join("MANIFEST");
    manifest.is_file().then_some(manifest)
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
