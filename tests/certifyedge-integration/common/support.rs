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

/// Atomic PCS release-run fixtures (`tests/fixtures/release-run/`).
pub fn release_run_dir() -> PathBuf {
    repo_root().join("tests/fixtures/release-run")
}

pub fn release_run_fixture(name: &str) -> PathBuf {
    release_run_dir().join(name)
}

pub fn load_json_path(path: &Path) -> serde_json::Value {
    serde_json::from_str(&std::fs::read_to_string(path).expect("read fixture JSON")).unwrap()
}

/// CLI-generated release certificate committed at `trace_certificate.json`.
pub fn labtrust_release_certificate_fixture() -> PathBuf {
    release_run_fixture("trace_certificate.json")
}

/// Negative / invalid traces only (`tests/fixtures/labtrust-release/`).
pub fn labtrust_release_dir() -> PathBuf {
    repo_root().join("tests/fixtures/labtrust-release")
}

pub fn labtrust_release_fixture(name: &str) -> PathBuf {
    labtrust_release_dir().join(name)
}

/// Runbook-relative spec path from repository root.
pub fn runbook_spec_qc_release() -> PathBuf {
    repo_root().join("templates/hospital_lab/qc_release.stl")
}

/// Runbook-relative trace path from repository root.
pub fn runbook_labtrust_release_trace() -> PathBuf {
    release_run_fixture("trace.json")
}

/// Committed release manifest (`tests/fixtures/release-run/RELEASE_FIXTURE_MANIFEST.json`).
pub fn release_fixture_manifest_path() -> PathBuf {
    release_run_fixture("RELEASE_FIXTURE_MANIFEST.json")
}

/// CertifyEdge `source_commit` recorded in the release manifest (must match `trace_certificate.json`).
pub fn release_manifest_certifyedge_commit() -> String {
    let value = load_json_path(&release_fixture_manifest_path());
    value["certifyedge_commit"]
        .as_str()
        .expect("certifyedge_commit")
        .to_string()
}

/// `git rev-parse HEAD` in the CertifyEdge repository root.
pub fn git_head_commit() -> Option<String> {
    let root = repo_root();
    let root_str = root.to_str()?;
    let output = std::process::Command::new("git")
        .args(["-C", root_str, "rev-parse", "HEAD"])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let commit = String::from_utf8_lossy(&output.stdout).trim().to_string();
    (commit.len() >= 7).then_some(commit)
}

/// Run `f` with `CERTIFYEDGE_SOURCE_COMMIT` set to `commit`, restoring the prior value afterward.
pub fn with_source_commit<R>(commit: &str, f: impl FnOnce() -> R) -> R {
    let _guard = env_lock();
    let previous = std::env::var("CERTIFYEDGE_SOURCE_COMMIT").ok();
    std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", commit);
    let result = f();
    if let Some(value) = previous {
        std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", value);
    } else {
        std::env::remove_var("CERTIFYEDGE_SOURCE_COMMIT");
    }
    result
}

/// Invalid-trace fixtures under `tests/fixtures/labtrust-release/`.
pub const LABTRUST_NEGATIVE_FIXTURES: &[&str] = &[
    "invalid_missing_qc_trace.json",
    "invalid_missing_qc_counterexample.json",
    "invalid_unauthorized_trace.json",
    "invalid_unauthorized_counterexample.json",
];

pub fn validate_labtrust_negative_fixture_tree() {
    for name in LABTRUST_NEGATIVE_FIXTURES {
        let path = labtrust_release_fixture(name);
        assert!(path.is_file(), "missing fixture {}", path.display());
    }
}

mod handoff;

pub use handoff::{
    assert_certificate_id_handoff_through_pf_chain,
    assert_certificate_id_handoff_trace_to_certified_bundle,
    assert_release_chain_certificate_and_trace_hash_propagation,
    assert_release_run_manifest_provenance,
    validate_release_run_fixture_tree,
};

pub fn validate_labtrust_release_fixture_tree() {
    validate_release_run_fixture_tree();
    validate_labtrust_negative_fixture_tree();
}

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
