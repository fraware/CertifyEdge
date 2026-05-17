//! Regenerate LabTrust traces and the release certificate fixture.
//!
//! ```bash
//! cargo build -p certifyedge
//! cargo test -p certifyedge-integration write_fixtures -- --ignored --nocapture
//! ```

use std::process::Command;

use labtrust_adapter::{
    check_property,
    workflow_sim::{run_workflow, WorkflowStep},
    PropertySpec, TraceView,
};
use pcs_certificate::{build_certificate, counterexample_to_json, CertifyEdgeMetadata};
use serde_json::to_string_pretty;
use std::path::PathBuf;

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

const RELEASE_FIXTURE_SOURCE_COMMIT: &str =
    "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";

fn certifyedge_bin() -> PathBuf {
    if let Ok(path) = std::env::var("CARGO_BIN_EXE_certifyedge") {
        return PathBuf::from(path);
    }
    let root = repo_root();
    for name in ["certifyedge.exe", "certifyedge"] {
        let candidate = root.join("target/debug").join(name);
        if candidate.is_file() {
            return candidate;
        }
    }
    panic!("certifyedge binary not found; run `cargo build -p certifyedge` first");
}

fn emit_release_certificate_fixture() {
    let out_dir = repo_root().join("tests/fixtures/labtrust");
    std::fs::create_dir_all(&out_dir).unwrap();
    let out = out_dir.join("trace_certificate.valid.json");
    let spec = repo_root().join("templates/hospital_lab/qc_release.stl");
    let trace = repo_root().join("tests/labtrust/valid_trace.json");

    std::env::set_var("CERTIFYEDGE_SOURCE_COMMIT", RELEASE_FIXTURE_SOURCE_COMMIT);
    let status = Command::new(certifyedge_bin())
        .args([
            "emit-pcs-certificate",
            "--spec",
            spec.to_str().unwrap(),
            "--trace",
            trace.to_str().unwrap(),
            "--out",
            out.to_str().unwrap(),
        ])
        .status()
        .expect("spawn certifyedge emit-pcs-certificate");
    std::env::remove_var("CERTIFYEDGE_SOURCE_COMMIT");
    assert!(
        status.success(),
        "certifyedge emit-pcs-certificate failed for release fixture"
    );
    println!("wrote release certificate {}", out.display());
}

fn step(action: &str, actor_id: &str, role: &str, ts: &str) -> WorkflowStep {
    WorkflowStep {
        action: action.into(),
        actor_id: actor_id.into(),
        actor_role: role.into(),
        timestamp: ts.into(),
    }
}

#[test]
#[ignore]
fn write_fixtures() {
    let out_dir = repo_root().join("tests/labtrust");
    std::fs::create_dir_all(&out_dir).unwrap();

    let valid = run_workflow(
        "qc-release",
        "PCS-SAMPLE-001",
        &[
            step(
                "accession_sample",
                "acc-tech-01",
                "accession_tech",
                "2026-01-15T08:00:00+00:00",
            ),
            step(
                "perform_qc",
                "qc-tech-01",
                "qc_tech",
                "2026-01-15T09:00:00+00:00",
            ),
            step(
                "record_analysis",
                "analyst-01",
                "analyst",
                "2026-01-15T10:00:00+00:00",
            ),
            step(
                "release_sample",
                "rel-mgr-01",
                "release_manager",
                "2026-01-15T11:00:00+00:00",
            ),
        ],
    );
    let missing_qc = run_workflow(
        "qc-release-invalid-missing-qc",
        "PCS-SAMPLE-002",
        &[
            step(
                "accession_sample",
                "acc-tech-01",
                "accession_tech",
                "2026-01-15T08:00:00+00:00",
            ),
            step(
                "release_sample",
                "rel-mgr-01",
                "release_manager",
                "2026-01-15T10:00:00+00:00",
            ),
        ],
    );
    let unauthorized = run_workflow(
        "qc-release-invalid-unauthorized",
        "PCS-SAMPLE-003",
        &[
            step(
                "accession_sample",
                "acc-tech-01",
                "accession_tech",
                "2026-01-15T08:00:00+00:00",
            ),
            step(
                "perform_qc",
                "qc-tech-01",
                "qc_tech",
                "2026-01-15T09:00:00+00:00",
            ),
            step(
                "record_analysis",
                "analyst-01",
                "analyst",
                "2026-01-15T10:00:00+00:00",
            ),
            step(
                "release_sample",
                "intern-01",
                "unauthorized_user",
                "2026-01-15T11:00:00+00:00",
            ),
        ],
    );

    for (name, trace) in [
        ("valid_trace.json", valid.clone()),
        ("invalid_missing_qc_trace.json", missing_qc.clone()),
        ("invalid_unauthorized_trace.json", unauthorized.clone()),
    ] {
        let json = to_string_pretty(&trace).unwrap();
        std::fs::write(out_dir.join(name), format!("{json}\n")).unwrap();
    }

    let spec =
        PropertySpec::load(&repo_root().join("templates/hospital_lab/qc_release.stl")).unwrap();
    let mut meta = CertifyEdgeMetadata::dev_default();
    meta.source_commit = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into();

    let valid_check = check_property(&TraceView::from(valid.clone()), &spec);
    let valid_cert = build_certificate(&valid.trace_hash, &spec, &valid_check, &meta, None);
    std::fs::write(
        out_dir.join("expected_valid_certificate.json"),
        format!("{}\n", to_string_pretty(&valid_cert.certificate).unwrap()),
    )
    .unwrap();

    let missing_spec =
        PropertySpec::load(&repo_root().join("templates/hospital_lab/no_release_before_qc.stl"))
            .unwrap();
    let missing_check = check_property(&TraceView::from(missing_qc), &missing_spec);
    let missing_cx = missing_check.counterexample.unwrap();
    std::fs::write(
        out_dir.join("expected_missing_qc_counterexample.json"),
        format!("{}\n", counterexample_to_json(&missing_cx).unwrap()),
    )
    .unwrap();

    let auth_spec =
        PropertySpec::load(&repo_root().join("templates/hospital_lab/authorized_release_only.stl"))
            .unwrap();
    let unauthorized_check = check_property(&TraceView::from(unauthorized), &auth_spec);
    let unauthorized_cx = unauthorized_check.counterexample.unwrap();
    std::fs::write(
        out_dir.join("expected_unauthorized_counterexample.json"),
        format!("{}\n", counterexample_to_json(&unauthorized_cx).unwrap()),
    )
    .unwrap();

    emit_release_certificate_fixture();

    println!("wrote fixtures to {}", out_dir.display());
}
