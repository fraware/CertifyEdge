//! Regenerate `tests/labtrust/` and negative fixtures under `tests/fixtures/labtrust-release/`.
//! Full PCS release-run: `make release-run`.
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

fn run_certifyedge_expect_fail(args: &[&str]) {
    let status = Command::new(certifyedge_bin())
        .current_dir(repo_root())
        .args(args)
        .status()
        .expect("spawn certifyedge");
    assert!(!status.success(), "certifyedge {:?} should fail", args);
}

fn write_labtrust_negative_fixtures(
    missing_qc: &labtrust_adapter::LabTrustTrace,
    unauthorized: &labtrust_adapter::LabTrustTrace,
) {
    let root = repo_root();
    let release_dir = root.join("tests/fixtures/labtrust-release");
    std::fs::create_dir_all(&release_dir).unwrap();

    let spec = root
        .join("templates/hospital_lab/qc_release.stl")
        .to_string_lossy()
        .into_owned();

    let missing_trace_path = release_dir.join("invalid_missing_qc_trace.json");
    let unauthorized_trace_path = release_dir.join("invalid_unauthorized_trace.json");
    let missing_cx_path = release_dir.join("invalid_missing_qc_counterexample.json");
    let unauthorized_cx_path = release_dir.join("invalid_unauthorized_counterexample.json");

    std::fs::write(
        &missing_trace_path,
        format!("{}\n", to_string_pretty(missing_qc).unwrap()),
    )
    .unwrap();
    std::fs::write(
        &unauthorized_trace_path,
        format!("{}\n", to_string_pretty(unauthorized).unwrap()),
    )
    .unwrap();

    run_certifyedge_expect_fail(&[
        "check-trace",
        "--spec",
        &spec,
        "--trace",
        missing_trace_path.to_str().unwrap(),
        "--counterexample-out",
        missing_cx_path.to_str().unwrap(),
    ]);

    run_certifyedge_expect_fail(&[
        "check-trace",
        "--spec",
        &spec,
        "--trace",
        unauthorized_trace_path.to_str().unwrap(),
        "--counterexample-out",
        unauthorized_cx_path.to_str().unwrap(),
    ]);

    println!(
        "wrote labtrust negative fixtures under {}",
        release_dir.display()
    );
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
    let meta = CertifyEdgeMetadata::dev_default();

    let valid_check = check_property(&TraceView::from(valid.clone()), &spec);
    let valid_cert =
        build_certificate(&valid.trace_hash, &spec, &valid_check, &meta, None).unwrap();
    std::fs::write(
        out_dir.join("expected_valid_certificate.json"),
        format!("{}\n", to_string_pretty(&valid_cert.certificate).unwrap()),
    )
    .unwrap();

    let missing_spec =
        PropertySpec::load(&repo_root().join("templates/hospital_lab/no_release_before_qc.stl"))
            .unwrap();
    let missing_check = check_property(&TraceView::from(missing_qc.clone()), &missing_spec);
    let missing_cx = missing_check.counterexample.unwrap();
    std::fs::write(
        out_dir.join("expected_missing_qc_counterexample.json"),
        format!("{}\n", counterexample_to_json(&missing_cx).unwrap()),
    )
    .unwrap();

    let auth_spec =
        PropertySpec::load(&repo_root().join("templates/hospital_lab/authorized_release_only.stl"))
            .unwrap();
    let unauthorized_check = check_property(&TraceView::from(unauthorized.clone()), &auth_spec);
    let unauthorized_cx = unauthorized_check.counterexample.unwrap();
    std::fs::write(
        out_dir.join("expected_unauthorized_counterexample.json"),
        format!("{}\n", counterexample_to_json(&unauthorized_cx).unwrap()),
    )
    .unwrap();

    write_labtrust_negative_fixtures(&missing_qc, &unauthorized);

    println!("wrote fixtures to {}", out_dir.display());
}
