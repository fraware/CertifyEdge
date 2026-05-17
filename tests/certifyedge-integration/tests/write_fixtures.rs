//! Regenerate `tests/labtrust/*.json` fixtures. Run: cargo test -p certifyedge-integration write_fixtures -- --ignored --nocapture

use labtrust_adapter::{
    check_property, PropertySpec, TraceView, workflow_sim::{run_workflow, WorkflowStep},
};
use pcs_certificate::{build_certificate, counterexample_to_json, CertifyEdgeMetadata};
use serde_json::to_string_pretty;
use std::path::PathBuf;

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
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
            step("accession_sample", "acc-tech-01", "accession_tech", "2026-01-15T08:00:00+00:00"),
            step("perform_qc", "qc-tech-01", "qc_tech", "2026-01-15T09:00:00+00:00"),
            step("record_analysis", "analyst-01", "analyst", "2026-01-15T10:00:00+00:00"),
            step("release_sample", "rel-mgr-01", "release_manager", "2026-01-15T11:00:00+00:00"),
        ],
    );
    let missing_qc = run_workflow(
        "qc-release-invalid-missing-qc",
        "PCS-SAMPLE-002",
        &[
            step("accession_sample", "acc-tech-01", "accession_tech", "2026-01-15T08:00:00+00:00"),
            step("release_sample", "rel-mgr-01", "release_manager", "2026-01-15T10:00:00+00:00"),
        ],
    );
    let unauthorized = run_workflow(
        "qc-release-invalid-unauthorized",
        "PCS-SAMPLE-003",
        &[
            step("accession_sample", "acc-tech-01", "accession_tech", "2026-01-15T08:00:00+00:00"),
            step("perform_qc", "qc-tech-01", "qc_tech", "2026-01-15T09:00:00+00:00"),
            step("record_analysis", "analyst-01", "analyst", "2026-01-15T10:00:00+00:00"),
            step("release_sample", "intern-01", "unauthorized_user", "2026-01-15T11:00:00+00:00"),
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

    let spec = PropertySpec::load(&repo_root().join("templates/hospital_lab/qc_release.stl")).unwrap();
    let mut meta = CertifyEdgeMetadata::dev_default();
    meta.source_commit = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into();

    let valid_check = check_property(&TraceView::from(valid.clone()), &spec);
    let valid_cert = build_certificate(&valid.trace_hash, &spec, &valid_check, &meta, None);
    std::fs::write(
        out_dir.join("expected_valid_certificate.json"),
        format!(
            "{}\n",
            to_string_pretty(&valid_cert.certificate).unwrap()
        ),
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

    let auth_spec = PropertySpec::load(
        &repo_root().join("templates/hospital_lab/authorized_release_only.stl"),
    )
    .unwrap();
    let unauthorized_check = check_property(&TraceView::from(unauthorized), &auth_spec);
    let unauthorized_cx = unauthorized_check.counterexample.unwrap();
    std::fs::write(
        out_dir.join("expected_unauthorized_counterexample.json"),
        format!("{}\n", counterexample_to_json(&unauthorized_cx).unwrap()),
    )
    .unwrap();

    println!("wrote fixtures to {}", out_dir.display());
}
