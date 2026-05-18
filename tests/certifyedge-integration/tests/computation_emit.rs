//! Direct emit for scientific_computation.reproducibility_v0 from a fixture directory.

#[path = "../common/support.rs"]
mod support;

use pcs_certificate::{
    emit_certificate_for_profile, load_computation_inputs_from_dir,
    validate_computation_witness_schema, CertifyEdgeMetadata, PropertyProfileRegistry,
    ARTIFACT_COMPUTATION_WITNESS,
};
use support::repo_root;

#[test]
fn test_emit_computation_witness_from_fixture_dir() {
    let root = repo_root();
    let registry = PropertyProfileRegistry::from_certifyedge_root(&root);
    let profile = registry
        .load("scientific_computation.reproducibility_v0")
        .unwrap();
    assert_eq!(
        profile.output_certificate_artifact,
        ARTIFACT_COMPUTATION_WITNESS
    );

    let fixture_dir = root.join("tests/computation");
    let inputs = load_computation_inputs_from_dir(&fixture_dir).unwrap();
    let run_bytes = std::fs::read(fixture_dir.join("computation_run_receipt.json")).unwrap();
    let mut meta = CertifyEdgeMetadata::dev_default();
    meta.source_commit = "abcdef0123456789abcdef0123456789abcdef01".into();
    meta.release_mode = true;

    let outcome = emit_certificate_for_profile(
        &profile,
        &registry,
        &root.join(&profile.template),
        &run_bytes,
        &meta,
        None,
        Some(inputs),
    )
    .expect("emit computation witness");

    let cert = outcome.certificate.as_value();
    assert_eq!(cert["status"], "CertificateChecked");
    validate_computation_witness_schema(&cert).unwrap();
}
