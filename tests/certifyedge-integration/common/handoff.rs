//! PCS release-run certificate identity and manifest provenance checks.

use std::path::Path;

use serde_json::Value;

use super::{load_json_path, release_run_dir, release_run_fixture};

pub fn verification_result_certificate_ref(vr: &Value) -> Option<String> {
    if let Some(checks) = vr.get("checks").and_then(|c| c.as_array()) {
        for check in checks {
            if check.get("check_id").and_then(|v| v.as_str()) == Some("evidence_refs_complete") {
                if let Some(id) = check
                    .get("details")
                    .and_then(|d| d.get("certificate_refs"))
                    .and_then(|r| r.as_array())
                    .and_then(|a| a.first())
                    .and_then(|v| v.as_str())
                {
                    return Some(id.to_string());
                }
            }
        }
    }
    vr.get("verified_input")
        .and_then(|v| v.get("certificate_id"))
        .and_then(|v| v.as_str())
        .map(str::to_string)
}

/// Assert `trace_certificate.certificate_id` propagates into the certified science-claim bundle.
pub fn assert_certificate_id_handoff_trace_to_certified_bundle(run: &Path) {
    let trace_cert = load_json_path(&run.join("trace_certificate.json"));
    let certified = load_json_path(&run.join("science_claim_bundle.certified.json"));

    let cert_id = trace_cert["certificate_id"]
        .as_str()
        .expect("trace_certificate.certificate_id");

    assert_eq!(
        certified["certificates"][0]["certificate_id"]
            .as_str()
            .unwrap(),
        cert_id
    );
    assert_eq!(
        certified["claim_artifact"]["certificate_refs"][0]
            .as_str()
            .unwrap(),
        cert_id
    );
    assert_eq!(
        certified["evidence_bundle"]["certificate_refs"][0]
            .as_str()
            .unwrap(),
        cert_id
    );
}

/// Assert PF verification/signing preserves the same certificate identity when artifacts exist.
pub fn assert_certificate_id_handoff_through_pf_chain(run: &Path) {
    let vr_path = run.join("verification_result.json");
    let signed_path = run.join("signed_science_claim_bundle.json");
    if !vr_path.is_file() || !signed_path.is_file() {
        return;
    }

    let trace_cert = load_json_path(&run.join("trace_certificate.json"));
    let cert_id = trace_cert["certificate_id"]
        .as_str()
        .expect("trace_certificate.certificate_id");

    let vr = load_json_path(&vr_path);
    let vr_cert = verification_result_certificate_ref(&vr)
        .expect("verification_result evidence_refs_complete.certificate_refs[0]");
    assert_eq!(vr_cert, cert_id);

    let signed = load_json_path(&signed_path);
    let signed_cert = signed["science_claim_bundle"]["certificates"][0]["certificate_id"]
        .as_str()
        .expect("signed bundle certificate_id");
    assert_eq!(signed_cert, cert_id);
}

/// Full release-chain propagation: certificate identity and trace hash through the signed bundle.
pub fn assert_release_chain_certificate_and_trace_hash_propagation(run: &Path) {
    let trace_cert = load_json_path(&run.join("trace_certificate.json"));
    let certified = load_json_path(&run.join("science_claim_bundle.certified.json"));
    let signed = load_json_path(&run.join("signed_science_claim_bundle.json"));
    let signed_bundle = &signed["science_claim_bundle"];

    let cert_id = trace_cert["certificate_id"]
        .as_str()
        .expect("trace_certificate.certificate_id");
    let certified_cert_id = certified["certificates"][0]["certificate_id"]
        .as_str()
        .expect("certified.certificates[0].certificate_id");
    let claim_ref = certified["claim_artifact"]["certificate_refs"][0]
        .as_str()
        .expect("certified.claim_artifact.certificate_refs[0]");
    let evidence_ref = certified["evidence_bundle"]["certificate_refs"][0]
        .as_str()
        .expect("certified.evidence_bundle.certificate_refs[0]");
    let signed_cert_id = signed_bundle["certificates"][0]["certificate_id"]
        .as_str()
        .expect("signed.science_claim_bundle.certificates[0].certificate_id");

    assert_eq!(certified_cert_id, cert_id, "certified.certificates[0].certificate_id");
    assert_eq!(claim_ref, cert_id, "certified.claim_artifact.certificate_refs[0]");
    assert_eq!(evidence_ref, cert_id, "certified.evidence_bundle.certificate_refs[0]");
    assert_eq!(signed_cert_id, cert_id, "signed.science_claim_bundle.certificates[0].certificate_id");

    let trace_hash = trace_cert["trace_hash"]
        .as_str()
        .expect("trace_certificate.trace_hash");
    let certified_receipt_hash = certified["runtime_receipts"][0]["trace_hash"]
        .as_str()
        .expect("certified.runtime_receipts[0].trace_hash");
    let signed_receipt_hash = signed_bundle["runtime_receipts"][0]["trace_hash"]
        .as_str()
        .expect("signed.runtime_receipts[0].trace_hash");

    assert_eq!(
        certified_receipt_hash, trace_hash,
        "certified.runtime_receipts[0].trace_hash"
    );
    assert_eq!(
        signed_receipt_hash, trace_hash,
        "signed.runtime_receipts[0].trace_hash"
    );
}

pub fn assert_release_run_manifest_provenance(run: &Path) {
    let manifest = load_json_path(&run.join("RELEASE_FIXTURE_MANIFEST.json"));
    let trace_cert = load_json_path(&run.join("trace_certificate.json"));
    let certified = load_json_path(&run.join("science_claim_bundle.certified.json"));

    assert_eq!(
        manifest["certificate_id"].as_str().unwrap(),
        trace_cert["certificate_id"].as_str().unwrap()
    );
    assert_eq!(
        manifest["trace_hash"].as_str().unwrap(),
        trace_cert["trace_hash"].as_str().unwrap()
    );
    assert_eq!(
        manifest["certifyedge_commit"].as_str().unwrap(),
        trace_cert["source_commit"].as_str().unwrap()
    );
    assert_eq!(
        manifest["labtrust_gym_commit"].as_str().unwrap(),
        certified["source_commit"].as_str().unwrap()
    );

    let vr_path = run.join("verification_result.json");
    if vr_path.is_file() {
        let vr = load_json_path(&vr_path);
        if let Some(pf_commit) = manifest
            .get("provability_fabric_commit")
            .and_then(|v| v.as_str())
        {
            assert_eq!(vr["source_commit"].as_str().unwrap(), pf_commit);
        }
    }

    let cert_id = trace_cert["certificate_id"].as_str().unwrap();
    if let Some(handoff_id) = manifest.get("certificate_id").and_then(|v| v.as_str()) {
        assert_eq!(handoff_id, cert_id);
    }
}

pub fn validate_release_run_fixture_tree() {
    const REQUIRED: &[&str] = &[
        "RELEASE_FIXTURE_MANIFEST.json",
        "trace.json",
        "runtime_receipt.json",
        "trace_certificate.json",
        "science_claim_bundle.pending.json",
        "science_claim_bundle.certified.json",
        "verification_result.json",
        "signed_science_claim_bundle.json",
        "certificate_summary.json",
    ];

    let run = release_run_dir();
    for name in REQUIRED {
        let path = run.join(name);
        assert!(
            path.is_file(),
            "missing release-run fixture {}",
            path.display()
        );
    }

    super::validate_certificate_against_pcs_core(&release_run_fixture("trace_certificate.json"));

    let run_path = release_run_dir();
    assert_certificate_id_handoff_trace_to_certified_bundle(&run_path);
    assert_certificate_id_handoff_through_pf_chain(&run_path);
    assert_release_chain_certificate_and_trace_hash_propagation(&run_path);
    assert_release_run_manifest_provenance(&run_path);
}
