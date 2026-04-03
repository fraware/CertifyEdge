//! End-to-end test: compile a specification, run verification, produce a signed certificate.

use certificate::CertificateService;
use smt_verifier::{SMTVerifier, SolverType};
use stl_compiler::{Compiler, CompilerConfig};

#[tokio::test]
async fn compile_verify_and_sign_certificate() {
    let compiler = Compiler::new(CompilerConfig::for_tests_without_external_tools());
    let spec_text = "grid_spec\nvoltage > 220";

    let compilation = compiler
        .compile(spec_text)
        .await
        .expect("compile specification without external Lean, Z3, or CVC5");

    let smt_script = compilation.smt_output.smt_lib_code.clone();
    assert!(
        smt_script.contains("(set-logic"),
        "expected generated SMT-LIB to declare logic"
    );

    let mut verifier = SMTVerifier::new().expect("verifier");
    let v = verifier
        .verify_script(&smt_script, Some(vec![SolverType::Z3]))
        .await
        .expect("verify");

    assert!(
        v.success,
        "verification should succeed without external solver binaries"
    );

    let cert_service = CertificateService::new().expect("certificate service");
    let cert = cert_service
        .create_certificate(
            b"spec-hash".to_vec(),
            b"lean-hash".to_vec(),
            vec![b"smt-proof".to_vec()],
            b"model-hash".to_vec(),
            "test-solver".to_string(),
            "test-proof".to_string(),
            vec!["test-component".to_string()],
        )
        .await
        .expect("certificate");

    assert!(!cert.certificate_id.is_empty());
    assert!(cert.is_signed());

    let verified = cert_service
        .verify_certificate(&cert)
        .await
        .expect("verify cert");
    assert!(verified.valid);
}
