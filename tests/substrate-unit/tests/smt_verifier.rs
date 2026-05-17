use smt_verifier::{SMTVerifier, SolverType};

#[tokio::test]
async fn verify_requires_set_logic() {
    let mut verifier = SMTVerifier::new().expect("verifier");
    let err = verifier
        .verify_script("(declare-fun x () Real)\n(check-sat)\n", None)
        .await;
    assert!(err.is_err());
}

#[tokio::test]
#[ignore = "requires z3 or cvc5 on PATH"]
async fn verify_with_solver() {
    let mut verifier = SMTVerifier::new().expect("verifier");
    let script = "(set-logic QF_LRA)\n(declare-fun x () Real)\n(assert (> x 0))\n(check-sat)\n";
    let result = verifier
        .verify_script(script, Some(vec![SolverType::Z3]))
        .await
        .expect("verify");
    assert!(result.success);
}
