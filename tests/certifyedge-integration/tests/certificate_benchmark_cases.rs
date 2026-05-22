//! Benchmark case.json schema validation for the committed case tree.

#[path = "../common/support.rs"]
mod support;

use pcs_certificate::validate_certificate_benchmark_cases_tree;

use support::repo_root;

#[test]
fn committed_certificate_benchmark_cases_validate() {
    validate_certificate_benchmark_cases_tree(&repo_root()).expect("benchmark case tree");
}
