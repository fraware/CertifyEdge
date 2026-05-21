//! PCS certificate construction, profile registry, and handoff emit for CertifyEdge.

pub mod certificate_benchmark;
pub mod pcs_benchmark_bridge;
pub mod computation_check;
pub mod computation_receipt;
pub mod computation_violation;
pub mod computation_witness;
pub mod emit_summary;
pub mod emitted_certificate;
pub mod formal_facts;
pub mod handoff;
pub mod hash;
pub mod metadata;
pub mod pcs_schema;
pub mod pcs_schema_external;
pub mod pcs_validate;
pub mod property_profile;
pub mod registry_contribution;
pub mod repair_hint;
pub mod signing;
pub mod source_commit;
pub mod status_policy;
pub mod tool_use_certificate;
pub mod tool_use_check;
pub mod tool_use_trace;
pub mod tool_use_violation;
pub mod trace_certificate;
pub mod validation;

pub use certificate_benchmark::{
    benchmark_suite_dir_for_profile, run_certificate_benchmark,
    validate_certificate_benchmark_cases_tree, BenchmarkCertificatesOptions,
    CertificateBenchmarkOutcome, CertificateBenchmarkSuiteV0, CertificateCoverageReport,
    BENCHMARK_CASE_SPEC_SCHEMA, BENCHMARKED_PROFILE_IDS, CERTIFICATE_COVERAGE_REPORT_SCHEMA,
    PROFILE_COVERAGE_REPORT_SCHEMA,
};
pub use pcs_benchmark_bridge::{
    build_json_summary, validate_pcs_benchmark_output_dir, BenchmarkCertificatesJsonSummary,
    RepairHintQuality, CERTIFICATE_BENCHMARK_SUITE_SCHEMA,
};
pub use pcs_schema_external::validate_pcs_core_output_dir;
pub use computation_check::{
    check_computation_reproducibility, ComputationCheckResult, ComputationPropertySpec,
};
pub use computation_receipt::{
    load_computation_inputs_from_dir, ComputationEmitInputs, ARTIFACT_COMPUTATION_RUN_RECEIPT,
    ARTIFACT_DATASET_RECEIPT, ARTIFACT_ENVIRONMENT_RECEIPT, ARTIFACT_RESULT_ARTIFACT,
    COMPUTATION_RUN_RECEIPT_FILE, DATASET_RECEIPT_FILE, ENVIRONMENT_RECEIPT_FILE,
    RESULT_ARTIFACT_FILE,
};
pub use computation_witness::{build_computation_witness, ComputationWitnessV0};
pub use emit_summary::{summary_to_json, CertificateEmitSummary};
pub use emitted_certificate::{
    default_certificate_output_name, default_counterexample_filename, emit_certificate_for_profile,
    emit_check_failure_stderr, CertificateEmitOutcome, EmittedCertificate,
};
pub use formal_facts::{
    admissible_for_release, build_certificate_formal_facts, formal_facts_to_json_pretty,
    validate_formal_facts_consistency, validate_profile_formalization,
    ARTIFACT_CERTIFICATE_FORMAL_FACTS, DEFAULT_FORMAL_FACTS_FILENAME,
    PREDICATE_CERTIFICATE_MATCHES_RUNTIME, PREDICATE_COMPUTATION_WITNESS_BINDS_RESULTS,
};
pub use handoff::{
    build_certificate_to_bundle_handoff, file_digest, finalize_handoff_digest,
    load_handoff_manifest, plan_emit_from_handoff, refresh_handoff_digest_file,
    validate_handoff_artifact, write_handoff_manifest, HandoffArtifactRef, HandoffEmitPlan,
    HandoffManifestV0,
    COMPONENT_CERTIFYEDGE, COMPONENT_LABTRUST, HANDOFF_KIND_CERTIFICATE_TO_BUNDLE,
    HANDOFF_KIND_RUNTIME_TO_CERTIFICATE,
};
pub use metadata::CertifyEdgeMetadata;
pub use pcs_schema::{
    detect_certificate_artifact_type, validate_certificate_formal_facts_schema,
    validate_certificate_schema_for_type, validate_computation_witness_schema,
    validate_handoff_manifest_schema, validate_tool_use_certificate_schema,
    validate_benchmark_case_spec_schema, validate_benchmark_report_schema,
    benchmark_run_core_from_certificate_run, validate_benchmark_run_schema,
    validate_certificate_benchmark_run_schema,
    validate_certificate_benchmark_suite_schema,
    validate_certificate_coverage_report_schema, validate_coverage_report_schema,
    validate_explain_quality_report_schema, validate_failure_localization_result_schema,
    validate_pcs_bench_ingest_schema, validate_profile_coverage_report_schema,
    validate_tool_use_trace_schema,
    validate_trace_certificate_schema,
};
pub use pcs_validate::{
    registry_check_artifact, validate_certificate_artifact, validate_certificate_json,
    validate_certificate_json_for_profile,
};
pub use property_profile::{
    list_registered_property_ids, load_property_profile, resolve_property_profile,
    spec_path_for_property_id, validate_property_profile_value,
    validate_runtime_to_certificate_profile, ProfileFormalization, ProfileRepairHint,
    PropertyProfile, PropertyProfileRegistry, ARTIFACT_COMPUTATION_WITNESS,
    ARTIFACT_LABTRUST_TRACE, ARTIFACT_TOOL_USE_CERTIFICATE, ARTIFACT_TOOL_USE_TRACE,
    ARTIFACT_TRACE_CERTIFICATE, RUNTIME_TO_CERTIFICATE_OUTPUT_ARTIFACT, SUPPORTED_OUTPUT_ARTIFACTS,
};
pub use registry_contribution::{
    validate_default_certificate_formal_facts_registry_contribution,
    validate_default_computation_witness_registry_contribution,
    validate_default_tool_use_certificate_registry_contribution,
    validate_default_trace_certificate_registry_contribution, validate_registry_contribution_entry,
};
pub use repair_hint::{
    emit_certificate_failure, repair_hint_from_profile, repair_temporal_check_failed,
    repair_tool_use_check_failed, validate_release_mode_fields, CertificateFailure, RepairHint,
};
pub use source_commit::{
    certifyedge_repo_root, is_placeholder_source_commit, is_zero_source_commit, labtrust_gym_root,
    SourceCommitResolution, ZERO_SOURCE_COMMIT,
};
pub use status_policy::{
    is_terminal_certificate_status, validate_certificate_status_transition,
    STATUS_CERTIFICATE_CHECKED, STATUS_CERTIFICATE_PENDING, STATUS_REJECTED,
};
pub use tool_use_certificate::{build_tool_use_certificate, ToolUseCertificateV0};
pub use tool_use_check::{check_tool_use_property, ToolUseCheckResult, ToolUsePropertySpec};
pub use tool_use_trace::{parse_tool_use_trace_json, ToolUseTraceV0};
pub use trace_certificate::{
    build_certificate, certificate_from_json, certificate_to_json, counterexample_from_json,
    counterexample_to_json, explain_counterexample, CertificateOutcome, SOURCE_REPO,
};
pub use trace_certificate::{build_certificate_with_profile, resolve_profile_registry};
pub use validation::verify_certificate_document;
