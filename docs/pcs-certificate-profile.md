# CertifyEdge PCS certificate profile

Phase 2 protocol profile for the CertifyEdge producer. Copy `pcs_registry/TraceCertificate.v0.registry.json` into pcs-core `ArtifactRegistry.v0` when promoting definitions.

## Profile

| Field | Value |
|-------|--------|
| **component** | CertifyEdge |
| **input artifact** | `trace.json` |
| **input handoff kind** | `runtime_to_certificate` |
| **property profile** | `hospital_lab.qc_release` |
| **output artifact** | `TraceCertificate.v0` (`trace_certificate.json`) |
| **output handoff kind** | `certificate_to_bundle` |
| **valid success status** | `CertificateChecked` |
| **valid failure status** | `Rejected` |

## Handoff manifests

| Direction | File | `handoff_kind` |
|-----------|------|----------------|
| LabTrust-Gym → CertifyEdge | `labtrust_to_certifyedge_handoff.json` | `runtime_to_certificate` |
| CertifyEdge → LabTrust-Gym | `certifyedge_to_labtrust_handoff.json` | `certificate_to_bundle` |

Property profile registry (`templates/profiles/`):

- `schema.json` — JSON Schema for profile documents
- `<property_id>.json` — maps `property_id` to STL template, PCS artifact types, and certificate statuses

| Profile | Input | Output | STL |
|---------|-------|--------|-----|
| `hospital_lab.qc_release.json` | `LabTrust.Trace.v0` | `TraceCertificate.v0` | `templates/hospital_lab/qc_release.stl` |
| `hospital_lab.no_release_before_qc.json` | `LabTrust.Trace.v0` | `TraceCertificate.v0` | `templates/hospital_lab/no_release_before_qc.stl` |
| `agent_tool_use.safety_v0.json` | `ToolUseTrace.v0` | `ToolUseCertificate.v0` | `templates/tool_use/no_unauthorized_tool.stl` |
| `scientific_computation.reproducibility_v0.json` | `ComputationRunReceipt.v0` (+ supporting receipts) | `ComputationWitness.v0` | `templates/computation/result_hashes_match.stl` |

Computation profiles declare `supporting_artifacts` (`DatasetReceipt.v0`, `EnvironmentReceipt.v0`, `ResultArtifact.v0`). Handoff directories include four hashed input files; invariants use `run_hash` instead of `trace_hash`.

Each profile JSON defines:

- `property_id`, `template`, `input_trace_artifact`, `output_certificate_artifact`, `counterexample_artifact`, optional `supporting_artifacts`
- `valid_success_status`, `valid_failure_status`
- `release_mode_required_fields` (release-mode certificate field gate; alias `required_release_fields`)
- `formalization` — Lean-facing metadata (`certificate_predicate`, `required_fields`, `admissible_status`, `rejected_status`, `stale_status`)
- `repair_hints` — map of `failure_code` → `{ kind, command, responsible_component? }` for PF explain mode

### Formalization block

| Profile family | `certificate_predicate` | Typical `required_fields` |
|----------------|-------------------------|---------------------------|
| LabTrust / tool-use | `CertificateMatchesRuntime` | `certificate_id`, `trace_hash`, `status`, provenance fields |
| Computation witness | `ComputationWitnessBindsResults` | `witness_id`, `dataset_hash`, `environment_hash`, `run_receipt_hash`, `result_hashes`, `status` |

Formal facts are emitted with `--formal-facts-out certificate_formal_facts.json` and validated against `CertificateFormalFacts.v0`. See [pcs-core-certificate-formal-facts-proposal.md](pcs-core-certificate-formal-facts-proposal.md).

Validate all profiles: `make validate-profiles` or `bash scripts/validate-profiles.sh`.

`emit-pcs-certificate --handoff` resolves `invariants.property_id` through the registry (unknown IDs and template mismatches fail). Add a new workflow by adding a profile JSON file and STL template; no emit logic changes required.

## Counterexample behavior

When temporal checking fails:

1. Emit `TraceCertificate.v0` with `status = Rejected`.
2. Write `counterexample.json` (default beside `--out`, or `--counterexample-out`).
3. Set `counterexample_ref` on the certificate when a path is available.
4. Emit outbound `certificate_to_bundle` handoff with `invariants.status = Rejected`, `invariants.counterexample_ref = counterexample.json`, and empty `expected_outputs` (downstream must not treat the bundle as admissible).

Explain counterexamples: `certifyedge explain-counterexample`.

## Release-mode provenance

With `--release-mode`:

- CertifyEdge `source_commit` must resolve to a non-placeholder git commit (`CERTIFYEDGE_SOURCE_COMMIT` or repo HEAD).
- Inbound `HandoffManifest.v0` is validated with vendored schema, digest, and `pcs validate` when the pcs-core CLI is installed.
- Outbound handoff and certificate artifacts are validated the same way before exit.
- `source_repo` must match the canonical CertifyEdge repository URL on verify/emit.

## Certificate benchmarks

Profile-driven benchmark cases live under `benchmarks/certificates/<suite>/{valid,invalid}/`.
Each case includes `case.json` (`BenchmarkCaseSpec.v0`), `handoff.json`, and input artifacts.

```bash
make validate-certificate-benchmarks   # schema + layout gates
make benchmark-certificates            # run all three profile suites
certifyedge benchmark validate-cases   # case.json schema only
certifyedge benchmark certificates \
  --profile hospital_lab.qc_release \
  --cases benchmarks/certificates/hospital_lab_qc_release \
  --out benchmark_runs/hospital_lab_qc_release
```

Outputs under `--out` (validated against vendored pcs-core schemas):

| File | Schema |
|------|--------|
| `benchmark_report.v0.json` | `BenchmarkReport.v0` (primary ingest for pcs-bench) |
| `benchmark_run.<case_id>.v0.json` | `BenchmarkRun.v0` per case |
| `certificate_coverage_report.v0.json` | `CoverageReport.v0` (`certificate_completeness`) |
| `profile_coverage_report.v0.json` | `ProfileCoverageReport.v0` |
| `repair_hint_quality_report.v0.json` | `CoverageReport.v0` (`repair_hint_quality`) |
| `repair_hint_manifest.v0.json` | Per-case repair-hint quality map for scoring |
| `certificate_benchmark_suite.v0.json` | CertifyEdge suite metrics + `repair_hint_quality` |
| `benchmark_summary.v0.json` | Compact summary when `--json-summary` is set |

Each rejected case with an expected repair hint records `repair_hint_quality` on the
suite report (`repair_hint_present`, `repair_hint_kind`, `responsible_component`,
`repair_command`).

Regenerate cases: `python3 scripts/generate-certificate-benchmark-cases.py`  
Sync benchmark schemas: `make sync-pcs-benchmark-schemas`  
Drift check: `make check-pcs-benchmark-schemas`

## CLI

Property profiles:

```bash
certifyedge profiles list
certifyedge profiles explain hospital_lab.qc_release
certifyedge profiles validate templates/profiles/hospital_lab.qc_release.json
```

Handoff-driven emit (profile registry defaults to `templates/profiles`):

```bash
certifyedge emit-pcs-certificate \
  --release-mode \
  --handoff labtrust_to_certifyedge_handoff.json \
  --profile-registry templates/profiles \
  --out trace_certificate.json \
  --summary-out certificate_summary.json \
  --handoff-out certifyedge_to_labtrust_handoff.json \
  --formal-facts-out certificate_formal_facts.json
```

`certificate_summary.json` includes `formal_predicate`, `formal_fact_artifact`, and `admissible_for_release` for release-run identity handoff.

Legacy path (no handoff): `--spec`, `--trace`, `--out`.

Failed checks print JSON repair hints on stderr (for PF explain mode); rejected emits still exit 0 when artifacts are written.

## Registry

Registry contributions (pcs-core `ArtifactRegistry.v0` `registry_entry` shape):

| File | Output artifact |
|------|-----------------|
| `pcs_registry/TraceCertificate.v0.registry.json` | `TraceCertificate.v0` |
| `pcs_registry/ToolUseCertificate.v0.registry.json` | `ToolUseCertificate.v0` |
| `pcs_registry/ComputationWitness.v0.registry.json` | `ComputationWitness.v0` |
| `pcs_registry/CertificateFormalFacts.v0.registry.json` | `CertificateFormalFacts.v0` |
| `pcs_registry/BenchmarkRun.v0.registry.json` | `BenchmarkRun.v0` (CertifyEdge CI metrics) |
| `pcs_registry/CertificateCoverageReport.v0.registry.json` | `CertificateCoverageReport.v0` |

Certificate registry entries also declare `formal_predicate`, `formal_fact_artifact`, `lean_module`, and `admissible_status` for pcs-core formalization.

Shared fields:

- `schema_owner`: pcs-core
- `runtime_producer` / `allowed_runtime_producers`: CertifyEdge
- `semantic_checks`: structured objects (`check_id`, `severity`, `responsible_component`, `execution_required_in_release_mode`, `allowed_to_skip`) aligned with pcs-core
- `consumer_repos`: CertifyEdge, LabTrust-Gym, Provability Fabric, Scientific Memory (promoted into pcs-core)
- `canonical_hash_required` / `release_mode_required`: true

Validate locally: `make check-pcs-registry` (requires `PCS_CORE_PATH` or sibling `pcs-core` checkout).

Release-mode emit runs vendored schema validation, then `pcs registry check-artifact` when the pcs CLI is installed (warning and skip in local dev without pcs).
