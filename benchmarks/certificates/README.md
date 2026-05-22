# Certificate benchmarks

Profile-driven benchmark cases for PCS certificate emission. Each profile has
`valid/` and `invalid/` case directories containing:

- `case.json` — `case_category`, expected status, failure code, counterexample, repair-hint, and formal-facts expectations
- `handoff.json` — runtime handoff manifest (digest refreshed at run time)
- Input artifacts referenced by the handoff (`trace.json`, computation receipts, etc.)

## Benchmarked profiles

| Profile ID | Cases directory | Output suite |
|------------|-----------------|--------------|
| `hospital_lab.qc_release` | `hospital_lab_qc_release/` | `benchmark_runs/hospital_lab_qc_release/` |
| `agent_tool_use.safety_v0` | `tool_use_safety/` | `benchmark_runs/tool_use_safety/` |
| `scientific_computation.reproducibility_v0` | `computation_reproducibility/` | `benchmark_runs/computation_reproducibility/` |

## Live-required categories (per profile)

Each benchmarked profile must include at least:

- 1 `valid` case
- 3 invalid field/hash cases (`invalid_missing_required_field`, `invalid_hash_mismatch`, `invalid_source_provenance`)
- 1 `rejected_certificate` case
- 1 `repair_hint_quality` case
- 1 `formal_facts` case

Generate cases from committed test fixtures:

```bash
python3 scripts/generate-certificate-benchmark-cases.py
```

## Producer targets

Release-grade producer gate (tool-use safety suite + pcs-bench consumer validation):

```bash
export CERTIFYEDGE_SOURCE_COMMIT="$(git rev-parse HEAD)"
make pcs-bench-producer
```

All three profiles plus release-grade ingest validation:

```bash
export CERTIFYEDGE_SOURCE_COMMIT="$(git rev-parse HEAD)"
make pcs-bench-producer-all-profiles
```

Full benchmark generation (same three profiles, no ingest re-validation):

```bash
make benchmark-certificates
make validate-benchmark-outputs
```

## Outputs under `--out`

| File / directory | Role |
|------------------|------|
| `benchmark_report.v0.json` | pcs-core `BenchmarkReport.v0` aggregate (`evidence_grade`, `metric_summaries`) |
| `runs/<case_id>.benchmark_run.v0.json` | Per-case `CertificateBenchmarkRun.v0` (pcs `BenchmarkRun` core + extensions) |
| `certificate_coverage_report.v0.json` | CertifyEdge-native `CertificateCoverageReport.v0` |
| `profile_coverage_report.v0.json` | pcs-core `ProfileCoverageReport.v0` |
| `repair_hint_quality_report.v0.json` | pcs-core `CoverageReport.v0` for repair-hint scoring |
| `repair_hint_manifest.v0.json` | Per-case repair-hint quality map (when repair-hint cases exist) |
| `failure_localization/<case_id>.failure_localization_result.v0.json` | Sidecar `FailureLocalizationResult.v0` per invalid/rejected case |
| `explain_quality/<case_id>.explain_quality_report.v0.json` | Sidecar `ExplainQualityReport.v0` per rejection/repair-hint case |
| `pcs_bench_ingest.v0.json` | pcs-core `PcsBenchIngest.v0` bundle (primary entry point for pcs-bench) |
| `benchmark_summary.v0.json` | Normalized stdout summary when `--json-summary` is set |

### `artifact_refs` and sidecar provenance

`pcs_bench_ingest.v0.json` embeds canonical benchmark objects and lists `artifact_refs`
(`BenchmarkArtifactRef.v0`) that point at on-disk sidecars with matching `sha256` digests.

Embedded types (required refs for certifyedge per pcs-core semantics):

- `BenchmarkRun.v0` → `runs/*.benchmark_run.v0.json`
- `CoverageReport.v0` → `certificate_coverage_report.v0.json`, `repair_hint_quality_report.v0.json`
- `ProfileCoverageReport.v0` → `profile_coverage_report.v0.json`
- `FailureLocalizationResult.v0` → `failure_localization/*.json`
- `ExplainQualityReport.v0` → `explain_quality/*.json`

Top-level producer files (`benchmark_report.v0.json`, `pcs_bench_ingest.v0.json`,
`repair_hint_manifest.v0.json`) are documented in
`coverage_reports[].details.sidecar_artifact_paths` because pcs-core ingest refs must
target embedded artifact types only.

## Failure localization mapping

| Failure code | Responsible component |
|--------------|---------------------|
| `policy_hash_mismatch` | `unknown` (ambiguous: certificate or runtime producer) |
| `unauthorized_tool_call` | `runtime_producer` |
| `dataset_hash_mismatch` | `runtime_producer` |
| `environment_digest_mismatch` | `runtime_producer` |
| `result_hash_mismatch` | `runtime_producer` |
| `missing_code_commit` | `runtime_producer` |
| `unknown_profile` | `certificate_producer` |
| `invalid_handoff` | `handoff` |
| `rejected_certificate` | `certificate_producer` |

Ambiguity reasons are recorded in `coverage_reports[].details.ambiguous_localizations`.

## Explain quality (rejection / repair-hint)

Reports require sections `provenance`, `hashes`, `verification`, `limitations`, `repair_hints`
with `quality_score >= 0.8`. Section presence is derived from emitted certificates,
counterexamples, handoffs, and repair hints captured during the benchmark run.

## Validation

```bash
certifyedge benchmark validate-cases
make validate-certificate-benchmarks
make validate-benchmark-outputs
make validate-pcs-bench-ingest
```

With pcs-core checkout:

```bash
pcs-bench validate-ingest \
  --input benchmark_runs/tool_use_safety/pcs_bench_ingest.v0.json \
  --pcs-core ../pcs-core \
  --release-grade
```

Optional: `--validate-pcs-core-output ../pcs-core` on `benchmark certificates` validates
outputs against upstream schemas during generation.
