# PCS schemas (vendored from pcs-core)

These files support offline PCS validation in CertifyEdge. Certificate and handoff
schemas are synced from [pcs-core](https://github.com/SentinelOps-CI/pcs-core); benchmark
report schemas follow the same contract as `pcs-bench`.

## Certificate artifacts

| Schema | Used by |
|--------|---------|
| `TraceCertificate.v0.schema.json` | LabTrust profiles |
| `ToolUseCertificate.v0.schema.json` | `agent_tool_use.safety_v0` |
| `ToolUseTrace.v0.schema.json` | Tool-use trace validation |
| `ComputationWitness.v0.schema.json` | `scientific_computation.reproducibility_v0` |
| `CertificateFormalFacts.v0.schema.json` | `--formal-facts-out` |
| `HandoffManifest.v0.schema.json` | Runtime and certificate handoffs |
| `ArtifactRegistry.v0.schema.json` | `pcs_registry/*.registry.json` entries |

## pcs-core benchmark contract (pcs-bench ingest)

| Schema | Output file |
|--------|-------------|
| `BenchmarkReport.v0.schema.json` | `benchmark_report.v0.json` |
| `BenchmarkRun.v0.schema.json` | `benchmark_run.<case_id>.v0.json` |
| `CoverageReport.v0.schema.json` | `certificate_coverage_report.v0.json`, `repair_hint_quality_report.v0.json` |
| `ProfileCoverageReport.v0.schema.json` | `profile_coverage_report.v0.json` |

## CertifyEdge benchmark extensions

| Schema | Output file |
|--------|-------------|
| `BenchmarkCaseSpec.v0.schema.json` | `benchmarks/certificates/**/case.json` |
| `CertificateBenchmarkSuite.v0.schema.json` | `certificate_benchmark_suite.v0.json` |
| `CertificateCoverageReport.v0.schema.json` | Nested metrics inside the suite report |

`repair_hint_manifest.v0.json` is a CertifyEdge aggregate of per-case `repair_hint_quality`
objects for scoring (not a separate pcs-core schema yet).

## Sync

```bash
make sync-pcs-schemas              # certificates + handoff + benchmark schemas
make sync-pcs-benchmark-schemas    # benchmark-only refresh
make check-pcs-benchmark-schemas   # drift gate (requires local pcs-core checkout)
```

`common.defs.json` merges pcs-core benchmark vocabulary with CertifyEdge-only defs
(`certificate_benchmark_case_category`, `repair_hint_quality`, etc.).
