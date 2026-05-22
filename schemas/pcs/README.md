# Vendored PCS schemas

JSON schemas in this directory are synced from [pcs-core](https://github.com/SentinelOps-CI/pcs-core) so CertifyEdge can validate artifacts offline. Usage and synchronization commands appear in [docs/pcs-guide.md](../../docs/pcs-guide.md).

## Certificate and handoff

| Schema | Used for |
|--------|----------|
| `TraceCertificate.v0.schema.json` | LabTrust profiles |
| `ToolUseCertificate.v0.schema.json` | Tool-use safety |
| `ToolUseTrace.v0.schema.json` | Tool-use traces |
| `ComputationWitness.v0.schema.json` | Computation reproducibility |
| `CertificateFormalFacts.v0.schema.json` | `--formal-facts-out` |
| `HandoffManifest.v0.schema.json` | Runtime and certificate handoffs |
| `ArtifactRegistry.v0.schema.json` | `pcs_registry/*.registry.json` |

## Benchmark contract

| Schema | Output file |
|--------|-------------|
| `BenchmarkReport.v0.schema.json` | `benchmark_report.v0.json` |
| `BenchmarkRun.v0.schema.json` | Core fields in `CertificateBenchmarkRun.v0` |
| `CoverageReport.v0.schema.json` | `repair_hint_quality_report.v0.json` |
| `ProfileCoverageReport.v0.schema.json` | `profile_coverage_report.v0.json` |
| `PcsBenchIngest.v0.schema.json` | `pcs_bench_ingest.v0.json` |
| `CertificateBenchmarkRun.v0.schema.json` | `runs/*.benchmark_run.v0.json` |
| `CertificateCoverageReport.v0.schema.json` | `certificate_coverage_report.v0.json` |
| `FailureLocalizationResult.v0.schema.json` | `failure_localization/*.json` |
| `ExplainQualityReport.v0.schema.json` | `explain_quality/*.json` |

CertifyEdge-only extensions include `BenchmarkCaseSpec.v0`, `CertificateBenchmarkSuite.v0`, and `BenchmarkArtifactRef.v0`.

## Sync

```bash
make sync-pcs-schemas
make sync-pcs-benchmark-schemas
make check-pcs-benchmark-schemas
```

`common.defs.json` merges pcs-core vocabulary with CertifyEdge-only definitions.
