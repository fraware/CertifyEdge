# PCS schemas (vendored from pcs-core)

These files are copied from [pcs-core](https://github.com/SentinelOps-CI/pcs-core) `schemas/` for offline PCS validation in CertifyEdge:

| Schema | Used by |
|--------|---------|
| `TraceCertificate.v0.schema.json` | LabTrust profiles |
| `ToolUseCertificate.v0.schema.json` | `agent_tool_use.safety_v0` |
| `ToolUseTrace.v0.schema.json` | Tool-use trace validation |
| `ComputationWitness.v0.schema.json` | `scientific_computation.reproducibility_v0` |
| `CertificateFormalFacts.v0.schema.json` | `--formal-facts-out` (Lean-fact sources; propose upstream to pcs-core) |
| `BenchmarkCaseSpec.v0.schema.json` | `benchmarks/certificates/**/case.json` expectations |
| `BenchmarkRun.v0.schema.json` | `certifyedge benchmark certificates` run summary |
| `CertificateCoverageReport.v0.schema.json` | Per-profile benchmark metrics and repair-hint accuracy |
| `ProfileCoverageReport.v0.schema.json` | Profile/template coverage nested in coverage reports |
| `HandoffManifest.v0.schema.json` | Runtime and certificate handoffs |
| `ArtifactRegistry.v0.schema.json` | `pcs_registry/*.registry.json` entries |

Run `make sync-pcs-schemas` when pcs-core schema versions change.

CertifyEdge validates traces and certificates in-process against the vendored schemas. `ComputationWitness.v0` uses in-process schema and registry contribution checks in release mode until pcs-core CLI registers the artifact type; LabTrust and tool-use artifacts still run optional `pcs validate` / `pcs registry check-artifact` when the pcs CLI is installed.
