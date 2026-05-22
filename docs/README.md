# CertifyEdge documentation

This index helps you choose the right guide. The repository delivers two related capabilities, namely **PCS v0.1** with profile-driven proof-carrying certificates, and an **STL/SMT specification stack** that covers temporal formulas, solvers, and signed certificates for classical temporal-logic workflows.

---

## New here?

Begin with the [Quick start](quick-start.md) to clone the repository and install the Rust toolchain, then follow the [PCS guide](pcs-guide.md#build-and-install-the-cli) to build the CLI and run the runbook smoke test. When you plan to open a pull request, read [Contributing](../CONTRIBUTING.md) for the test gates that match continuous integration.

---

## Proof-Carrying Science (PCS) v0.1

The [PCS guide](pcs-guide.md) is the main reference for property profiles, the `certifyedge` CLI, benchmark suites, schema synchronization, cross-repository chains, and the pre-release checklist maintainers run before tagging.

| Document | Read when you need to… |
|----------|-------------------------|
| [PCS guide](pcs-guide.md) | Use or ship the certificate engine |
| [Cross-repo handoff](pcs-handoff.md) | Wire LabTrust-Gym, CertifyEdge, and downstream verifiers |
| [Trace certificates](pcs-trace-certificates.md) | Understand `TraceCertificate.v0` fields and canonical fixtures |
| [Property profiles](pcs-certificate-profile.md) | Edit profiles or registry contributions |
| [LabTrust adapter](labtrust-adapter.md) | Parse traces, hashes, and hospital-lab property templates |
| [Certificate benchmarks](../benchmarks/certificates/README.md) | Benchmark case layout |
| [PCS schemas](../schemas/pcs/README.md) | Vendored JSON schema reference |

---

## Development and architecture

| Document | Purpose |
|----------|---------|
| [Quick start](quick-start.md) | Rust, Bazel, CI, and repository layout |
| [Contributing](../CONTRIBUTING.md) | Pull requests, formatting, and test gates |
| [Root README](../README.md) | Project overview |
| [STL compiler](../services/stl-compiler/README.md) | STL/SMT crate, separate from PCS property profiles |

### Architecture decision records

See the [ADR index](adr/README.md).

| ADR | Topic |
|-----|--------|
| [001](adr/001-bazel-canonical-build.md) | Canonical build graph |
| [002](adr/002-ci-integration-test.md) | GitHub Actions and integration tests |
| [003](adr/003-proto-and-grpc.md) | Protocol buffers and future gRPC |
| [004](adr/004-threat-model-outline.md) | Security outline (summary) |
| [005](adr/005-pcs-v01-labtrust-certification.md) | LabTrust certification architecture |

---

## External references

- [pcs-core](https://github.com/SentinelOps-CI/pcs-core) hosts schemas, the `pcs` CLI, and benchmark ingest tooling.
- [LabTrust-Gym](https://github.com/fraware/LabTrust-Gym) supplies simulation traces and runtime handoffs for the hospital-lab demonstration workflow.
