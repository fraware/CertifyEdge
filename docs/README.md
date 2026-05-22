# CertifyEdge documentation

Use this index to find the right guide. The repository ships two related capabilities: **PCS v0.1** (profile-driven proof-carrying certificates) and an **STL/SMT specification stack** (temporal formulas, solvers, signed certificates).

---

## New here?

1. Clone and build: [Quick start](quick-start.md)
2. Run the PCS smoke test: [PCS guide — Build and install](pcs-guide.md#build-and-install-the-cli)
3. Before contributing: [Contributing](../CONTRIBUTING.md)

---

## Proof-Carrying Science (PCS) v0.1

**[PCS guide](pcs-guide.md)** is the main reference: property profiles, the `certifyedge` CLI, benchmarks, schema sync, cross-repo chains, and the pre-release checklist.

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
| [STL compiler](../services/stl-compiler/README.md) | STL/SMT crate (separate from PCS property profiles) |

### Architecture decision records

[Index](adr/README.md)

| ADR | Topic |
|-----|--------|
| [001 — Bazel](adr/001-bazel-canonical-build.md) | Canonical build graph |
| [002 — CI](adr/002-ci-integration-test.md) | GitHub Actions and integration tests |
| [003 — Protos](adr/003-proto-and-grpc.md) | Protocol buffers and future gRPC |
| [004 — Threat model](adr/004-threat-model-outline.md) | Security outline (summary) |
| [005 — PCS v0.1](adr/005-pcs-v01-labtrust-certification.md) | LabTrust certification architecture |

---

## External references

- [pcs-core](https://github.com/SentinelOps-CI/pcs-core) — schemas, `pcs` CLI, and benchmark ingest
- [LabTrust-Gym](https://github.com/fraware/LabTrust-Gym) — simulation traces and runtime handoffs for the hospital-lab demo
