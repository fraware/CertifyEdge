# Documentation

## Proof-Carrying Science (PCS) v0.1

**[PCS guide](pcs-guide.md)** — start here: profiles, CLI, benchmarks, cross-repo chain, pre-release checklist.

| Document | When to read |
|----------|--------------|
| [PCS guide](pcs-guide.md) | Everything you need to use or release the certificate engine |
| [Cross-repo handoff](pcs-handoff.md) | LabTrust-Gym → CertifyEdge → Provability Fabric step-by-step |
| [Trace certificates](pcs-trace-certificates.md) | LabTrust `TraceCertificate.v0` fields and canonical fixtures |
| [Property profiles](pcs-certificate-profile.md) | Profile registry and artifact registry contributions |
| [LabTrust adapter](labtrust-adapter.md) | Trace format, hashing, temporal property templates |

## General development

| Document | Purpose |
|----------|---------|
| [Quick start](quick-start.md) | Rust/Bazel setup, legacy STL/SMT stack |
| [Contributing](../CONTRIBUTING.md) | Pull requests and PCS pre-merge checks |
| [Root README](../README.md) | Project overview |

## Architecture decision records

[ADR index](adr/README.md)

| ADR | Topic |
|-----|--------|
| [001 — Bazel](adr/001-bazel-canonical-build.md) | Build graph |
| [002 — CI](adr/002-ci-integration-test.md) | GitHub Actions and integration tests |
| [003 — Protos](adr/003-proto-and-grpc.md) | Protocol buffers |
| [004 — Threat model](adr/004-threat-model-outline.md) | Security outline (placeholder) |
| [005 — PCS v0.1](adr/005-pcs-v01-labtrust-certification.md) | LabTrust certification decision |

## Service notes

- [STL compiler](../services/stl-compiler/README.md) — legacy signal temporal logic / SMT stack (separate from PCS v0.1 profiles)
