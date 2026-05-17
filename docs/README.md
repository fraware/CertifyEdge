# Documentation

Start here for how the repository is organized, how to build and test it, and why major choices were made.

| Document | Purpose |
|----------|---------|
| [Quick start](quick-start.md) | Install tools, run Cargo and Bazel, repository layout |
| [PCS trace certificates](pcs-trace-certificates.md) | LabTrust v0.1 CLI runbook, `TraceCertificate.v0`, release mode |
| [LabTrust adapter](labtrust-adapter.md) | Trace parsing, hashing, temporal properties |
| [PCS handoff](pcs-handoff.md) | LabTrust-Gym → CertifyEdge → Provability Fabric contract |
| [Contributing](../CONTRIBUTING.md) | Pull requests, formatting, commands to run before submitting |
| [Architecture decisions (ADRs)](adr/) | Short records of build system, CI, protos, and security outline |
| [Root README](../README.md) | Project overview and goals |

## Architecture decision records

Directory listing: [docs/adr/README.md](adr/README.md).

| ADR | Topic |
|-----|--------|
| [001 — Bazel as canonical build graph](adr/001-bazel-canonical-build.md) | `MODULE.bazel`, Cargo lockfile, toolchain alignment |
| [002 — CI and end-to-end integration test](adr/002-ci-integration-test.md) | GitHub Actions and `integration_tests` / Bazel `pipeline_integration` |
| [003 — Protocol buffers and gRPC](adr/003-proto-and-grpc.md) | `.proto` schema today; gRPC when needed |
| [004 — Threat model outline](adr/004-threat-model-outline.md) | Placeholder for security documentation |
| [005 — PCS v0.1 LabTrust certification](adr/005-pcs-v01-labtrust-certification.md) | Trace certificates, runbook CLI, pcs-core validation |

## PCS v0.1 (LabTrust)

```bash
make test          # integration tests + clippy (PCS crates)
make runbook       # full handoff script (scripts/pcs-runbook.sh)
```

LabTrust traces live under `tests/labtrust/`. Deterministic release handoff fixtures are under `tests/fixtures/labtrust-release/` (CLI-generated certificate and counterexamples). Regenerate with:

`cargo test -p certifyedge-integration write_fixtures -- --ignored --nocapture`

## Service-specific notes

- [STL compiler](../services/stl-compiler/README.md) — parsing, outputs, configuration, and how to run tests for that crate
