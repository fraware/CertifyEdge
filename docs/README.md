# Documentation

Start here for how the repository is organized, how to build and test it, and why major choices were made.

| Document | Purpose |
|----------|---------|
| [Quick start](quick-start.md) | Install tools, run Cargo and Bazel, repository layout |
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

## Service-specific notes

- [STL compiler](../services/stl-compiler/README.md) — parsing, outputs, configuration, and how to run tests for that crate
