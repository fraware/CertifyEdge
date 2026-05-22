# ADR 003 — Protocol buffers and gRPC

## Status

Accepted

## Context

The STL compiler ships a `.proto` file and generated Rust types so tools and future services share a stable schema for compiler output. The end-to-end integration test in `tests/pipeline_integration` calls the Rust libraries directly inside one process and therefore leaves gRPC servers unstarted during CI.

## Decision

The repository keeps the `.proto` file and generated Rust types as the public schema for the compiler output shape. gRPC servers and clients arrive only when a concrete requirement appears to run components on separate machines or processes. `prost` and `tonic` versions in Cargo stay aligned with the Bazel proto rules whenever gRPC is enabled.

## Consequences

Continuous integration runs the integration test through the in-process Cargo path until gRPC ships, at which point maintainers must verify dependency versions in both Cargo and Bazel.

## Related

- [ADR 001 — Bazel as canonical build graph](001-bazel-canonical-build.md)
- [ADR 002 — CI and end-to-end integration test](002-ci-integration-test.md)
