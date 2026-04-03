# ADR 003: Protocol buffers and gRPC (when to add them)

## Status

Accepted

## Context

The STL compiler ships a `.proto` file and generated Rust types so there is a stable schema for tools and future services. The end-to-end integration test in `tests/pipeline_integration` calls the Rust libraries directly in one process; it does not start a gRPC server.

## Decision

- Keep the `.proto` file and generated Rust types as the public schema for the compiler output shape.
- Add gRPC servers and clients only when there is a concrete need to run components on separate machines or processes.
- Keep `prost` and `tonic` versions in Cargo aligned with whatever the Bazel proto rules expect when gRPC is enabled.

## Consequences

- Continuous integration does not need a running gRPC stack for the integration test.
- When gRPC is introduced, dependency versions must be checked in both Cargo and Bazel.

## Related

- [ADR 001 — Bazel as canonical build graph](001-bazel-canonical-build.md)
- [ADR 002 — CI and end-to-end integration test](002-ci-integration-test.md)
