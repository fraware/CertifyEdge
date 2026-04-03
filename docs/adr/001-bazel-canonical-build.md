# ADR 001: Bazel as the canonical build graph

## Status

Accepted

## Context

The repository contains several Rust services. Builds for releases and automation should be repeatable and not depend on one developer’s machine. Cargo remains where dependencies are declared and locked; Bazel reads the workspace `Cargo.toml` and `Cargo.lock` to fetch third-party crates in a controlled way.

## Decision

- Use `MODULE.bazel` with `rules_rust`, `rules_proto`, and `protobuf` from the Bazel Central Registry.
- Pin the Rust toolchain in `MODULE.bazel` and use the same version in continuous integration (`.github/workflows/ci.yml`) and `rust-toolchain.toml` (currently **1.88.0**).
- Keep `WORKSPACE` only as a minimal workspace name for older Bazel expectations.

## Consequences

- Contributors can use `cargo` for day-to-day work; automation and release checks should use Bazel where it is configured.
- Protocol buffer contracts live under `services/*/proto` as `proto_library` targets. Rust gRPC code generation can be added when a networked API is needed.

## Related

- [ADR 002 — CI and end-to-end integration test](002-ci-integration-test.md)
- [ADR 003 — Protocol buffers and gRPC](003-proto-and-grpc.md)
