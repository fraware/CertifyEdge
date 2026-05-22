# ADR 001 — Bazel as the canonical build graph

## Status

Accepted

## Context

The repository contains several Rust services, and releases together with automation should produce repeatable builds that depend on declared toolchains and locked dependencies alone. Cargo remains where dependencies are declared and locked, while Bazel reads the workspace `Cargo.toml` and `Cargo.lock` to fetch third-party crates in a controlled way.

## Decision

The project adopts `MODULE.bazel` with `rules_rust`, `rules_proto`, and `protobuf` from the Bazel Central Registry. The Rust toolchain is pinned in `MODULE.bazel` and matches continuous integration in `.github/workflows/ci.yml` and `rust-toolchain.toml` at version **1.88.0**. `WORKSPACE` remains a minimal workspace name for older Bazel expectations.

## Consequences

Contributors may use `cargo` for day-to-day iteration, and automation together with release checks should use Bazel where targets are defined. Protocol buffer contracts live under `services/*/proto` as `proto_library` targets, and Rust gRPC code generation can be added when a networked API becomes necessary.

## Related

- [ADR 002 — CI and end-to-end integration test](002-ci-integration-test.md)
- [ADR 003 — Protocol buffers and gRPC](003-proto-and-grpc.md)
