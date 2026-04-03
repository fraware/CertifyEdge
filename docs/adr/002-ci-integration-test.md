# ADR 002: Continuous integration and the end-to-end integration test

## Status

Accepted

## Context

Some jobs referenced build targets that did not exist, so automation did not reflect real behavior. The project needs one test that exercises the main libraries on every change.

## Decision

- Add an integration test that:
  1. Compiles a small **signal temporal logic (STL)** specification with `Compiler` and `CompilerConfig::for_tests_without_external_tools()` (no separate Lean, Z3, or CVC5 programs on the machine).
  2. Runs **satisfiability modulo theories (SMT)** checks on generated SMT-LIB with `SMTVerifier`.
  3. Creates and checks an Ed25519-signed certificate with `CertificateService`.
- Keep this test in the Cargo workspace package `integration_tests` (under `tests/pipeline_integration/`) and expose the same logic to Bazel as `//tests/pipeline_integration:pipeline_integration`.
- GitHub Actions runs `cargo fmt --check`, `cargo test --workspace`, and `bazel test --config=ci //tests/pipeline_integration:pipeline_integration`, with a cached Bazel output directory.

## Consequences

- Automation matches what is actually built today. Additional checks (coverage, software bills of materials, signing infrastructure) can be added when those targets exist.

## Related

- [ADR 001 — Bazel as canonical build graph](001-bazel-canonical-build.md)
- [ADR 003 — Protocol buffers and gRPC](003-proto-and-grpc.md)
