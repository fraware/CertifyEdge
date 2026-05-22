# ADR 002: Continuous integration and the end-to-end integration test

## Status

Accepted (updated 2026-05 for PCS v0.1)

## Context

The project needs automation that matches what is actually built. Two tracks coexist:

1. **STL/SMT pipeline** — `integration_tests` compiles specs, runs SMT checks, and signs certificates without external Lean/Z3/CVC5 when configured for tests.
2. **PCS v0.1 certificate engine** — profile-driven `certifyedge` CLI, certificate benchmarks, pcs-core validation, and optional cross-repo clean-checkout.

## Decision

### STL/SMT integration test

- Keep `integration_tests` (Cargo) and `//tests/pipeline_integration:pipeline_integration` (Bazel).
- `CompilerConfig::for_tests_without_external_tools()` avoids external solver binaries in CI.

### PCS v0.1 (primary release gate)

GitHub Actions (`.github/workflows/ci.yml`) runs on every push/PR:

**Rust job:** `cargo fmt`, `cargo check`, PCS clippy, profile validation, `make benchmark-certificates`, `certifyedge-integration` tests, `pcs-runbook.sh`, pcs-core checkout, fixture validation, handoff emit gates, benchmark output validation, `make pcs-bench-producer`, pcs-bench ingest validation, registry drift, LabTrust-Gym clean-checkout.

**Bazel job:** PCS graph build and `scripts/bazel-pcs-test.sh`.

Local equivalent before a PCS-related PR:

```bash
export CERTIFYEDGE_SOURCE_COMMIT="$(git rev-parse HEAD)"
make pcs-test
```

Full release checklist: [docs/pcs-guide.md](../pcs-guide.md#pre-release-checklist).

## Consequences

- PCS changes must pass `make pcs-test` at minimum; release tagging should follow the full checklist in the PCS guide.
- STL/SMT pipeline tests remain for `stl-compiler` / `smt-verifier` / `certificate` crates.

## Related

- [ADR 001 — Bazel as canonical build graph](001-bazel-canonical-build.md)
- [ADR 005 — PCS v0.1 LabTrust certification](005-pcs-v01-labtrust-certification.md)
- [PCS guide](../pcs-guide.md)
