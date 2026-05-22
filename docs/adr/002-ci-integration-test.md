# ADR 002 — Continuous integration and the end-to-end integration test

## Status

Accepted (updated 2026-05 for PCS v0.1)

## Context

Automation should exercise the software the repository actually ships. Two tracks coexist today. The STL/SMT pipeline uses `integration_tests` to compile specifications, run SMT checks, and sign certificates while `CompilerConfig::for_tests_without_external_tools()` keeps external Lean, Z3, and CVC5 binaries off the CI runners. The PCS v0.1 certificate engine adds a profile-driven `certifyedge` CLI, certificate benchmarks, pcs-core validation, and an optional cross-repo clean-checkout with LabTrust-Gym.

## Decision

### STL/SMT integration test

The project keeps `integration_tests` in Cargo and `//tests/pipeline_integration:pipeline_integration` in Bazel, and tests use `CompilerConfig::for_tests_without_external_tools()` so CI runners need no external solver installation.

### PCS v0.1 (primary release gate)

GitHub Actions in `.github/workflows/ci.yml` runs on every push and pull request. The Rust job performs `cargo fmt`, `cargo check`, PCS clippy, profile validation, `make benchmark-certificates`, `certifyedge-integration` tests, `pcs-runbook.sh`, a pcs-core checkout, fixture validation, handoff emit gates, benchmark output validation, `make pcs-bench-producer`, pcs-bench ingest validation, registry drift checks, and a LabTrust-Gym clean-checkout. The Bazel job builds the PCS graph and runs `scripts/bazel-pcs-test.sh`.

Before a PCS-related pull request, contributors should run the local equivalent.

```bash
export CERTIFYEDGE_SOURCE_COMMIT="$(git rev-parse HEAD)"
make pcs-test
```

Maintainers follow the full checklist in [docs/pcs-guide.md](../pcs-guide.md#pre-release-checklist) before tagging a release.

## Consequences

PCS changes must pass `make pcs-test` at minimum, and release tagging should follow the full checklist in the PCS guide. STL/SMT pipeline tests continue for the `stl-compiler`, `smt-verifier`, and `certificate` crates.

## Related

- [ADR 001 — Bazel as canonical build graph](001-bazel-canonical-build.md)
- [ADR 005 — PCS v0.1 LabTrust certification](005-pcs-v01-labtrust-certification.md)
- [PCS guide](../pcs-guide.md)
