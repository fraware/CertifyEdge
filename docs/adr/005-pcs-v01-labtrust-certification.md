# ADR 005: PCS v0.1 LabTrust trace certification

## Status

Accepted (2026-05)

## Context

[Proof-Carrying Science (pcs-core)](https://github.com/SentinelOps-CI/pcs-core) v0.1 requires a checker that consumes LabTrust-Gym traces, evaluates hospital-lab temporal properties, and emits `TraceCertificate.v0` for downstream verification. CertifyEdge already had an STL/SMT/certificate stack for a different certification model.

## Decision

1. **New crates** — `labtrust-adapter` (parse, hash, temporal check) and `pcs-certificate` (profiles, emit, handoffs, benchmarks).
2. **CLI** — `certifyedge` with stable commands: `check-trace`, `emit-pcs-certificate`, `verify-certificate`, `explain-counterexample`, `profiles`, `benchmark`.
3. **Property profiles** — `templates/profiles/*.json` map workflows to templates; `templates/hospital_lab/*.stl` are a constrained temporal-property DSL, not general STL.
4. **pcs-core integration** — Vendored `schemas/pcs/`; `pcs validate` in CI and `--release-mode` for real `source_commit`.
5. **Trace hash** — Canonical body matches LabTrust-Gym `compute_trace_hash`.

Extended profiles (tool-use, computation) and certificate benchmarks were added on the same profile-driven architecture.

## Consequences

- PCS v0.1 is gated in GitHub Actions and via `make pcs-test` / `make pcs-bench-producer`.
- Bazel job runs `bazel-pcs-test.sh` for the PCS graph.
- Legacy `stl-compiler` / `smt-verifier` / `certificate` crates remain for the original pipeline.
- Simulation-only disclaimer on all v0.1 artifacts.

## References

- [PCS guide](../pcs-guide.md)
- [pcs-handoff.md](../pcs-handoff.md)
- [labtrust-adapter.md](../labtrust-adapter.md)
