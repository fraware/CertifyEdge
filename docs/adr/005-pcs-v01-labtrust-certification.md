# ADR 005: PCS v0.1 LabTrust trace certification

## Status

Accepted (2026-05)

## Context

[Proof-Carrying Science (PCS)](https://github.com/SentinelOps-CI/pcs-core) v0.1 requires a checker that consumes LabTrust-Gym `trace.json`, evaluates hospital-lab temporal properties, and emits `TraceCertificate.v0` for Provability Fabric. CertifyEdge already had STL/SMT/certificate services for a different certification model.

## Decision

1. **New crates** — `labtrust-adapter` (parse, hash, temporal check) and `pcs-certificate` (`TraceCertificate.v0`, vendored schema validation, metadata).
2. **CLI** — `certifyedge` binary with stable runbook commands: `check-trace`, `emit-pcs-certificate`, `verify-certificate`, `explain-counterexample`.
3. **Property profile** — `templates/hospital_lab/*.stl` are a constrained LabTrust temporal-property DSL, not general STL.
4. **pcs-core integration** — Vendored `schemas/pcs/` for offline validation; optional `pcs validate` in CI and `--release-mode` for real `source_commit`.
5. **Trace hash** — Canonical body matches `labtrust_gym.pcs.trace.compute_trace_hash` (`schema_version`, `version`, `run_id`, `sample_id`, `event_hashes`).

## Consequences

- PCS v0.1 tests run in GitHub Actions (`certifyedge-integration`, `scripts/pcs-runbook.sh`, pcs-core checkout).
- Legacy `stl-compiler` / `smt-verifier` / `certificate` crates remain; Bazel CI does not gate PCS v0.1.
- Simulation-only disclaimer on all v0.1 artifacts.

## References

- [docs/pcs-handoff.md](../pcs-handoff.md)
- [docs/pcs-trace-certificates.md](../pcs-trace-certificates.md)
- [docs/labtrust-adapter.md](../labtrust-adapter.md)
