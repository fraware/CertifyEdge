# ADR 005 — PCS v0.1 LabTrust trace certification

## Status

Accepted (2026-05)

## Context

[Proof-Carrying Science (pcs-core)](https://github.com/SentinelOps-CI/pcs-core) v0.1 requires a checker that consumes LabTrust-Gym traces, evaluates hospital-lab temporal properties, and emits `TraceCertificate.v0` for downstream verification. CertifyEdge already shipped an STL/SMT/certificate stack aimed at a different certification model, and the PCS path extends the repository with profile-driven emission that shares the workspace while following pcs-core contracts.

## Decision

The project adds `labtrust-adapter` for parse, hash, and temporal check logic, and `pcs-certificate` for profiles, emit, handoffs, and benchmarks. The `certifyedge` CLI exposes stable commands including `check-trace`, `emit-pcs-certificate`, `verify-certificate`, `explain-counterexample`, `profiles`, and `benchmark`. Property profiles under `templates/profiles/*.json` map workflows to templates, while `templates/hospital_lab/*.stl` files implement a constrained temporal-property DSL for hospital-lab v0.1 as a dedicated profile format separate from a general STL grammar. pcs-core integration vendors `schemas/pcs/`, runs `pcs validate` in CI, and uses `--release-mode` so `source_commit` reflects a real repository revision. Trace hashing uses the canonical body defined by LabTrust-Gym `compute_trace_hash`. Tool-use and computation profiles together with certificate benchmarks extend the same profile-driven architecture.

## Consequences

PCS v0.1 is gated in GitHub Actions and through `make pcs-test` and `make pcs-bench-producer`. The Bazel job runs `bazel-pcs-test.sh` for the PCS graph. The `stl-compiler`, `smt-verifier`, and `certificate` crates remain for the original pipeline. All v0.1 artifacts carry a simulation-only disclaimer.

## References

- [PCS guide](../pcs-guide.md)
- [pcs-handoff.md](../pcs-handoff.md)
- [labtrust-adapter.md](../labtrust-adapter.md)
