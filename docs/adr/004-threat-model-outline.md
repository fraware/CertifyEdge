# ADR 004 — Threat model (outline)

## Status

Accepted (summary only; detailed threat analysis is planned separately)

## Context

CertifyEdge produces certificates and verification artifacts that downstream systems may treat as evidence. Security expectations depend on signing keys, solver configuration, supply-chain integrity, and how release artifacts are distributed. A full threat-model document with structured threats, mitigations, and deployment diagrams will follow when production deployment targets are defined.

## Decision (current scope)

Until a dedicated security guide exists, the project treats the following as high-value assets.

| Asset | Notes |
|-------|--------|
| **Signing keys** | Protect private keys used for Ed25519 certificate signing |
| **Verifier configuration** | SMT solver paths and flags affect what is considered verified |
| **Solver binaries** | Z3 and CVC5 installations should be pinned and access-controlled in production |
| **Release artifacts** | PCS certificates and `source_commit` provenance must match intended repository state |
| **Vendored schemas** | `schemas/pcs/` must stay aligned with [pcs-core](https://github.com/SentinelOps-CI/pcs-core) through drift checks |

Integration tests use the in-process compiler configuration by default, and production setups that enable Lean, Z3, or CVC5 should configure them explicitly and restrict who may change those settings.

PCS v0.1 hospital-lab certificates apply only to **simulation** workflows and should be presented as engineering evidence for the protocol that remains distinct from clinical or production laboratory certification.

## Consequences

Default CI focuses on build correctness, schema conformance, and reproducible benchmarks. Security reviews can reference this ADR while the standard pipeline continues on its existing schedule. A future ADR or `docs/security.md` may supersede this outline when deployment guidance is ready.

## Related

- [ADR 002 — CI and integration tests](002-ci-integration-test.md)
- [ADR 005 — PCS v0.1 LabTrust certification](005-pcs-v01-labtrust-certification.md)
- [PCS guide](../pcs-guide.md)
