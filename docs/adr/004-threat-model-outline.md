# ADR 004: Threat model (outline)

## Status

Proposed (summary only; detailed work deferred)

## Context

Formal verification, certificates, and operations security should be described in one place. A full threat model (for example structured lists of threats and mitigations, with diagrams) fits better next to dedicated security documentation and tooling as those land.

## Decision (for now)

- Treat **signing keys**, **verifier configuration**, and **solver binaries** as high-value assets.
- Integration tests run without requiring external solver installations; production setups that use Z3 or CVC5 should configure them explicitly and restrict access appropriately.
- Expand or replace this note when security workflows and deployment targets are defined.

## Consequences

- Application continuous integration stays focused on build and test correctness. Security reviews can reference this document without blocking the default pipeline.

## Related

- [ADR 002 — CI and end-to-end integration test](002-ci-integration-test.md)
