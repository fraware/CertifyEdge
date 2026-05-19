# pcs-core proposal: `CertificateFormalFacts.v0`

CertifyEdge emits Lean-fact sources alongside PCS certificates so Provability Fabric and Scientific Memory can extract proof obligations without re-implementing certificate semantics.

## Artifact

| Field | Value |
|-------|--------|
| **artifact_type** | `CertificateFormalFacts.v0` |
| **schema** | `schemas/CertificateFormalFacts.v0.schema.json` |
| **producer** | CertifyEdge (`--formal-facts-out`) |
| **consumers** | Provability Fabric, Scientific Memory, pcs-core formalization pipeline |

## Relationship to certificates

Each formal-facts document references the emitted certificate file (`artifact` basename) and mirrors:

- `certificate_id`, `certificate_type`, `status`
- Profile-driven hash fields (`trace_hash`, `run_receipt_hash`, `witness_id`, …)
- `formal_predicate` from the property profile (`CertificateMatchesRuntime` or `ComputationWitnessBindsResults`)
- `admissible_for_release` (boolean, consistent with certificate status)

Rejected certificates include `failure_code`, `formal_implication`, and `repair_hint` so downstream tools can explain why Lean obligations were not generated.

## Registry

CertifyEdge ships:

- `pcs_registry/CertificateFormalFacts.v0.registry.json` — artifact registry contribution
- Certificate-family contributions (`TraceCertificate.v0`, `ToolUseCertificate.v0`, `ComputationWitness.v0`) reference `formal_fact_artifact: CertificateFormalFacts.v0` and their Lean predicate.

## Handoff

Outbound `certificate_to_bundle` handoffs include:

- `invariants.formal_predicate`, `invariants.admissible_for_release`
- Optional `input_artifacts[certificate_formal_facts.json]` when `--formal-facts-out` is used

## Promotion checklist for pcs-core

1. Add `CertificateFormalFacts.v0.schema.json` and `common.defs` refs (copy from CertifyEdge `schemas/pcs/`).
2. Register `CertificateFormalFacts.v0` in `ArtifactRegistry.v0` with semantic checks:
   - `formal_facts_certificate_id_matches_certificate`
   - `admissible_for_release_matches_certificate_status`
3. Add `formal_predicate`, `formal_fact_artifact`, `lean_module`, `admissible_status` to certificate registry entries (Trace, ToolUse, ComputationWitness).
4. Expose Lean modules `PCS.Certificate` and `PCS.ComputationWitness` (predicates as documented in CertifyEdge profiles).

Until promoted, CertifyEdge validates formal facts in-process against the vendored schema.
