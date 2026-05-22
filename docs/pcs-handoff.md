# Cross-repo PCS handoff

> **Start here:** [PCS guide](pcs-guide.md) for local workflows, benchmarks, and pre-release checklist.

This document lists the **end-to-end chain** from LabTrust-Gym through CertifyEdge to downstream consumers. Canonical chain documentation also lives in [LabTrust-Gym `docs/pcs_v01_clean_chain.md`](https://github.com/fraware/LabTrust-Gym/blob/main/docs/pcs_v01_clean_chain.md).

## Automated chain (recommended)

From CertifyEdge (sibling `../LabTrust-Gym`, `pcs` and `labtrust` on PATH):

```bash
export PCS_DETERMINISTIC=1
make clean-checkout-certified   # LabTrust + CertifyEdge + attach
make clean-checkout             # Full chain (Provability Fabric + Scientific Memory)
```

Windows: `.\scripts\pcs-v01-clean-checkout.ps1`

| Variable | Role |
|----------|------|
| `PCS_DETERMINISTIC` | Set to `1` for reproducible demo runs |
| `LABTRUST_GYM_ROOT` | Path to LabTrust-Gym (default `../LabTrust-Gym`) |
| `CERTIFYEDGE_ROOT` | Path to this repository |
| `PCS_CHAIN_WORK` | Working directory for chain artifacts |
| `PF_BIN` | Provability Fabric CLI (`pf`) |
| `SCIENTIFIC_MEMORY_ROOT` | Sibling scientific-memory repo |

---

## Manual chain

Run from **LabTrust-Gym** unless noted.

### LabTrust-Gym

```bash
PCS_DETERMINISTIC=1 labtrust run-demo qc-release
labtrust export-trace --run runs/qc-release --out trace.json
labtrust export-runtime-receipt --run runs/qc-release --out runtime_receipt.json
labtrust export-pcs --run runs/qc-release --out science_claim_bundle.pending.json
pcs validate science_claim_bundle.pending.json

labtrust emit-handoff-to-certifyedge \
  --trace trace.json \
  --runtime-receipt runtime_receipt.json \
  --out labtrust_to_certifyedge_handoff.json \
  --release-mode
pcs validate labtrust_to_certifyedge_handoff.json
```

### CertifyEdge (handoff-driven)

Example fixture: `tests/fixtures/handoff/labtrust_to_certifyedge_handoff.json`.

```bash
export CERTIFYEDGE_SOURCE_COMMIT="$(git rev-parse HEAD)"
cargo run -p certifyedge -- --release-mode emit-pcs-certificate \
  --handoff labtrust_to_certifyedge_handoff.json \
  --profile-registry templates/profiles \
  --out trace_certificate.json \
  --summary-out certificate_summary.json \
  --handoff-out certifyedge_to_labtrust_handoff.json \
  --formal-facts-out certificate_formal_facts.json
cargo run -p certifyedge -- verify-certificate trace_certificate.json --trace trace.json
pcs validate trace_certificate.json
pcs validate certifyedge_to_labtrust_handoff.json
```

Legacy path (explicit spec + trace, no handoff):

```bash
cargo run -p certifyedge -- emit-pcs-certificate \
  --spec templates/hospital_lab/qc_release.stl \
  --trace trace.json \
  --out trace_certificate.json
```

### Tool-use profile

Same emit path; profile `agent_tool_use.safety_v0` produces `ToolUseCertificate.v0`. Handoff expects `ToolUseTrace.v0` input and `ToolUseCertificate.v0` output.

### Computation profile

Profile `scientific_computation.reproducibility_v0` produces `ComputationWitness.v0` from a multi-file handoff directory:

| File | Artifact type |
|------|----------------|
| `computation_run_receipt.json` | `ComputationRunReceipt.v0` |
| `dataset_receipt.json` | `DatasetReceipt.v0` |
| `environment_receipt.json` | `EnvironmentReceipt.v0` |
| `result_artifact.json` | `ResultArtifact.v0` |

Handoff invariants use `run_hash` (not `trace_hash`).

### Rejected certificates (all profiles)

| Artifact | Content |
|----------|---------|
| Certificate JSON | `status = Rejected` |
| Counterexample | Profile-specific path |
| Outbound handoff | `certificate_to_bundle`, empty `expected_outputs` |

### LabTrust-Gym (attach)

```bash
labtrust attach-certificate \
  --bundle science_claim_bundle.pending.json \
  --certificate trace_certificate.json \
  --out science_claim_bundle.certified.json
pcs validate science_claim_bundle.certified.json
```

### Provability Fabric

```bash
pf verify science-claim science_claim_bundle.certified.json --out verification_result.json
pf sign science-claim science_claim_bundle.certified.json --out signed_science_claim_bundle.json
pcs validate signed_science_claim_bundle.json
```

### Scientific Memory

```bash
cd ../scientific-memory
just pcs-import-bundle ../LabTrust-Gym/signed_science_claim_bundle.json
just pcs-render-claim claim-pcs-qc-release-v0.1
```

Post-chain validation (LabTrust-Gym):

```bash
python examples/pcs_qc_release/scripts/verify_pcs_v01_chain.py --work . --stage full
```

---

## Hash compatibility

- `certificate.trace_hash` must equal `trace.json` → `trace_hash`.
- That value must equal LabTrust `RuntimeReceipt.v0` → `trace_hash`.
- CertifyEdge uses the same canonical digest rules as LabTrust-Gym `compute_trace_hash`.

## Counterexample reasons

`release_before_qc`, `unauthorized_release`, `invalid_event_order`, `malformed_trace`.

| Invalid trace fixture | Expected reason |
|-----------------------|-----------------|
| `invalid_missing_qc_trace.json` | `release_before_qc` |
| `invalid_unauthorized_trace.json` | `unauthorized_release` |

## Simulation disclaimer

All artifacts describe LabTrust-Gym **simulation** runs only—not clinical or production laboratory certification.
