# Cross-repo PCS handoff

Local workflows, benchmarks, and the pre-release checklist appear in the [PCS guide](pcs-guide.md). This page lists the end-to-end chain from LabTrust-Gym through CertifyEdge to downstream consumers, and LabTrust-Gym also documents the same chain in [`docs/pcs_v01_clean_chain.md`](https://github.com/fraware/LabTrust-Gym/blob/main/docs/pcs_v01_clean_chain.md).

## Automated chain (recommended)

From CertifyEdge you need a sibling `../LabTrust-Gym` checkout with `pcs` and `labtrust` on your path.

```bash
export PCS_DETERMINISTIC=1
make clean-checkout-certified
make clean-checkout
```

On Windows run `.\scripts\pcs-v01-clean-checkout.ps1`.

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

Run the LabTrust-Gym steps from that repository unless a heading states otherwise.

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

The committed example handoff is `tests/fixtures/handoff/labtrust_to_certifyedge_handoff.json`.

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

An alternate path passes an explicit spec and trace directly when teams supply spec-and-trace inputs in place of a handoff manifest.

```bash
cargo run -p certifyedge -- emit-pcs-certificate \
  --spec templates/hospital_lab/qc_release.stl \
  --trace trace.json \
  --out trace_certificate.json
```

### Tool-use profile

The same emit command applies with profile `agent_tool_use.safety_v0`, which yields `ToolUseCertificate.v0` when the handoff references `ToolUseTrace.v0` input and `ToolUseCertificate.v0` output.

### Computation profile

Profile `scientific_computation.reproducibility_v0` yields `ComputationWitness.v0` from a multi-file handoff directory.

| File | Artifact type |
|------|----------------|
| `computation_run_receipt.json` | `ComputationRunReceipt.v0` |
| `dataset_receipt.json` | `DatasetReceipt.v0` |
| `environment_receipt.json` | `EnvironmentReceipt.v0` |
| `result_artifact.json` | `ResultArtifact.v0` |

Computation handoffs carry `run_hash` in invariants, whereas trace-oriented handoffs carry `trace_hash`.

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

Post-chain validation in LabTrust-Gym:

```bash
python examples/pcs_qc_release/scripts/verify_pcs_v01_chain.py --work . --stage full
```

---

## Hash compatibility

`certificate.trace_hash` must equal the `trace_hash` field inside `trace.json`, and that value must match `RuntimeReceipt.v0.trace_hash` from LabTrust-Gym. CertifyEdge applies the same canonical digest rules as LabTrust-Gym `compute_trace_hash`.

## Counterexample reasons

`release_before_qc`, `unauthorized_release`, `invalid_event_order`, `malformed_trace`.

| Invalid trace fixture | Expected reason |
|-----------------------|-----------------|
| `invalid_missing_qc_trace.json` | `release_before_qc` |
| `invalid_unauthorized_trace.json` | `unauthorized_release` |

## Simulation disclaimer

All artifacts in this chain describe LabTrust-Gym **simulation** runs and document protocol behavior on synthetic data, which means they support engineering review of the trust loop and remain simulation evidence distinct from clinical or production laboratory certification.
