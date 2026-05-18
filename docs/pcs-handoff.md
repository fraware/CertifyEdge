# PCS v0.1 handoff (LabTrust-Gym → CertifyEdge → Provability Fabric)

## Clean-checkout chain (release gate)

PCS v0.1 is **release-ready** when the full cross-repo chain succeeds. Canonical commands are documented in [LabTrust-Gym `docs/pcs_v01_clean_chain.md`](https://github.com/fraware/LabTrust-Gym/blob/main/docs/pcs_v01_clean_chain.md).

From **CertifyEdge** (sibling `../LabTrust-Gym`, `pcs` and `labtrust` on `PATH`):

```bash
export PCS_DETERMINISTIC=1
make clean-checkout                    # full chain (PF + Scientific Memory)
make clean-checkout-certified          # LabTrust export + CertifyEdge + attach only
```

Or:

```bash
./scripts/pcs-v01-clean-checkout.sh
./scripts/pcs-v01-clean-checkout.sh --through-certified
```

On Windows (Git Bash for `--through-certified`):

```powershell
$env:PCS_DETERMINISTIC = "1"
.\scripts\pcs-v01-clean-checkout.ps1
```

### Manual chain (exact runbook commands)

Run from **LabTrust-Gym** repo root unless noted.

**LabTrust-Gym**

```bash
PCS_DETERMINISTIC=1 labtrust run-demo qc-release
PCS_DETERMINISTIC=1 labtrust run-demo qc-release-invalid-missing-qc
PCS_DETERMINISTIC=1 labtrust run-demo qc-release-invalid-unauthorized

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

Clean-chain scripts (`run_pcs_v01_clean_chain.sh`, `make release-run`) write `labtrust_to_certifyedge_handoff.json` into the staging workdir automatically (and mirror `handoff_to_certifyedge.json` for release fixtures).

**CertifyEdge** (from `CERTIFYEDGE_ROOT` or set `CERTIFYEDGE_SPEC` to an absolute path)

Legacy (explicit spec + trace):

```bash
certifyedge emit-pcs-certificate \
  --spec templates/hospital_lab/qc_release.stl \
  --trace trace.json \
  --out trace_certificate.json
pcs validate trace_certificate.json
certifyedge verify-certificate trace_certificate.json --trace trace.json
```

### Phase 2: `HandoffManifest.v0` (preferred)

Canonical committed input fixture: `tests/fixtures/handoff/labtrust_to_certifyedge_handoff.json` (synced from RC trace via `make write-handoff-fixture`).

```bash
certifyedge --release-mode emit-pcs-certificate \
  --handoff labtrust_to_certifyedge_handoff.json \
  --out trace_certificate.json \
  --handoff-out certifyedge_to_labtrust_handoff.json
certifyedge verify-certificate trace_certificate.json --trace trace.json
```

CertifyEdge validates:

- `handoff_kind = runtime_to_certificate`, `to_component = CertifyEdge`
- input `trace.json` file hash and `invariants.trace_hash`
- `invariants.property_id` matches the hospital-lab spec template
- release-mode rejects placeholder handoff `source_commit`
- outbound `certificate_to_bundle` handoff with `certificate_id`, `trace_hash`, `status = CertificateChecked`

See [pcs-certificate-profile.md](pcs-certificate-profile.md) and `pcs_registry/TraceCertificate.v0.registry.json`.

**LabTrust-Gym (attach)**

```bash
labtrust attach-certificate \
  --bundle science_claim_bundle.pending.json \
  --certificate trace_certificate.json \
  --out science_claim_bundle.certified.json
pcs validate science_claim_bundle.certified.json
```

**Provability Fabric**

```bash
pf verify science-claim science_claim_bundle.certified.json \
  --out verification_result.json
pcs validate verification_result.json

pf sign science-claim science_claim_bundle.certified.json \
  --out signed_science_claim_bundle.json
pcs validate signed_science_claim_bundle.json
pf inspect science-claim signed_science_claim_bundle.json
```

**Scientific Memory** (positional `just` args, not `BUNDLE=` / `CLAIM_ID=`)

```bash
cd ../scientific-memory
just pcs-import-bundle ../LabTrust-Gym/signed_science_claim_bundle.json
just pcs-render-claim claim-pcs-qc-release-v0.1
```

Post-chain validation (LabTrust-Gym):

```bash
python examples/pcs_qc_release/scripts/verify_pcs_v01_chain.py --work . --stage full
```

### Environment overrides

| Variable | Role |
|----------|------|
| `PCS_DETERMINISTIC` | `1` for golden demos |
| `LABTRUST_GYM_ROOT` | Path to LabTrust-Gym (default `../LabTrust-Gym`) |
| `CERTIFYEDGE_ROOT` | Path to CertifyEdge (default: this repo) |
| `CERTIFYEDGE_BIN` | Default `$CERTIFYEDGE_ROOT/scripts/certifyedge.sh` |
| `PCS_CHAIN_WORK` | Artifact directory (LabTrust repo root by default) |
| `PF_BIN` | Provability Fabric CLI (`pf`) |
| `SCIENTIFIC_MEMORY_ROOT` | Sibling `scientific-memory` |

## Artifacts CertifyEdge produces

| Output | When |
|--------|------|
| `trace_certificate.json` | `emit-pcs-certificate` on any trace |
| `counterexample.json` | Rejected traces (default beside certificate, or `--counterexample-out`) |

Committed release fixtures: `tests/fixtures/labtrust-release/` (`trace.json`, CLI-generated `trace_certificate.json`, invalid traces and counterexamples; see [pcs-trace-certificates.md](pcs-trace-certificates.md)).

## TraceCertificate.v0 contract

```json
{
  "certificate_id": "cert-trace-...",
  "schema_version": "v0",
  "trace_hash": "sha256:...",
  "spec_hash": "sha256:...",
  "property_id": "hospital_lab.qc_release",
  "checker": "CertifyEdge",
  "checker_version": "0.1.0",
  "status": "CertificateChecked",
  "counterexample_ref": null,
  "created_at": "2026-05-16T12:00:00Z",
  "producer": "CertifyEdge",
  "producer_version": "0.1.0",
  "source_repo": "https://github.com/fraware/CertifyEdge",
  "source_commit": "<git sha, never all-zero in release mode>",
  "signature_or_digest": "sha256:..."
}
```

Rejected traces use `"status": "Rejected"` and a non-null `counterexample_ref`.

## Hash compatibility (critical)

- `certificate.trace_hash` **must equal** `trace.json` → `trace_hash`.
- That value **must equal** LabTrust `RuntimeReceipt.v0` → `trace_hash`.
- CertifyEdge uses the same canonical digest rules as `labtrust_gym.pcs.trace.compute_trace_hash` (body includes `schema_version`, `version`, `run_id`, `sample_id`, `event_hashes`).

## Counterexample shape

```json
{
  "counterexample_id": "cx-...",
  "property_id": "hospital_lab.no_release_before_qc",
  "sample_id": "PCS-SAMPLE-002",
  "violating_event_id": "...",
  "reason": "release_before_qc",
  "expected_precondition": "...",
  "actual_trace_fragment": [ ... ]
}
```

Reason codes: `release_before_qc`, `unauthorized_release`, `invalid_event_order`, `malformed_trace`.

Invalid-trace `check-trace` (from CertifyEdge, `qc_release.stl` spec):

| Trace | Expected `reason` |
|-------|-------------------|
| `invalid_missing_qc_trace.json` | `release_before_qc` |
| `invalid_unauthorized_trace.json` | `unauthorized_release` |

## Property templates

| File | Property ID |
|------|-------------|
| `templates/hospital_lab/qc_release.stl` | `hospital_lab.qc_release` |
| `templates/hospital_lab/no_release_before_qc.stl` | `hospital_lab.no_release_before_qc` |
| `templates/hospital_lab/authorized_release_only.stl` | `hospital_lab.authorized_release_only` |

These are a **LabTrust temporal-property profile**, not full STL.

## Validation

1. In-process: vendored pcs-core JSON Schema (`schemas/pcs/`).
2. External (CI / release): `pcs validate trace_certificate.json` from pcs-core.

Use `--release-mode` for CI and handoff builds. In release mode, `CERTIFYEDGE_SOURCE_COMMIT` must be a non-zero git SHA (or omit it and run inside a git checkout).

## Runbook commands

```bash
certifyedge check-trace --spec templates/hospital_lab/qc_release.stl --trace trace.json
certifyedge emit-pcs-certificate --spec templates/hospital_lab/qc_release.stl --trace trace.json --out trace_certificate.json
certifyedge verify-certificate trace_certificate.json --trace trace.json
certifyedge explain-counterexample counterexample.json
certifyedge --release-mode emit-pcs-certificate ...   # CI / release artifacts
```

Local CertifyEdge-only runbook:

```bash
make runbook
PCS_RUNBOOK_RELEASE=1 ./scripts/pcs-runbook.sh
```

Snake_case aliases (`check_trace`, `emit_pcs_certificate`, …) are accepted.

## Simulation disclaimer

All artifacts describe LabTrust-Gym **simulation** runs only—not clinical or production laboratory certification.
