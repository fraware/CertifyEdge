# CertifyEdge PCS certificate profile

Phase 2 protocol profile for the CertifyEdge producer. Copy `pcs_registry/TraceCertificate.v0.registry.json` into pcs-core `ArtifactRegistry.v0` when promoting definitions.

## Profile

| Field | Value |
|-------|--------|
| **component** | CertifyEdge |
| **input artifact** | `trace.json` |
| **input handoff kind** | `runtime_to_certificate` |
| **property profile** | `hospital_lab.qc_release` |
| **output artifact** | `TraceCertificate.v0` (`trace_certificate.json`) |
| **output handoff kind** | `certificate_to_bundle` |
| **valid success status** | `CertificateChecked` |
| **valid failure status** | `Rejected` |

## Handoff manifests

| Direction | File | `handoff_kind` |
|-----------|------|----------------|
| LabTrust-Gym → CertifyEdge | `labtrust_to_certifyedge_handoff.json` | `runtime_to_certificate` |
| CertifyEdge → LabTrust-Gym | `certifyedge_to_labtrust_handoff.json` | `certificate_to_bundle` |

Property spec template: `templates/hospital_lab/qc_release.stl`.

## Counterexample behavior

When temporal checking fails:

1. Emit `TraceCertificate.v0` with `status = Rejected`.
2. Write `counterexample.json` (default beside `--out`, or `--counterexample-out`).
3. Set `counterexample_ref` on the certificate when a path is available.
4. Emit outbound `certificate_to_bundle` handoff with `invariants.status = Rejected` and **no** `science_claim_bundle.certified.json` in `expected_outputs` (downstream must not treat the bundle as admissible).

Explain counterexamples: `certifyedge explain-counterexample`.

## Release-mode provenance

With `--release-mode`:

- CertifyEdge `source_commit` must resolve to a non-placeholder git commit (`CERTIFYEDGE_SOURCE_COMMIT` or repo HEAD).
- Inbound `HandoffManifest.v0` is validated with vendored schema, digest, and `pcs validate` when the pcs-core CLI is installed.
- Outbound handoff and certificate artifacts are validated the same way before exit.
- `source_repo` must match the canonical CertifyEdge repository URL on verify/emit.

## CLI

```bash
certifyedge emit-pcs-certificate \
  --release-mode \
  --handoff labtrust_to_certifyedge_handoff.json \
  --out trace_certificate.json \
  --summary-out certificate_summary.json \
  --handoff-out certifyedge_to_labtrust_handoff.json
```

Legacy path (no handoff): `--spec`, `--trace`, `--out`.

## Registry

See `pcs_registry/TraceCertificate.v0.registry.json`. CI runs `pcs registry check-artifact` on emitted certificates when pcs-core is available.
