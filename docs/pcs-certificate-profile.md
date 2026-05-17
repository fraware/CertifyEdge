# CertifyEdge PCS certificate profile

Phase 2 artifact registry entry for the CertifyEdge producer. Copy `pcs_registry/TraceCertificate.v0.registry.json` into pcs-core `ArtifactRegistry.v0` when promoting protocol definitions.

## Producer

| Field | Value |
|-------|--------|
| Producer | CertifyEdge |
| Artifact type | TraceCertificate.v0 |
| Schema | `TraceCertificate.v0.schema.json` (pcs-core) |

## Input

| Input | Type | Notes |
|-------|------|--------|
| `trace.json` | LabTrust runtime trace | Consumed via `HandoffManifest.v0` (`runtime_to_certificate`) or `--trace` |
| Property profile | `hospital_lab.qc_release` (v0.1) | Template: `templates/hospital_lab/qc_release.stl` |

## Output

| Output | Type | Valid release status | Invalid status |
|--------|------|----------------------|----------------|
| `trace_certificate.json` | TraceCertificate.v0 | `CertificateChecked` | `Rejected` |

## Handoff

| Direction | `handoff_kind` | Manifest |
|-----------|----------------|----------|
| LabTrust-Gym → CertifyEdge | `runtime_to_certificate` | `labtrust_to_certifyedge_handoff.json` |
| CertifyEdge → LabTrust-Gym | `certificate_to_bundle` | `certifyedge_to_labtrust_handoff.json` |

## Counterexample behavior

When temporal checking fails, CertifyEdge emits `Rejected` with optional `counterexample_ref` pointing at a JSON counterexample file (`--counterexample-out` or default beside `--out`). Counterexamples are explained via `certifyedge explain-counterexample`.

## CLI

```bash
certifyedge emit-pcs-certificate \
  --handoff labtrust_to_certifyedge_handoff.json \
  --out trace_certificate.json \
  --handoff-out certifyedge_to_labtrust_handoff.json
```

Release mode (`--release-mode`) requires a real CertifyEdge `source_commit` and strict handoff provenance validation.
