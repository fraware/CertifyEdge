# PCS v0.1 handoff (LabTrust-Gym → CertifyEdge → Provability Fabric)

## Artifacts CertifyEdge produces

| Output | When |
|--------|------|
| `trace_certificate.json` | `emit-pcs-certificate` on any trace |
| `counterexample.json` | Rejected traces (default beside certificate, or `--counterexample-out`) |

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
- CertifyEdge uses the same canonical digest rules as `labtrust_gym.pcs.hash` / pcs-core.

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

Use `--release-mode` for CI and handoff builds.

## Simulation disclaimer

All artifacts describe LabTrust-Gym **simulation** runs only—not clinical or production laboratory certification.
