# PCS Trace Certificates

CertifyEdge v0.1 emits **TraceCertificate.v0** artifacts defined in [pcs-core](https://github.com/SentinelOps-CI/pcs-core). Certificates bind a LabTrust trace hash to a temporal property spec hash and record whether the checker accepted or rejected the trace.

## Commands

```bash
certifyedge check-trace \
  --spec templates/hospital_lab/qc_release.stl \
  --trace tests/labtrust/valid_trace.json

certifyedge emit-pcs-certificate \
  --spec templates/hospital_lab/qc_release.stl \
  --trace tests/labtrust/valid_trace.json \
  --out trace_certificate.json

certifyedge verify-certificate trace_certificate.json \
  --trace tests/labtrust/valid_trace.json

certifyedge explain-counterexample tests/labtrust/expected_missing_qc_counterexample.json
```

## Certificate fields

| Field | Role |
|-------|------|
| `trace_hash` | PCS digest of the LabTrust trace (must match `RuntimeReceipt.v0.trace_hash`) |
| `spec_hash` | PCS digest of the STL property spec and `property_id` |
| `property_id` | e.g. `hospital_lab.qc_release` |
| `checker` / `checker_version` | `CertifyEdge` and crate version |
| `status` | `CertificateChecked` or `Rejected` |
| `counterexample_ref` | `null` when checked; path when rejected |
| `signature_or_digest` | PCS canonical hash over the certificate body |

## Status values

Use pcs-core status strings only: `CertificateChecked`, `Rejected`, `CertificatePending`, `Stale`.

## pcs-core alignment

`TraceCertificate.v0` field names and `signature_or_digest` rules match [pcs-core](https://github.com/SentinelOps-CI/pcs-core). Validate emitted artifacts with:

```bash
pcs validate trace_certificate.json
```

## Handoff to Provability Fabric

Provability Fabric verifies that `trace_hash` matches the science-claim bundle’s runtime receipt and that `signature_or_digest` is consistent with pcs-core canonical hashing.

## Simulation disclaimer

Certificates attest to **simulation traces** from LabTrust-Gym. They are not clinical or production laboratory guarantees.
