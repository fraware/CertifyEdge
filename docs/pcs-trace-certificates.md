# Trace certificates (LabTrust)

Build, emit, verify, benchmarks, and the release checklist are covered in the [PCS guide](pcs-guide.md). This page records **LabTrust-specific** details for `TraceCertificate.v0`, while tool-use and computation certificates follow the same CLI with different profiles as described in [pcs-certificate-profile.md](pcs-certificate-profile.md).

## Certificate fields

| Field | Role |
|-------|------|
| `trace_hash` | PCS digest of the LabTrust trace (matches `RuntimeReceipt.v0.trace_hash`) |
| `spec_hash` | PCS digest of the property template and `property_id` |
| `property_id` | e.g. `hospital_lab.qc_release` |
| `checker` / `checker_version` | `CertifyEdge` and crate version |
| `status` | `CertificateChecked`, `Rejected`, `CertificatePending`, or `Stale` (pcs-core strings) |
| `counterexample_ref` | `null` when checked; path when rejected |
| `signature_or_digest` | PCS canonical hash over the certificate body |

## Canonical pcs-core fixtures

Files synced from [pcs-core](https://github.com/SentinelOps-CI/pcs-core) `examples/labtrust-release/` into `tests/fixtures/labtrust-release/` include the following.

| File | Role |
|------|------|
| `trace.json` | Canonical LabTrust runtime trace |
| `trace_certificate.json` | Canonical `TraceCertificate.v0` (`CertificateChecked`) |
| `PCS_CORE_RC_MANIFEST.json` | Copy of pcs-core release manifest |

```bash
PCS_CORE_PATH=../pcs-core make sync-pcs-core-rc
make check-pcs-core-rc
```

Verify against the canonical trace with the command below.

```bash
cargo run -p certifyedge -- verify-certificate \
  tests/fixtures/labtrust-release/trace_certificate.json \
  --trace tests/fixtures/labtrust-release/trace.json
```

Release-mode verify enforces `source_repo` and requires `source_commit` values that satisfy the release policy, including real repository revisions in place of placeholder commits.

## Release-run fixtures

The directory `tests/fixtures/release-run/` holds a full artifact set produced by `make release-run`. Provenance appears in `RELEASE_FIXTURE_MANIFEST.json`, and the `certifyedge_commit` field must match the certificate `source_commit`.

## Release mode rules

Release mode resolves `source_commit` from `CERTIFYEDGE_SOURCE_COMMIT` or from `git rev-parse HEAD` inside this repository. The gate declines `local-dev`, all-zero SHAs, and the forty-character test patterns `aaaa…`, `bbbb…`, and `cccc…`. When LabTrust-Gym is discoverable, release mode also declines a `CERTIFYEDGE_SOURCE_COMMIT` that matches LabTrust-Gym HEAD while differing from CertifyEdge HEAD. Emit runs `pcs validate` on the output when the `pcs` CLI is installed. Development builds that omit `--release-mode` may write a zero `source_commit` when git returns an empty revision.
