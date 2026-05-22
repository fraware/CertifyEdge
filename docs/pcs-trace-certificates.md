# Trace certificates (LabTrust)

> **Start here:** [PCS guide](pcs-guide.md) covers build, emit, verify, benchmarks, and release checklist.

This page documents **LabTrust-specific** details for `TraceCertificate.v0`. Tool-use and computation certificates use the same CLI with different profiles—see [pcs-certificate-profile.md](pcs-certificate-profile.md).

## Certificate fields

| Field | Role |
|-------|------|
| `trace_hash` | PCS digest of the LabTrust trace (must match `RuntimeReceipt.v0.trace_hash`) |
| `spec_hash` | PCS digest of the property template and `property_id` |
| `property_id` | e.g. `hospital_lab.qc_release` |
| `checker` / `checker_version` | `CertifyEdge` and crate version |
| `status` | `CertificateChecked`, `Rejected`, `CertificatePending`, or `Stale` (pcs-core strings) |
| `counterexample_ref` | `null` when checked; path when rejected |
| `signature_or_digest` | PCS canonical hash over the certificate body |

## Canonical pcs-core fixtures

Synced from [pcs-core](https://github.com/SentinelOps-CI/pcs-core) `examples/labtrust-release/` into `tests/fixtures/labtrust-release/`:

| File | Role |
|------|------|
| `trace.json` | Canonical LabTrust runtime trace |
| `trace_certificate.json` | Canonical `TraceCertificate.v0` (`CertificateChecked`) |
| `PCS_CORE_RC_MANIFEST.json` | Copy of pcs-core release manifest |

```bash
PCS_CORE_PATH=../pcs-core make sync-pcs-core-rc
make check-pcs-core-rc
```

Verify against the canonical trace:

```bash
cargo run -p certifyedge -- verify-certificate \
  tests/fixtures/labtrust-release/trace_certificate.json \
  --trace tests/fixtures/labtrust-release/trace.json
```

Release-mode verify enforces `source_repo` and rejects placeholder `source_commit` values.

## Release-run fixtures

Non-canonical full artifact set: `tests/fixtures/release-run/` (built with `make release-run`). Provenance is in `RELEASE_FIXTURE_MANIFEST.json` (`certifyedge_commit` must match certificate `source_commit`).

## Release mode rules

- `source_commit` from `CERTIFYEDGE_SOURCE_COMMIT` or `git rev-parse HEAD` inside this repository.
- Rejects placeholders: `local-dev`, all-zero SHAs, and test patterns `aaaa…`, `bbbb…`, `cccc…` (40 hex digits).
- If LabTrust-Gym is discoverable, rejects a `CERTIFYEDGE_SOURCE_COMMIT` that equals LabTrust-Gym HEAD but not CertifyEdge HEAD.
- Runs `pcs validate` on output when `pcs` is available.

Without `--release-mode`, a zero `source_commit` placeholder may be used when no git commit is available.
