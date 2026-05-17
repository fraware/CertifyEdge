# PCS Trace Certificates

CertifyEdge v0.1 emits **TraceCertificate.v0** artifacts defined in [pcs-core](https://github.com/SentinelOps-CI/pcs-core). Certificates bind a LabTrust trace hash to a temporal property spec hash and record whether the checker accepted or rejected the trace.

## Property templates (not general STL)

For v0.1, files under `templates/hospital_lab/*.stl` are parsed as a **constrained LabTrust temporal-property profile** (property id, allowed release roles, comments). They are **not** a full general-purpose signal temporal logic (STL) implementation. The historical `.stl` suffix marks the hospital-lab profile only.

## CLI

The runbook commands are implemented in the `certifyedge` binary (`cli/` crate). Command names are defined as constants in `cli/src/lib.rs` (`CMD_CHECK_TRACE`, `CMD_EMIT_PCS_CERTIFICATE`, etc.) for code search and stable runbooks.

Build (does **not** put `certifyedge` on your shell `PATH`):

```bash
cargo build -p certifyedge
# binary: target/debug/certifyedge.exe (Windows) or target/debug/certifyedge (Unix)
```

Run commands in one of these ways:

**Option A — `cargo run` (recommended, always works):**

```bash
cargo run -p certifyedge -- check-trace \
  --spec templates/hospital_lab/qc_release.stl \
  --trace tests/labtrust/valid_trace.json

cargo run -p certifyedge -- emit-pcs-certificate \
  --spec templates/hospital_lab/qc_release.stl \
  --trace tests/labtrust/valid_trace.json \
  --out trace_certificate.json

cargo run -p certifyedge -- verify-certificate trace_certificate.json

# Optional: also assert trace_hash matches a trace file
cargo run -p certifyedge -- verify-certificate trace_certificate.json \
  --trace tests/labtrust/valid_trace.json

cargo run -p certifyedge -- explain-counterexample counterexample.json
```

**Option B — built binary (Git Bash / Linux / macOS):**

```bash
./target/debug/certifyedge.exe check-trace \
  --spec templates/hospital_lab/qc_release.stl \
  --trace tests/labtrust/valid_trace.json
```

**Option C — wrapper script:**

```bash
./scripts/certifyedge.sh check-trace --spec templates/hospital_lab/qc_release.stl --trace tests/labtrust/valid_trace.json
```

**Option D — install onto `PATH`:**

```bash
# Recommended on Windows/Git Bash (reuses workspace build; no crates.io fetch):
./scripts/install-certifyedge.sh

# Or copy the binary yourself:
# cp target/debug/certifyedge.exe ~/.cargo/bin/
```

If `cargo install --path cli --force` fails with `CRYPT_E_NO_REVOCATION_CHECK` / SSL errors on Windows, either use the script above or:

```bash
export CARGO_HTTP_CHECK_REVOKE=false
cargo install --path cli --force --offline
```

(`--offline` only works after `cargo build -p certifyedge` has populated the local cache.)

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

## Release mode

Use `--release-mode` (or `CERTIFYEDGE_RELEASE_MODE=1`) when emitting artifacts for CI or handoff:

- `source_commit` must resolve from `CERTIFYEDGE_SOURCE_COMMIT` or `git rev-parse HEAD` (never the all-zero placeholder).
- `emit-pcs-certificate` runs `pcs validate` on the output and fails if validation fails or `pcs` is missing.

Local development without `--release-mode` may use the zero `source_commit` placeholder when no git commit is available.

## pcs-core alignment

`TraceCertificate.v0` field names and `signature_or_digest` rules match [pcs-core](https://github.com/SentinelOps-CI/pcs-core). `emit-pcs-certificate` validates the written file with `pcs validate` in release mode. You can also validate manually:

```bash
pcs validate trace_certificate.json
```

`certificate.trace_hash` must equal the LabTrust trace document’s `trace_hash` (and `RuntimeReceipt.v0.trace_hash`).

## Handoff to Provability Fabric

Provability Fabric verifies that `trace_hash` matches the science-claim bundle’s runtime receipt and that `signature_or_digest` is consistent with pcs-core canonical hashing.

## Simulation disclaimer

Certificates attest to **simulation traces** from LabTrust-Gym. They are not clinical or production laboratory guarantees.
