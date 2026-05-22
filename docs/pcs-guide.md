# Proof-Carrying Science (PCS) in CertifyEdge

CertifyEdge is the **certificate producer** for [Proof-Carrying Science](https://github.com/SentinelOps-CI/pcs-core) v0.1. It reads runtime traces or handoff manifests, checks temporal properties, and writes versioned JSON certificates that downstream tools (LabTrust-Gym, Provability Fabric, Scientific Memory) can validate with the `pcs` CLI.

**Simulation only:** v0.1 certificates attest to LabTrust-Gym simulation traces. They are not clinical or production laboratory guarantees.

---

## What you need

| Tool | Purpose |
|------|---------|
| Rust (see `rust-toolchain.toml`) | Build `certifyedge` |
| [pcs-core](https://github.com/SentinelOps-CI/pcs-core) (optional locally) | `pcs validate`, schema drift checks, benchmark ingest |
| [LabTrust-Gym](https://github.com/fraware/LabTrust-Gym) (optional) | Full cross-repo release chain |

Install the PCS CLI when you have pcs-core checked out:

```bash
pip install -e ../pcs-core/python
```

---

## Property profiles

Workflows are driven by JSON files in `templates/profiles/`. Each profile maps inputs to a property template (`.stl` files under `templates/`) and an output certificate type.

| Profile ID | Input | Output certificate |
|------------|-------|-------------------|
| `hospital_lab.qc_release` | LabTrust trace | `TraceCertificate.v0` |
| `agent_tool_use.safety_v0` | Tool-use trace | `ToolUseCertificate.v0` |
| `scientific_computation.reproducibility_v0` | Computation receipts | `ComputationWitness.v0` |

Add a workflow by adding a profile JSON file and template—no changes to emit logic.

List and validate profiles:

```bash
make validate-profiles
# or
cargo run -p certifyedge -- profiles list
cargo run -p certifyedge -- profiles explain hospital_lab.qc_release
```

**Note on `.stl` files:** For PCS v0.1, files under `templates/hospital_lab/` are a **constrained temporal-property profile** (property id, allowed roles, comments)—not general signal temporal logic. See [labtrust-adapter.md](labtrust-adapter.md).

---

## Build and install the CLI

```bash
cargo build -p certifyedge
# Run via cargo (always works):
cargo run -p certifyedge -- --help
# Or put on PATH:
./scripts/install-certifyedge.sh
```

On Windows, if `cargo install` fails with SSL errors, use `./scripts/install-certifyedge.sh` instead.

---

## Local certificate workflow (single repo)

These commands use the hospital-lab demo trace. Make targets wrap the same calls.

```bash
# Check trace against property
cargo run -p certifyedge -- check-trace \
  --spec templates/hospital_lab/qc_release.stl \
  --trace tests/labtrust/valid_trace.json

# Emit certificate
cargo run -p certifyedge -- emit-pcs-certificate \
  --spec templates/hospital_lab/qc_release.stl \
  --trace tests/labtrust/valid_trace.json \
  --out trace_certificate.json

# Verify schema and digest
cargo run -p certifyedge -- verify-certificate trace_certificate.json

# Explain a counterexample (rejected traces)
cargo run -p certifyedge -- explain-counterexample counterexample.json
```

**Make shortcuts:** `make check-trace`, `make emit-certificate`, `make verify-certificate`, `make runbook`.

### Release mode

For CI and release artifacts, use `--release-mode` so `source_commit` is a real git SHA (not a placeholder):

```bash
export CERTIFYEDGE_SOURCE_COMMIT="$(git rev-parse HEAD)"
cargo run -p certifyedge -- --release-mode emit-pcs-certificate \
  --spec templates/hospital_lab/qc_release.stl \
  --trace tests/labtrust/valid_trace.json \
  --out trace_certificate.json
```

Release mode also runs `pcs validate` on the output when the `pcs` CLI is installed.

Validate with pcs-core manually:

```bash
pcs validate trace_certificate.json
```

---

## Handoff-driven emit (recommended for integrations)

Runtime producers send a `HandoffManifest.v0` (`handoff_kind: runtime_to_certificate`). CertifyEdge emits the certificate and an outbound `certificate_to_bundle` handoff.

```bash
export CERTIFYEDGE_SOURCE_COMMIT="$(git rev-parse HEAD)"
cargo run -p certifyedge -- --release-mode emit-pcs-certificate \
  --handoff labtrust_to_certifyedge_handoff.json \
  --profile-registry templates/profiles \
  --out trace_certificate.json \
  --summary-out certificate_summary.json \
  --handoff-out certifyedge_to_labtrust_handoff.json \
  --formal-facts-out certificate_formal_facts.json
```

Committed example handoff: `tests/fixtures/handoff/labtrust_to_certifyedge_handoff.json`.

Rejected traces still produce valid protocol artifacts (`status: Rejected`, counterexample, empty downstream `expected_outputs`). See [pcs-handoff.md](pcs-handoff.md) for the full cross-repo chain with LabTrust-Gym and Provability Fabric.

---

## Canonical fixtures

| Path | Purpose |
|------|---------|
| `tests/fixtures/labtrust-release/` | Canonical trace and certificate synced from pcs-core (`make sync-pcs-core-rc`) |
| `tests/fixtures/release-run/` | Full release artifact set from `make release-run` |
| `tests/labtrust/` | Golden traces for integration tests |

Do not regenerate canonical pcs-core fixtures locally—sync from upstream:

```bash
PCS_CORE_PATH=../pcs-core make sync-pcs-core-rc
make check-pcs-core-rc
```

Regenerate negative test fixtures only:

```bash
make fixtures
# or: cargo test -p certifyedge-integration write_fixtures -- --ignored --nocapture
```

---

## Certificate benchmarks

Benchmark cases live under `benchmarks/certificates/<suite>/` with `valid/` and `invalid/` directories. Each case has `case.json`, `handoff.json`, and input artifacts.

| Suite directory | Profile |
|-----------------|---------|
| `hospital_lab_qc_release/` | `hospital_lab.qc_release` |
| `tool_use_safety/` | `agent_tool_use.safety_v0` |
| `computation_reproducibility/` | `scientific_computation.reproducibility_v0` |

**Before running benchmarks**, set the source commit:

```bash
export CERTIFYEDGE_SOURCE_COMMIT="$(git rev-parse HEAD)"
```

| Command | What it does |
|---------|----------------|
| `make validate-certificate-benchmarks` | Validate case layout and drift |
| `make benchmark-certificates` | Run all three suites → `benchmark_runs/` |
| `make validate-benchmark-outputs` | Schema-check output trees |
| `make pcs-bench-producer` | Tool-use suite + strict pcs-bench ingest validation (CI default) |
| `make pcs-bench-producer-all-profiles` | All suites + ingest validation |
| `make validate-pcs-bench-ingest` | Validate ingest JSON for all suites |

Primary downstream artifact: `benchmark_runs/<suite>/pcs_bench_ingest.v0.json` (for [pcs-bench](https://github.com/SentinelOps-CI/pcs-core)).

Case layout details: [benchmarks/certificates/README.md](../benchmarks/certificates/README.md). Schema reference: [schemas/pcs/README.md](../schemas/pcs/README.md).

---

## Cross-repo release chain

The full v0.1 release gate runs LabTrust-Gym → CertifyEdge → attach certificate → (optionally) Provability Fabric and Scientific Memory.

From CertifyEdge (requires sibling `../LabTrust-Gym`, `pcs` and `labtrust` on PATH):

```bash
export PCS_DETERMINISTIC=1
make clean-checkout-certified   # LabTrust export + CertifyEdge + attach (CI default)
make clean-checkout             # Full chain including PF and Scientific Memory
```

Windows (PowerShell): `.\scripts\pcs-v01-clean-checkout.ps1`

Step-by-step commands: [pcs-handoff.md](pcs-handoff.md). LabTrust-Gym also documents the chain in its `docs/pcs_v01_clean_chain.md`.

---

## Vendored schemas and registry

Offline validation uses JSON schemas in `schemas/pcs/` (synced from pcs-core).

```bash
make sync-pcs-schemas
make sync-pcs-benchmark-schemas
make check-pcs-hash-vectors      # digest vectors vs pcs-core
make sync-pcs-registry           # refresh pcs_registry/*.registry.json from pcs-core
make check-pcs-registry          # registry contributions vs pcs-core (needs PCS_CORE_PATH)
```

Registry contributions: `pcs_registry/*.registry.json`.

Profile and handoff details: [pcs-certificate-profile.md](pcs-certificate-profile.md). Trace hashing: [labtrust-adapter.md](labtrust-adapter.md).

---

## Pre-release checklist

Run these from the repository root before tagging a release. Order matches CI.

```bash
export CERTIFYEDGE_SOURCE_COMMIT="$(git rev-parse HEAD)"
export PCS_CORE_PATH=../pcs-core   # if pcs-core is a sibling checkout

# 1. Core PCS gate (build, tests, profiles, benchmarks, optional pcs-core checks)
make pcs-test

# 2. Regenerate and validate all benchmark outputs + pcs-bench ingest
make pcs-bench-producer-all-profiles

# 3. Local runbook smoke
make runbook

# 4. With pcs-core: drift and registry
make check-pcs-core-rc
make check-pcs-hash-vectors
make sync-pcs-benchmark-schemas
make check-pcs-benchmark-schemas
make sync-pcs-registry
make check-pcs-registry

# 5. Cross-repo chain (needs LabTrust-Gym + pcs + labtrust)
export PCS_DETERMINISTIC=1
make clean-checkout-certified

# 6. Bazel PCS graph (optional, matches CI bazel job)
make bazel-pcs-test
```

**Contributors:** `make pcs-test` is the minimum before opening a PR that touches PCS code. CI runs the full sequence in [.github/workflows/ci.yml](../.github/workflows/ci.yml).

### Windows notes

- Use **Git Bash** for `make` targets that invoke `scripts/*.sh`, or run the equivalent `cargo` commands from this guide.
- If `python3` is not on PATH: `make PYTHON=python …` (PCS `make` targets honor `PYTHON`).
- Ensure `cargo` is on PATH when running shell scripts from Git Bash.

---

## Repository map (PCS)

| Path | Role |
|------|------|
| `cli/` | `certifyedge` binary |
| `services/labtrust-adapter/` | Trace parsing, hashing, temporal checks |
| `services/pcs-certificate/` | Profiles, emit, handoffs, repair hints, benchmarks |
| `templates/profiles/` | Property profile registry |
| `templates/hospital_lab/`, `tool_use/`, `computation/` | Property templates |
| `benchmarks/certificates/` | Benchmark case inputs |
| `benchmark_runs/` | Generated benchmark outputs (gitignored or committed per policy) |
| `schemas/pcs/` | Vendored JSON schemas |
| `pcs_registry/` | Artifact registry contributions |
| `scripts/pcs-*.sh` | Runbook, clean-checkout, benchmark validation |

---

## Further reading

| Document | Topic |
|----------|--------|
| [pcs-handoff.md](pcs-handoff.md) | Cross-repo commands and artifact contracts |
| [pcs-certificate-profile.md](pcs-certificate-profile.md) | Profile registry fields and registry entries |
| [labtrust-adapter.md](labtrust-adapter.md) | Trace format and hash rules |
| [adr/005-pcs-v01-labtrust-certification.md](adr/005-pcs-v01-labtrust-certification.md) | Architecture decision record |
