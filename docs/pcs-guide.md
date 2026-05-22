# Proof-Carrying Science (PCS) in CertifyEdge

CertifyEdge acts as the **certificate producer** for [Proof-Carrying Science](https://github.com/SentinelOps-CI/pcs-core) v0.1. The CLI reads runtime traces or handoff manifests, evaluates temporal properties registered under `templates/profiles/`, and writes versioned JSON certificates that downstream tools such as LabTrust-Gym, Provability Fabric, and Scientific Memory can validate with the `pcs` CLI.

Certificates produced under v0.1 attest to LabTrust-Gym simulation traces and therefore document protocol conformance on synthetic hospital-lab workflows, which readers should treat as engineering evidence for the trust loop and as distinct from clinical or production laboratory certification.

---

## What you need

| Tool | Purpose |
|------|---------|
| Rust (see `rust-toolchain.toml`) | Build `certifyedge` |
| [pcs-core](https://github.com/SentinelOps-CI/pcs-core) (optional locally) | `pcs validate`, schema drift checks, benchmark ingest |
| [LabTrust-Gym](https://github.com/fraware/LabTrust-Gym) (optional) | Full cross-repo release chain |

Install the PCS CLI after you clone pcs-core.

```bash
pip install -e ../pcs-core/python
```

---

## Property profiles

Workflows are driven by JSON files in `templates/profiles/`. Each profile maps inputs to a property template under `templates/` and to an output certificate type.

| Profile ID | Input | Output certificate |
|------------|-------|-------------------|
| `hospital_lab.qc_release` | LabTrust trace | `TraceCertificate.v0` |
| `agent_tool_use.safety_v0` | Tool-use trace | `ToolUseCertificate.v0` |
| `scientific_computation.reproducibility_v0` | Computation receipts | `ComputationWitness.v0` |

You extend the system by adding a profile JSON file and a matching template, and the emit pipeline registers the new workflow through the same core emit path used by existing profiles.

List and validate profiles with `make validate-profiles`, or invoke the CLI directly.

```bash
cargo run -p certifyedge -- profiles list
cargo run -p certifyedge -- profiles explain hospital_lab.qc_release
```

Files under `templates/hospital_lab/` implement a **constrained temporal-property profile** for v0.1, carrying property identifiers, allowed roles, and comments, and they function as hospital-lab profile documents that stand apart from general signal temporal logic specifications. The [LabTrust adapter](labtrust-adapter.md) explains parsing and hashing rules in full.

---

## Build and install the CLI

```bash
cargo build -p certifyedge
cargo run -p certifyedge -- --help
./scripts/install-certifyedge.sh
```

On Windows, `./scripts/install-certifyedge.sh` is the dependable path when `cargo install` fails with SSL errors against crates.io.

---

## Local certificate workflow (single repo)

The commands below use the hospital-lab demo trace, and the Makefile exposes the same operations through `make check-trace`, `make emit-certificate`, `make verify-certificate`, and `make runbook`.

```bash
cargo run -p certifyedge -- check-trace \
  --spec templates/hospital_lab/qc_release.stl \
  --trace tests/labtrust/valid_trace.json

cargo run -p certifyedge -- emit-pcs-certificate \
  --spec templates/hospital_lab/qc_release.stl \
  --trace tests/labtrust/valid_trace.json \
  --out trace_certificate.json

cargo run -p certifyedge -- verify-certificate trace_certificate.json

cargo run -p certifyedge -- explain-counterexample counterexample.json
```

### Release mode

Continuous integration and release builds should pass `--release-mode` so `source_commit` resolves to a real git SHA from the CertifyEdge repository.

```bash
export CERTIFYEDGE_SOURCE_COMMIT="$(git rev-parse HEAD)"
cargo run -p certifyedge -- --release-mode emit-pcs-certificate \
  --spec templates/hospital_lab/qc_release.stl \
  --trace tests/labtrust/valid_trace.json \
  --out trace_certificate.json
```

Release mode invokes `pcs validate` on the written file when the `pcs` CLI is installed. You can repeat validation manually with `pcs validate trace_certificate.json`.

---

## Handoff-driven emit (recommended for integrations)

Runtime producers supply a `HandoffManifest.v0` with `handoff_kind` set to `runtime_to_certificate`, and CertifyEdge responds with the certificate plus an outbound `certificate_to_bundle` handoff for downstream bundle assembly.

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

A committed example handoff lives at `tests/fixtures/handoff/labtrust_to_certifyedge_handoff.json`. Rejected traces still yield protocol-valid artifacts with `status` set to `Rejected`, a counterexample when the profile defines one, and empty `expected_outputs` on the outbound handoff so downstream systems defer bundle admissibility until a checked certificate arrives. The [cross-repo handoff](pcs-handoff.md) document lists LabTrust-Gym and Provability Fabric steps in execution order.

---

## Canonical fixtures

| Path | Purpose |
|------|---------|
| `tests/fixtures/labtrust-release/` | Canonical trace and certificate synced from pcs-core (`make sync-pcs-core-rc`) |
| `tests/fixtures/release-run/` | Full release artifact set from `make release-run` |
| `tests/labtrust/` | Golden traces for integration tests |

Canonical pcs-core fixtures should be refreshed from upstream with `PCS_CORE_PATH=../pcs-core make sync-pcs-core-rc` followed by `make check-pcs-core-rc`. Negative test fixtures alone may be regenerated with `make fixtures` or `cargo test -p certifyedge-integration write_fixtures -- --ignored --nocapture`.

---

## Certificate benchmarks

Benchmark cases live under `benchmarks/certificates/<suite>/` in `valid/` and `invalid/` directories, and each case includes `case.json`, `handoff.json`, and the input artifacts the handoff references.

| Suite directory | Profile |
|-----------------|---------|
| `hospital_lab_qc_release/` | `hospital_lab.qc_release` |
| `tool_use_safety/` | `agent_tool_use.safety_v0` |
| `computation_reproducibility/` | `scientific_computation.reproducibility_v0` |

Set the source commit before you generate benchmarks.

```bash
export CERTIFYEDGE_SOURCE_COMMIT="$(git rev-parse HEAD)"
```

| Command | What it does |
|---------|----------------|
| `make validate-certificate-benchmarks` | Validate case layout and drift |
| `make benchmark-certificates` | Run all three suites → `benchmark_runs/` |
| `make validate-benchmark-outputs` | Schema-check output trees |
| `make pcs-bench-producer` | Tool-use suite plus strict pcs-bench ingest validation (CI default) |
| `make pcs-bench-producer-all-profiles` | All suites plus ingest validation |
| `make validate-pcs-bench-ingest` | Validate ingest JSON for all suites |

The primary downstream bundle is `benchmark_runs/<suite>/pcs_bench_ingest.v0.json`, which [pcs-bench](https://github.com/SentinelOps-CI/pcs-core) consumes. Case layout appears in [benchmarks/certificates/README.md](../benchmarks/certificates/README.md), and schema names appear in [schemas/pcs/README.md](../schemas/pcs/README.md).

---

## Cross-repo release chain

The v0.1 release gate exercises LabTrust-Gym export, CertifyEdge emission, certificate attach, and optionally Provability Fabric and Scientific Memory when you run the extended target. From this repository you need a sibling `../LabTrust-Gym` checkout together with `pcs` and `labtrust` on your path.

```bash
export PCS_DETERMINISTIC=1
make clean-checkout-certified
make clean-checkout
```

On Windows you may invoke `.\scripts\pcs-v01-clean-checkout.ps1`. Step-by-step commands appear in [pcs-handoff.md](pcs-handoff.md), and LabTrust-Gym maintains parallel documentation in `docs/pcs_v01_clean_chain.md`.

---

## Vendored schemas and registry

Offline validation uses JSON schemas under `schemas/pcs/` that track pcs-core. Sync and drift targets include `make sync-pcs-schemas`, `make sync-pcs-benchmark-schemas`, `make check-pcs-hash-vectors`, `make sync-pcs-registry`, and `make check-pcs-registry` when `PCS_CORE_PATH` points at a pcs-core checkout. Registry contributions live under `pcs_registry/*.registry.json`. Profile fields and handoff kinds are documented in [pcs-certificate-profile.md](pcs-certificate-profile.md), and trace hashing appears in [labtrust-adapter.md](labtrust-adapter.md).

---

## Pre-release checklist

Run these commands from the repository root before tagging a release, in the same order continuous integration uses.

```bash
export CERTIFYEDGE_SOURCE_COMMIT="$(git rev-parse HEAD)"
export PCS_CORE_PATH=../pcs-core

make pcs-test
make pcs-bench-producer-all-profiles
make runbook
make check-pcs-core-rc
make check-pcs-hash-vectors
make sync-pcs-benchmark-schemas
make check-pcs-benchmark-schemas
make sync-pcs-registry
make check-pcs-registry
export PCS_DETERMINISTIC=1
make clean-checkout-certified
make bazel-pcs-test
```

`make pcs-test` is the minimum gate before a pull request that touches PCS code. The workflow file [.github/workflows/ci.yml](../.github/workflows/ci.yml) runs the same sequence on GitHub-hosted runners.

### Windows notes

Use Git Bash for `make` targets that call `scripts/*.sh`, or translate each step to the equivalent `cargo` and Python commands from this guide. Set `PYTHON=python` when `python3` is missing from your path, because every PCS `make` target honors the `PYTHON` variable. Ensure `cargo` appears on `PATH` inside the same shell session that runs the scripts.

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
| `benchmark_runs/` | Generated benchmark outputs (gitignored) |
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
