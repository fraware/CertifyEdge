# Quick start

This guide gets a development environment running on Linux, macOS, or Windows. For proof-carrying certificates, start with the [PCS guide](pcs-guide.md) after the steps below.

---

## Prerequisites

| Requirement | Notes |
|-------------|--------|
| **Rust 1.88.0** | Pinned in [`rust-toolchain.toml`](../rust-toolchain.toml) |
| **Git** | Clone from the repository root for all commands |
| **Bazelisk** (optional) | Runs the Bazel version in [`.bazelversion`](../.bazelversion) |
| **Python 3** (optional) | Profile validation and benchmark scripts; on Windows use `make PYTHON=python` |
| **Lean / Z3 / CVC5** (optional) | Only for full STL/SMT toolchains—not required for default tests |

**Windows:** Git Bash is recommended for `make` targets that run `scripts/*.sh`. Add `%USERPROFILE%\.cargo\bin` to `PATH`. See [PCS guide — Windows notes](pcs-guide.md#windows-notes).

---

## 1. Clone and install Rust

```bash
git clone https://github.com/fraware/CertifyEdge.git
cd CertifyEdge
```

Install Rust if needed ([rustup](https://rustup.rs/)):

```bash
rustup toolchain install 1.88.0
rustup default 1.88.0
rustup component add clippy rustfmt
```

Verify:

```bash
rustc --version
cargo --version
```

---

## 2. PCS smoke test (recommended)

```bash
cargo build -p certifyedge
make runbook
```

If that succeeds, the certificate engine is working. Continue in [pcs-guide.md](pcs-guide.md) for emit/verify, benchmarks, and release checks.

Optional: install the pcs-core CLI for schema validation:

```bash
git clone https://github.com/SentinelOps-CI/pcs-core.git ../pcs-core
pip install -e ../pcs-core/python
export PCS_CORE_PATH=../pcs-core
```

---

## 3. Full workspace build and test

```bash
cargo check --workspace
cargo test --workspace
cargo test -p integration_tests
cargo test -p certifyedge-integration
```

PCS-focused gate (matches most of CI for certificate changes):

```bash
export CERTIFYEDGE_SOURCE_COMMIT="$(git rev-parse HEAD)"
make pcs-test
```

Formatting (required before pull requests):

```bash
cargo fmt --all -- --check
```

---

## 4. Bazel (optional)

Install [Bazelisk](https://github.com/bazelbuild/bazelisk), then from the repository root:

```bash
bazel test --config=ci //tests/pipeline_integration:pipeline_integration
make bazel-pcs-test
```

Example build targets:

```bash
bazel build //services/stl-compiler:stl_compiler_lib
bazel build //cli:certifyedge
```

---

## Repository layout

```
CertifyEdge/
├── cli/                    # certifyedge binary (PCS)
├── services/
│   ├── labtrust-adapter/   # Trace parsing and temporal checks
│   ├── pcs-certificate/    # Profiles, emit, benchmarks
│   ├── stl-compiler/       # STL/SMT specification compiler
│   ├── smt-verifier/       # SMT verification service
│   └── certificate/        # Ed25519-signed certificates
├── templates/
│   ├── profiles/           # PCS property profile registry
│   ├── hospital_lab/       # Hospital-lab property templates
│   ├── tool_use/
│   └── computation/
├── benchmarks/certificates/  # PCS benchmark cases
├── schemas/pcs/            # Vendored pcs-core JSON schemas
├── pcs_registry/           # Artifact registry contributions
├── tests/
│   ├── certifyedge-integration/
│   └── pipeline_integration/
├── docs/                   # Guides and ADRs
└── scripts/                # Runbooks, sync, and validation
```

Generated benchmark outputs go under `benchmark_runs/` (gitignored).

---

## Continuous integration

GitHub Actions runs:

- `cargo fmt`, `cargo check`, and workspace tests
- PCS profile validation, certificate benchmarks, and pcs-core drift checks
- Optional LabTrust-Gym clean-checkout on `main` / `develop`
- Bazel PCS graph and pipeline integration test

Details: [ADR 002](adr/002-ci-integration-test.md). Release checklist: [PCS guide](pcs-guide.md#pre-release-checklist).

---

## Troubleshooting

**Build failures after dependency changes:**

```bash
cargo clean && cargo check --workspace
```

**Bazel cache issues:**

```bash
bazel clean --expunge
bazel test --config=ci //tests/pipeline_integration:pipeline_integration --test_output=errors
```

**Integration test details:**

```bash
cargo test -p integration_tests -- --nocapture
cargo test -p certifyedge-integration -- --nocapture
```

---

## Next steps

| Goal | Document |
|------|----------|
| Ship PCS certificates | [PCS guide](pcs-guide.md) |
| Cross-repo demo chain | [PCS handoff](pcs-handoff.md) |
| STL/SMT libraries | [STL compiler README](../services/stl-compiler/README.md) |
| Contribute | [CONTRIBUTING.md](../CONTRIBUTING.md) |

---

## License

Apache License 2.0 — see [LICENSE](../LICENSE).
