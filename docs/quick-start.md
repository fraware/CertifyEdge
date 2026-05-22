# Quick start

This guide walks through a minimal development environment on Linux, macOS, or Windows. After you can build the workspace, continue with the [PCS guide](pcs-guide.md) if your goal is proof-carrying certificates.

---

## Prerequisites

| Requirement | Notes |
|-------------|--------|
| **Rust 1.88.0** | Pinned in [`rust-toolchain.toml`](../rust-toolchain.toml) |
| **Git** | Run all commands from the repository root |
| **Bazelisk** (optional) | Runs the Bazel version in [`.bazelversion`](../.bazelversion) |
| **Python 3** (optional) | Profile validation and benchmark scripts; on Windows use `make PYTHON=python` |
| **Lean / Z3 / CVC5** (optional) | Full STL/SMT toolchains; default tests use the in-process test compiler configuration |

Windows developers typically use Git Bash for `make` targets that invoke `scripts/*.sh`, add `%USERPROFILE%\.cargo\bin` to `PATH`, and follow the [PCS guide Windows notes](pcs-guide.md#pre-release-checklist) when shell scripts call Python or Cargo.

---

## 1. Clone and install Rust

```bash
git clone https://github.com/fraware/CertifyEdge.git
cd CertifyEdge
```

Install Rust through [rustup](https://rustup.rs/) when it is missing on your machine.

```bash
rustup toolchain install 1.88.0
rustup default 1.88.0
rustup component add clippy rustfmt
```

Confirm the toolchain with `rustc --version` and `cargo --version` before you proceed.

---

## 2. PCS smoke test (recommended)

```bash
cargo build -p certifyedge
make runbook
```

A successful runbook means the certificate engine can check traces, emit certificates, verify digests, and exercise counterexample explanation against the bundled fixtures. The [PCS guide](pcs-guide.md) continues with emit and verify commands, benchmark generation, and release checks.

Optional schema validation uses the pcs-core CLI. Clone pcs-core beside this repository and install the Python package.

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

Certificate-related changes should also pass the PCS gate that aligns with most continuous integration steps for profiles and benchmarks.

```bash
export CERTIFYEDGE_SOURCE_COMMIT="$(git rev-parse HEAD)"
make pcs-test
```

Pull requests must pass `cargo fmt --all -- --check` before merge.

---

## 4. Bazel (optional)

Install [Bazelisk](https://github.com/bazelbuild/bazelisk), then run the pipeline integration test and the PCS graph test from the repository root.

```bash
bazel test --config=ci //tests/pipeline_integration:pipeline_integration
make bazel-pcs-test
```

Example build targets include `//services/stl-compiler:stl_compiler_lib` and `//cli:certifyedge`.

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

Generated benchmark outputs are written under `benchmark_runs/`, which is listed in `.gitignore`.

---

## Continuous integration

GitHub Actions runs formatting, workspace checks, PCS profile validation, certificate benchmarks, pcs-core drift checks, an optional LabTrust-Gym clean-checkout on mainline branches, and a Bazel job that builds the PCS graph plus the pipeline integration test. [ADR 002](adr/002-ci-integration-test.md) describes the jobs, and the [PCS guide pre-release checklist](pcs-guide.md#pre-release-checklist) lists the local commands maintainers run before a tag.

---

## Troubleshooting

When dependency upgrades leave the tree in a confusing state, `cargo clean && cargo check --workspace` usually restores a predictable build. Bazel users who see stale analysis can run `bazel clean --expunge` followed by `bazel test --config=ci //tests/pipeline_integration:pipeline_integration --test_output=errors`. Integration tests accept `--nocapture` on both Cargo targets when you need full stdout from failing cases.

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
