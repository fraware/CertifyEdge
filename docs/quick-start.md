# CertifyEdge quick start

## Overview

This project helps you work with **signal temporal logic (STL)** specifications, generate **SMT-LIB**, optionally connect to **Lean** and SMT solvers, and produce **signed certificates**. This guide covers a minimal development setup.

## Prerequisites

### Machine

- **OS:** Linux, macOS, or Windows (Windows often works best with WSL2 for tool parity)
- **RAM / disk:** Enough to build Rust; Bazel first runs can be large

### Software

- **Rust:** version pinned in [rust-toolchain.toml](../rust-toolchain.toml)
- **Cargo:** run all commands from the repository root unless noted
- **Bazel:** optional; version pinned in [.bazelversion](../.bazelversion), typically installed through [Bazelisk](https://github.com/bazelbuild/bazelisk)

### Optional

- **Node.js:** only if you add or build a frontend under `web/`
- **Lean, Z3, CVC5:** when you want full compilation paths (see `CompilerConfig::for_tests_without_external_tools()` in `stl-compiler` for a configuration that skips external binaries)
- **Docker:** only for container-based workflows you define

## Installation

### 1. Clone the repository

Use the clone URL shown on the GitHub page for this project, then:

```bash
cd CertifyEdge
```

### 2. Install Bazelisk (optional)

[Bazelisk](https://github.com/bazelbuild/bazelisk) runs the Bazel version from [.bazelversion](../.bazelversion). Install it using the instructions for your OS (release binaries, package managers, or `npm install -g @bazel/bazelisk`). Ensure the `bazel` command you run resolves to Bazelisk so version pinning applies.

### 3. Install Rust

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source ~/.cargo/env
rustup default 1.88.0
rustup component add clippy rustfmt
```

## Development

### Check versions

```bash
rustc --version
cargo --version
bazel --version   # if using Bazel
```

### Build and test with Cargo

```bash
cargo check --workspace
cargo test --workspace
cargo test -p integration_tests
```

### Integration test with Bazel

```bash
bazel test --config=ci //tests/pipeline_integration:pipeline_integration
```

### Run `certctl` after a Bazel build

```bash
bazel run //services/certificate:certctl -- --help
```

## Repository layout (abbreviated)

```
CertifyEdge/
├── MODULE.bazel, WORKSPACE, BUILD.bazel   # Bazel
├── Cargo.toml, Cargo.lock                 # Rust workspace
├── services/                              # Rust crates (compiler, verifier, certificate, …)
├── tests/
│   ├── pipeline_integration/              # End-to-end integration test (Cargo + Bazel)
│   ├── unit/                              # Extra test sources (not all wired to Bazel)
│   └── …                                  # Scripts and helpers
├── docs/                                  # Documentation and decision records
└── infrastructure/                      # Deployment-related files
```

## Common commands

### Bazel build (selected targets)

```bash
bazel build //services/stl-compiler:stl_compiler_lib //services/smt-verifier:smt_verifier //services/certificate:certificate
bazel build --config=ci //services/smt-verifier:verifierd
```

### Formatting and Clippy

```bash
cargo fmt --all -- --check
cargo clippy --workspace -- -D warnings
```

## Continuous integration

The default pipeline runs `cargo fmt --check`, `cargo test --workspace`, and `bazel test --config=ci //tests/pipeline_integration:pipeline_integration`. Further checks can be added as new targets exist. Details: [ADR 002](adr/002-ci-integration-test.md); full index: [Documentation](README.md).

## Troubleshooting

```bash
cargo clean && cargo check --workspace
bazel clean --expunge
bazel test --config=ci //tests/pipeline_integration:pipeline_integration
```

```bash
cargo test -p integration_tests -- --nocapture
bazel test --config=ci //tests/pipeline_integration:pipeline_integration --test_output=errors
```

## Next steps

- Read [CONTRIBUTING.md](../CONTRIBUTING.md)
- Explore `services/certificate/` and `services/stl-compiler/`
- PCS certificate engine: [pcs-certificate-profile.md](pcs-certificate-profile.md), [pcs-handoff.md](pcs-handoff.md); `make validate-profiles` checks the property profile registry

## Support

Use **Issues** and **Discussions** on this repository’s GitHub page.

## License

Apache License 2.0 — see [LICENSE](../LICENSE).
