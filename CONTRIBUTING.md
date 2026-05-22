# Contributing to CertifyEdge

Thank you for helping improve CertifyEdge. This document summarizes how to build, test, and submit changes.

---

## Documentation

| Guide | Use for |
|-------|---------|
| [Documentation index](docs/README.md) | Find the right guide |
| [PCS guide](docs/pcs-guide.md) | Certificate engine, benchmarks, release checklist |
| [Quick start](docs/quick-start.md) | Environment setup |
| [STL compiler](services/stl-compiler/README.md) | STL/SMT crate |

---

## Development setup

1. Install Rust **1.88.0** (see [`rust-toolchain.toml`](rust-toolchain.toml)).
2. Clone the repository and run `cargo check --workspace` from the root.
3. Read [docs/quick-start.md](docs/quick-start.md) for Bazel and optional tools.

---

## Tests to run

### All contributors

```bash
cargo fmt --all -- --check
cargo check --workspace
cargo test --workspace
```

### STL / SMT changes

```bash
cargo test -p integration_tests
bazel test --config=ci //tests/pipeline_integration:pipeline_integration
```

### PCS v0.1 changes

If you touch profiles, certificates, benchmarks, handoffs, or scripts under `scripts/pcs-*`:

```bash
export CERTIFYEDGE_SOURCE_COMMIT="$(git rev-parse HEAD)"
make pcs-test
```

For benchmark or ingest output changes, also run:

```bash
make pcs-bench-producer-all-profiles
```

Full release sequence: [docs/pcs-guide.md#pre-release-checklist](docs/pcs-guide.md#pre-release-checklist).

On Windows, use Git Bash for `make` shell targets and set `PYTHON=python` if `python3` is not on PATH.

---

## Optional git hooks

To reject unwanted `Co-authored-by` trailers in commit messages (for example from automated coding assistants):

```bash
git config core.hooksPath .githooks
```

Hooks are optional and local to your clone.

---

## Pull request guidelines

1. Fork the repository and branch from `main`.
2. Keep each pull request focused on one topic.
3. Match existing naming and code style.
4. Run the test commands above for the areas you changed.
5. Update documentation when behavior or public commands change.
6. Describe what you tested in the pull request body.

---

## License

By contributing, you agree that your contributions are licensed under the [Apache License 2.0](LICENSE).
