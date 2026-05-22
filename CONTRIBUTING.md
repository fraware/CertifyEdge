# Contributing to CertifyEdge

Thank you for helping improve CertifyEdge. The sections below summarize how to build, test, and submit changes so reviewers can merge your work with confidence.

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

Install Rust **1.88.0** as pinned in [`rust-toolchain.toml`](rust-toolchain.toml), clone the repository, and run `cargo check --workspace` from the root. The [quick start](docs/quick-start.md) explains Bazel, optional Python usage for benchmark scripts, and platform-specific notes for Windows developers who rely on Git Bash.

---

## Tests to run

### All contributors

Every pull request should pass formatting and the workspace build before review.

```bash
cargo fmt --all -- --check
cargo check --workspace
cargo test --workspace
```

### STL / SMT changes

When you modify the compiler, verifier, or classical certificate crates, run the pipeline integration test in Cargo and Bazel so both build graphs stay aligned.

```bash
cargo test -p integration_tests
bazel test --config=ci //tests/pipeline_integration:pipeline_integration
```

### PCS v0.1 changes

When you touch profiles, certificates, benchmarks, handoffs, or scripts whose names begin with `pcs-`, set the source commit and run the PCS gate that mirrors most of the certificate-related continuous integration job.

```bash
export CERTIFYEDGE_SOURCE_COMMIT="$(git rev-parse HEAD)"
make pcs-test
```

Benchmark or ingest output changes should also run the full producer target for all three profile suites.

```bash
make pcs-bench-producer-all-profiles
```

The complete sequence maintainers use before a release tag lives in the [PCS guide pre-release checklist](docs/pcs-guide.md#pre-release-checklist). On Windows, run `make` shell targets from Git Bash and set `PYTHON=python` when your shell exposes `python` as the Python 3 interpreter.

---

## Optional git hooks

You may point Git at the repository hooks directory if you want the commit-msg hook to decline messages that include unwanted `Co-authored-by` trailers from automated coding assistants.

```bash
git config core.hooksPath .githooks
```

Hooks remain optional and apply only to your local clone.

---

## Pull request guidelines

Fork the repository and branch from `main`, keeping each pull request focused on a single topic so review stays tractable. Match existing naming and code style, run the test commands that apply to your change set, and update documentation whenever behavior or public commands change. Describe what you tested in the pull request body so reviewers can reproduce your results.

---

## License

By contributing, you agree that your contributions are licensed under the [Apache License 2.0](LICENSE).
