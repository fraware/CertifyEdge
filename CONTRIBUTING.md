# Contributing to CertifyEdge

## Documentation

- [Documentation index](docs/README.md)
- [PCS guide](docs/pcs-guide.md) — certificate engine, benchmarks, release checklist
- [STL compiler crate](services/stl-compiler/README.md) — legacy STL/SMT stack

## Build and test

- **Rust:** Toolchain pinned in `rust-toolchain.toml` (currently **1.88.0**).
- **Workspace:** `cargo check --workspace` and `cargo test --workspace`.
- **Legacy integration test:** `cargo test -p integration_tests`.
- **Bazel:** `bazel test --config=ci //tests/pipeline_integration:pipeline_integration`.

## PCS v0.1 changes

If you touch profiles, certificates, benchmarks, handoffs, or PCS scripts, run before opening a PR:

```bash
export CERTIFYEDGE_SOURCE_COMMIT="$(git rev-parse HEAD)"
make pcs-test
```

For benchmark or ingest changes, also run:

```bash
make pcs-bench-producer-all-profiles
```

Full pre-release sequence: [docs/pcs-guide.md#pre-release-checklist](docs/pcs-guide.md#pre-release-checklist).

## Git hooks (optional)

To block Cursor IDE `Co-authored-by: Cursor <cursoragent@cursor.com>` trailers:

```bash
git config core.hooksPath .githooks
```

## Pull requests

1. Fork and branch from `main`.
2. Keep changes focused; match existing style.
3. Run `cargo fmt --all` (CI runs `cargo fmt --all -- --check`).
4. Run the tests above for the areas you changed.
5. If you change Bazel files or `.proto` definitions, run the Bazel integration test.

## License

Contributions are licensed under the Apache License 2.0 — see [LICENSE](LICENSE).
