# Contributing to CertifyEdge

## Documentation

- [Documentation index](docs/README.md) — quick start, ADRs, and links
- [STL compiler crate](services/stl-compiler/README.md) — service-specific build and API notes

## Build and test

- **Rust:** The toolchain version is pinned in `rust-toolchain.toml` (currently **1.88.0**, driven by dependency requirements on crates.io).
- **Rust:** From the repository root, `cargo check --workspace` and `cargo test --workspace`. The end-to-end integration test lives in the `integration_tests` package: `cargo test -p integration_tests`.
- **Bazel:** Install [Bazelisk](https://github.com/bazelbuild/bazelisk). From the repository root run `bazel test --config=ci //tests/pipeline_integration:pipeline_integration`. Example library targets: `//services/stl-compiler:stl_compiler_lib`, `//services/smt-verifier:smt_verifier`, `//services/certificate:certificate`.

## Git hooks (optional)

To block Cursor IDE `Co-authored-by: Cursor <cursoragent@cursor.com>` trailers from commit messages:

```bash
git config core.hooksPath .githooks
```

## Pull requests

1. Fork and branch from `main`.
2. Keep changes focused; match existing style and naming.
3. Run `cargo fmt --all` (continuous integration runs `cargo fmt --all -- --check`) and ensure `cargo test --workspace` passes, or explain any exceptions in the pull request.
4. If you change Bazel files or `.proto` definitions, run the Bazel integration test command above.

## License

By contributing, you agree that your contributions are licensed under the Apache License 2.0, as described in [LICENSE](LICENSE).
