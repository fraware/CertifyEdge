# STL compiler (`stl-compiler`)

Rust library and CLI that parse **signal temporal logic (STL)**-style specifications and produce **Lean 4**-oriented output and **SMT-LIB** where configured.

This crate is part of the CertifyEdge **STL/SMT stack**. It is separate from **PCS v0.1** property profiles and the `certifyedge` certificate CLI—see [PCS guide](../../docs/pcs-guide.md) for proof-carrying certificates.

## What it does today

- **Parse** specifications from text (custom parser in Rust, not code-generated grammar).
- **Emit** Lean-oriented and SMT-LIB artifacts through the `Compiler` API and related types.
- **Configure** Lean, Z3, and CVC5 paths and behavior via `CompilerConfig` (see `src/config.rs`).
- **Test without local provers** using `CompilerConfig::for_tests_without_external_tools()` for automated runs that skip external Lean/Z3/CVC5 binaries.

## Requirements

- **Rust:** same toolchain as the repo root ([`rust-toolchain.toml`](../../rust-toolchain.toml)); currently **1.88.0**.
- **Lean / Z3 / CVC5:** optional; enable and install when you want full toolchains (not required for the default integration test configuration).

## Build and test

From the **repository root** (this crate is a workspace member):

```bash
cargo check -p stl-compiler
cargo test -p stl-compiler
```

### Bazel (from repository root)

Targets defined in [`BUILD.bazel`](BUILD.bazel):

```bash
# Library
bazel build //services/stl-compiler:stl_compiler_lib

# CLI binary
bazel build //services/stl-compiler:stl_compiler

# Integration-style tests (this crate’s Bazel `rust_test`)
bazel test //services/stl-compiler:stl_compiler_integration_tests
```

## CLI usage

After `cargo build -p stl-compiler` or the Bazel binary above, the `stl-compiler` executable exposes subcommands (see `src/main.rs` and `--help`). Typical flows include compiling or validating a specification file.

## Library usage

```rust
use stl_compiler::{Compiler, CompilerConfig};

let config = CompilerConfig::default();
let compiler = Compiler::new(config);

// async context
let spec_text = "my_spec\nvoltage > 220";
let result = compiler.compile(spec_text).await?;
// result.lean4_output, result.smt_output, result.stats, …
```

For tests that must not spawn external tools, use `CompilerConfig::for_tests_without_external_tools()` instead of `default()`.

## Protocol buffers

`proto/stl_compiler.proto` defines a schema for interoperability. Bazel exposes it as `//services/stl-compiler:stl_compiler_proto`. See [ADR 003: Protocol buffers and gRPC](../../docs/adr/003-proto-and-grpc.md).

## Configuration

JSON-shaped configuration is supported via `CompilerConfig` serialization (see `src/config.rs` and tests for fields). Versions and paths for Lean and SMT solvers should match what you have installed when those features are enabled.

## Specification syntax (summary)

Example body:

```text
voltage_safety
voltage > 220 && current < 100
param: max_voltage real 240.0 Maximum voltage threshold
constraint: voltage_bounds bounds voltage <= 250.0
meta: author Example author
meta: version 1.0.0
```

Temporal operators include forms such as `G[0,10] φ` (always over an interval), `F[0,5] φ` (eventually), `X φ` (next), with `&&`, `||`, `!`, `->`, `<->` for boolean structure. See `src/parser.rs` for the exact supported surface.

## Contributing

Follow the repository [Contributing guide](../../CONTRIBUTING.md): `cargo fmt`, `cargo test --workspace`, and (if you touch Bazel or protos) `bazel test --config=ci //tests/pipeline_integration:pipeline_integration`.

## License

Apache License 2.0 — see [LICENSE](../../LICENSE).

## References

- [Signal temporal logic](https://en.wikipedia.org/wiki/Signal_temporal_logic)
- [Lean 4](https://leanprover.github.io/lean4/)
- [SMT-LIB](https://smtlib.cs.uiowa.edu/)
- [Z3](https://github.com/Z3Prover/z3)
- [cvc5](https://cvc5.github.io/)
