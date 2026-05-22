# STL compiler (`stl-compiler`)

Rust library and CLI that parse **signal temporal logic (STL)**-style specifications and produce **Lean 4**-oriented output and **SMT-LIB** when configured.

This crate belongs to the CertifyEdge **STL/SMT stack**, which remains separate from **PCS v0.1** property profiles and the `certifyedge` certificate CLI. Proof-carrying certificate workflows are documented in the [PCS guide](../../docs/pcs-guide.md).

## What it does today

The parser reads specifications from text through a custom Rust implementation. The `Compiler` API and related types emit Lean-oriented and SMT-LIB artifacts. `CompilerConfig` in `src/config.rs` controls Lean, Z3, and CVC5 paths and behavior. Automated runs can call `CompilerConfig::for_tests_without_external_tools()` to exercise the pipeline on hosts where only the Rust toolchain is installed.

## Requirements

Rust follows the toolchain pinned at the repository root in [`rust-toolchain.toml`](../../rust-toolchain.toml), currently **1.88.0**. Lean, Z3, and CVC5 are optional and become necessary only when you enable full toolchains beyond the default integration test configuration.

## Build and test

From the repository root, because this crate is a workspace member:

```bash
cargo check -p stl-compiler
cargo test -p stl-compiler
```

### Bazel (from repository root)

Targets appear in [`BUILD.bazel`](BUILD.bazel).

```bash
bazel build //services/stl-compiler:stl_compiler_lib
bazel build //services/stl-compiler:stl_compiler
bazel test //services/stl-compiler:stl_compiler_integration_tests
```

## CLI usage

After `cargo build -p stl-compiler` or the Bazel binary build, the `stl-compiler` executable exposes subcommands described in `src/main.rs` and `--help`. Typical flows compile or validate a specification file.

## Library usage

```rust
use stl_compiler::{Compiler, CompilerConfig};

let config = CompilerConfig::default();
let compiler = Compiler::new(config);

let spec_text = "my_spec\nvoltage > 220";
let result = compiler.compile(spec_text).await?;
```

Tests that must avoid spawning external tools should construct `CompilerConfig::for_tests_without_external_tools()` in place of `default()`.

## Protocol buffers

`proto/stl_compiler.proto` defines a schema for interoperability. Bazel exposes it as `//services/stl-compiler:stl_compiler_proto`. See [ADR 003 — Protocol buffers and gRPC](../../docs/adr/003-proto-and-grpc.md).

## Configuration

JSON-shaped configuration flows through `CompilerConfig` serialization; see `src/config.rs` and crate tests for fields. Lean and SMT solver versions and paths should match your installation when those features are enabled.

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

Temporal operators include forms such as `G[0,10] φ` (always over an interval), `F[0,5] φ` (eventually), and `X φ` (next), with `&&`, `||`, `!`, `->`, and `<->` for boolean structure. See `src/parser.rs` for the exact supported surface.

## Contributing

Follow the repository [Contributing guide](../../CONTRIBUTING.md). Run `cargo fmt`, `cargo test --workspace`, and, when you touch Bazel or protos, `bazel test --config=ci //tests/pipeline_integration:pipeline_integration`.

## License

Apache License 2.0 — see [LICENSE](../../LICENSE).

## References

- [Signal temporal logic](https://en.wikipedia.org/wiki/Signal_temporal_logic)
- [Lean 4](https://leanprover.github.io/lean4/)
- [SMT-LIB](https://smtlib.cs.uiowa.edu/)
- [Z3](https://github.com/Z3Prover/z3)
- [cvc5](https://cvc5.github.io/)
