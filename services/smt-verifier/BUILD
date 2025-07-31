load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test")
load("@rules_proto//proto:defs.bzl", "proto_library")
load("@rules_proto_grpc//rust:defs.bzl", "rust_proto_library")
load("@rules_wasm//wasm:defs.bzl", "wasm_binary")

package(default_visibility = ["//visibility:public"])

# SMT verifier library
rust_library(
    name = "smt_verifier",
    srcs = glob([
        "src/**/*.rs",
    ]),
    deps = [
        "//services/stl-compiler:stl_compiler",
        "@crates//:tokio",
        "@crates//:serde",
        "@crates//:serde_json",
        "@crates//:tonic",
        "@crates//:prost",
        "@crates//:uuid",
        "@crates//:chrono",
        "@crates//:thiserror",
        "@crates//:tracing",
        "@crates//:prometheus",
        "@crates//:opentelemetry",
        "@crates//:sqlx",
        "@crates//:wasmtime",
    ],
    visibility = ["//visibility:public"],
)

# SMT verifier binary
rust_binary(
    name = "verifierd",
    srcs = ["src/main.rs"],
    deps = [
        ":smt_verifier",
        "@crates//:clap",
        "@crates//:tokio",
        "@crates//:tracing",
        "@crates//:tracing_subscriber",
    ],
    visibility = ["//visibility:public"],
)

# Tests
rust_test(
    name = "smt_verifier_test",
    srcs = glob([
        "tests/**/*.rs",
    ]),
    deps = [
        ":smt_verifier",
        "@crates//:tokio",
        "@crates//:proptest",
        "@crates//:criterion",
        "@crates//:tempfile",
    ],
    tags = ["unit", "property", "formal"],
)

# Integration tests
rust_test(
    name = "smt_verifier_integration_test",
    srcs = ["tests/integration_test.rs"],
    deps = [
        ":smt_verifier",
        "//services/stl-compiler:stl_compiler",
        "@crates//:tokio",
        "@crates//:tempfile",
    ],
    tags = ["integration"],
)

# Performance benchmarks
rust_test(
    name = "smt_verifier_benchmark",
    srcs = ["benches/verifier_benchmark.rs"],
    deps = [
        ":smt_verifier",
        "@crates//:criterion",
        "@crates//:tokio",
    ],
    tags = ["benchmark"],
)

# WebAssembly sandbox for SMT solvers
wasm_binary(
    name = "z3_wasm",
    srcs = ["wasm/z3.wasm"],
    visibility = ["//visibility:public"],
)

wasm_binary(
    name = "cvc5_wasm",
    srcs = ["wasm/cvc5.wasm"],
    visibility = ["//visibility:public"],
)

# Documentation
filegroup(
    name = "smt_verifier_docs",
    srcs = glob([
        "docs/**/*.md",
        "README.md",
    ]),
    visibility = ["//visibility:public"],
)

# Configuration files
filegroup(
    name = "smt_verifier_config",
    srcs = glob([
        "config/**/*.toml",
        "config/**/*.yaml",
        "config/**/*.json",
    ]),
    visibility = ["//visibility:public"],
)

# Example SMT-LIB scripts
filegroup(
    name = "smt_verifier_examples",
    srcs = glob([
        "examples/**/*.smt2",
        "examples/**/*.smt",
    ]),
    visibility = ["//visibility:public"],
) 