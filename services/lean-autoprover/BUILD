load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test")
load("@rules_lean//lean:defs.bzl", "lean_library", "lean_binary")
load("@rules_proto//proto:defs.bzl", "proto_library")
load("@rules_proto_grpc//rust:defs.bzl", "rust_proto_library")

package(default_visibility = ["//visibility:public"])

# Lean 4 autoprover plugin library
lean_library(
    name = "certify_tactics",
    srcs = glob([
        "src/**/*.lean",
    ]),
    deps = [
        "@lean//:core",
        "@lean//:mathlib",
    ],
    visibility = ["//visibility:public"],
)

# Rust wrapper for Lean 4 autoprover
rust_library(
    name = "lean_autoprover",
    srcs = glob([
        "src/**/*.rs",
    ]),
    deps = [
        "//services/stl-compiler:stl_compiler",
        "@crates//:tokio",
        "@crates//:serde",
        "@crates//:serde_json",
        "@crates//:sqlx",
        "@crates//:uuid",
        "@crates//:chrono",
        "@crates//:thiserror",
        "@crates//:tracing",
    ],
    visibility = ["//visibility:public"],
)

# Lean autoprover binary
rust_binary(
    name = "lean_autoprover_bin",
    srcs = ["src/main.rs"],
    deps = [
        ":lean_autoprover",
        "@crates//:clap",
        "@crates//:tokio",
        "@crates//:tracing",
        "@crates//:tracing_subscriber",
    ],
    visibility = ["//visibility:public"],
)

# Tests
rust_test(
    name = "lean_autoprover_test",
    srcs = glob([
        "tests/**/*.rs",
    ]),
    deps = [
        ":lean_autoprover",
        "@crates//:tokio",
        "@crates//:proptest",
        "@crates//:criterion",
    ],
    tags = ["unit", "property", "formal"],
)

# Integration tests
rust_test(
    name = "lean_autoprover_integration_test",
    srcs = ["tests/integration_test.rs"],
    deps = [
        ":lean_autoprover",
        "//services/stl-compiler:stl_compiler",
        "@crates//:tokio",
        "@crates//:tempfile",
    ],
    tags = ["integration"],
)

# Performance benchmarks
rust_test(
    name = "lean_autoprover_benchmark",
    srcs = ["benches/autoprover_benchmark.rs"],
    deps = [
        ":lean_autoprover",
        "@crates//:criterion",
        "@crates//:tokio",
    ],
    tags = ["benchmark"],
)

# Documentation
filegroup(
    name = "lean_autoprover_docs",
    srcs = glob([
        "docs/**/*.md",
        "README.md",
    ]),
    visibility = ["//visibility:public"],
)

# Configuration files
filegroup(
    name = "lean_autoprover_config",
    srcs = glob([
        "config/**/*.toml",
        "config/**/*.yaml",
        "config/**/*.json",
    ]),
    visibility = ["//visibility:public"],
)

# Example specifications
filegroup(
    name = "lean_autoprover_examples",
    srcs = glob([
        "examples/**/*.stl",
        "examples/**/*.lean",
    ]),
    visibility = ["//visibility:public"],
) 