load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test")
load("@rules_proto//proto:defs.bzl", "proto_library")
load("@rules_proto_grpc//rust:defs.bzl", "rust_proto_library")

package(default_visibility = ["//visibility:public"])

# Certificate library
rust_library(
    name = "certificate",
    srcs = glob([
        "src/**/*.rs",
    ]),
    deps = [
        "@crates//:serde",
        "@crates//:serde_json",
        "@crates//:prost",
        "@crates//:ed25519_dalek",
        "@crates//:sha2",
        "@crates//:uuid",
        "@crates//:chrono",
        "@crates//:thiserror",
        "@crates//:tracing",
        "@crates//:sigstore",
        "@crates//:cosign",
    ],
    visibility = ["//visibility:public"],
)

# Certificate binary
rust_binary(
    name = "certctl",
    srcs = ["src/main.rs"],
    deps = [
        ":certificate",
        "@crates//:clap",
        "@crates//:tokio",
        "@crates//:tracing",
        "@crates//:tracing_subscriber",
    ],
    visibility = ["//visibility:public"],
)

# Tests
rust_test(
    name = "certificate_test",
    srcs = glob([
        "tests/**/*.rs",
    ]),
    deps = [
        ":certificate",
        "@crates//:tokio",
        "@crates//:proptest",
        "@crates//:criterion",
        "@crates//:tempfile",
    ],
    tags = ["unit", "property", "formal"],
)

# Integration tests
rust_test(
    name = "certificate_integration_test",
    srcs = ["tests/integration_test.rs"],
    deps = [
        ":certificate",
        "@crates//:tokio",
        "@crates//:tempfile",
    ],
    tags = ["integration"],
)

# Performance benchmarks
rust_test(
    name = "certificate_benchmark",
    srcs = ["benches/certificate_benchmark.rs"],
    deps = [
        ":certificate",
        "@crates//:criterion",
        "@crates//:tokio",
    ],
    tags = ["benchmark"],
)

# Documentation
filegroup(
    name = "certificate_docs",
    srcs = glob([
        "docs/**/*.md",
        "README.md",
    ]),
    visibility = ["//visibility:public"],
)

# Configuration files
filegroup(
    name = "certificate_config",
    srcs = glob([
        "config/**/*.toml",
        "config/**/*.yaml",
        "config/**/*.json",
    ]),
    visibility = ["//visibility:public"],
)

# Example certificates
filegroup(
    name = "certificate_examples",
    srcs = glob([
        "examples/**/*.cert",
        "examples/**/*.json",
    ]),
    visibility = ["//visibility:public"],
) 