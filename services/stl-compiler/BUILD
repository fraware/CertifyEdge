load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test")
load("@rules_proto//proto:defs.bzl", "proto_library")
load("@rules_proto_grpc//rust:defs.bzl", "rust_grpc_library", "rust_proto_library")

package(default_visibility = ["//visibility:public"])

# STL Compiler Library
rust_library(
    name = "stl_compiler_lib",
    srcs = glob([
        "src/**/*.rs",
    ]),
    edition = "2021",
    deps = [
        "//services/stl-compiler:stl_compiler_proto",
        "@crate_index//:serde",
        "@crate_index//:serde_json",
        "@crate_index//:tokio",
        "@crate_index//:axum",
        "@crate_index//:tower",
        "@crate_index//:tower-http",
        "@crate_index//:anyhow",
        "@crate_index//:thiserror",
        "@crate_index//:tracing",
        "@crate_index//:tracing-subscriber",
        "@crate_index//:opentelemetry",
        "@crate_index//:opentelemetry-http",
        "@crate_index//:config",
        "@crate_index//:clap",
        "@crate_index//:tempfile",
        "@crate_index//:which",
        "@crate_index//:reqwest",
        "@crate_index//:z3",
        "@crate_index//:cvc5",
    ],
    proc_macro_deps = [
        "@crate_index//:serde",
    ],
    test_deps = [
        "@crate_index//:proptest",
        "@crate_index//:criterion",
        "@crate_index//:tempfile",
    ],
    features = ["full"],
)

# STL Compiler Binary
rust_binary(
    name = "stl_compiler",
    srcs = ["src/main.rs"],
    edition = "2021",
    deps = [
        ":stl_compiler_lib",
    ],
    data = [
        "//services/stl-compiler:config",
    ],
)

# Protocol Buffer Definitions
proto_library(
    name = "stl_compiler_proto",
    srcs = [
        "proto/stl_compiler.proto",
    ],
    deps = [
        "@com_google_protobuf//:timestamp_proto",
    ],
)

# Rust Protocol Buffer Library
rust_proto_library(
    name = "stl_compiler_rust_proto",
    deps = [
        ":stl_compiler_proto",
    ],
)

# gRPC Library
rust_grpc_library(
    name = "stl_compiler_grpc",
    deps = [
        ":stl_compiler_proto",
    ],
)

# Configuration files
filegroup(
    name = "config",
    srcs = glob([
        "config/**/*",
        "*.toml",
        "*.json",
        "*.yaml",
        "*.yml",
    ]),
    visibility = ["//visibility:public"],
)

# Documentation
filegroup(
    name = "docs",
    srcs = glob([
        "docs/**/*",
        "*.md",
        "*.rst",
        "*.txt",
    ]),
    visibility = ["//visibility:public"],
)

# Test files
filegroup(
    name = "tests",
    srcs = glob([
        "tests/**/*",
        "**/*_test.rs",
        "**/*.test.*",
        "**/*.spec.*",
    ]),
    visibility = ["//visibility:public"],
)

# Unit tests
rust_test(
    name = "stl_compiler_unit_tests",
    srcs = glob([
        "src/**/*_test.rs",
    ]),
    edition = "2021",
    deps = [
        ":stl_compiler_lib",
    ],
    test_deps = [
        "@crate_index//:proptest",
        "@crate_index//:criterion",
        "@crate_index//:tempfile",
    ],
    tags = ["unit"],
)

# Integration tests
rust_test(
    name = "stl_compiler_integration_tests",
    srcs = glob([
        "tests/**/*_test.rs",
    ]),
    edition = "2021",
    deps = [
        ":stl_compiler_lib",
    ],
    test_deps = [
        "@crate_index//:proptest",
        "@crate_index//:criterion",
        "@crate_index//:tempfile",
    ],
    tags = ["integration"],
)

# Property-based tests
rust_test(
    name = "stl_compiler_property_tests",
    srcs = glob([
        "tests/property/**/*_test.rs",
    ]),
    edition = "2021",
    deps = [
        ":stl_compiler_lib",
    ],
    test_deps = [
        "@crate_index//:proptest",
        "@crate_index//:criterion",
    ],
    tags = ["property"],
)

# Performance benchmarks
rust_test(
    name = "stl_compiler_benchmarks",
    srcs = glob([
        "benches/**/*.rs",
    ]),
    edition = "2021",
    deps = [
        ":stl_compiler_lib",
    ],
    test_deps = [
        "@crate_index//:criterion",
    ],
    tags = ["benchmark"],
)

# All tests
filegroup(
    name = "all_tests",
    srcs = [
        ":stl_compiler_unit_tests",
        ":stl_compiler_integration_tests",
        ":stl_compiler_property_tests",
        ":stl_compiler_benchmarks",
    ],
    visibility = ["//visibility:public"],
)

# All targets
filegroup(
    name = "all_targets",
    srcs = [
        ":stl_compiler_lib",
        ":stl_compiler",
        ":stl_compiler_proto",
        ":stl_compiler_rust_proto",
        ":stl_compiler_grpc",
        ":all_tests",
    ],
    visibility = ["//visibility:public"],
) 