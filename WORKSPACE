workspace(name = "certifyedge")

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

# Rust toolchain - using a known working version
http_archive(
    name = "rules_rust",
    sha256 = "bcf0059d478dd6d67518f4f00e3ccec7635762f4e1662f9dff62e8e9795c8c3",
    strip_prefix = "rules_rust-1.0.0",
    urls = ["https://github.com/bazelbuild/rules_rust/releases/download/1.0.0/rules_rust-v1.0.0.tar.gz"],
)

load("@rules_rust//rust:repositories.bzl", "rules_rust_dependencies", "rust_register_toolchains")
rules_rust_dependencies()
rust_register_toolchains(
    edition = "2021",
    versions = ["1.75.0"],
)

# Python toolchain
http_archive(
    name = "rules_python",
    sha256 = "94750828b1804453e98a0f3f9f955e4b416c2f8b3e3e7b3f3f3f3f3f3f3f3f3f",
    strip_prefix = "rules_python-0.25.0",
    urls = ["https://github.com/bazelbuild/rules_python/releases/download/0.25.0/rules_python-0.25.0.tar.gz"],
)

load("@rules_python//python:repositories.bzl", "python_register_toolchains")
python_register_toolchains(
    name = "python",
    python_version = "PY3",
) 