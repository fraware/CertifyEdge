package(default_visibility=["//visibility:public"])

# CertifyEdge Platform - Production-grade, formally-verified, audit-ready platform
# for certifying AI agents in power grid applications

exports_files(
    [
        "WORKSPACE",
        "BUILD",
        "README.md",
        "CHANGELOG.md",
        "LICENSE",
        ".bazelrc",
        ".bazelversion",
    ]
)

# Main package groups for different components
filegroup(
    name="all_sources",
    srcs=glob(
        [
            "**/*.rs",
            "**/*.ts",
            "**/*.tsx",
            "**/*.py",
            "**/*.lean",
            "**/*.proto",
            "**/*.bzl",
            "**/*.bazel",
            "**/*.md",
            "**/*.yml",
            "**/*.yaml",
            "**/*.json",
            "**/*.toml",
            "**/*.lock",
        ]
    ),
    visibility=["//visibility:public"],
)

# Documentation
filegroup(
    name="docs",
    srcs=glob(
        [
            "docs/**/*",
            "*.md",
        ]
    ),
    visibility=["//visibility:public"],
)

# Configuration files
filegroup(
    name="config",
    srcs=glob(
        [
            "**/*.yml",
            "**/*.yaml",
            "**/*.json",
            "**/*.toml",
            "**/*.env*",
            "**/*.config.*",
        ]
    ),
    visibility=["//visibility:public"],
)

# Test files
filegroup(
    name="tests",
    srcs=glob(
        [
            "**/*_test.rs",
            "**/*_test.ts",
            "**/*_test.tsx",
            "**/*_test.py",
            "**/*.test.*",
            "**/*.spec.*",
        ]
    ),
    visibility=["//visibility:public"],
)

# Security and compliance files
filegroup(
    name="security",
    srcs=glob(
        [
            "**/*.rego",
            "**/*.policy",
            "**/*.sig",
            "**/*.cert",
            "**/*.key",
            "**/*.crt",
            "**/*.pem",
            "**/sbom.*",
            "**/SLSA*",
        ]
    ),
    visibility=["//visibility:public"],
)

# Infrastructure files
filegroup(
    name="infrastructure",
    srcs=glob(
        [
            "**/*.tf",
            "**/*.tfvars",
            "**/*.tfstate*",
            "**/*.k8s.yaml",
            "**/*.k8s.yml",
            "**/*.helm.yaml",
            "**/*.helm.yml",
            "**/Dockerfile*",
            "**/docker-compose*",
            "**/skaffold*",
            "**/kustomization*",
        ]
    ),
    visibility=["//visibility:public"],
)

# CI/CD files
filegroup(
    name="cicd",
    srcs=glob(
        [
            ".github/**/*",
            "**/.github/**/*",
            "**/*.github.*",
            "**/*.gitlab*",
            "**/*.jenkins*",
            "**/*.circle*",
            "**/*.travis*",
            "**/*.azure*",
        ]
    ),
    visibility=["//visibility:public"],
)

# Protobuf schemas
filegroup(
    name="protos",
    srcs=glob(
        [
            "**/*.proto",
        ]
    ),
    visibility=["//visibility:public"],
)

# Lean 4 files
filegroup(
    name="lean",
    srcs=glob(
        [
            "**/*.lean",
            "**/*.lake",
        ]
    ),
    visibility=["//visibility:public"],
)

# WebAssembly files
filegroup(
    name="wasm",
    srcs=glob(
        [
            "**/*.wasm",
            "**/*.wat",
        ]
    ),
    visibility=["//visibility:public"],
)

# GPU/CUDA files
filegroup(
    name="gpu",
    srcs=glob(
        [
            "**/*.cu",
            "**/*.cuh",
            "**/*.cubin",
            "**/*.ptx",
        ]
    ),
    visibility=["//visibility:public"],
)

# Monitoring and observability
filegroup(
    name="monitoring",
    srcs=glob(
        [
            "**/*.prometheus",
            "**/*.grafana",
            "**/*.alertmanager",
            "**/*.loki",
            "**/*.jaeger",
            "**/*.zipkin",
            "**/*.otlp",
        ]
    ),
    visibility=["//visibility:public"],
)

# All targets for testing
filegroup(
    name="all_targets",
    srcs=[
        "//services/...:all",
        "//web/...:all",
        "//tools/...:all",
        "//docs/...:all",
        "//tests/...:all",
    ],
    visibility=["//visibility:public"],
)

# Development tools
filegroup(
    name="dev_tools",
    srcs=glob(
        [
            "tools/**/*",
            "scripts/**/*",
            "**/*.bazelrc",
            "**/*.bazelversion",
            "**/*.bazelignore",
        ]
    ),
    visibility=["//visibility:public"],
)
