package(default_visibility = ["//visibility:public"])

# CertifyEdge Testing Infrastructure
# Comprehensive testing framework for all components

filegroup(
    name = "all_tests",
    srcs = glob([
        "**/*_test.rs",
        "**/*_test.py",
        "**/*_test.ts",
        "**/*_test.tsx",
        "**/*.test.*",
        "**/*.spec.*",
        "**/*_test.lean",
    ]),
    visibility = ["//visibility:public"],
)

# Unit tests
filegroup(
    name = "unit_tests",
    srcs = glob([
        "**/unit/**/*",
        "**/*_unit_test.*",
        "**/*.unit.test.*",
    ]),
    visibility = ["//visibility:public"],
)

# Integration tests
filegroup(
    name = "integration_tests",
    srcs = glob([
        "**/integration/**/*",
        "**/*_integration_test.*",
        "**/*.integration.test.*",
    ]),
    visibility = ["//visibility:public"],
)

# Property-based tests
filegroup(
    name = "property_tests",
    srcs = glob([
        "**/property/**/*",
        "**/*_property_test.*",
        "**/*.property.test.*",
    ]),
    visibility = ["//visibility:public"],
)

# Formal verification tests
filegroup(
    name = "formal_tests",
    srcs = glob([
        "**/formal/**/*",
        "**/*_formal_test.*",
        "**/*.formal.test.*",
        "**/*.lean",
    ]),
    visibility = ["//visibility:public"],
)

# Performance tests
filegroup(
    name = "performance_tests",
    srcs = glob([
        "**/performance/**/*",
        "**/*_performance_test.*",
        "**/*.performance.test.*",
        "**/*_benchmark.*",
    ]),
    visibility = ["//visibility:public"],
)

# Security tests
filegroup(
    name = "security_tests",
    srcs = glob([
        "**/security/**/*",
        "**/*_security_test.*",
        "**/*.security.test.*",
    ]),
    visibility = ["//visibility:public"],
)

# End-to-end tests
filegroup(
    name = "e2e_tests",
    srcs = glob([
        "**/e2e/**/*",
        "**/*_e2e_test.*",
        "**/*.e2e.test.*",
    ]),
    visibility = ["//visibility:public"],
)

# Grid-in-loop tests
filegroup(
    name = "grid_in_loop_tests",
    srcs = glob([
        "**/grid-in-loop/**/*",
        "**/*_grid_test.*",
        "**/*.grid.test.*",
    ]),
    visibility = ["//visibility:public"],
)

# Mutation tests
filegroup(
    name = "mutation_tests",
    srcs = glob([
        "**/mutation/**/*",
        "**/*_mutation_test.*",
        "**/*.mutation.test.*",
    ]),
    visibility = ["//visibility:public"],
)

# Contract tests
filegroup(
    name = "contract_tests",
    srcs = glob([
        "**/contract/**/*",
        "**/*_contract_test.*",
        "**/*.contract.test.*",
    ]),
    visibility = ["//visibility:public"],
)

# Differential tests
filegroup(
    name = "differential_tests",
    srcs = glob([
        "**/differential/**/*",
        "**/*_differential_test.*",
        "**/*.differential.test.*",
    ]),
    visibility = ["//visibility:public"],
)

# Test data and fixtures
filegroup(
    name = "test_data",
    srcs = glob([
        "**/fixtures/**/*",
        "**/data/**/*",
        "**/*.json",
        "**/*.yaml",
        "**/*.yml",
        "**/*.csv",
        "**/*.xml",
    ]),
    visibility = ["//visibility:public"],
)

# Test configuration
filegroup(
    name = "test_config",
    srcs = glob([
        "**/*.config.*",
        "**/*.conf",
        "**/*.ini",
        "**/*.env*",
    ]),
    visibility = ["//visibility:public"],
)

# Test documentation
filegroup(
    name = "test_docs",
    srcs = glob([
        "**/*.md",
        "**/*.rst",
        "**/*.txt",
    ]),
    visibility = ["//visibility:public"],
) 