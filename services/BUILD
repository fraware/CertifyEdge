package(default_visibility=["//visibility:public"])

# CertifyEdge Microservices
# Core services for the CertifyEdge platform

filegroup(
    name="all_services",
    srcs=glob(
        [
            "**/*.rs",
            "**/*.proto",
            "**/*.toml",
            "**/*.json",
            "**/*.yaml",
            "**/*.yml",
        ]
    ),
    visibility=["//visibility:public"],
)

# Service-specific filegroups
filegroup(
    name="stl_compiler",
    srcs=glob(
        [
            "stl-compiler/**/*",
        ]
    ),
    visibility=["//visibility:public"],
)

filegroup(
    name="lean_autoprover",
    srcs=glob(
        [
            "lean-autoprover/**/*",
        ]
    ),
    visibility=["//visibility:public"],
)

filegroup(
    name="smt_verifier",
    srcs=glob(
        [
            "smt-verifier/**/*",
        ]
    ),
    visibility=["//visibility:public"],
)

filegroup(
    name="certificate_service",
    srcs=glob(
        [
            "certificate/**/*",
        ]
    ),
    visibility=["//visibility:public"],
)

filegroup(
    name="auditor_api",
    srcs=glob(
        [
            "auditor-api/**/*",
        ]
    ),
    visibility=["//visibility:public"],
)

filegroup(
    name="gpu_farm",
    srcs=glob(
        [
            "gpu-farm/**/*",
        ]
    ),
    visibility=["//visibility:public"],
)

filegroup(
    name="grid_in_loop",
    srcs=glob(
        [
            "grid-in-loop/**/*",
        ]
    ),
    visibility=["//visibility:public"],
)

filegroup(
    name="provenance_service",
    srcs=glob(
        [
            "provenance-service/**/*",
        ]
    ),
    visibility=["//visibility:public"],
)

filegroup(
    name="policy_engine",
    srcs=glob(
        [
            "policy-engine/**/*",
        ]
    ),
    visibility=["//visibility:public"],
)

filegroup(
    name="cert_mgmt",
    srcs=glob(
        [
            "cert-mgmt/**/*",
        ]
    ),
    visibility=["//visibility:public"],
)

# Test targets
filegroup(
    name="all_tests",
    srcs=glob(
        [
            "**/*_test.rs",
            "**/*.test.*",
            "**/*.spec.*",
        ]
    ),
    visibility=["//visibility:public"],
)

# Configuration files
filegroup(
    name="configs",
    srcs=glob(
        [
            "**/*.toml",
            "**/*.json",
            "**/*.yaml",
            "**/*.yml",
            "**/*.env*",
        ]
    ),
    visibility=["//visibility:public"],
)

# Documentation
filegroup(
    name="docs",
    srcs=glob(
        [
            "**/*.md",
            "**/*.rst",
            "**/*.txt",
        ]
    ),
    visibility=["//visibility:public"],
)
