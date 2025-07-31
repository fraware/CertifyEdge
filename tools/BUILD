package(default_visibility=["//visibility:public"])

# CertifyEdge Development Tools
# Development utilities, scripts, and tooling

filegroup(
    name="all_tools",
    srcs=glob(
        [
            "**/*.py",
            "**/*.rs",
            "**/*.sh",
            "**/*.bash",
            "**/*.ps1",
            "**/*.js",
            "**/*.ts",
            "**/*.json",
            "**/*.yaml",
            "**/*.yml",
        ]
    ),
    visibility=["//visibility:public"],
)

# Python tools
filegroup(
    name="python_tools",
    srcs=glob(
        [
            "**/*.py",
            "**/requirements.txt",
            "**/pyproject.toml",
            "**/setup.py",
            "**/setup.cfg",
        ]
    ),
    visibility=["//visibility:public"],
)

# Rust tools
filegroup(
    name="rust_tools",
    srcs=glob(
        [
            "**/*.rs",
            "**/Cargo.toml",
            "**/Cargo.lock",
        ]
    ),
    visibility=["//visibility:public"],
)

# Shell scripts
filegroup(
    name="shell_scripts",
    srcs=glob(
        [
            "**/*.sh",
            "**/*.bash",
            "**/*.zsh",
        ]
    ),
    visibility=["//visibility:public"],
)

# PowerShell scripts
filegroup(
    name="powershell_scripts",
    srcs=glob(
        [
            "**/*.ps1",
            "**/*.psm1",
        ]
    ),
    visibility=["//visibility:public"],
)

# Node.js tools
filegroup(
    name="node_tools",
    srcs=glob(
        [
            "**/*.js",
            "**/*.ts",
            "**/package.json",
            "**/package-lock.json",
            "**/yarn.lock",
            "**/pnpm-lock.yaml",
        ]
    ),
    visibility=["//visibility:public"],
)

# Configuration tools
filegroup(
    name="config_tools",
    srcs=glob(
        [
            "**/*.json",
            "**/*.yaml",
            "**/*.yml",
            "**/*.toml",
            "**/*.ini",
            "**/*.cfg",
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
