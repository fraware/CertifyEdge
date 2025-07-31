package(default_visibility=["//visibility:public"])

# CertifyEdge Web Frontend
# Next.js web application for CertifyEdge platform

filegroup(
    name="all_web",
    srcs=glob(
        [
            "**/*.ts",
            "**/*.tsx",
            "**/*.js",
            "**/*.jsx",
            "**/*.css",
            "**/*.scss",
            "**/*.sass",
            "**/*.json",
            "**/*.md",
        ]
    ),
    visibility=["//visibility:public"],
)

# Next.js specific files
filegroup(
    name="nextjs",
    srcs=glob(
        [
            "**/next.config.*",
            "**/package.json",
            "**/package-lock.json",
            "**/yarn.lock",
            "**/pnpm-lock.yaml",
            "**/tsconfig.json",
            "**/tailwind.config.*",
            "**/postcss.config.*",
        ]
    ),
    visibility=["//visibility:public"],
)

# React components
filegroup(
    name="components",
    srcs=glob(
        [
            "**/components/**/*",
            "**/ui/**/*",
            "**/shared/**/*",
        ]
    ),
    visibility=["//visibility:public"],
)

# Pages and routing
filegroup(
    name="pages",
    srcs=glob(
        [
            "**/pages/**/*",
            "**/app/**/*",
            "**/src/app/**/*",
        ]
    ),
    visibility=["//visibility:public"],
)

# Styles and assets
filegroup(
    name="styles",
    srcs=glob(
        [
            "**/*.css",
            "**/*.scss",
            "**/*.sass",
            "**/*.less",
            "**/styles/**/*",
        ]
    ),
    visibility=["//visibility:public"],
)

filegroup(
    name="assets",
    srcs=glob(
        [
            "**/public/**/*",
            "**/assets/**/*",
            "**/static/**/*",
        ]
    ),
    visibility=["//visibility:public"],
)

# Tests
filegroup(
    name="tests",
    srcs=glob(
        [
            "**/*.test.*",
            "**/*.spec.*",
            "**/__tests__/**/*",
            "**/tests/**/*",
        ]
    ),
    visibility=["//visibility:public"],
)

# Configuration
filegroup(
    name="config",
    srcs=glob(
        [
            "**/*.config.*",
            "**/*.env*",
            "**/config/**/*",
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
            "**/docs/**/*",
        ]
    ),
    visibility=["//visibility:public"],
)
