package(default_visibility = ["//visibility:public"])

# CertifyEdge Infrastructure
# Kubernetes, Terraform, and deployment configurations

filegroup(
    name = "all_infrastructure",
    srcs = glob([
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
    ]),
    visibility = ["//visibility:public"],
)

# Terraform configurations
filegroup(
    name = "terraform",
    srcs = glob([
        "**/*.tf",
        "**/*.tfvars",
        "**/*.tfstate*",
        "**/terraform/**/*",
    ]),
    visibility = ["//visibility:public"],
)

# Kubernetes manifests
filegroup(
    name = "kubernetes",
    srcs = glob([
        "**/*.k8s.yaml",
        "**/*.k8s.yml",
        "**/k8s/**/*",
        "**/kubernetes/**/*",
    ]),
    visibility = ["//visibility:public"],
)

# Helm charts
filegroup(
    name = "helm",
    srcs = glob([
        "**/*.helm.yaml",
        "**/*.helm.yml",
        "**/helm/**/*",
        "**/charts/**/*",
    ]),
    visibility = ["//visibility:public"],
)

# Docker configurations
filegroup(
    name = "docker",
    srcs = glob([
        "**/Dockerfile*",
        "**/docker-compose*",
        "**/.dockerignore",
        "**/docker/**/*",
    ]),
    visibility = ["//visibility:public"],
)

# Skaffold configurations
filegroup(
    name = "skaffold",
    srcs = glob([
        "**/skaffold*",
        "**/skaffold/**/*",
    ]),
    visibility = ["//visibility:public"],
)

# Kustomize configurations
filegroup(
    name = "kustomize",
    srcs = glob([
        "**/kustomization*",
        "**/kustomize/**/*",
    ]),
    visibility = ["//visibility:public"],
)

# Monitoring and observability
filegroup(
    name = "monitoring",
    srcs = glob([
        "**/*.prometheus",
        "**/*.grafana",
        "**/*.alertmanager",
        "**/*.loki",
        "**/*.jaeger",
        "**/*.zipkin",
        "**/*.otlp",
        "**/monitoring/**/*",
    ]),
    visibility = ["//visibility:public"],
)

# Security configurations
filegroup(
    name = "security",
    srcs = glob([
        "**/*.rego",
        "**/*.policy",
        "**/*.opa",
        "**/security/**/*",
    ]),
    visibility = ["//visibility:public"],
)

# Network policies
filegroup(
    name = "network_policies",
    srcs = glob([
        "**/*network-policy*",
        "**/*networkpolicy*",
        "**/network/**/*",
    ]),
    visibility = ["//visibility:public"],
)

# RBAC configurations
filegroup(
    name = "rbac",
    srcs = glob([
        "**/*rbac*",
        "**/*role*",
        "**/*clusterrole*",
        "**/rbac/**/*",
    ]),
    visibility = ["//visibility:public"],
)

# Service mesh configurations
filegroup(
    name = "service_mesh",
    srcs = glob([
        "**/*istio*",
        "**/*linkerd*",
        "**/*consul*",
        "**/service-mesh/**/*",
    ]),
    visibility = ["//visibility:public"],
)

# Documentation
filegroup(
    name = "docs",
    srcs = glob([
        "**/*.md",
        "**/*.rst",
        "**/*.txt",
    ]),
    visibility = ["//visibility:public"],
) 