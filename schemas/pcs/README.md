# PCS schemas (vendored from pcs-core)

These files are copied from [pcs-core](https://github.com/SentinelOps-CI/pcs-core) `schemas/` for offline PCS validation in CertifyEdge (`TraceCertificate.v0`, `ToolUseCertificate.v0`, `ToolUseTrace.v0`, `HandoffManifest.v0`, `ArtifactRegistry.v0` registry entries). Run `make sync-pcs-schemas` when pcs-core schema versions change.

CertifyEdge validates tool-use traces and certificates in-process against the vendored schemas before optional `pcs validate` / `pcs registry check-artifact` (release mode only).
