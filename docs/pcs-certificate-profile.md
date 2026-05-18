# CertifyEdge PCS certificate profile

Phase 2 protocol profile for the CertifyEdge producer. Copy `pcs_registry/TraceCertificate.v0.registry.json` into pcs-core `ArtifactRegistry.v0` when promoting definitions.

## Profile

| Field | Value |
|-------|--------|
| **component** | CertifyEdge |
| **input artifact** | `trace.json` |
| **input handoff kind** | `runtime_to_certificate` |
| **property profile** | `hospital_lab.qc_release` |
| **output artifact** | `TraceCertificate.v0` (`trace_certificate.json`) |
| **output handoff kind** | `certificate_to_bundle` |
| **valid success status** | `CertificateChecked` |
| **valid failure status** | `Rejected` |

## Handoff manifests

| Direction | File | `handoff_kind` |
|-----------|------|----------------|
| LabTrust-Gym → CertifyEdge | `labtrust_to_certifyedge_handoff.json` | `runtime_to_certificate` |
| CertifyEdge → LabTrust-Gym | `certifyedge_to_labtrust_handoff.json` | `certificate_to_bundle` |

Property profile registry (`templates/profiles/`):

- `schema.json` — JSON Schema for profile documents
- `<property_id>.json` — maps `property_id` to STL template, PCS artifact types, and certificate statuses

| Profile | Input | Output | STL |
|---------|-------|--------|-----|
| `hospital_lab.qc_release.json` | `LabTrust.Trace.v0` | `TraceCertificate.v0` | `templates/hospital_lab/qc_release.stl` |
| `hospital_lab.no_release_before_qc.json` | `LabTrust.Trace.v0` | `TraceCertificate.v0` | `templates/hospital_lab/no_release_before_qc.stl` |
| `agent_tool_use.safety_v0.json` | `ToolUseTrace.v0` | `ToolUseCertificate.v0` | `templates/tool_use/no_unauthorized_tool.stl` |

Each profile JSON defines:

- `property_id`, `template`, `input_trace_artifact`, `output_certificate_artifact`, `counterexample_artifact`
- `valid_success_status`, `valid_failure_status`
- `release_mode_required_fields` (release-mode certificate field gate; alias `required_release_fields`)
- `repair_hints` — map of `failure_code` → `{ kind, command, responsible_component? }` for PF explain mode

Validate all profiles: `make validate-profiles` or `bash scripts/validate-profiles.sh`.

`emit-pcs-certificate --handoff` resolves `invariants.property_id` through the registry (unknown IDs and template mismatches fail). Add a new workflow by adding a profile JSON file and STL template; no emit logic changes required.

## Counterexample behavior

When temporal checking fails:

1. Emit `TraceCertificate.v0` with `status = Rejected`.
2. Write `counterexample.json` (default beside `--out`, or `--counterexample-out`).
3. Set `counterexample_ref` on the certificate when a path is available.
4. Emit outbound `certificate_to_bundle` handoff with `invariants.status = Rejected`, `invariants.counterexample_ref = counterexample.json`, and empty `expected_outputs` (downstream must not treat the bundle as admissible).

Explain counterexamples: `certifyedge explain-counterexample`.

## Release-mode provenance

With `--release-mode`:

- CertifyEdge `source_commit` must resolve to a non-placeholder git commit (`CERTIFYEDGE_SOURCE_COMMIT` or repo HEAD).
- Inbound `HandoffManifest.v0` is validated with vendored schema, digest, and `pcs validate` when the pcs-core CLI is installed.
- Outbound handoff and certificate artifacts are validated the same way before exit.
- `source_repo` must match the canonical CertifyEdge repository URL on verify/emit.

## CLI

Property profiles:

```bash
certifyedge profiles list
certifyedge profiles explain hospital_lab.qc_release
certifyedge profiles validate templates/profiles/hospital_lab.qc_release.json
```

Handoff-driven emit (profile registry defaults to `templates/profiles`):

```bash
certifyedge emit-pcs-certificate \
  --release-mode \
  --handoff labtrust_to_certifyedge_handoff.json \
  --profile-registry templates/profiles \
  --out trace_certificate.json \
  --summary-out certificate_summary.json \
  --handoff-out certifyedge_to_labtrust_handoff.json
```

Legacy path (no handoff): `--spec`, `--trace`, `--out`.

Failed checks print JSON repair hints on stderr (for PF explain mode); rejected emits still exit 0 when artifacts are written.

## Registry

See `pcs_registry/TraceCertificate.v0.registry.json` and `pcs_registry/ToolUseCertificate.v0.registry.json` (pcs-core `ArtifactRegistry.v0` `registry_entry` shape):

- `schema_owner`: pcs-core
- `runtime_producer` / `allowed_runtime_producers`: CertifyEdge
- `semantic_checks`: structured objects (`check_id`, `severity`, `responsible_component`, `execution_required_in_release_mode`, `allowed_to_skip`) aligned with pcs-core
- `consumer_repos`: CertifyEdge, LabTrust-Gym, Provability Fabric, Scientific Memory (promoted into pcs-core)
- `canonical_hash_required` / `release_mode_required`: true

Validate locally: `make check-pcs-registry` (requires `PCS_CORE_PATH` or sibling `pcs-core` checkout).

Release-mode emit runs vendored schema validation, then `pcs registry check-artifact` when the pcs CLI is installed (warning and skip in local dev without pcs).
