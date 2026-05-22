# Property profiles and registry

Commands, benchmarks, and the release checklist appear in the [PCS guide](pcs-guide.md). CertifyEdge maps **property profiles** (`templates/profiles/<property_id>.json`) to input artifacts, STL templates, output certificate types, and handoff kinds.

## Default LabTrust profile

| Field | Value |
|-------|--------|
| **component** | CertifyEdge |
| **input** | `trace.json` (`LabTrust.Trace.v0`) |
| **input handoff** | `runtime_to_certificate` |
| **property** | `hospital_lab.qc_release` |
| **output** | `TraceCertificate.v0` |
| **output handoff** | `certificate_to_bundle` |
| **success status** | `CertificateChecked` |
| **failure status** | `Rejected` |

## All v0.1 profiles

| Profile | Input | Output | Template |
|---------|-------|--------|----------|
| `hospital_lab.qc_release` | LabTrust trace | `TraceCertificate.v0` | `templates/hospital_lab/qc_release.stl` |
| `hospital_lab.no_release_before_qc` | LabTrust trace | `TraceCertificate.v0` | `templates/hospital_lab/no_release_before_qc.stl` |
| `agent_tool_use.safety_v0` | Tool-use trace | `ToolUseCertificate.v0` | `templates/tool_use/no_unauthorized_tool.stl` |
| `scientific_computation.reproducibility_v0` | Computation receipts (+ supporting) | `ComputationWitness.v0` | `templates/computation/result_hashes_match.stl` |

Computation profiles list `supporting_artifacts` (`DatasetReceipt.v0`, `EnvironmentReceipt.v0`, `ResultArtifact.v0`), and their handoff invariants use `run_hash`.

## Profile document fields

Each `templates/profiles/<id>.json` carries `property_id`, `template`, input and output artifact types, counterexample artifact names, `valid_success_status`, `valid_failure_status`, `release_mode_required_fields`, a `formalization` block with predicate name and required fields, and `repair_hints` that map `failure_code` values to repair commands for downstream explain tooling.

| Profile family | Formal predicate | Typical required fields |
|----------------|------------------|-------------------------|
| LabTrust / tool-use | `CertificateMatchesRuntime` | `certificate_id`, `trace_hash`, `status`, provenance |
| Computation | `ComputationWitnessBindsResults` | `witness_id`, hashes, `status` |

Emit formal facts with `--formal-facts-out certificate_formal_facts.json` to produce `CertificateFormalFacts.v0`. Run `make validate-profiles` to check every profile file.

## Handoff kinds

| Direction | File | `handoff_kind` |
|-----------|------|----------------|
| Runtime → CertifyEdge | `labtrust_to_certifyedge_handoff.json` | `runtime_to_certificate` |
| CertifyEdge → bundle | `certifyedge_to_labtrust_handoff.json` | `certificate_to_bundle` |

`emit-pcs-certificate --handoff` resolves `invariants.property_id` through the registry.

## Registry contributions

Promote these files into pcs-core `ArtifactRegistry.v0` when upstream accepts the entry.

| File | Output artifact |
|------|-----------------|
| `pcs_registry/TraceCertificate.v0.registry.json` | `TraceCertificate.v0` |
| `pcs_registry/ToolUseCertificate.v0.registry.json` | `ToolUseCertificate.v0` |
| `pcs_registry/ComputationWitness.v0.registry.json` | `ComputationWitness.v0` |
| `pcs_registry/CertificateFormalFacts.v0.registry.json` | `CertificateFormalFacts.v0` |
| `pcs_registry/BenchmarkRun.v0.registry.json` | `BenchmarkRun.v0` |
| `pcs_registry/CertificateCoverageReport.v0.registry.json` | `CertificateCoverageReport.v0` |

Run `make check-pcs-registry` with `PCS_CORE_PATH` or a sibling `pcs-core` checkout to detect drift.

## Benchmarks

Case layout and producer commands appear in [benchmarks/certificates/README.md](../benchmarks/certificates/README.md) and in the [PCS guide certificate benchmarks section](pcs-guide.md#certificate-benchmarks).
