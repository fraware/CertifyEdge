# LabTrust trace adapter

The PCS v0.1 path depends on this crate for trace parsing and hashing, and the [PCS guide](pcs-guide.md) explains how emitted certificates connect to the wider workflow.

The `labtrust-adapter` crate parses LabTrust `trace.json` documents from [LabTrust-Gym](https://github.com/fraware/LabTrust-Gym) and computes trace digests that align with LabTrust’s hash chain and with pcs-core expectations.

## Trace document shape

```json
{
  "version": "0",
  "artifact_kind": "Trace",
  "run_id": "qc-release",
  "sample_id": "PCS-SAMPLE-001",
  "events": [ ... ],
  "trace_hash": "sha256:..."
}
```

Each event carries `event_hash` and `previous_event_hash`, forming a chain that begins at the genesis hash of sixty-four zero digits.

## Hash rules

| Digest | Input |
|--------|--------|
| Event hash | SHA-256 of canonical JSON of the event body (excluding `event_hash`) |
| Trace hash | PCS `sha256:` digest of `{ schema_version, version, run_id, sample_id, event_hashes[] }`, matching LabTrust-Gym `compute_trace_hash` |

Canonical JSON uses sorted object keys and compact separators, following `labtrust_gym.pcs.hash` and pcs-core conventions.

## Validation

`validate_trace` checks required top-level and per-event fields, verifies hash chain integrity, and recomputes `trace_hash`. Malformed traces return reason `malformed_trace`.

## Temporal property profile (`.stl` files)

PCS v0.1 treats `templates/hospital_lab/*.stl` as the **LabTrust temporal-property profile**, a constrained format for v0.1 hospital-lab workflows.

| Provided in the profile | Deferred beyond v0.1 |
|-------------------------|---------------------|
| Property id (`property: hospital_lab.*`) | STL formula grammar (`G`, `F`, until, etc.) |
| `allowed_release_roles:` | Continuous-time or signal semantics |
| Comments | Arbitrary compositional specs beyond the three hospital-lab properties |

The checker in `services/labtrust-adapter/src/temporal.rs` encodes `no_release_before_qc`, `authorized_release_only`, and `qc_release` directly. Future versions may add a full STL parser; until then, treat these files as profile documents tied to the three named properties.

## Property templates

Hospital-lab profile files under `templates/hospital_lab/` map to property IDs as follows.

| Template | Property ID |
|----------|-------------|
| `no_release_before_qc.stl` | `hospital_lab.no_release_before_qc` |
| `authorized_release_only.stl` | `hospital_lab.authorized_release_only` |
| `qc_release.stl` | `hospital_lab.qc_release` |

## Fixtures

Golden traces live under `tests/labtrust/`. Regenerate negative fixtures after workflow changes with `cargo test -p certifyedge-integration write_fixtures -- --ignored --nocapture`.
