# LabTrust trace adapter

> Part of the PCS v0.1 path — overview: [PCS guide](pcs-guide.md).

The `labtrust-adapter` crate parses LabTrust `trace.json` documents from [LabTrust-Gym](https://github.com/fraware/LabTrust-Gym) and computes trace digests compatible with LabTrust’s hash chain.

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

Each event includes `event_hash` and `previous_event_hash` forming a chain from the genesis hash (`64` zero digits).

## Hash rules

| Digest | Input |
|--------|--------|
| Event hash | SHA-256 of canonical JSON of the event body (excluding `event_hash`) |
| Trace hash | PCS `sha256:` digest of `{ schema_version, version, run_id, sample_id, event_hashes[] }` (matches LabTrust-Gym `compute_trace_hash`) |

Canonical JSON uses sorted object keys and compact separators, matching `labtrust_gym.pcs.hash` and pcs-core.

## Validation

`validate_trace` checks:

- Required top-level and per-event fields
- Hash chain integrity
- `trace_hash` recomputation

Malformed traces fail with reason `malformed_trace`.

## Temporal property profile (`.stl` files)

PCS v0.1 uses `templates/hospital_lab/*.stl` as the **LabTrust temporal-property profile** (v0.1), not as general STL:

| Supported in profile | Not implemented |
|---------------------|-----------------|
| Property id (`property: hospital_lab.*`) | STL formula grammar (`G`, `F`, until, etc.) |
| `allowed_release_roles:` | Continuous-time or signal semantics |
| Comments | Arbitrary compositional specs beyond the three hospital-lab properties |

The checker in `services/labtrust-adapter/src/temporal.rs` encodes the three properties directly (`no_release_before_qc`, `authorized_release_only`, `qc_release`). Do not document or depend on full STL semantics unless a future version adds a real parser.

## Property templates

Hospital-lab profile files under `templates/hospital_lab/` map to property IDs:

| Template | Property ID |
|----------|-------------|
| `no_release_before_qc.stl` | `hospital_lab.no_release_before_qc` |
| `authorized_release_only.stl` | `hospital_lab.authorized_release_only` |
| `qc_release.stl` | `hospital_lab.qc_release` |

## Fixtures

Golden traces live in `tests/labtrust/`. Regenerate after workflow changes:

```bash
cargo test -p certifyedge-integration write_fixtures -- --ignored --nocapture
```
