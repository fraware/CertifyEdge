# LabTrust trace adapter

The `labtrust-adapter` crate parses LabTrust `trace.json` documents produced by [LabTrust-Gym](https://github.com/fraware/LabTrust-Gym) and computes trace digests compatible with LabTrust’s hash chain.

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

For v0.1, `templates/hospital_lab/*.stl` files are **not** parsed as full STL formulas. They use a small LabTrust temporal-property DSL: a property id line, optional `allowed_release_roles:`, and comments. The checker in `services/labtrust-adapter/src/temporal.rs` implements the semantics directly.

Do not assume general STL operators (e.g. global `G`, bounded `F`, continuous signals) apply to these templates.

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
