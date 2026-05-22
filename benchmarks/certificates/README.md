# Certificate benchmark cases

> **Commands and release checklist:** [docs/pcs-guide.md](../../docs/pcs-guide.md#certificate-benchmarks)

Each profile has `valid/` and `invalid/` case directories:

- `case.json` — expected status, failure code, repair-hint expectations
- `handoff.json` — runtime handoff manifest (digest refreshed at run time)
- Input artifacts referenced by the handoff

## Suites

| Profile ID | Cases directory | Output |
|------------|-----------------|--------|
| `hospital_lab.qc_release` | `hospital_lab_qc_release/` | `benchmark_runs/hospital_lab_qc_release/` |
| `agent_tool_use.safety_v0` | `tool_use_safety/` | `benchmark_runs/tool_use_safety/` |
| `scientific_computation.reproducibility_v0` | `computation_reproducibility/` | `benchmark_runs/computation_reproducibility/` |

## Required case categories (per profile)

At least: 1 `valid`, 3 invalid field/hash cases, 1 `rejected_certificate`, 1 `repair_hint_quality`, 1 `formal_facts`.

Regenerate from fixtures:

```bash
python3 scripts/generate-certificate-benchmark-cases.py
```

## Outputs (under `benchmark_runs/<suite>/`)

| File | Role |
|------|------|
| `pcs_bench_ingest.v0.json` | Primary ingest bundle for pcs-bench |
| `benchmark_report.v0.json` | Aggregate report |
| `runs/<case_id>.benchmark_run.v0.json` | Per-case run record |
| `failure_localization/*.json` | Per invalid/rejected case |
| `explain_quality/*.json` | Per rejection/repair-hint case |

Schema details: [schemas/pcs/README.md](../../schemas/pcs/README.md).
