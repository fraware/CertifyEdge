# Certificate benchmark cases

Commands and the release checklist appear in [docs/pcs-guide.md](../../docs/pcs-guide.md#certificate-benchmarks).

Each profile maintains `valid/` and `invalid/` case directories. Every case includes `case.json` with expected status and failure metadata, `handoff.json` with a runtime handoff manifest whose digest is refreshed at run time, and the input artifacts referenced by the handoff.

## Suites

| Profile ID | Cases directory | Output |
|------------|-----------------|--------|
| `hospital_lab.qc_release` | `hospital_lab_qc_release/` | `benchmark_runs/hospital_lab_qc_release/` |
| `agent_tool_use.safety_v0` | `tool_use_safety/` | `benchmark_runs/tool_use_safety/` |
| `scientific_computation.reproducibility_v0` | `computation_reproducibility/` | `benchmark_runs/computation_reproducibility/` |

## Required case categories (per profile)

Each benchmarked profile includes at least one `valid` case, three invalid field or hash cases, one `rejected_certificate` case, one `repair_hint_quality` case, and one `formal_facts` case.

Regenerate cases from committed fixtures with the commands below.

```bash
python3 scripts/generate-certificate-benchmark-cases.py
python scripts/generate-certificate-benchmark-cases.py
make PYTHON=python generate-certificate-benchmarks
```

## Outputs (under `benchmark_runs/<suite>/`)

| File | Role |
|------|------|
| `pcs_bench_ingest.v0.json` | Primary ingest bundle for pcs-bench |
| `benchmark_report.v0.json` | Aggregate report |
| `runs/<case_id>.benchmark_run.v0.json` | Per-case run record |
| `failure_localization/*.json` | Per invalid or rejected case |
| `explain_quality/*.json` | Per rejection or repair-hint case |

Schema names and sync commands appear in [schemas/pcs/README.md](../../schemas/pcs/README.md).
