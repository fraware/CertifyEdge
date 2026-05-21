# Certificate benchmarks

Profile-driven benchmark cases for PCS certificate emission. Each profile has
`valid/` and `invalid/` case directories containing:

- `case.json` — `case_category`, expected status, failure code, counterexample, repair-hint, and formal-facts expectations
- `handoff.json` — runtime handoff manifest (digest refreshed at run time)
- Input artifacts referenced by the handoff (`trace.json`, computation receipts, etc.)

## Live-required categories (per profile)

Each benchmarked profile must include at least:

- 1 `valid` case
- 3 invalid field/hash cases (`invalid_missing_required_field`, `invalid_hash_mismatch`, `invalid_source_provenance`)
- 1 `rejected_certificate` case
- 1 `repair_hint_quality` case
- 1 `formal_facts` case

Generate cases from committed test fixtures:

```bash
py -3 scripts/generate-certificate-benchmark-cases.py
```

Run a suite:

```bash
certifyedge benchmark certificates \
  --profile agent_tool_use.safety_v0 \
  --cases benchmarks/certificates/tool_use_safety \
  --out benchmark_runs/tool_use_safety \
  --json-summary
```

## Outputs under `--out`

| File | Role |
|------|------|
| `benchmark_report.v0.json` | pcs-core suite aggregate |
| `runs/<case_id>.benchmark_run.v0.json` | Per-case `CertificateBenchmarkRun.v0` (pcs `BenchmarkRun` core + extensions) |
| `certificate_coverage_report.v0.json` | CertifyEdge-native `CertificateCoverageReport.v0` |
| `profile_coverage_report.v0.json` | pcs-core `ProfileCoverageReport.v0` |
| `certificate_benchmark_suite.v0.json` | CertifyEdge suite metrics + nested coverage |
| `repair_hint_quality_report.v0.json` | pcs-core `CoverageReport.v0` for repair-hint scoring |
| `repair_hint_manifest.v0.json` | Per-case repair-hint quality map |
| `pcs_bench_ingest.v0.json` | Single-file pcs-bench ingest bundle (primary entry point) |
| `benchmark_summary.v0.json` | pcs-bench-normalized summary when `--json-summary` is set |

Optional: `--validate-pcs-core-output ../pcs-core` validates against an external pcs-core checkout.

Validate the committed case tree without running emit:

```bash
certifyedge benchmark validate-cases
make validate-certificate-benchmarks
```

All three profiles:

```bash
make benchmark-certificates
```
