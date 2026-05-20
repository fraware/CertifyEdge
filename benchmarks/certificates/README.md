# Certificate benchmarks

Profile-driven benchmark cases for PCS certificate emission. Each profile has
`valid/` and `invalid/` case directories containing:

- `case.json` — `case_category`, expected status, failure code, counterexample, and repair-hint expectations
- `handoff.json` — runtime handoff manifest (digest refreshed at run time)
- Input artifacts referenced by the handoff (`trace.json`, computation receipts, etc.)

Generate cases from committed test fixtures:

```bash
python3 scripts/generate-certificate-benchmark-cases.py
```

Run a suite:

```bash
certifyedge benchmark certificates \
  --profile agent_tool_use.safety_v0 \
  --cases benchmarks/certificates/tool_use_safety \
  --out benchmark_runs/tool_use_safety \
  --json-summary
```

Outputs under `--out` (validated against vendored pcs-core schemas before exit):

- `benchmark_report.v0.json` — pcs-core `BenchmarkReport.v0` (suite aggregate for pcs-bench)
- `benchmark_run.<case_id>.v0.json` — pcs-core per-case `BenchmarkRun.v0`
- `certificate_coverage_report.v0.json` — pcs-core `CoverageReport.v0` (`certificate_completeness`)
- `profile_coverage_report.v0.json` — pcs-core `ProfileCoverageReport.v0`
- `certificate_benchmark_suite.v0.json` — CertifyEdge `CertificateBenchmarkSuite.v0` with per-case metrics and `repair_hint_quality`
- `repair_hint_quality_report.v0.json` — pcs-core `CoverageReport.v0` for repair-hint scoring
- `repair_hint_manifest.v0.json` — per-case repair-hint quality map (pcs-bench ingest)
- `benchmark_summary.v0.json` — compact summary when `--json-summary` is set

Validate the committed case tree without running emit:

```bash
certifyedge benchmark validate-cases
make validate-certificate-benchmarks
```

All three profiles:

```bash
make benchmark-certificates
```
