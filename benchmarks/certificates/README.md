# Certificate benchmarks

Profile-driven benchmark cases for PCS certificate emission. Each profile has
`valid/` and `invalid/` case directories containing:

- `case.json` — expected status, failure code, counterexample, and repair-hint expectations
- `handoff.json` — runtime handoff manifest (digest refreshed at run time)
- Input artifacts referenced by the handoff (`trace.json`, computation receipts, etc.)

Generate cases from committed test fixtures:

```bash
python3 scripts/generate-certificate-benchmark-cases.py
```

Run a suite:

```bash
certifyedge benchmark certificates \
  --profile hospital_lab.qc_release \
  --cases benchmarks/certificates/hospital_lab_qc_release \
  --out benchmark_runs/hospital_lab_qc_release
```

Outputs under `--out` (validated against vendored PCS schemas before exit):

- `benchmark_run.v0.json` — `BenchmarkRun.v0` with per-case results and aggregate pass/fail
- `certificate_coverage_report.v0.json` — `CertificateCoverageReport.v0` with repair-hint accuracy and nested `ProfileCoverageReport.v0`

Validate the committed case tree without running emit:

```bash
certifyedge benchmark validate-cases
make validate-certificate-benchmarks
```

All three profiles:

```bash
make benchmark-certificates
```
