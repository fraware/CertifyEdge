#!/usr/bin/env bash
# Validate benchmark_runs/* output trees (CertifyEdge schemas + optional pcs-core).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

PCS_CORE="${PCS_CORE_PATH:-${PCS_CORE_ROOT:-../pcs-core}}"
EXTRA=()
if [[ -d "$PCS_CORE/schemas" ]]; then
  EXTRA=(--validate-pcs-core-output "$PCS_CORE")
fi

cargo build -p certifyedge --quiet

for suite in hospital_lab_qc_release tool_use_safety computation_reproducibility; do
  out="$ROOT/benchmark_runs/$suite"
  if [[ ! -f "$out/pcs_bench_ingest.v0.json" ]]; then
    echo "error: missing $out/pcs_bench_ingest.v0.json (run: make benchmark-certificates)" >&2
    exit 1
  fi
  cargo run -p certifyedge --quiet -- benchmark validate-output --out "$out" "${EXTRA[@]}"
done

echo "OK certificate benchmark output trees"
