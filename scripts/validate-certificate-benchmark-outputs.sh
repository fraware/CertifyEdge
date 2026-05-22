#!/usr/bin/env bash
# Validate benchmark_runs/* output trees (CertifyEdge schemas + optional pcs-core).
set -eu
(set -o pipefail) 2>/dev/null && set -o pipefail || true

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

python3 "$ROOT/scripts/validate-pcs-bench-ingest-shape.py" "$ROOT"

if [[ -d "$PCS_CORE/schemas" ]] || [[ -d "$PCS_CORE/python/pcs_core" ]]; then
  export PCS_CORE_PATH="$PCS_CORE"
  for suite in hospital_lab_qc_release tool_use_safety computation_reproducibility; do
    bash "$ROOT/scripts/validate-pcs-bench-ingest-consumer.sh" \
      "$ROOT/benchmark_runs/$suite/pcs_bench_ingest.v0.json"
  done
fi

echo "OK certificate benchmark output trees"
