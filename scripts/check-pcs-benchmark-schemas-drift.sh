#!/usr/bin/env bash
# Fail if vendored pcs-core benchmark schemas drift from upstream pcs-core.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PARENT="$(dirname "$ROOT")"
PCS_CORE="${PCS_CORE_PATH:-${PCS_CORE_ROOT:-$PARENT/pcs-core}}"
DEST="$ROOT/schemas/pcs"

if [[ ! -d "$PCS_CORE/schemas" ]]; then
  echo "error: pcs-core schemas not found at $PCS_CORE" >&2
  exit 1
fi

python3 - "$PCS_CORE/schemas" "$DEST" <<'PY'
import json
import sys
from pathlib import Path

pcs_root = Path(sys.argv[1])
local_root = Path(sys.argv[2])
errors: list[str] = []

for name in (
    "BenchmarkReport.v0.schema.json",
    "BenchmarkRun.v0.schema.json",
    "CoverageReport.v0.schema.json",
    "ProfileCoverageReport.v0.schema.json",
    "PcsBenchIngest.v0.schema.json",
    "FailureLocalizationResult.v0.schema.json",
    "ExplainQualityReport.v0.schema.json",
    "MetricSummary.v0.schema.json",
):
    upstream = pcs_root / name
    local = local_root / name
    if not local.is_file():
        errors.append(f"missing local schema: {local}")
        continue
    if upstream.read_text(encoding="utf-8") != local.read_text(encoding="utf-8"):
        errors.append(f"schema drift: {name} (run: make sync-pcs-benchmark-schemas)")

pcs_defs = json.loads((pcs_root / "common.defs.json").read_text(encoding="utf-8")).get("$defs", {})
local_defs = json.loads((local_root / "common.defs.json").read_text(encoding="utf-8")).get("$defs", {})
PCS_BENCHMARK_DEF_KEYS = {
    k
    for k in pcs_defs
    if k.startswith("benchmark_")
    or k.startswith("explain_quality")
    or k
    in (
        "conformance_run_ref",
        "nullable_benchmark_responsible_component",
        "nullable_benchmark_repair_hint_kind",
        "system_admission_outcome",
        "release_chain_status",
        "certificate_status_value",
        "scientific_memory_import_status",
        "scientific_memory_render_status",
        "metric_summary_applicability",
    )
}

for name in ("BenchmarkArtifactRef.v0.schema.json",):
    upstream = pcs_root / name
    local = local_root / name
    if upstream.is_file():
        if not local.is_file():
            errors.append(f"missing local schema: {local}")
        elif upstream.read_text(encoding="utf-8") != local.read_text(encoding="utf-8"):
            errors.append(f"schema drift: {name} (run: make sync-pcs-benchmark-schemas)")

for key in PCS_BENCHMARK_DEF_KEYS:
    value = pcs_defs[key]
    if local_defs.get(key) != value:
        errors.append(f"common.defs drift: {key}")

if errors:
    for err in errors:
        print(f"error: {err}", file=sys.stderr)
    sys.exit(1)
print("OK pcs-core benchmark schemas match CertifyEdge vendored copies")
PY
