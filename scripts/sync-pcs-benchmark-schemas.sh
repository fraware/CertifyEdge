#!/usr/bin/env bash
# Sync pcs-core benchmark JSON schemas into CertifyEdge without overwriting CertifyEdge-only schemas.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=lib/python_cmd.sh
. "$SCRIPT_DIR/lib/python_cmd.sh"
PY="$(resolve_python)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
PCS_CORE="${PCS_CORE_ROOT:-../pcs-core}"
DEST="$ROOT/schemas/pcs"

if [[ ! -d "$PCS_CORE/schemas" ]]; then
  echo "pcs-core not found at $PCS_CORE (set PCS_CORE_ROOT)" >&2
  exit 1
fi

mkdir -p "$DEST"
for name in \
  BenchmarkReport.v0.schema.json \
  BenchmarkRun.v0.schema.json \
  CoverageReport.v0.schema.json \
  ProfileCoverageReport.v0.schema.json \
  PcsBenchIngest.v0.schema.json \
  FailureLocalizationResult.v0.schema.json \
  ExplainQualityReport.v0.schema.json \
  MetricSummary.v0.schema.json \
  BenchmarkArtifactRef.v0.schema.json
do
  cp -f "$PCS_CORE/schemas/$name" "$DEST/"
done

"$PY" - "$PCS_CORE/schemas/common.defs.json" "$DEST/common.defs.json" <<'PY'
import json
import sys
from pathlib import Path

pcs_path, local_path = Path(sys.argv[1]), Path(sys.argv[2])
pcs = json.loads(pcs_path.read_text(encoding="utf-8"))
local = json.loads(local_path.read_text(encoding="utf-8"))
pcs_defs = pcs.get("$defs", {})
local_defs = local.setdefault("$defs", {})

# Merge pcs-core benchmark vocabulary without clobbering CertifyEdge-only defs.
MERGE_KEYS = [
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
]
for key in MERGE_KEYS:
    if key in local_defs and key.startswith("certificate_benchmark"):
        continue
    local_defs[key] = pcs_defs[key]

local_path.write_text(json.dumps(local, indent=2) + "\n", encoding="utf-8")
print(f"Merged {len(MERGE_KEYS)} benchmark defs into {local_path}")
PY

"$PY" "$SCRIPT_DIR/merge-pcs-benchmark-defs.py" "$PCS_CORE"

echo "Synced pcs-core benchmark schemas -> $DEST"
echo "Preserved CertifyEdge-only: BenchmarkCaseSpec, CertificateBenchmarkRun, CertificateCoverageReport, CertificateBenchmarkSuite"
