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
for key, value in pcs_defs.items():
    if not key.startswith("benchmark_") and key != "conformance_run_ref":
        continue
    if local_defs.get(key) != value:
        errors.append(f"common.defs drift: {key}")

if errors:
    for err in errors:
        print(f"error: {err}", file=sys.stderr)
    sys.exit(1)
print("OK pcs-core benchmark schemas match CertifyEdge vendored copies")
PY
