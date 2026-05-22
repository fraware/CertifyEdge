#!/usr/bin/env bash
# Validate CertifyEdge pcs_bench_ingest.v0.json using pcs-bench (preferred) or pcs-core semantics.
set -eu
(set -o pipefail) 2>/dev/null && set -o pipefail || true

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

INPUT="${1:-benchmark_runs/tool_use_safety/pcs_bench_ingest.v0.json}"
PCS_CORE="${PCS_CORE_PATH:-${PCS_CORE_ROOT:-../pcs-core}}"

if [[ ! -f "$INPUT" ]]; then
  echo "error: missing ingest file: $INPUT (run: make pcs-bench-producer)" >&2
  exit 1
fi

if command -v pcs-bench >/dev/null 2>&1; then
  echo "validate-ingest via pcs-bench: $INPUT"
  pcs-bench validate-ingest --input "$INPUT" --pcs-core "$PCS_CORE"
  exit 0
fi

if [[ ! -d "$PCS_CORE/python/pcs_core" ]]; then
  echo "error: pcs-bench not on PATH and pcs-core python package missing at $PCS_CORE" >&2
  exit 1
fi

echo "validate-ingest via pcs-core (pcs validate + semantic checks): $INPUT"
export PYTHONPATH="$PCS_CORE/python${PYTHONPATH:+:$PYTHONPATH}"
python3 - <<'PY' "$INPUT"
import json
import sys
from pathlib import Path

from pcs_core.benchmark_validate import validate_pcs_bench_ingest_semantics
from pcs_core.validate import ValidationError, validate_file

path = Path(sys.argv[1])
errors: list[str] = []
try:
    validate_file(path)
except ValidationError as exc:
    errors.append(str(exc))
    errors.extend(exc.errors)
doc = json.loads(path.read_text(encoding="utf-8"))
errors.extend(validate_pcs_bench_ingest_semantics(doc))
if errors:
    for err in errors:
        print(f"error: {err}", file=sys.stderr)
    raise SystemExit(1)
print(f"OK pcs-core ingest validation: {path}")
PY
