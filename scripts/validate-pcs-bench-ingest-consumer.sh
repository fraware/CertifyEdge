#!/usr/bin/env bash
# Validate CertifyEdge pcs_bench_ingest.v0.json using pcs-bench (preferred) or pcs-core semantics.
set -eu
(set -o pipefail) 2>/dev/null && set -o pipefail || true

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

PYTHON="${PYTHON:-}"
if [[ -z "$PYTHON" ]]; then
  for candidate in python3 python py; do
    if command -v "$candidate" >/dev/null 2>&1; then
      PYTHON="$candidate"
      break
    fi
  done
fi
if [[ -z "$PYTHON" ]]; then
  echo "error: python3, python, or py required on PATH" >&2
  exit 1
fi

INPUT="${1:-benchmark_runs/tool_use_safety/pcs_bench_ingest.v0.json}"
RELEASE_GRADE="${PCS_BENCH_RELEASE_GRADE:-}"
if [[ "${2:-}" == "--release-grade" ]]; then
  RELEASE_GRADE=1
fi
PCS_CORE="${PCS_CORE_PATH:-${PCS_CORE_ROOT:-../pcs-core}}"

if [[ ! -f "$INPUT" ]]; then
  echo "error: missing ingest file: $INPUT (run: make pcs-bench-producer)" >&2
  exit 1
fi

if command -v pcs-bench >/dev/null 2>&1; then
  echo "validate-ingest via pcs-bench: $INPUT"
  if [[ -n "$RELEASE_GRADE" ]]; then
    pcs-bench validate-ingest --input "$INPUT" --pcs-core "$PCS_CORE" --release-grade
  else
    pcs-bench validate-ingest --input "$INPUT" --pcs-core "$PCS_CORE"
  fi
  exit 0
fi

if [[ ! -d "$PCS_CORE/python/pcs_core" ]]; then
  echo "error: pcs-bench not on PATH and pcs-core python package missing at $PCS_CORE" >&2
  exit 1
fi

echo "validate-ingest via pcs-core (pcs validate + semantic checks): $INPUT"
export PYTHONPATH="$PCS_CORE/python${PYTHONPATH:+:$PYTHONPATH}"
if [[ -n "$RELEASE_GRADE" ]]; then
  export PCS_BENCH_RELEASE_GRADE=1
fi
"$PYTHON" - <<'PY' "$INPUT" "${2:-}"
import json
import os
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
release_grade = os.environ.get("PCS_BENCH_RELEASE_GRADE") == "1" or (
    len(sys.argv) > 2 and sys.argv[2] == "--release-grade"
)
if release_grade:
    from pcs_core.benchmark_ingest import validate_benchmark_ingest_file

    tier_errors = validate_benchmark_ingest_file(path, check_release_grade=True)
    errors.extend(err for err in tier_errors if err not in errors)
if errors:
    for err in errors:
        print(f"error: {err}", file=sys.stderr)
    raise SystemExit(1)
grade_note = " (release-grade)" if release_grade else ""
print(f"OK pcs-core ingest validation{grade_note}: {path}")
PY
