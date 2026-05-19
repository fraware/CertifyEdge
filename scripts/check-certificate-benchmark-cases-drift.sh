#!/usr/bin/env bash
# Fail if benchmark case trees are missing required files after generation.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash ./scripts/validate-certificate-benchmark-cases.sh

# Ensure each case has handoff + at least one input artifact besides case.json.
python3 - "$ROOT/benchmarks/certificates" <<'PY'
import sys
from pathlib import Path

bench = Path(sys.argv[1])
errors: list[str] = []

for case_json in bench.glob("*/*/*/case.json"):
    case_dir = case_json.parent
    handoff = case_dir / "handoff.json"
    if not handoff.is_file():
        errors.append(f"{case_dir}: missing handoff.json")
        continue
    artifacts = [p for p in case_dir.iterdir() if p.is_file() and p.name not in ("case.json", "handoff.json")]
    if not artifacts:
        errors.append(f"{case_dir}: no input artifacts")

if errors:
    for e in errors:
        print(f"error: {e}", file=sys.stderr)
    sys.exit(1)
print("OK benchmark case artifact layout")
PY
