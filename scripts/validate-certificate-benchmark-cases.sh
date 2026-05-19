#!/usr/bin/env bash
# Validate benchmarks/certificates case.json files and profile benchmark coverage.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

cargo build -p certifyedge --quiet
cargo run -p certifyedge --quiet -- benchmark validate-cases

python3 - "$ROOT" <<'PY'
import json
import sys
from pathlib import Path

root = Path(sys.argv[1])
profiles_dir = root / "templates/profiles"
bench_root = root / "benchmarks/certificates"

# property_id -> suite directory (must match certificate_benchmark.rs)
expected = {
    "hospital_lab.qc_release": "hospital_lab_qc_release",
    "agent_tool_use.safety_v0": "tool_use_safety",
    "scientific_computation.reproducibility_v0": "computation_reproducibility",
}

for pid, suite in expected.items():
    suite_dir = bench_root / suite
    if not suite_dir.is_dir():
        print(f"error: missing benchmark suite for {pid}: {suite_dir}", file=sys.stderr)
        sys.exit(1)
    for kind in ("valid", "invalid"):
        if not (suite_dir / kind).is_dir():
            print(f"error: {suite_dir} missing {kind}/", file=sys.stderr)
            sys.exit(1)

# Profiles without a benchmark suite must be explicitly optional (none today).
for path in sorted(profiles_dir.glob("*.json")):
    if path.name == "schema.json":
        continue
    doc = json.loads(path.read_text(encoding="utf-8"))
    pid = doc["property_id"]
    if pid in expected:
        continue
    print(
        f"warning: profile {pid} has no certificate benchmark suite "
        f"(add to expected map or document as optional)",
        file=sys.stderr,
    )

print("OK certificate benchmark profile coverage")
PY

echo "OK certificate benchmark cases"
