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

# Live-required minimums per benchmarked profile (pcs-bench ingestion).
LIVE_REQUIRED = {
    "valid": 1,
    "invalid_field_or_hash": {
        "invalid_missing_required_field",
        "invalid_hash_mismatch",
        "invalid_source_provenance",
    },
    "rejected_certificate": 1,
    "repair_hint_quality": 1,
    "formal_facts": 1,
}

INVALID_FIELD_OR_HASH = LIVE_REQUIRED["invalid_field_or_hash"]


def count_categories(suite: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for case_json in (bench_root / suite).glob("*/*/case.json"):
        doc = json.loads(case_json.read_text(encoding="utf-8"))
        cat = doc.get("case_category")
        if not cat:
            continue
        counts[cat] = counts.get(cat, 0) + 1
    return counts


for pid, suite in expected.items():
    counts = count_categories(suite)
    errors: list[str] = []

    if counts.get("valid", 0) < LIVE_REQUIRED["valid"]:
        errors.append(f"need >= {LIVE_REQUIRED['valid']} valid case(s)")

    for cat in sorted(INVALID_FIELD_OR_HASH):
        if counts.get(cat, 0) < 1:
            errors.append(f"missing invalid field/hash category: {cat}")

    if counts.get("rejected_certificate", 0) < LIVE_REQUIRED["rejected_certificate"]:
        errors.append("need >= 1 rejected_certificate case")

    if counts.get("repair_hint_quality", 0) < LIVE_REQUIRED["repair_hint_quality"]:
        errors.append("need >= 1 repair_hint_quality case")

    if counts.get("formal_facts", 0) < LIVE_REQUIRED["formal_facts"]:
        errors.append("need >= 1 formal_facts case")

    if errors:
        print(f"error: suite {suite} ({pid}):", file=sys.stderr)
        for msg in errors:
            print(f"  - {msg}", file=sys.stderr)
        sys.exit(1)

print("OK certificate benchmark profile coverage")
PY

echo "OK certificate benchmark cases"
