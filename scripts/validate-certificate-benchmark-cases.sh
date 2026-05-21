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

for path in sorted(profiles_dir.glob("*.json")):
    if path.name == "schema.json":
        continue
    doc = json.loads(path.read_text(encoding="utf-8"))
    pid = doc["property_id"]
    if pid in expected:
        continue
    print(
        f"warning: profile {pid} has no certificate benchmark suite",
        file=sys.stderr,
    )

LIVE_MIN = {
    "valid": 1,
    "invalid_cases": 3,
    "rejected_certificate": 1,
    "counterexample_cases": 1,
    "repair_hint_quality": 1,
    "formal_facts": 1,
}


def suite_stats(suite: str) -> tuple[dict[str, int], int, int]:
    counts: dict[str, int] = {}
    invalid_total = 0
    counterexample_cases = 0
    for case_json in (bench_root / suite).glob("*/*/case.json"):
        doc = json.loads(case_json.read_text(encoding="utf-8"))
        kind = case_json.parent.parent.name
        if kind == "invalid":
            invalid_total += 1
        if doc.get("expect_counterexample"):
            counterexample_cases += 1
        cat = doc.get("case_category")
        if cat:
            counts[cat] = counts.get(cat, 0) + 1
    return counts, invalid_total, counterexample_cases


for pid, suite in expected.items():
    counts, invalid_total, counterexample_cases = suite_stats(suite)
    errors: list[str] = []

    if counts.get("valid", 0) < LIVE_MIN["valid"]:
        errors.append("need >= 1 valid case")
    if invalid_total < LIVE_MIN["invalid_cases"]:
        errors.append(f"need >= {LIVE_MIN['invalid_cases']} invalid cases (have {invalid_total})")
    if counts.get("rejected_certificate", 0) < LIVE_MIN["rejected_certificate"]:
        errors.append("need >= 1 rejected_certificate case")
    if counterexample_cases < LIVE_MIN["counterexample_cases"]:
        errors.append("need >= 1 case with expect_counterexample=true")
    if counts.get("repair_hint_quality", 0) < LIVE_MIN["repair_hint_quality"]:
        errors.append("need >= 1 repair_hint_quality case")
    if counts.get("formal_facts", 0) < LIVE_MIN["formal_facts"]:
        errors.append("need >= 1 formal_facts case")

    if errors:
        print(f"error: suite {suite} ({pid}):", file=sys.stderr)
        for msg in errors:
            print(f"  - {msg}", file=sys.stderr)
        sys.exit(1)

print("OK certificate benchmark profile coverage")
PY

echo "OK certificate benchmark cases"
