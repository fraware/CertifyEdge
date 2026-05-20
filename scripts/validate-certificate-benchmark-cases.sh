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

REQUIRED = {
    "hospital_lab.qc_release": {
        "valid",
        "invalid_missing_required_field",
        "invalid_hash_mismatch",
        "invalid_policy_or_property_violation",
        "invalid_source_provenance",
        "rejected_certificate",
    },
    "agent_tool_use.safety_v0": {
        "valid",
        "invalid_missing_required_field",
        "invalid_hash_mismatch",
        "invalid_policy_or_property_violation",
        "invalid_source_provenance",
        "rejected_certificate",
        "unauthorized_tool_call",
        "missing_policy_hash",
        "unknown_authorization_status",
        "policy_hash_mismatch",
    },
    "scientific_computation.reproducibility_v0": {
        "valid",
        "invalid_missing_required_field",
        "invalid_hash_mismatch",
        "invalid_policy_or_property_violation",
        "invalid_source_provenance",
        "rejected_certificate",
        "dataset_hash_mismatch",
        "environment_digest_mismatch",
        "result_hash_mismatch",
        "missing_code_commit",
        "nonzero_exit_code",
    },
}

for pid, suite in expected.items():
    found: set[str] = set()
    for case_json in (bench_root / suite).glob("*/*/case.json"):
        doc = json.loads(case_json.read_text(encoding="utf-8"))
        cat = doc.get("case_category")
        if cat:
            found.add(cat)
    missing = sorted(REQUIRED[pid] - found)
    if missing:
        print(
            f"error: suite {suite} missing case categories: {', '.join(missing)}",
            file=sys.stderr,
        )
        sys.exit(1)

print("OK certificate benchmark profile coverage")
PY

echo "OK certificate benchmark cases"
