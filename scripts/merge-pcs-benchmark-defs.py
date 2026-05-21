#!/usr/bin/env python3
"""Merge pcs-core benchmark-related $defs into CertifyEdge common.defs.json."""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PCS_CORE = Path(
    sys.argv[1] if len(sys.argv) > 1 else ROOT.parent / "pcs-core"
)
pcs_path = PCS_CORE / "schemas" / "common.defs.json"
local_path = ROOT / "schemas" / "pcs" / "common.defs.json"

pcs = json.loads(pcs_path.read_text(encoding="utf-8"))
local = json.loads(local_path.read_text(encoding="utf-8"))
pcs_defs = pcs.get("$defs", {})
local_defs = local.setdefault("$defs", {})

merge_keys = [
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

for key in merge_keys:
    if key in local_defs and key.startswith("certificate_benchmark"):
        continue
    local_defs[key] = pcs_defs[key]

local_path.write_text(json.dumps(local, indent=2) + "\n", encoding="utf-8")
print(f"Merged {len(merge_keys)} benchmark defs into {local_path}")
