#!/usr/bin/env python3
"""Align RELEASE_FIXTURE_MANIFEST repo commits with artifact provenance fields."""
from __future__ import annotations

import json
import sys
from pathlib import Path


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: sync-release-manifest-commits.py <release-run-dir>", file=sys.stderr)
        return 2

    run = Path(sys.argv[1])
    manifest_path = run / "RELEASE_FIXTURE_MANIFEST.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    certified = json.loads((run / "science_claim_bundle.certified.json").read_text(encoding="utf-8"))
    trace_cert = json.loads((run / "trace_certificate.json").read_text(encoding="utf-8"))

    manifest["labtrust_gym_commit"] = certified.get("source_commit")
    manifest["certifyedge_commit"] = trace_cert.get("source_commit")

    vr_path = run / "verification_result.json"
    if vr_path.is_file():
        vr = json.loads(vr_path.read_text(encoding="utf-8"))
        manifest["provability_fabric_commit"] = vr.get("source_commit")

    sm_path = run / "scientific_memory_import_report.json"
    if sm_path.is_file():
        report = json.loads(sm_path.read_text(encoding="utf-8"))
        manifest["scientific_memory_commit"] = report.get("scientific_memory_commit") or report.get(
            "source_commit"
        )

    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(f"synced commits in {manifest_path.name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
