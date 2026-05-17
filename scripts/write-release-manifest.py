#!/usr/bin/env python3
"""Write RELEASE_FIXTURE_MANIFEST.json for a completed release-run staging directory."""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


def git_head(repo: Path) -> str | None:
    if not (repo / ".git").exists():
        return None
    out = subprocess.run(
        ["git", "-C", str(repo), "rev-parse", "HEAD"],
        check=True,
        capture_output=True,
        text=True,
    )
    return out.stdout.strip()


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: write-release-manifest.py <release-run-dir>", file=sys.stderr)
        return 2

    run = Path(sys.argv[1])
    root = Path(__file__).resolve().parents[1]
    parent = root.parent

    trace_cert = json.loads((run / "trace_certificate.json").read_text(encoding="utf-8"))
    certified = json.loads((run / "science_claim_bundle.certified.json").read_text(encoding="utf-8"))

    manifest: dict[str, object] = {
        "schema_version": "v0",
        "certificate_id": trace_cert["certificate_id"],
        "trace_hash": trace_cert["trace_hash"],
        "labtrust_gym_commit": certified.get("source_commit"),
        "certifyedge_commit": trace_cert.get("source_commit"),
        "provability_fabric_commit": None,
        "scientific_memory_commit": None,
    }

    lt = parent / "LabTrust-Gym"
    pf = parent / "Provability-Fabric"
    sm = parent / "scientific-memory"
    if head := git_head(root):
        manifest["certifyedge_commit"] = head
    if head := git_head(lt):
        manifest["labtrust_gym_commit"] = head

    vr_path = run / "verification_result.json"
    if vr_path.is_file():
        vr = json.loads(vr_path.read_text(encoding="utf-8"))
        manifest["provability_fabric_commit"] = vr.get("source_commit") or git_head(pf)

    sm_report = run / "scientific_memory_import_report.json"
    if sm_report.is_file():
        report = json.loads(sm_report.read_text(encoding="utf-8"))
        manifest["scientific_memory_commit"] = report.get("scientific_memory_commit") or report.get(
            "source_commit"
        )
    elif head := git_head(sm):
        manifest["scientific_memory_commit"] = head

    out = run / "RELEASE_FIXTURE_MANIFEST.json"
    out.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
