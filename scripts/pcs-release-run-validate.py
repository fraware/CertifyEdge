#!/usr/bin/env python3
"""Validate CertifyEdge release-run certificate identity and manifest provenance."""
from __future__ import annotations

import json
import sys
from pathlib import Path


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def check_certificate_refs(vr: dict) -> str | None:
    for check in vr.get("checks", []):
        if check.get("check_id") == "evidence_refs_complete":
            refs = (check.get("details") or {}).get("certificate_refs") or []
            if refs:
                return refs[0]
    verified = vr.get("verified_input") or {}
    return verified.get("certificate_id")


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: pcs-release-run-validate.py <release-run-dir>", file=sys.stderr)
        return 2

    run = Path(sys.argv[1])
    manifest = load_json(run / "RELEASE_FIXTURE_MANIFEST.json")
    trace_cert = load_json(run / "trace_certificate.json")
    certified = load_json(run / "science_claim_bundle.certified.json")

    cert_id = trace_cert["certificate_id"]
    bundle_cert_id = certified["certificates"][0]["certificate_id"]
    claim_ref = certified["claim_artifact"]["certificate_refs"][0]
    evidence_ref = certified["evidence_bundle"]["certificate_refs"][0]

    signed_path = run / "signed_science_claim_bundle.json"
    if not signed_path.is_file():
        print("missing signed_science_claim_bundle.json", file=sys.stderr)
        return 1

    signed = load_json(signed_path)
    signed_bundle = signed["science_claim_bundle"]
    signed_cert = signed_bundle["certificates"][0]["certificate_id"]

    if not (cert_id == bundle_cert_id == claim_ref == evidence_ref == signed_cert):
        print(
            "certificate_id mismatch in release chain:",
            cert_id,
            bundle_cert_id,
            claim_ref,
            evidence_ref,
            signed_cert,
            file=sys.stderr,
        )
        return 1

    trace_hash = trace_cert["trace_hash"]
    certified_receipt_hash = certified["runtime_receipts"][0]["trace_hash"]
    signed_receipt_hash = signed_bundle["runtime_receipts"][0]["trace_hash"]
    if trace_hash != certified_receipt_hash or trace_hash != signed_receipt_hash:
        print(
            "trace_hash mismatch in release chain:",
            trace_hash,
            certified_receipt_hash,
            signed_receipt_hash,
            file=sys.stderr,
        )
        return 1

    if trace_cert.get("trace_hash") != manifest.get("trace_hash"):
        print("trace_hash mismatch manifest vs trace_certificate", file=sys.stderr)
        return 1

    if trace_cert.get("source_commit") != manifest.get("certifyedge_commit"):
        print("certifyedge_commit mismatch manifest vs trace_certificate", file=sys.stderr)
        return 1

    lt_commit = manifest.get("labtrust_gym_commit")
    if certified.get("source_commit") != lt_commit:
        print(
            f"labtrust_gym_commit mismatch manifest vs certified bundle: "
            f"{lt_commit!r} != {certified.get('source_commit')!r}",
            file=sys.stderr,
        )
        return 1
    for receipt in certified.get("runtime_receipts") or []:
        if receipt.get("source_commit") != lt_commit:
            print("runtime_receipt source_commit != manifest.labtrust_gym_commit", file=sys.stderr)
            return 1

    vr_path = run / "verification_result.json"
    if vr_path.is_file():
        vr = load_json(vr_path)
        vr_cert = check_certificate_refs(vr)
        if cert_id != vr_cert:
            print(
                f"verification_result certificate_id mismatch: trace={cert_id!r} vr={vr_cert!r}",
                file=sys.stderr,
            )
            return 1
        if vr.get("source_commit") != manifest.get("provability_fabric_commit"):
            print("provability_fabric_commit mismatch manifest vs verification_result", file=sys.stderr)
            return 1

    summary_path = run / "certificate_summary.json"
    if summary_path.is_file():
        summary = load_json(summary_path)
        for key in ("certificate_id", "trace_hash", "spec_hash", "source_commit"):
            if summary.get(key) != trace_cert.get(key):
                print(f"certificate_summary.{key} mismatch", file=sys.stderr)
                return 1

    print(f"OK: release-run aligned on {cert_id}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
