#!/usr/bin/env python3
"""Generate benchmarks/certificates/* case trees from repo test fixtures."""
from __future__ import annotations

import hashlib
import json
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BENCH = ROOT / "benchmarks" / "certificates"


def sha256_hex(data: bytes) -> str:
    return "sha256:" + hashlib.sha256(data).hexdigest()


def write_json(path: Path, obj: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2) + "\n", encoding="utf-8")


def finalize_handoff(handoff: dict) -> dict:
    payload = dict(handoff)
    payload["signature_or_digest"] = ""
    digest = sha256_hex(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    )
    payload["signature_or_digest"] = digest
    return payload


def write_case(
    case_dir: Path,
    *,
    case_id: str,
    profile_id: str,
    kind: str,
    expected_status: str | None,
    failure_code: str | None,
    expect_counterexample: bool,
    expect_cli_success: bool = True,
    repair_hint: dict | None = None,
    handoff: dict,
    artifacts: dict[str, Path],
) -> None:
    case_dir.mkdir(parents=True, exist_ok=True)
    for name, src in artifacts.items():
        dst = case_dir / name
        if src.resolve() != dst.resolve():
            shutil.copy2(src, dst)
    write_json(case_dir / "handoff.json", finalize_handoff(handoff))
    spec = {
        "schema_version": "v0",
        "case_id": case_id,
        "profile_id": profile_id,
        "kind": kind,
        "handoff_file": "handoff.json",
        "expect_cli_success": expect_cli_success,
        "expected_certificate_status": expected_status,
        "expected_failure_code": failure_code,
        "expect_counterexample": expect_counterexample,
    }
    if repair_hint:
        spec["expected_repair_hint"] = repair_hint
    write_json(case_dir / "case.json", spec)


def labtrust_handoff(
    trace_path: Path, *, case_id: str, property_id: str, trace_hash: str, out_name: str
) -> dict:
    trace_bytes = trace_path.read_bytes()
    return {
        "schema_version": "v0",
        "handoff_id": f"bench-{case_id}-handoff",
        "handoff_kind": "runtime_to_certificate",
        "from_component": "LabTrust-Gym",
        "to_component": "CertifyEdge",
        "created_at": "2026-05-17T17:01:22Z",
        "source_repo": "https://github.com/fraware/LabTrust-Gym",
        "source_commit": "4c5439ae358733f9a4c4a58e33fdaed1ab0d29de",
        "input_artifacts": {
            "trace.json": {
                "artifact_type": "Trace",
                "sha256": sha256_hex(trace_bytes),
            }
        },
        "expected_outputs": {
            out_name: {"artifact_type": "TraceCertificate.v0"}
        },
        "invariants": {
            "trace_hash": trace_hash,
            "property_id": property_id,
        },
        "status": "Validated",
        "signature_or_digest": "",
    }


def tool_use_handoff(trace_path: Path, *, property_id: str, trace_hash: str, policy_hash: str | None) -> dict:
    trace_bytes = trace_path.read_bytes()
    inv = {"trace_hash": trace_hash, "property_id": property_id}
    if policy_hash:
        inv["policy_hash"] = policy_hash
    return {
        "schema_version": "v0",
        "handoff_id": "bench-tool-use-handoff",
        "handoff_kind": "runtime_to_certificate",
        "from_component": "LabTrust-Gym",
        "to_component": "CertifyEdge",
        "created_at": "2026-05-17T17:01:22Z",
        "source_repo": "https://github.com/fraware/LabTrust-Gym",
        "source_commit": "abcdef0123456789abcdef0123456789abcdef01",
        "input_artifacts": {
            "trace.json": {
                "artifact_type": "ToolUseTrace.v0",
                "sha256": sha256_hex(trace_bytes),
            }
        },
        "expected_outputs": {
            "certificate.json": {"artifact_type": "ToolUseCertificate.v0"}
        },
        "invariants": inv,
        "status": "Validated",
        "signature_or_digest": "",
    }


def computation_handoff(fixture_dir: Path, run_name: str) -> dict:
    files = {
        "computation_run_receipt.json": "ComputationRunReceipt.v0",
        "dataset_receipt.json": "DatasetReceipt.v0",
        "environment_receipt.json": "EnvironmentReceipt.v0",
        "result_artifact.json": "ResultArtifact.v0",
    }
    input_artifacts = {}
    for fname, atype in files.items():
        data = (fixture_dir / fname).read_bytes() if fname != "computation_run_receipt.json" else (fixture_dir / run_name).read_bytes()
        key = "computation_run_receipt.json" if fname == "computation_run_receipt.json" else fname
        if fname == "computation_run_receipt.json":
            input_artifacts[key] = {
                "artifact_type": atype,
                "sha256": sha256_hex((fixture_dir / run_name).read_bytes()),
            }
        else:
            input_artifacts[key] = {
                "artifact_type": atype,
                "sha256": sha256_hex((fixture_dir / fname).read_bytes()),
            }
    run = json.loads((fixture_dir / run_name).read_text(encoding="utf-8"))
    return {
        "schema_version": "v0",
        "handoff_id": "bench-computation-handoff",
        "handoff_kind": "runtime_to_certificate",
        "from_component": "LabTrust-Gym",
        "to_component": "CertifyEdge",
        "created_at": "2026-05-17T17:01:22Z",
        "source_repo": "https://github.com/fraware/LabTrust-Gym",
        "source_commit": "abcdef0123456789abcdef0123456789abcdef01",
        "input_artifacts": input_artifacts,
        "expected_outputs": {
            "certificate.json": {"artifact_type": "ComputationWitness.v0"}
        },
        "invariants": {
            "run_hash": run["run_hash"],
            "property_id": "scientific_computation.reproducibility_v0",
        },
        "status": "Validated",
        "signature_or_digest": "",
    }


def gen_hospital_lab() -> None:
    base = BENCH / "hospital_lab_qc_release"
    valid_trace = ROOT / "tests/labtrust/valid_trace.json"
    trace = json.loads(valid_trace.read_text(encoding="utf-8"))
    trace_hash = trace["trace_hash"]

    write_case(
        base / "valid" / "ok",
        case_id="ok",
        profile_id="hospital_lab.qc_release",
        kind="valid",
        expected_status="CertificateChecked",
        failure_code=None,
        expect_counterexample=False,
        handoff=labtrust_handoff(valid_trace, case_id="ok", property_id="hospital_lab.qc_release", trace_hash=trace_hash, out_name="trace_certificate.json"),
        artifacts={"trace.json": valid_trace},
    )

    missing_qc = ROOT / "tests/labtrust/invalid_missing_qc_trace.json"
    t = json.loads(missing_qc.read_text(encoding="utf-8"))
    write_case(
        base / "invalid" / "missing_qc_event",
        case_id="missing_qc_event",
        profile_id="hospital_lab.qc_release",
        kind="invalid",
        expected_status="Rejected",
        failure_code="temporal_check_failed",
        expect_counterexample=True,
        repair_hint={
            "kind": "fix_trace_or_property",
            "command_contains": "check-trace",
            "responsible_component": "runtime_producer",
        },
        handoff=labtrust_handoff(missing_qc, case_id="missing_qc_event", property_id="hospital_lab.qc_release", trace_hash=t["trace_hash"], out_name="trace_certificate.json"),
        artifacts={"trace.json": missing_qc},
    )

    unauthorized = ROOT / "tests/labtrust/invalid_unauthorized_trace.json"
    t = json.loads(unauthorized.read_text(encoding="utf-8"))
    write_case(
        base / "invalid" / "unauthorized_release",
        case_id="unauthorized_release",
        profile_id="hospital_lab.qc_release",
        kind="invalid",
        expected_status="Rejected",
        failure_code="temporal_check_failed",
        expect_counterexample=True,
        repair_hint={
            "kind": "fix_trace_or_property",
            "command_contains": "check-trace",
            "responsible_component": "runtime_producer",
        },
        handoff=labtrust_handoff(unauthorized, case_id="unauthorized_release", property_id="hospital_lab.qc_release", trace_hash=t["trace_hash"], out_name="trace_certificate.json"),
        artifacts={"trace.json": unauthorized},
    )

    bad_hash_handoff = labtrust_handoff(valid_trace, case_id="trace_hash_mismatch", property_id="hospital_lab.qc_release", trace_hash="sha256:" + "1" * 64, out_name="trace_certificate.json")
    write_case(
        base / "invalid" / "trace_hash_mismatch",
        case_id="trace_hash_mismatch",
        profile_id="hospital_lab.qc_release",
        kind="invalid",
        expected_status=None,
        failure_code="trace_hash_mismatch",
        expect_counterexample=False,
        expect_cli_success=False,
        repair_hint={
            "kind": "regenerate_trace_or_handoff",
            "command_contains": "labtrust",
        },
        handoff=bad_hash_handoff,
        artifacts={"trace.json": valid_trace},
    )

    unknown_prop = labtrust_handoff(valid_trace, case_id="property_id_mismatch", property_id="hospital_lab.unknown_domain", trace_hash=trace_hash, out_name="trace_certificate.json")
    write_case(
        base / "invalid" / "property_id_mismatch",
        case_id="property_id_mismatch",
        profile_id="hospital_lab.qc_release",
        kind="invalid",
        expected_status=None,
        failure_code="unknown_property_id",
        expect_counterexample=False,
        expect_cli_success=False,
        repair_hint={
            "kind": "add_property_profile",
            "command_contains": "hospital_lab.unknown_domain",
        },
        handoff=unknown_prop,
        artifacts={"trace.json": valid_trace},
    )


def gen_tool_use() -> None:
    base = BENCH / "tool_use_safety"
    valid_trace = ROOT / "tests/tool_use/valid_tool_trace.json"
    trace = json.loads(valid_trace.read_text(encoding="utf-8"))

    write_case(
        base / "valid" / "ok",
        case_id="ok",
        profile_id="agent_tool_use.safety_v0",
        kind="valid",
        expected_status="CertificateChecked",
        failure_code=None,
        expect_counterexample=False,
        handoff=tool_use_handoff(valid_trace, property_id="agent_tool_use.safety_v0", trace_hash=trace["trace_hash"], policy_hash=trace.get("policy_hash")),
        artifacts={"trace.json": valid_trace},
    )

    unauthorized_src = json.loads(
        (ROOT / "tests/tool_use/unauthorized_tool_trace.json").read_text(encoding="utf-8")
    )
    unauthorized_src["policy_hash"] = "sha256:" + "d" * 64
    unauthorized_path = base / "invalid" / "unauthorized_tool_call" / "trace.json"
    unauthorized_path.parent.mkdir(parents=True, exist_ok=True)
    unauthorized_path.write_text(json.dumps(unauthorized_src, indent=2) + "\n", encoding="utf-8")
    write_case(
        base / "invalid" / "unauthorized_tool_call",
        case_id="unauthorized_tool_call",
        profile_id="agent_tool_use.safety_v0",
        kind="invalid",
        expected_status="Rejected",
        failure_code="unauthorized_tool_call",
        expect_counterexample=True,
        repair_hint={
            "kind": "fix_trace_or_policy",
            "command_contains": "regenerate",
            "responsible_component": "runtime_producer",
        },
        handoff=tool_use_handoff(
            unauthorized_path,
            property_id="agent_tool_use.safety_v0",
            trace_hash=unauthorized_src["trace_hash"],
            policy_hash=unauthorized_src["policy_hash"],
        ),
        artifacts={"trace.json": unauthorized_path},
    )

    missing_policy = ROOT / "tests/tool_use/missing_policy_hash_trace.json"
    t = json.loads(missing_policy.read_text(encoding="utf-8"))
    write_case(
        base / "invalid" / "missing_policy_hash",
        case_id="missing_policy_hash",
        profile_id="agent_tool_use.safety_v0",
        kind="invalid",
        expected_status="Rejected",
        failure_code="policy_hash_missing",
        expect_counterexample=True,
        repair_hint={
            "kind": "fix_trace_or_policy",
            "command_contains": "policy_hash",
            "responsible_component": "runtime_producer",
        },
        handoff=tool_use_handoff(missing_policy, property_id="agent_tool_use.safety_v0", trace_hash=t["trace_hash"], policy_hash=None),
        artifacts={"trace.json": missing_policy},
    )

    unknown_auth = json.loads(valid_trace.read_text(encoding="utf-8"))
    unknown_auth["tool_calls"][0]["authorization_status"] = "unknown"
    unknown_path = base / "invalid" / "unknown_authorization_status" / "trace.json"
    unknown_path.parent.mkdir(parents=True, exist_ok=True)
    unknown_path.write_text(json.dumps(unknown_auth, indent=2) + "\n", encoding="utf-8")
    write_case(
        base / "invalid" / "unknown_authorization_status",
        case_id="unknown_authorization_status",
        profile_id="agent_tool_use.safety_v0",
        kind="invalid",
        expected_status="Rejected",
        failure_code="unknown_authorization_status",
        expect_counterexample=True,
        repair_hint={
            "kind": "fix_trace_or_policy",
            "command_contains": "authorization",
            "responsible_component": "runtime_producer",
        },
        handoff=tool_use_handoff(unknown_path, property_id="agent_tool_use.safety_v0", trace_hash=unknown_auth["trace_hash"], policy_hash=unknown_auth.get("policy_hash")),
        artifacts={"trace.json": unknown_path},
    )

    policy_mismatch_handoff = tool_use_handoff(
        valid_trace,
        property_id="agent_tool_use.safety_v0",
        trace_hash=trace["trace_hash"],
        policy_hash="sha256:" + "c" * 64,
    )
    write_case(
        base / "invalid" / "policy_hash_mismatch",
        case_id="policy_hash_mismatch",
        profile_id="agent_tool_use.safety_v0",
        kind="invalid",
        expected_status=None,
        failure_code="policy_hash_mismatch",
        expect_counterexample=False,
        expect_cli_success=False,
        repair_hint={
            "kind": "regenerate_trace_or_handoff",
            "command_contains": "labtrust",
        },
        handoff=policy_mismatch_handoff,
        artifacts={"trace.json": valid_trace},
    )


def gen_computation() -> None:
    base = BENCH / "computation_reproducibility"
    fixture = ROOT / "tests/computation"
    run_ok = "computation_run_receipt.json"

    write_case(
        base / "valid" / "ok",
        case_id="ok",
        profile_id="scientific_computation.reproducibility_v0",
        kind="valid",
        expected_status="CertificateChecked",
        failure_code=None,
        expect_counterexample=False,
        handoff=computation_handoff(fixture, run_ok),
        artifacts={
            "computation_run_receipt.json": fixture / run_ok,
            "dataset_receipt.json": fixture / "dataset_receipt.json",
            "environment_receipt.json": fixture / "environment_receipt.json",
            "result_artifact.json": fixture / "result_artifact.json",
        },
    )

    cases = [
        (
            "dataset_hash_mismatch",
            "dataset_hash_mismatch",
            {
                "kind": "fix_computation_receipts",
                "command_contains": "dataset",
                "responsible_component": "runtime_producer",
            },
        ),
        (
            "environment_digest_mismatch",
            "environment_digest_mismatch",
            {
                "kind": "fix_computation_receipts",
                "command_contains": "environment",
                "responsible_component": "runtime_producer",
            },
        ),
        (
            "result_hash_mismatch",
            "result_hash_mismatch",
            {
                "kind": "fix_result_artifact",
                "command_contains": "result",
                "responsible_component": "runtime_producer",
            },
        ),
        (
            "missing_code_commit",
            "missing_code_commit",
            {
                "kind": "fix_run_receipt",
                "command_contains": "code_commit",
                "responsible_component": "runtime_producer",
            },
        ),
        (
            "nonzero_exit_code",
            "nonzero_exit_code",
            {
                "kind": "fix_computation_run",
                "command_contains": "exit_code",
                "responsible_component": "runtime_producer",
            },
        ),
    ]
    run_files = {
        "dataset_hash_mismatch": "dataset_hash_mismatch_run_receipt.json",
        "environment_digest_mismatch": "environment_hash_mismatch_run_receipt.json",
        "result_hash_mismatch": "result_hash_mismatch_run_receipt.json",
        "missing_code_commit": "missing_code_commit_run_receipt.json",
        "nonzero_exit_code": "invalid_exit_code_run_receipt.json",
    }
    for case_id, failure_code, repair_hint in cases:
        run_name = run_files[case_id]
        write_case(
            base / "invalid" / case_id,
            case_id=case_id,
            profile_id="scientific_computation.reproducibility_v0",
            kind="invalid",
            expected_status="Rejected",
            failure_code=failure_code,
            expect_counterexample=True,
            repair_hint=repair_hint,
            handoff=computation_handoff(fixture, run_name),
            artifacts={
                "computation_run_receipt.json": fixture / run_name,
                "dataset_receipt.json": fixture / "dataset_receipt.json",
                "environment_receipt.json": fixture / "environment_receipt.json",
                "result_artifact.json": fixture / "result_artifact.json",
            },
        )


def main() -> None:
    gen_hospital_lab()
    gen_tool_use()
    gen_computation()
    print(f"Wrote certificate benchmarks under {BENCH}")


if __name__ == "__main__":
    main()
