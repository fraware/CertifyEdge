#!/usr/bin/env python3
"""Assert pcs_bench_ingest.v0.json uses pcs-core canonical PcsBenchIngest.v0 (not legacy CertifyEdge fields)."""
from __future__ import annotations

import json
import sys
from pathlib import Path

LEGACY_TOP_LEVEL = frozenset(
    {
        "artifact",
        "benchmark_suite_id",
        "workflow_profile_id",
        "certificate_coverage_report",
        "profile_coverage_report",
        "repair_hint_quality",
    }
)

REQUIRED_TOP_LEVEL = frozenset(
    {
        "schema_version",
        "producer_id",
        "suite_id",
        "workflow_id",
        "benchmark_runs",
        "coverage_reports",
        "failure_localization_reports",
        "explain_quality_reports",
        "profile_coverage_reports",
        "commands",
        "logs",
        "source_repo",
        "source_commit",
        "signature_or_digest",
    }
)


def validate_ingest(path: Path) -> list[str]:
    errors: list[str] = []
    try:
        doc = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [f"{path}: {exc}"]

    keys = set(doc.keys())
    for legacy in LEGACY_TOP_LEVEL:
        if legacy in keys:
            errors.append(f"{path}: legacy top-level field {legacy!r} (use pcs-core PcsBenchIngest.v0)")
    missing = REQUIRED_TOP_LEVEL - keys
    if missing:
        errors.append(f"{path}: missing required fields: {sorted(missing)}")

    if not isinstance(doc.get("benchmark_runs"), list):
        errors.append(f"{path}: benchmark_runs must be an array")
    elif doc["benchmark_runs"]:
        first = doc["benchmark_runs"][0]
        if isinstance(first, dict):
            for ext in (
                "suite_id",
                "workflow_profile_id",
                "expected_benchmark_status",
                "observed_benchmark_status",
            ):
                if ext in first:
                    errors.append(
                        f"{path}: benchmark_runs[0] must be BenchmarkRun.v0 core, not CertificateBenchmarkRun (found {ext!r})"
                    )
                    break

    coverage = doc.get("coverage_reports")
    if not isinstance(coverage, list) or not coverage:
        errors.append(f"{path}: coverage_reports must be a non-empty array")
    else:
        metrics = {
            c.get("metric")
            for c in coverage
            if isinstance(c, dict) and isinstance(c.get("metric"), str)
        }
        for required in ("certificate_completeness", "repair_hint_quality"):
            if required not in metrics:
                errors.append(f"{path}: coverage_reports missing metric {required!r}")

    workflow_id = doc.get("workflow_id")
    if not isinstance(workflow_id, str) or not workflow_id:
        errors.append(f"{path}: workflow_id must be a non-empty string")
    elif workflow_id == doc.get("workflow_profile_id"):
        errors.append(f"{path}: workflow_id must not duplicate legacy workflow_profile_id")

    producer_id = doc.get("producer_id")
    if producer_id == "certifyedge":
        refs = doc.get("artifact_refs")
        if not isinstance(refs, list) or not refs:
            errors.append(f"{path}: certifyedge producer requires non-empty artifact_refs")
        else:
            paths = {
                r.get("path")
                for r in refs
                if isinstance(r, dict) and isinstance(r.get("path"), str)
            }
            for required_path in (
                "profile_coverage_report.v0.json",
                "repair_hint_quality_report.v0.json",
            ):
                if required_path not in paths:
                    errors.append(
                        f"{path}: artifact_refs missing path {required_path!r}"
                    )
            if not any(
                isinstance(p, str) and p.startswith("runs/") and p.endswith(".benchmark_run.v0.json")
                for p in paths
            ):
                errors.append(f"{path}: artifact_refs missing runs/*.benchmark_run.v0.json")
            suite_dir = path.parent
            for required_file in (
                "benchmark_report.v0.json",
                "pcs_bench_ingest.v0.json",
            ):
                if not (suite_dir / required_file).is_file():
                    errors.append(f"{path}: missing producer output {required_file}")
            if not (suite_dir / "repair_hint_quality_report.v0.json").is_file():
                errors.append(f"{path}: missing producer output repair_hint_quality_report.v0.json")
            if not (suite_dir / "certificate_coverage_report.v0.json").is_file():
                errors.append(f"{path}: missing producer output certificate_coverage_report.v0.json")

            failed_runs = [
                r
                for r in doc.get("benchmark_runs", [])
                if isinstance(r, dict) and r.get("observed_status") == "failed"
            ]
            fl = doc.get("failure_localization_reports")
            eq = doc.get("explain_quality_reports")
            if failed_runs:
                if not isinstance(fl, list) or not fl:
                    errors.append(
                        f"{path}: failure_localization_reports required when benchmark_runs include failures"
                    )
                if not isinstance(eq, list) or not eq:
                    errors.append(
                        f"{path}: explain_quality_reports required when benchmark_runs include failures"
                    )
            if isinstance(fl, list):
                fl_paths = {
                    r.get("path")
                    for r in refs
                    if isinstance(r, dict)
                    and r.get("artifact_type") == "FailureLocalizationResult.v0"
                    and isinstance(r.get("path"), str)
                }
                if fl and not any(
                    isinstance(p, str) and p.startswith("failure_localization/") for p in fl_paths
                ):
                    errors.append(f"{path}: artifact_refs missing failure_localization/ entries")
            if isinstance(eq, list):
                eq_paths = {
                    r.get("path")
                    for r in refs
                    if isinstance(r, dict)
                    and r.get("artifact_type") == "ExplainQualityReport.v0"
                    and isinstance(r.get("path"), str)
                }
                if eq and not any(
                    isinstance(p, str) and p.startswith("explain_quality/") for p in eq_paths
                ):
                    errors.append(f"{path}: artifact_refs missing explain_quality/ entries")

    return errors


def discover_ingest_paths(args: list[str]) -> list[Path]:
    if not args:
        root = Path(".").resolve()
        return [
            root / "benchmark_runs" / suite / "pcs_bench_ingest.v0.json"
            for suite in (
                "hospital_lab_qc_release",
                "tool_use_safety",
                "computation_reproducibility",
            )
        ]
    first = Path(args[0]).resolve()
    if first.name == "pcs_bench_ingest.v0.json":
        return [first]
    if (first / "pcs_bench_ingest.v0.json").is_file():
        return [first / "pcs_bench_ingest.v0.json"]
    if first.name == "benchmark_runs" or (first / "benchmark_runs").is_dir():
        bench = first if first.name == "benchmark_runs" else first / "benchmark_runs"
        suites = args[1:] if len(args) > 1 else [
            p.name for p in bench.iterdir() if p.is_dir()
        ]
        return [bench / suite / "pcs_bench_ingest.v0.json" for suite in suites]
    # e.g. target/certificate_benchmark — discover all ingest files under tree
    return sorted(first.rglob("pcs_bench_ingest.v0.json"))


def main() -> int:
    paths = discover_ingest_paths(sys.argv[1:])
    if not paths:
        print("error: no pcs_bench_ingest.v0.json paths to validate", file=sys.stderr)
        return 1
    all_errors: list[str] = []
    for path in paths:
        if not path.is_file():
            all_errors.append(f"missing {path} (run: make benchmark-certificates)")
            continue
        all_errors.extend(validate_ingest(path))

    if all_errors:
        for err in all_errors:
            print(f"error: {err}", file=sys.stderr)
        return 1
    print("OK pcs_bench_ingest canonical shape")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
