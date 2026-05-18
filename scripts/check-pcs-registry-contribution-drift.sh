#!/usr/bin/env bash
# Fail if CertifyEdge registry contribution drifts from pcs-core TraceCertificate.v0 entry.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PARENT="$(dirname "$ROOT")"
PCS_CORE="${PCS_CORE_PATH:-${PCS_CORE_ROOT:-$PARENT/pcs-core}}"
UPSTREAM="$PCS_CORE/examples/artifact_registry.valid.json"
LOCAL="$ROOT/pcs_registry/TraceCertificate.v0.registry.json"

if [ ! -f "$UPSTREAM" ]; then
  echo "error: pcs-core registry not found: $UPSTREAM" >&2
  exit 1
fi
if [ ! -f "$LOCAL" ]; then
  echo "error: missing local contribution: $LOCAL" >&2
  exit 1
fi

python3 - "$UPSTREAM" "$LOCAL" <<'PY'
import json
import sys

upstream_path, local_path = sys.argv[1:3]
upstream = json.load(open(upstream_path, encoding="utf-8"))
local = json.load(open(local_path, encoding="utf-8"))
entry = upstream["entries"]["TraceCertificate.v0"]

COMPARE_KEYS = [
    "artifact_type",
    "schema",
    "schema_owner",
    "runtime_producer",
    "allowed_runtime_producers",
    "producer",
    "allowed_statuses",
    "required_release_fields",
    "semantic_checks",
    "canonical_hash_required",
    "release_mode_required",
]

errors: list[str] = []
for key in COMPARE_KEYS:
    if entry.get(key) != local.get(key):
        errors.append(f"field drift: {key}")

if entry.get("consumer_repos") != local.get("consumer_repos"):
    errors.append("field drift: consumer_repos")

if errors:
    for err in errors:
        print(f"error: {err}", file=sys.stderr)
    sys.exit(1)

print("OK TraceCertificate.v0 registry contribution matches pcs-core entry")
PY
