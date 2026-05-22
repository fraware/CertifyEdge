#!/usr/bin/env bash
# Sync pcs_registry/*.registry.json COMPARE fields from pcs-core ArtifactRegistry.v0.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=lib/python_cmd.sh
. "$SCRIPT_DIR/lib/python_cmd.sh"
PY="$(resolve_python)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
PARENT="$(dirname "$ROOT")"
PCS_CORE="${PCS_CORE_PATH:-${PCS_CORE_ROOT:-$PARENT/pcs-core}}"
UPSTREAM="$PCS_CORE/examples/artifact_registry.valid.json"

if [[ ! -f "$UPSTREAM" ]]; then
  echo "error: pcs-core registry not found: $UPSTREAM" >&2
  exit 1
fi

"$PY" - "$UPSTREAM" "$ROOT/pcs_registry" <<'PY'
import json
import sys
from pathlib import Path

upstream = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
registry_dir = Path(sys.argv[2])
compare_keys = [
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
formal_keys = [
    "formal_predicate",
    "formal_fact_artifact",
    "lean_module",
    "admissible_status",
]

for path in sorted(registry_dir.glob("*.registry.json")):
    artifact = path.stem.replace(".registry", "")
    if artifact not in upstream.get("entries", {}):
        print(f"skip {path.name} (no pcs-core entry)")
        continue
    entry = upstream["entries"][artifact]
    doc = json.loads(path.read_text(encoding="utf-8"))
    for key in compare_keys:
        if key in entry:
            doc[key] = entry[key]
    if "consumer_repos" in entry:
        doc["consumer_repos"] = entry["consumer_repos"]
    for key in formal_keys:
        if key in entry:
            doc[key] = entry[key]
    path.write_text(json.dumps(doc, indent=2) + "\n", encoding="utf-8")
    print(f"synced {path.name}")
PY

echo "Registry contributions synced from $UPSTREAM"
