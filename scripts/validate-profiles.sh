#!/usr/bin/env bash
# Validate all property profile JSON files under templates/profiles/.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=lib/python_cmd.sh
. "$SCRIPT_DIR/lib/python_cmd.sh"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

cargo build -p certifyedge --quiet

PROFILES_DIR="$ROOT/templates/profiles"
failed=0

for path in "$PROFILES_DIR"/*.json; do
  base="$(basename "$path")"
  if [ "$base" = "schema.json" ]; then
    continue
  fi
  if ! cargo run -p certifyedge --quiet -- profiles validate "$path"; then
    echo "error: invalid profile $path" >&2
    failed=1
  fi
done

if [ "$failed" -ne 0 ]; then
  exit 1
fi

if ! PY="$(resolve_python 2>/dev/null)"; then
  echo "warning: python not found; skipped formalization predicate cross-check" >&2
else
  "$PY" - "$PROFILES_DIR" <<'PY'
import json
import sys
from pathlib import Path

profiles_dir = Path(sys.argv[1])
expected = {
    "scientific_computation.reproducibility_v0": "ComputationWitnessBindsResults",
}
default_predicate = "CertificateMatchesRuntime"

for path in sorted(profiles_dir.glob("*.json")):
    if path.name == "schema.json":
        continue
    doc = json.loads(path.read_text(encoding="utf-8"))
    pid = doc["property_id"]
    predicate = doc.get("formalization", {}).get("certificate_predicate")
    want = expected.get(pid, default_predicate)
    if predicate != want:
        print(
            f"error: {path.name} formalization.certificate_predicate must be {want}, got {predicate}",
            file=sys.stderr,
        )
        sys.exit(1)
print("OK formalization predicates")
PY
fi

echo "OK all property profiles in $PROFILES_DIR"
