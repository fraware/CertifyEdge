#!/usr/bin/env bash
# Validate all property profile JSON files under templates/profiles/.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
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

echo "OK all property profiles in $PROFILES_DIR"
