#!/usr/bin/env bash
# Fail if committed RC fixtures differ from pcs-core/examples/labtrust-release/.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PARENT="$(dirname "$ROOT")"
PCS_CORE="${PCS_CORE_PATH:-${PCS_CORE_ROOT:-$PARENT/pcs-core}}"
SRC="$PCS_CORE/examples/labtrust-release"
DEST="$ROOT/tests/fixtures/labtrust-release"

if [[ ! -d "$SRC" ]]; then
  echo "error: pcs-core RC directory not found: $SRC" >&2
  echo "Set PCS_CORE_PATH or PCS_CORE_ROOT." >&2
  exit 1
fi

failed=0
for name in trace.json trace_certificate.json; do
  if [[ ! -f "$SRC/$name" ]]; then
    echo "error: missing $SRC/$name" >&2
    failed=1
    continue
  fi
  if [[ ! -f "$DEST/$name" ]]; then
    echo "error: missing committed fixture $DEST/$name (run: make sync-pcs-core-rc)" >&2
    failed=1
    continue
  fi
  if ! diff -q "$SRC/$name" "$DEST/$name" >/dev/null; then
    echo "error: $name drifted from pcs-core (run: make sync-pcs-core-rc)" >&2
    diff -u "$SRC/$name" "$DEST/$name" || true
    failed=1
  fi
done

if [[ "$failed" -ne 0 ]]; then
  exit 1
fi

echo "PCS RC fixtures match $SRC"
