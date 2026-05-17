#!/usr/bin/env bash
# Sync canonical PCS RC fixtures from pcs-core/examples/labtrust-release/ (no local regeneration).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PARENT="$(dirname "$ROOT")"
PCS_CORE="${PCS_CORE_PATH:-${PCS_CORE_ROOT:-$PARENT/pcs-core}}"
SRC="$PCS_CORE/examples/labtrust-release"
DEST="$ROOT/tests/fixtures/labtrust-release"

if [[ ! -d "$SRC" ]]; then
  echo "error: canonical RC directory not found: $SRC" >&2
  echo "Set PCS_CORE_PATH or PCS_CORE_ROOT to your pcs-core checkout." >&2
  exit 1
fi

mkdir -p "$DEST"
for name in trace.json trace_certificate.json; do
  if [[ ! -f "$SRC/$name" ]]; then
    echo "error: missing $SRC/$name" >&2
    exit 1
  fi
  cp -f "$SRC/$name" "$DEST/$name"
done
cp -f "$SRC/RELEASE_FIXTURE_MANIFEST.json" "$DEST/PCS_CORE_RC_MANIFEST.json"

echo "synced PCS RC fixtures from $SRC -> $DEST"
echo "  trace.json trace_certificate.json PCS_CORE_RC_MANIFEST.json (from RELEASE_FIXTURE_MANIFEST.json)"
