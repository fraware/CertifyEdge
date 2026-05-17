#!/usr/bin/env bash
# Write tests/fixtures/handoff/labtrust_to_certifyedge_handoff.json from RC trace (deterministic).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DEST="$ROOT/tests/fixtures/handoff"
mkdir -p "$DEST"

export CERTIFYEDGE_ROOT="$ROOT"
cargo test -p certifyedge-integration write_labtrust_handoff_fixture -- --ignored --nocapture

if [[ ! -f "$DEST/labtrust_to_certifyedge_handoff.json" ]]; then
  echo "error: fixture not written to $DEST" >&2
  exit 1
fi

echo "wrote $DEST/labtrust_to_certifyedge_handoff.json"
