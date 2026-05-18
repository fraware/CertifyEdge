#!/usr/bin/env bash
# Run PCS drift checks when a pcs-core checkout is available; skip otherwise.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PARENT="$(dirname "$ROOT")"
PCS_CORE="${PCS_CORE_PATH:-${PCS_CORE_ROOT:-$PARENT/pcs-core}}"

if [ ! -d "$PCS_CORE/examples" ]; then
  echo "skip: pcs-core not found at $PCS_CORE (set PCS_CORE_PATH or PCS_CORE_ROOT)"
  exit 0
fi

export PCS_CORE_PATH="$PCS_CORE"

case "${1:-all}" in
  registry)
    bash "$ROOT/scripts/check-pcs-registry-contribution-drift.sh"
    ;;
  hash-vectors)
    bash "$ROOT/scripts/check-pcs-hash-vectors-drift.sh"
    ;;
  all)
    bash "$ROOT/scripts/check-pcs-registry-contribution-drift.sh"
    bash "$ROOT/scripts/check-pcs-hash-vectors-drift.sh"
    ;;
  *)
    echo "usage: $0 [registry|hash-vectors|all]" >&2
    exit 2
    ;;
esac
