#!/usr/bin/env bash
# Copy TraceCertificate.v0 JSON Schema from a local pcs-core checkout into CertifyEdge.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PCS_CORE="${PCS_CORE_ROOT:-../pcs-core}"
DEST="$ROOT/schemas/pcs"

if [[ ! -d "$PCS_CORE/schemas" ]]; then
  echo "pcs-core not found at $PCS_CORE (set PCS_CORE_ROOT)" >&2
  exit 1
fi

mkdir -p "$DEST"
cp -f "$PCS_CORE/schemas/TraceCertificate.v0.schema.json" "$DEST/"
cp -f "$PCS_CORE/schemas/HandoffManifest.v0.schema.json" "$DEST/"
cp -f "$PCS_CORE/schemas/common.defs.json" "$DEST/"
echo "Synced pcs-core schemas -> $DEST"
