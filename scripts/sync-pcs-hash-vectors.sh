#!/usr/bin/env bash
# Copy pcs-core canonical hash vectors into CertifyEdge test fixtures.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PCS_CORE="${PCS_CORE_PATH:-${PCS_CORE_ROOT:-$(dirname "$ROOT")/pcs-core}}"
VECTORS="$PCS_CORE/test_vectors/hash"
DEST="$ROOT/tests/fixtures/pcs-hash-vectors"

if [[ ! -d "$VECTORS" ]]; then
  echo "error: pcs-core hash vectors not found: $VECTORS" >&2
  echo "Set PCS_CORE_PATH or PCS_CORE_ROOT." >&2
  exit 1
fi

sync_vector() {
  local artifact="$1"
  local vector_file="$2"
  local input_name
  input_name="$(python3 -c "import json,sys; print(json.load(open(sys.argv[1]))['input_file'])" "$vector_file")"
  local out_dir="$DEST/$artifact"
  mkdir -p "$out_dir"
  cp -f "$PCS_CORE/test_vectors/hash/$input_name" "$out_dir/input.json" 2>/dev/null \
    || cp -f "$PCS_CORE/examples/$input_name" "$out_dir/input.json"
  python3 -c "
import json, pathlib, sys
v = json.load(open(sys.argv[1]))
pathlib.Path(sys.argv[2]).write_text(v['expected_digest'] + '\n')
pathlib.Path(sys.argv[3]).write_text(v.get('canonical_json', '') + '\n')
" "$vector_file" "$out_dir/digest.txt" "$out_dir/canonical.txt"
  echo "synced $artifact"
}

sync_vector "TraceCertificate.v0" "$VECTORS/tracecertificate.vector.json"
sync_vector "HandoffManifest.v0" "$VECTORS/handoffmanifest.vector.json"

echo "Hash vectors synced -> $DEST"
