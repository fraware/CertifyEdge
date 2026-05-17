#!/usr/bin/env bash
# Copy pcs-core canonical hash vectors into CertifyEdge test fixtures.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PCS_CORE="${PCS_CORE_PATH:-${PCS_CORE_ROOT:-$(dirname "$ROOT")/pcs-core}}"
VECTORS="$PCS_CORE/test_vectors/hash"
DEST="$ROOT/tests/fixtures/pcs-hash-vectors"

if [ ! -d "$VECTORS" ]; then
  echo "error: pcs-core hash vectors not found: $VECTORS" >&2
  echo "Set PCS_CORE_PATH or PCS_CORE_ROOT." >&2
  exit 1
fi

extract_digest() {
  sed -n 's/.*"expected_digest"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$1" | head -n1
}

extract_input() {
  sed -n 's/.*"input"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$1" | head -n1
}

extract_canonical() {
  sed -n 's/.*"canonical_json"[[:space:]]*:[[:space:]]*"\(.*\)".*/\1/p' "$1" | head -n1 | sed 's/\\"/"/g'
}

sync_vector() {
  local artifact="$1"
  local vector_file="$2"
  local input_rel expected_digest out_dir

  input_rel="$(extract_input "$vector_file")"
  expected_digest="$(extract_digest "$vector_file")"
  if [ -z "$input_rel" ] || [ -z "$expected_digest" ]; then
    echo "error: could not parse $vector_file" >&2
    return 1
  fi
  out_dir="$DEST/$artifact"
  mkdir -p "$out_dir"
  cp -f "$PCS_CORE/$input_rel" "$out_dir/input.json"
  printf '%s\n' "$expected_digest" >"$out_dir/digest.txt"
  extract_canonical "$vector_file" >"$out_dir/canonical.txt" || true
  echo "synced $artifact"
}

sync_vector "TraceCertificate.v0" "$VECTORS/trace_certificate.vector.json"
sync_vector "HandoffManifest.v0" "$VECTORS/handoff_manifest.vector.json"

echo "Hash vectors synced -> $DEST"
