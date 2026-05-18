#!/usr/bin/env bash
# Fail if committed hash vector fixtures differ from pcs-core test_vectors/hash/.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PARENT="$(dirname "$ROOT")"
PCS_CORE="${PCS_CORE_PATH:-${PCS_CORE_ROOT:-$PARENT/pcs-core}}"
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
  sed -n 's/.*"input_file"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$1" | head -n1 \
    || sed -n 's/.*"input"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$1" | head -n1
}

check_vector() {
  local artifact="$1"
  local vector_json="$2"
  local out_dir="$DEST/$artifact"
  local expected_digest input_rel upstream_input local_input local_digest

  expected_digest="$(extract_digest "$vector_json")"
  input_rel="$(extract_input "$vector_json")"
  if [ -z "$expected_digest" ] || [ -z "$input_rel" ]; then
    echo "error: could not parse $vector_json" >&2
    return 1
  fi
  if [ ! -f "$out_dir/digest.txt" ]; then
    echo "error: missing $out_dir/digest.txt (run: make sync-pcs-hash-vectors)" >&2
    return 1
  fi
  local_digest="$(tr -d '\r\n' < "$out_dir/digest.txt")"
  if [ "$local_digest" != "$expected_digest" ]; then
    echo "error: $artifact digest drift (expected $expected_digest, got $local_digest)" >&2
    return 1
  fi

  upstream_input="$PCS_CORE/$input_rel"
  local_input="$out_dir/input.json"
  if [ ! -f "$upstream_input" ]; then
    echo "error: missing upstream input for $artifact: $upstream_input" >&2
    return 1
  fi
  if [ ! -f "$local_input" ]; then
    echo "error: missing $local_input (run: make sync-pcs-hash-vectors)" >&2
    return 1
  fi
  if ! diff -q "$upstream_input" "$local_input" >/dev/null; then
    echo "error: $artifact input.json drifted from $upstream_input" >&2
    diff -u "$upstream_input" "$local_input" || true
    return 1
  fi
  echo "OK $artifact hash vector"
}

failed=0
check_vector "TraceCertificate.v0" "$VECTORS/trace_certificate.vector.json" || failed=1
check_vector "HandoffManifest.v0" "$VECTORS/handoff_manifest.vector.json" || failed=1

if [ "$failed" -ne 0 ]; then
  exit 1
fi
echo "PCS hash vectors match $VECTORS"
