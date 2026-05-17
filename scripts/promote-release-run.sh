#!/usr/bin/env bash
# Atomically promote target/release-run-staging/ -> tests/fixtures/release-run/
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
STAGING="${1:-$ROOT/target/release-run-staging}"
DEST="$ROOT/tests/fixtures/release-run"
TMP="$ROOT/tests/fixtures/.release-run-promote.$$"

if [[ ! -d "$STAGING" ]]; then
  echo "error: staging directory missing: $STAGING" >&2
  exit 1
fi

for required in \
  trace.json \
  runtime_receipt.json \
  trace_certificate.json \
  certificate_summary.json \
  science_claim_bundle.pending.json \
  science_claim_bundle.certified.json \
  verification_result.json \
  signed_science_claim_bundle.json \
  RELEASE_FIXTURE_MANIFEST.json; do
  if [[ ! -f "$STAGING/$required" ]]; then
    echo "error: staging missing required artifact: $required" >&2
    exit 1
  fi
done

rm -rf "$TMP"
mkdir -p "$TMP"
cp -a "$STAGING"/. "$TMP/"

rm -rf "${DEST}.old"
if [[ -d "$DEST" ]]; then
  mv "$DEST" "${DEST}.old"
fi
mv "$TMP" "$DEST"
rm -rf "${DEST}.old"

echo "promoted release-run -> $DEST"
