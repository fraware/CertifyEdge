#!/usr/bin/env bash
# PCS v0.1 LabTrust runbook — same commands as Provability Fabric / LabTrust-Gym handoff.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

pick_bin() {
  for profile in debug release; do
    for name in certifyedge certifyedge.exe; do
      local candidate="$ROOT/target/$profile/$name"
      if [[ -x "$candidate" || -f "$candidate" ]]; then
        echo "$candidate"
        return 0
      fi
    done
  done
  return 1
}

if ! BIN="$(pick_bin)"; then
  echo "certifyedge not built; run: cargo build -p certifyedge" >&2
  exit 1
fi

OUT_DIR="${PCS_RUNBOOK_OUT:-$ROOT/target/runbook}"
mkdir -p "$OUT_DIR"
CERT="$OUT_DIR/trace_certificate.json"
CX="$OUT_DIR/counterexample.json"
SPEC_QC="$ROOT/templates/hospital_lab/qc_release.stl"
TRACE_OK="$ROOT/tests/labtrust/valid_trace.json"
TRACE_BAD_QC="$ROOT/tests/labtrust/invalid_missing_qc_trace.json"

echo "==> check-trace (valid)"
"$BIN" check-trace --spec "$SPEC_QC" --trace "$TRACE_OK"

echo "==> emit-pcs-certificate (valid)"
rm -f "$CERT"
"$BIN" emit-pcs-certificate --spec "$SPEC_QC" --trace "$TRACE_OK" --out "$CERT"

echo "==> verify-certificate"
"$BIN" verify-certificate "$CERT"

echo "==> check-trace (missing QC, expect fail)"
set +e
"$BIN" check-trace --spec "$SPEC_QC" --trace "$TRACE_BAD_QC" --counterexample-out "$CX"
rc=$?
set -e
if [[ "$rc" -eq 0 ]]; then
  echo "expected check-trace to fail for missing QC trace" >&2
  exit 1
fi

echo "==> explain-counterexample"
"$BIN" explain-counterexample "$CX"

for stl in qc_release.stl no_release_before_qc.stl authorized_release_only.stl; do
  echo "==> check-trace valid trace / $stl"
  "$BIN" check-trace --spec "$ROOT/templates/hospital_lab/$stl" --trace "$TRACE_OK"
done

if command -v pcs >/dev/null 2>&1; then
  echo "==> pcs validate (emitted certificate)"
  pcs validate "$CERT"
  if [[ -f "$ROOT/tests/labtrust/expected_valid_certificate.json" ]]; then
    pcs validate "$ROOT/tests/labtrust/expected_valid_certificate.json"
  fi
else
  echo "==> pcs CLI not installed; skipped external validate (in-process schema runs in cargo test)"
fi

if [[ "${PCS_RUNBOOK_RELEASE:-}" == "1" ]]; then
  echo "==> release-mode emit"
  if [[ -z "${CERTIFYEDGE_SOURCE_COMMIT:-}" || "${CERTIFYEDGE_SOURCE_COMMIT}" =~ ^0+$ ]]; then
    if commit="$(git -C "$ROOT" rev-parse HEAD 2>/dev/null)"; then
      export CERTIFYEDGE_SOURCE_COMMIT="$commit"
      echo "    using CERTIFYEDGE_SOURCE_COMMIT=${commit:0:12}..."
    else
      echo "Set CERTIFYEDGE_SOURCE_COMMIT to a non-zero git SHA for release-mode emit." >&2
      exit 1
    fi
  fi
  REL_CERT="$OUT_DIR/trace_certificate_release.json"
  "$BIN" --release-mode emit-pcs-certificate \
    --spec "$SPEC_QC" --trace "$TRACE_OK" --out "$REL_CERT"
  if command -v pcs >/dev/null 2>&1; then
    pcs validate "$REL_CERT"
  fi
fi

echo "PCS runbook OK -> $OUT_DIR"
