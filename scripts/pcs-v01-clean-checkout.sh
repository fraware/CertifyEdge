#!/usr/bin/env bash
# PCS v0.1 clean-checkout chain from CertifyEdge (LabTrust-Gym -> CertifyEdge -> PF -> Scientific Memory).
#
# Prerequisites: labtrust, pcs, python; sibling LabTrust-Gym; optional pf + scientific-memory for full chain.
# See docs/pcs-handoff.md and LabTrust-Gym docs/pcs_v01_clean_chain.md
#
# Usage:
#   ./scripts/pcs-v01-clean-checkout.sh              # full chain (delegates to LabTrust-Gym script)
#   ./scripts/pcs-v01-clean-checkout.sh --through-certified   # LabTrust export + CertifyEdge + attach
#   ./scripts/pcs-v01-clean-checkout.sh --labtrust-only       # forward --labtrust-only
#   ./scripts/pcs-v01-clean-checkout.sh --skip-scientific-memory
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PARENT="$(dirname "$ROOT")"
LABTRUST_GYM="${LABTRUST_GYM_ROOT:-$PARENT/LabTrust-Gym}"
CHAIN_SCRIPT="$LABTRUST_GYM/examples/pcs_qc_release/scripts/run_pcs_v01_clean_chain.sh"
SPEC="$ROOT/templates/hospital_lab/qc_release.stl"

MODE="full"
FORWARD_ARGS=()
for arg in "$@"; do
  case "$arg" in
    --through-certified) MODE="certified" ;;
    --help|-h)
      echo "Usage: $0 [--through-certified] [--labtrust-only] [--skip-scientific-memory]"
      echo "Env: LABTRUST_GYM_ROOT, CERTIFYEDGE_ROOT (default: $ROOT), PCS_CHAIN_WORK, PCS_DETERMINISTIC=1"
      exit 0
      ;;
    *) FORWARD_ARGS+=("$arg") ;;
  esac
done

echo "==> build certifyedge"
cargo build -p certifyedge --manifest-path "$ROOT/Cargo.toml"

export CERTIFYEDGE_ROOT="$ROOT"
export CERTIFYEDGE_BIN="$ROOT/scripts/certifyedge.sh"
export CERTIFYEDGE_SPEC="$SPEC"
export PCS_DETERMINISTIC="${PCS_DETERMINISTIC:-1}"

CX_DIR="${PCS_CLEAN_CHECKOUT_CX:-$ROOT/target/pcs-v01-clean-checkout}"
mkdir -p "$CX_DIR"

_pcs_python() {
  if [[ -n "${PCS_PYTHON:-}" ]]; then
    "$PCS_PYTHON" "$@"
    return
  fi
  if command -v py >/dev/null 2>&1; then
    py -3 "$@"
    return
  fi
  for candidate in python3 python; do
    if command -v "$candidate" >/dev/null 2>&1; then
      if "$candidate" -c "import sys" >/dev/null 2>&1; then
        "$candidate" "$@"
        return
      fi
    fi
  done
  echo "error: python not found (set PCS_PYTHON)" >&2
  return 1
}

echo "==> CertifyEdge: invalid trace checks (LabTrust-aligned fixtures)"
"$CERTIFYEDGE_BIN" check-trace --spec "$SPEC" \
  --trace "$ROOT/tests/fixtures/labtrust-release/trace.json" >/dev/null

for pair in "missing_qc:release_before_qc:invalid_missing_qc_trace.json" \
              "unauthorized:unauthorized_release:invalid_unauthorized_trace.json"; do
  IFS=: read -r label reason file <<<"$pair"
  cx="$CX_DIR/counterexample_${label}.json"
  set +e
  "$CERTIFYEDGE_BIN" check-trace --spec "$SPEC" \
    --trace "$ROOT/tests/fixtures/labtrust-release/$file" --counterexample-out "$cx"
  rc=$?
  set -e
  if [[ "$rc" -eq 0 ]]; then
    echo "error: expected check-trace to fail for $file" >&2
    exit 1
  fi
  _pcs_python -c "
import json, sys
cx = json.load(open(sys.argv[1]))
assert cx.get('reason') == sys.argv[2], (cx.get('reason'), sys.argv[2])
print('OK counterexample', sys.argv[1], 'reason=', cx['reason'])
" "$cx" "$reason"
done

if [[ "$MODE" == "certified" ]]; then
  if [[ ! -d "$LABTRUST_GYM/policy" ]]; then
    echo "error: LabTrust-Gym not found at $LABTRUST_GYM (set LABTRUST_GYM_ROOT)" >&2
    exit 1
  fi
  # shellcheck source=/dev/null
  source "$LABTRUST_GYM/examples/pcs_qc_release/scripts/_pcs_chain_env.sh"
  pcs_chain_init
  pcs_require_cmd labtrust
  pcs_require_cmd pcs
  pcs_require_cmd python
  mkdir -p "$WORK" "$RUN_DIR"

  pcs_step "LabTrust-Gym: deterministic demos"
  labtrust run-demo qc-release --deterministic --out "$RUN_DIR"
  labtrust run-demo qc-release-invalid-missing-qc --deterministic
  labtrust run-demo qc-release-invalid-unauthorized --deterministic

  pcs_step "LabTrust-Gym: export PCS artifacts"
  labtrust export-trace --run "$RUN_DIR" --out "$TRACE_JSON"
  labtrust export-runtime-receipt --run "$RUN_DIR" --out "$RUNTIME_RECEIPT_JSON"
  labtrust export-pcs --run "$RUN_DIR" --out "$PENDING_JSON"
  pcs validate "$PENDING_JSON"

  HANDOFF_CE_JSON="${WORK}/labtrust_to_certifyedge_handoff.json"
  pcs_step "LabTrust-Gym: HandoffManifest.v0 (runtime_to_certificate) for CertifyEdge"
  labtrust emit-handoff-to-certifyedge \
    --trace "$TRACE_JSON" \
    --runtime-receipt "$RUNTIME_RECEIPT_JSON" \
    --out "$HANDOFF_CE_JSON" \
    --release-mode
  pcs validate "$HANDOFF_CE_JSON"
  cp -f "$HANDOFF_CE_JSON" "${WORK}/handoff_to_certifyedge.json"

  pcs_step "CertifyEdge: emit and verify TraceCertificate (HandoffManifest input)"
  "$CERTIFYEDGE_BIN" --release-mode emit-pcs-certificate \
    --handoff "$HANDOFF_CE_JSON" \
    --out "$TRACE_CERT_JSON"
  pcs validate "$TRACE_CERT_JSON"
  "$CERTIFYEDGE_BIN" verify-certificate "$TRACE_CERT_JSON" --trace "$TRACE_JSON"

  pcs_step "LabTrust-Gym: attach certificate"
  labtrust attach-certificate \
    --bundle "$PENDING_JSON" --certificate "$TRACE_CERT_JSON" --out "$CERTIFIED_JSON"
  pcs validate "$CERTIFIED_JSON"

  python "$LABTRUST_GYM/examples/pcs_qc_release/scripts/verify_pcs_v01_chain.py" \
    --work "$WORK" --stage certified

  echo ""
  echo "PCS v0.1 clean-checkout OK through certified bundle (workdir=$WORK)"
  exit 0
fi

if [[ ! -x "$CHAIN_SCRIPT" && ! -f "$CHAIN_SCRIPT" ]]; then
  echo "error: LabTrust-Gym chain script not found: $CHAIN_SCRIPT" >&2
  echo "Clone https://github.com/fraware/LabTrust-Gym as sibling or set LABTRUST_GYM_ROOT." >&2
  exit 1
fi

exec bash "$CHAIN_SCRIPT" "${FORWARD_ARGS[@]}"
