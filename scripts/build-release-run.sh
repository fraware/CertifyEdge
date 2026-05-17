#!/usr/bin/env bash
# Build a full PCS release-run in target/release-run-staging/ and promote to tests/fixtures/release-run/.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
STAGING="$ROOT/target/release-run-staging"
PARENT="$(dirname "$ROOT")"
LABTRUST="${LABTRUST_GYM_ROOT:-$PARENT/LabTrust-Gym}"
FINALIZE="$LABTRUST/examples/pcs_qc_release/scripts/finalize_release_run.py"
CHAIN="$LABTRUST/examples/pcs_qc_release/scripts/run_pcs_v01_clean_chain.sh"
PF_ROOT="${PROVABILITY_FABRIC_ROOT:-$PARENT/Provability-Fabric}"

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
      "$candidate" "$@"
      return
    fi
  done
  echo "error: python not found (set PCS_PYTHON)" >&2
  return 1
}

resolve_pf_bin() {
  if [[ ! -x "$PF_ROOT/core/cli/pf/pf" && ! -f "$PF_ROOT/core/cli/pf/pf.exe" ]]; then
    if command -v go >/dev/null 2>&1; then
      echo "==> build pf (Provability Fabric)"
      (cd "$PF_ROOT/core/cli/pf" && go build -o pf .)
    fi
  fi
  local candidate
  for candidate in \
    "$PF_ROOT/core/cli/pf/pf.exe" \
    "$PF_ROOT/core/cli/pf/pf"; do
    if [[ -n "$candidate" && ( -x "$candidate" || -f "$candidate" ) ]]; then
      printf '%s' "$candidate"
      return 0
    fi
  done
  return 1
}

echo "==> build certifyedge"
cargo build -p certifyedge --manifest-path "$ROOT/Cargo.toml"

rm -rf "$STAGING"
mkdir -p "$STAGING"

export CERTIFYEDGE_ROOT="$ROOT"
export CERTIFYEDGE_BIN="$ROOT/target/debug/certifyedge"
if [[ ! -x "$CERTIFYEDGE_BIN" && -f "${CERTIFYEDGE_BIN}.exe" ]]; then
  CERTIFYEDGE_BIN="${CERTIFYEDGE_BIN}.exe"
  export CERTIFYEDGE_BIN
fi
export CERTIFYEDGE_SPEC="$ROOT/templates/hospital_lab/qc_release.stl"
export PCS_CHAIN_WORK="$STAGING"
export PCS_RELEASE_RUN_DIR="$STAGING"
export PCS_DETERMINISTIC=1
export PCS_SKIP_SCIENTIFIC_MEMORY="${PCS_SKIP_SCIENTIFIC_MEMORY:-1}"
export PROVABILITY_FABRIC_ROOT="$PF_ROOT"

if PF_BIN="$(resolve_pf_bin)"; then
  export PF_BIN
else
  unset PF_BIN
  echo "warning: Provability Fabric pf not built; PF artifacts will be skipped" >&2
fi

if [[ ! -f "$CHAIN" ]]; then
  echo "error: LabTrust-Gym chain script not found: $CHAIN" >&2
  exit 1
fi

echo "==> LabTrust-Gym: export handoff artifacts -> $STAGING"
bash "$CHAIN" --labtrust-only

for required in trace.json runtime_receipt.json science_claim_bundle.pending.json; do
  if [[ ! -f "$STAGING/$required" ]]; then
    echo "error: staging missing $required after LabTrust export" >&2
    exit 1
  fi
done

SUMMARY="$STAGING/certificate_summary.json"
HANDOFF_IN="$STAGING/labtrust_to_certifyedge_handoff.json"
HANDOFF_OUT="$STAGING/certifyedge_to_labtrust_handoff.json"
echo "==> CertifyEdge: release-mode emit + summary"
if [[ -f "$HANDOFF_IN" ]]; then
  echo "    using HandoffManifest.v0 input: $HANDOFF_IN"
  "$CERTIFYEDGE_BIN" --release-mode emit-pcs-certificate \
    --handoff "$HANDOFF_IN" \
    --out "$STAGING/trace_certificate.json" \
    --handoff-out "$HANDOFF_OUT" \
    --summary-out "$SUMMARY" >/dev/null
else
  "$CERTIFYEDGE_BIN" --release-mode emit-pcs-certificate \
    --spec "$CERTIFYEDGE_SPEC" \
    --trace "$STAGING/trace.json" \
    --out "$STAGING/trace_certificate.json" \
    --summary-out "$SUMMARY" >/dev/null
fi
pcs validate "$STAGING/trace_certificate.json"
"$CERTIFYEDGE_BIN" verify-certificate "$STAGING/trace_certificate.json" \
  --trace "$STAGING/trace.json" >/dev/null
if command -v pcs >/dev/null 2>&1; then
  pcs registry check-artifact "$STAGING/trace_certificate.json"
  if [[ -f "$HANDOFF_OUT" ]]; then
    pcs validate "$HANDOFF_OUT"
  fi
fi

echo "==> LabTrust-Gym: attach certificate"
labtrust attach-certificate \
  --bundle "$STAGING/science_claim_bundle.pending.json" \
  --certificate "$STAGING/trace_certificate.json" \
  --out "$STAGING/science_claim_bundle.certified.json"
pcs validate "$STAGING/science_claim_bundle.certified.json"

_pcs_python "$FINALIZE" --run-dir "$STAGING" --no-promote

if [[ -n "${PF_BIN:-}" ]]; then
  echo "==> Provability Fabric: verify and sign"
  "$PF_BIN" verify science-claim "$STAGING/science_claim_bundle.certified.json" \
    --out "$STAGING/verification_result.json"
  pcs validate "$STAGING/verification_result.json"
  "$PF_BIN" sign science-claim "$STAGING/science_claim_bundle.certified.json" \
    --out "$STAGING/signed_science_claim_bundle.json"
  pcs validate "$STAGING/signed_science_claim_bundle.json"
  "$PF_BIN" inspect science-claim "$STAGING/signed_science_claim_bundle.json" >/dev/null
  _pcs_python "$FINALIZE" --run-dir "$STAGING" --no-promote
else
  echo "error: PF_BIN required for a complete release-run (build pf in Provability-Fabric)" >&2
  exit 1
fi

_pcs_python "$ROOT/scripts/sync-release-manifest-commits.py" "$STAGING"
_pcs_python "$ROOT/scripts/pcs-release-run-validate.py" "$STAGING"
"$ROOT/scripts/promote-release-run.sh" "$STAGING"
echo "release-run promoted to tests/fixtures/release-run"
