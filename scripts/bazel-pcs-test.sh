#!/usr/bin/env bash
# PCS + legacy substrate Bazel gate (mirrors CI bazel job).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if ! command -v bazel >/dev/null 2>&1; then
  echo "bazel not found; install Bazelisk: https://github.com/bazelbuild/bazelisk" >&2
  exit 1
fi

TARGETS=(
  "//tests/pipeline_integration:pipeline_integration"
)

# Library-only PCS tests work on all platforms; CLI subprocess tests need runfiles (Linux CI).
PCS_BAZEL_TESTS=(
  "//tests/certifyedge-integration:pcs_v01"
)
case "$(uname -s 2>/dev/null || echo unknown)" in
  Linux* | Darwin*)
    PCS_BAZEL_TESTS+=(
      "//tests/certifyedge-integration:cli"
      "//tests/certifyedge-integration:runbook"
    )
    ;;
  *)
    echo "note: skipping Bazel CLI/runbook PCS tests on this OS (use: cargo test -p certifyedge-integration)"
    ;;
esac

for t in "${PCS_BAZEL_TESTS[@]}"; do
  if bazel query "$t" >/dev/null 2>&1; then
    TARGETS+=("$t")
  fi
done

BAZEL_EXTRA=()
# Git Bash / MSYS on Windows: JVM often lacks BCR TLS trust without OS cert store.
case "$(uname -s 2>/dev/null || echo unknown)" in
  MINGW* | MSYS* | CYGWIN*) BAZEL_EXTRA+=(--bazelrc=.bazelrc.windows) ;;
esac
if [[ "${OS:-}" == "Windows_NT" ]] && [[ -f "$ROOT/.bazelrc.windows" ]]; then
  BAZEL_EXTRA+=(--bazelrc=.bazelrc.windows)
fi

run_bazel() {
  # --bazelrc must be a startup option (before the command), not after `test`.
  # Do not override CARGO_HOME here: rules_rust uses cargo_config = //:.cargo/config.toml.
  bazel "${BAZEL_EXTRA[@]}" test --config=ci "$@"
}

repin_if_needed() {
  if [[ ! -s "$ROOT/Cargo.Bazel.lock" ]] || [[ "${CARGO_BAZEL_REPIN:-}" == "1" ]]; then
    echo "Repinning crate_universe (CARGO_BAZEL_REPIN=1) ..."
    CARGO_BAZEL_REPIN=1 bazel "${BAZEL_EXTRA[@]}" mod deps --lockfile_mode=update 2>/dev/null \
      || CARGO_BAZEL_REPIN=1 bazel "${BAZEL_EXTRA[@]}" sync --only=crates 2>/dev/null \
      || true
  fi
}

repin_if_needed

echo "bazel test --config=ci ${TARGETS[*]}"
if ! run_bazel "${TARGETS[@]}"; then
  echo "" >&2
  echo "Bazel PCS gate failed (see errors above)." >&2
  echo "Try:" >&2
  echo "  1. ./scripts/test-substrate.sh   # Cargo-only substrate + PCS unit tests" >&2
  echo "  2. Update Java/Bazel: use Bazelisk and ensure Windows trusts https://bcr.bazel.build" >&2
  echo "  3. Corporate proxy: import your root CA into the JVM trust store" >&2
  exit 32
fi
