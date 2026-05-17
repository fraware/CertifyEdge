#!/usr/bin/env bash
# Substrate tests (Cargo package names differ from directory names).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

PACKAGES=(smt-verifier stl-compiler integration_tests)

if cargo metadata --no-deps --format-version=1 2>/dev/null \
  | grep -q '"name":"substrate-unit"'; then
  PACKAGES+=(substrate-unit)
else
  echo "note: tests/substrate-unit not in workspace; add to root Cargo.toml [workspace].members" >&2
fi

CARGO_ARGS=()
for pkg in "${PACKAGES[@]}"; do
  CARGO_ARGS+=(-p "$pkg")
done

echo "cargo test ${CARGO_ARGS[*]} $*"
cargo test "${CARGO_ARGS[@]}" "$@"
