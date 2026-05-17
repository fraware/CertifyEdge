#!/usr/bin/env bash
# Install certifyedge onto PATH without re-downloading crates.io (avoids Windows SSL revocation errors).
set -eu
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

export CARGO_HTTP_CHECK_REVOKE="${CARGO_HTTP_CHECK_REVOKE:-false}"

if [[ "${1:-}" != "--offline" ]]; then
  cargo build -p certifyedge --release 2>/dev/null || cargo build -p certifyedge
else
  cargo build -p certifyedge --offline 2>/dev/null \
    || cargo build -p certifyedge --release --offline 2>/dev/null \
    || cargo build -p certifyedge --offline
fi

pick_bin() {
  for profile in release debug; do
    for name in certifyedge certifyedge.exe; do
      local candidate="$ROOT/target/$profile/$name"
      if [[ -f "$candidate" ]]; then
        echo "$candidate"
        return 0
      fi
    done
  done
  return 1
}

BIN="$(pick_bin)" || {
  echo "certifyedge binary not found under target/{debug,release}/" >&2
  exit 1
}

DEST="${CERTIFYEDGE_INSTALL_DIR:-${CARGO_HOME:-$HOME/.cargo}/bin}"
mkdir -p "$DEST"

if [[ "$BIN" == *.exe ]]; then
  install -m 755 "$BIN" "$DEST/certifyedge.exe"
  # Git Bash on Windows often resolves certifyedge without .exe when .exe is present.
  ln -sf certifyedge.exe "$DEST/certifyedge" 2>/dev/null || cp -f "$BIN" "$DEST/certifyedge"
  echo "Installed: $DEST/certifyedge.exe"
else
  install -m 755 "$BIN" "$DEST/certifyedge"
  echo "Installed: $DEST/certifyedge"
fi

echo "Ensure this directory is on PATH: $DEST"
echo "Then run: certifyedge --help"
