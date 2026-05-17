#!/usr/bin/env bash
# Run the certifyedge CLI from the workspace build output (not on PATH by default).
set -eu
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
for profile in debug release; do
  for name in certifyedge certifyedge.exe; do
    BIN="$ROOT/target/$profile/$name"
    if [[ -x "$BIN" || -f "$BIN" ]]; then
      exec "$BIN" "$@"
    fi
  done
done
echo "certifyedge binary not found. Build with: cargo build -p certifyedge" >&2
exit 1
