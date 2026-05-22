#!/usr/bin/env bash
# CertifyEdge PCS benchmark producer gate (release-grade tool-use safety suite).
set -eu
(set -o pipefail) 2>/dev/null && set -o pipefail || true

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [[ -z "${CERTIFYEDGE_SOURCE_COMMIT:-}" ]]; then
  if command -v git >/dev/null 2>&1 && git -C "$ROOT" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    export CERTIFYEDGE_SOURCE_COMMIT="$(git -C "$ROOT" rev-parse HEAD)"
    echo "CERTIFYEDGE_SOURCE_COMMIT=$CERTIFYEDGE_SOURCE_COMMIT"
  else
    echo "error: set CERTIFYEDGE_SOURCE_COMMIT to a 40-character git commit" >&2
    exit 1
  fi
fi

if [[ "${CERTIFYEDGE_SOURCE_COMMIT}" =~ ^[0f]{40}$ ]]; then
  echo "error: CERTIFYEDGE_SOURCE_COMMIT must not be all zeros (release-grade)" >&2
  exit 1
fi

exec make pcs-bench-producer
