#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
TREE=$(git rev-parse 'HEAD^{tree}')
PARENT=$(git rev-parse 'HEAD^')
NEW=$(git commit-tree "$TREE" -p "$PARENT" -F target/commitmsg.txt)
git reset --hard "$NEW"
if git cat-file -p HEAD | grep -q 'Co-authored-by: Cursor <cursoragent@cursor.com>'; then
  echo "ERROR: trailer still on HEAD" >&2
  exit 1
fi
echo "HEAD amended without trailer: $(git rev-parse --short HEAD)"
