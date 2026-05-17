#!/usr/bin/env bash
# Rewrite local git history to remove Cursor IDE co-author trailers.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

export FILTER_BRANCH_SQUELCH_WARNING=1
TRAILER='^Co-authored-by: Cursor <cursoragent@cursor.com>$'

rm -rf .git/refs/original .git-rewrite 2>/dev/null || true

git filter-branch -f --msg-filter "grep -v '${TRAILER}' || true" HEAD

git for-each-ref --format='%(refname)' refs/original/ | while read -r ref; do
  git update-ref -d "$ref"
done
rm -rf .git/refs/original .git-rewrite 2>/dev/null || true

git reflog expire --expire=now --all
git gc --prune=now

if git log --format='%B' HEAD | grep -F 'Co-authored-by: Cursor <cursoragent@cursor.com>'; then
  echo "ERROR: trailer still present on HEAD history" >&2
  exit 1
fi
echo "OK: HEAD history has no Cursor co-author trailers"
