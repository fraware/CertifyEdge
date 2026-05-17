#!/usr/bin/env python3
"""Remove Cursor agent Co-authored-by trailer from a commit message (bytes)."""
import re
import sys

TRAILER = b"Co-authored-by: Cursor <cursoragent@cursor.com>"
# Also strip common variants (trailing whitespace, CRLF).
PATTERN = re.compile(
    rb"\r?\nCo-authored-by:\s*Cursor\s*<cursoragent@cursor\.com>\s*",
    re.IGNORECASE,
)


def strip_cursor_coauthor(message: bytes) -> bytes:
    if TRAILER not in message and not PATTERN.search(message):
        return message
    cleaned = PATTERN.sub(b"\n", message)
    if cleaned.endswith(TRAILER):
        cleaned = cleaned[: -len(TRAILER)]
    cleaned = cleaned.rstrip(b"\r\n") + b"\n"
    return cleaned


if __name__ == "__main__":
    data = sys.stdin.buffer.read()
    sys.stdout.buffer.write(strip_cursor_coauthor(data))
