# Resolve a Python interpreter for PCS shell scripts.
# Honors PYTHON from the environment (e.g. make PYTHON=python on Windows).
resolve_python() {
  if [ -n "${PYTHON:-}" ] && command -v "$PYTHON" >/dev/null 2>&1; then
    printf '%s\n' "$PYTHON"
    return 0
  fi
  for candidate in python3 python py; do
    if command -v "$candidate" >/dev/null 2>&1; then
      printf '%s\n' "$candidate"
      return 0
    fi
  done
  echo "error: python3, python, or py required on PATH (or set PYTHON=...)" >&2
  return 1
}
