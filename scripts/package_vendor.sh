#!/usr/bin/env bash
# Package/authenticate canonical lock-pinned vendor payloads; no live-tree writes.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "${SCRIPT_DIR}/.."
if [[ -n "${CLEAN_GATE_PYTHON:-}" ]]; then
  PY="${CLEAN_GATE_PYTHON}"
  "$PY" -c 'import sys; raise SystemExit(sys.version_info < (3, 11))' \
    || { echo 'error: CLEAN_GATE_PYTHON must select Python >= 3.11' >&2; exit 1; }
else
  PY=""
  for candidate in python3 python3.14 python3.13 python3.12 python3.11; do
    if command -v "$candidate" >/dev/null 2>&1 \
        && "$candidate" -c 'import sys; raise SystemExit(sys.version_info < (3, 11))' 2>/dev/null; then
      PY="$candidate"
      break
    fi
  done
  [[ -n "$PY" ]] || { echo 'error: Python >= 3.11 is required' >&2; exit 1; }
fi
exec "$PY" scripts/vendor_package.py "$@"
