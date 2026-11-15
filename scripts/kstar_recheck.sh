#!/usr/bin/env bash
# Copyright 2026 The Clean contributors
# SPDX-License-Identifier: Apache-2.0
# Q4: same-byte quorum replay. --selftest uses local stubs, never quorum votes.
set -euo pipefail
ANSWERS_PINNED_INPUTS=True
root=$(cd "$(dirname "$0")/.." && pwd -P)
python=${KSTAR_PYTHON:-python3}
if [[ ${1:-} == --selftest || ${1:-} == --pinned-inputs ]]; then
  exec "$python" "$root/scripts/kstar_recheck.py" "$@"
fi
if [[ -n ${HEAVY_GATE_HELD:-} ]]; then
  exec "$python" "$root/scripts/kstar_recheck.py" "$@"
fi
exec "$root/scripts/heavy_gate.sh" run 5 kstar-quorum-replay -- \
  "$python" "$root/scripts/kstar_recheck.py" "$@"
