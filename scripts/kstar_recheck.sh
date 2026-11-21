#!/usr/bin/env bash
# Copyright 2026 The Clean contributors
# SPDX-License-Identifier: Apache-2.0
# Q4: same-byte quorum replay. --selftest uses local stubs, never quorum votes.
set -euo pipefail
ANSWERS_PINNED_INPUTS=True
root=$(cd "$(dirname "$0")/.." && pwd -P)
# The input rule parses manifests with tomllib (Python >= 3.11); resolve one the
# way scripts/local_gate.sh does, since /usr/bin/python3 here is 3.9.
python=${KSTAR_PYTHON:-}
for cand in python3 python3.14 python3.13 python3.12 python3.11 /opt/homebrew/bin/python3; do
  [[ -z $python ]] || break
  command -v "$cand" >/dev/null 2>&1 && "$cand" -c 'import tomllib' >/dev/null 2>&1 && python=$cand
done
[[ -n $python ]] || { echo 'kstar_recheck.sh: no python3 with tomllib (>= 3.11); set KSTAR_PYTHON' >&2; exit 2; }
# --build-member stamps a member build inside the build's own reservation:
# `heavy_gate.sh run <gb> <label> -- scripts/kstar_recheck.sh --build-member ...`.
if [[ ${1:-} == --build-member && -z ${HEAVY_GATE_HELD:-} ]]; then
  echo 'kstar_recheck.sh: --build-member runs a member build; run it inside a heavy_gate.sh reservation' >&2; exit 2
fi
if [[ ${1:-} == --selftest || ${1:-} == --pinned-inputs ]]; then
  exec "$python" "$root/scripts/kstar_recheck.py" "$@"
fi
if [[ -n ${HEAVY_GATE_HELD:-} ]]; then
  exec "$python" "$root/scripts/kstar_recheck.py" "$@"
fi
exec "$root/scripts/heavy_gate.sh" run 5 kstar-quorum-replay -- \
  "$python" "$root/scripts/kstar_recheck.py" "$@"
