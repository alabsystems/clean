#!/usr/bin/env bash
# Re-verify every checked-in GREEN artifact against the CURRENT binary.
#
# WHY THIS EXISTS. A `reports/*-green.json` records that a `.lean` corpus checked
# clean at some commit, under some binary. Nothing re-ran it afterwards. On
# 2026-08-19 `scripts/mtype_green.sh` was found RED — MType.lean checked 32/49
# against a gate demanding 49/49 — and the source had not changed since
# 216ac5209. The regression was in the ELABORATOR, introduced somewhere in the
# 60 commits after the artifact was pinned, and it sat undetected for a week
# because no gate re-ran the claim.
#
# The full green scripts are slow (mtype's cert export alone is ~145 s), which is
# why they were not in the pre-push path. But the part that ROTTED is
# `clean check`, and that takes well under a second per file. This re-runs
# exactly that part and compares against the count the artifact recorded.
#
# Fail-closed: a missing binary, a missing artifact, an unparsable count, or a
# count that differs from the pin all FAIL. "Could not check" is never "green".
#
# Usage: scripts/green_artifact_recheck.sh [--bin path/to/clean]
set -euo pipefail

BIN="target/release/clean"
if [ "${1:-}" = "--bin" ]; then BIN="${2:?--bin needs a path}"; fi

if [ ! -x "$BIN" ]; then
  echo "GREEN_RECHECK=fail reason=no-binary path=$BIN" >&2
  echo "  build it first: cargo build --locked --release -p clean" >&2
  exit 1
fi

# artifact : json-path-to-count : lean source
CASES=(
  "reports/mtype-core-green.json:declarations_checked:data/graduation/clean-mtype/proof/MType.lean"
  "reports/mtype-core-green.json:indexed_core.declarations_checked:data/graduation/clean-mtype/proof/MTypeIndexed.lean"
  "reports/coind-core-green.json:declarations_checked:data/graduation/clean-coind/proof/Coind.lean"
  "reports/coind-full-green.json:declarations_checked:data/graduation/clean-coind/proof/CoindFull.lean"
  "reports/streams-green.json:declarations_checked:data/graduation/clean-streams/proof/Streams.lean"
)

rc=0
for case in "${CASES[@]}"; do
  artifact="${case%%:*}"; rest="${case#*:}"
  key="${rest%%:*}"; src="${rest#*:}"

  if [ ! -f "$artifact" ]; then
    echo "GREEN_RECHECK=fail artifact=$artifact reason=missing"; rc=1; continue
  fi
  if [ ! -f "$src" ]; then
    echo "GREEN_RECHECK=fail artifact=$artifact source=$src reason=missing-source"; rc=1; continue
  fi

  pinned="$(python3 - "$artifact" "$key" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
for part in sys.argv[2].split('.'):
    d = d.get(part) if isinstance(d, dict) else None
    if d is None:
        print(""); raise SystemExit(0)
print(d)
PY
)"
  if [ -z "$pinned" ]; then
    echo "GREEN_RECHECK=fail artifact=$artifact key=$key reason=unreadable-pin"; rc=1; continue
  fi

  # `clean check` prints "  N passed, M failed".
  out="$("$BIN" check "$src" --prelude builtin 2>&1 || true)"
  passed="$(printf '%s\n' "$out" | sed -n 's/^ *\([0-9][0-9]*\) passed.*/\1/p' | tail -1)"
  failed="$(printf '%s\n' "$out" | sed -n 's/.*, *\([0-9][0-9]*\) failed.*/\1/p' | tail -1)"

  if [ -z "$passed" ]; then
    echo "GREEN_RECHECK=fail source=$src reason=no-count-in-output"; rc=1; continue
  fi
  if [ "${failed:-0}" != "0" ] || [ "$passed" != "$pinned" ]; then
    echo "GREEN_RECHECK=fail source=$src pinned=$pinned now=${passed}passed/${failed:-?}failed artifact=$artifact"
    rc=1
    continue
  fi
  echo "GREEN_RECHECK=ok source=$src ${passed}/${pinned}"
done

if [ "$rc" -ne 0 ]; then
  echo "" >&2
  echo "A checked-in green artifact no longer reproduces. Either a regression" >&2
  echo "landed, or the artifact is stale — regenerate with the owning script" >&2
  echo "(scripts/mtype_green.sh, scripts/coind_green.sh, scripts/streams_green.sh)" >&2
  echo "once it is genuinely green." >&2
fi
exit "$rc"
