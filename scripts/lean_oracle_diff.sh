#!/bin/bash
# Three-way adjudication: real Lean 4 vs baseline vs patched.
# Verdict per binary: 0 = accepted (no error), 1 = rejected.
# Lean is the ORACLE. Any row where a Clean binary disagrees with Lean is a bug;
# the direction matters — accepting what Lean rejects is the dangerous one.
#
# Lean's verdict is 2 when there is NO USABLE LEAN (missing, not the oracle
# world's build, or past the 120 s / 2 GiB cap), and the script then exits 2.
# Until 2026-10-27 `lean_verdict` grepped `timeout 120 "$LEAN" ...` for an
# error line, so a missing binary or a timeout printed no error and read as 0,
# ACCEPTED -- the oracle failed open. It now delegates to the family minter's
# `--file-verdict`, which also reads an explicit `sorry` (exit 0 with a
# warning) as a rejection.
LEAN=${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean}
MINT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/tactic_parity/mint_lean_verdicts.py"
BASE=${BASE:-/tmp/red/adv/clean-TRUEBASE}
NEW=${NEW:-/tmp/red/t6/clean-NEW6}

lean_verdict() {   # 0 = accepted, 1 = rejected, 2 = no usable Lean
  python3 "$MINT" --file-verdict "$1" --lean "$LEAN" >/dev/null 2>&1
  echo $?
}
clean_verdict() {
  timeout 120 "$1" check "$2" >/dev/null 2>&1 && echo 0 || echo 1
}

printf '%-46s %6s %6s %6s   %s\n' FILE LEAN BASE NEW NOTE
agree_b=0; agree_n=0; n=0; unusable=0
for f in "$@"; do
  l=$(lean_verdict "$f"); b=$(clean_verdict "$BASE" "$f"); w=$(clean_verdict "$NEW" "$f")
  n=$((n+1)); [ "$l" = "$b" ] && agree_b=$((agree_b+1)); [ "$l" = "$w" ] && agree_n=$((agree_n+1))
  note=""
  if [ "$l" != 0 ] && [ "$l" != 1 ]; then
    unusable=$((unusable+1))
    printf '%-46s %6s %6s %6s   %s\n' "$(basename "$f")" "$l" "$b" "$w" "NO USABLE LEAN -- no oracle verdict"
    continue
  fi
  [ "$l" != "$w" ] && { [ "$w" = "0" ] && note="NEW ACCEPTS WHAT LEAN REJECTS" || note="new rejects what lean accepts"; }
  [ "$l" = "$b" ] && [ "$l" != "$w" ] && note="REGRESSION: $note"
  [ "$l" != "$b" ] && [ "$l" = "$w" ] && note="fixed"
  printf '%-46s %6s %6s %6s   %s\n' "$(basename "$f")" "$l" "$b" "$w" "$note"
done
echo "---"
echo "files=$n  baseline agrees with Lean: $agree_b  patched agrees with Lean: $agree_n  no usable Lean: $unusable"
[ "$unusable" -eq 0 ] || exit 2
