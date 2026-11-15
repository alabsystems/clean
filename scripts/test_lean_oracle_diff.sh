#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Self-test for scripts/lean_oracle_diff.sh's oracle column. Until 2026-10-27
# `lean_verdict` grepped Lean's output for an error line, so LEAN=/nonexistent
# (or a timeout) printed nothing and read as 0, ACCEPTED: the oracle failed
# open. It now delegates to `mint_lean_verdicts.py --file-verdict`, and a
# missing Lean must read 2 and exit 2. A fake oracle-world Lean that accepts
# is the control: the same row then reads 0 and the script exits 0. No real
# Lean and no Clean binary run here.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
tmp="$(mktemp -d "${TMPDIR:-/tmp}/lean-oracle-diff-test.XXXXXX")"
trap 'rm -rf "$tmp"' EXIT
printf 'theorem t : True := trivial\n' > "$tmp/t.lean"
pass=0; fail=0
check() { if eval "$2"; then pass=$((pass+1)); echo "ok: $1"; else fail=$((fail+1)); echo "FAIL: $1"; fi; }

out="$(LEAN=/nonexistent BASE=/usr/bin/false NEW=/usr/bin/false bash scripts/lean_oracle_diff.sh "$tmp/t.lean" 2>&1)"; rc=$?
printf '%s\n' "$out"
check "a missing Lean exits 2, not 0" '[ "$rc" -eq 2 ]'
check "a missing Lean reads 2 in the LEAN column, not 0" 'printf "%s\n" "$out" | grep -qE "^t\.lean +2 "'

gh="$(python3 -c 'import sys; sys.path.insert(0, "scripts/tactic_parity"); import lean_verdicts as f; print(f.ORACLE_GITHASHES["v4.30.0-rc2"])')"
cat > "$tmp/lean" <<FAKE
#!/bin/sh
case "\$1" in
  --version) echo "Lean (version 4.30.0-rc2, fake, commit $gh, Release)" ;;
  --githash) echo "$gh" ;;
esac
exit 0
FAKE
chmod +x "$tmp/lean"
out="$(LEAN="$tmp/lean" BASE=/usr/bin/false NEW=/usr/bin/false bash scripts/lean_oracle_diff.sh "$tmp/t.lean" 2>&1)"; rc=$?
printf '%s\n' "$out"
check "control: an oracle-world Lean that accepts reads 0 and exits 0" '[ "$rc" -eq 0 ] && printf "%s\n" "$out" | grep -qE "^t\.lean +0 "'

echo "=== Results: $pass passed, $fail failed ==="
[ "$fail" -eq 0 ]
