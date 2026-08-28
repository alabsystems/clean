#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# The `scripts/test_*.py` / `scripts/test_*.sh` suite, as one gate.
#
# WHY THIS EXISTS
# ---------------
# These are the self-tests of the gate and tooling scripts themselves — the
# things that decide whether `scripts/dead_code_audit.py`,
# `scripts/verify_runner.py`, `scripts/trust_verify_soundness_gate.py`,
# `scripts/merge_queue.py` or `scripts/source_elab_gate.sh` still do what their
# name says. Measured 2026-08-22: NOTHING ran any of them. Not
# `scripts/local_gate.sh`, not the justfile, not a hook, not a suite row. Twenty
# self-tests, zero callers.
#
# The cost of that showed up the moment they were run: TWO were RED at
# 51c893ce5 — `test_prove_theorem.sh` 8 passed / 6 failed and
# `test_publish_mathverse_mirror.sh` 16 passed / 4 failed — with nothing
# anywhere reporting it. Seven more (`test_build_test_index.py` and friends)
# cannot even IMPORT unless the repo root is on PYTHONPATH, which is exactly the
# kind of rot that a suite nobody runs accumulates silently.
#
# The suite is the DIRECTORY, not a hand-maintained list, so a new self-test is
# picked up by existing. A zero-test run is a FAILURE: an empty glob must never
# read as green.
#
# QUARANTINE, and why it is not an off switch
# -------------------------------------------
# `data/script_selftest_quarantine.json` names suites that are known red, with a
# reason and an expiry. Two rules keep it honest and both fail CLOSED:
#   * an EXPIRED row fails the gate — a quarantine that outlives its date is
#     just a deletion with extra steps;
#   * a quarantined suite that PASSES fails the gate — a stale row silently
#     re-opens the hole it was covering.
# Anything not in the ledger must pass. There is no environment-variable bypass.
#
# FALSIFIED, not assumed (measured 2026-08-22 at 51c893ce5, 21 s per run)
# ----------------------------------------------------------------------
# A gate nobody has seen fail is not a gate. Four mutation arms, each reverted:
#
#   1. UNQUARANTINED RED — `sys.exit(1)` prepended to scripts/test_merge_queue.py:
#        SCRIPT_SELFTESTS=fail unquarantined red: scripts/test_merge_queue.py(exit=1)   rc=1
#      (note: appending the failure to the END of that file does NOT fail it —
#      `unittest.main()` exits first. The arm has to run before the harness.)
#   2. STALE QUARANTINE — a row added for the PASSING scripts/test_merge_queue.py:
#        SCRIPT_SELFTESTS=fail STALE quarantine (these now PASS; ...)                   rc=1
#   3. EXPIRED QUARANTINE — the prove_theorem row's expires set to 2026-01-01:
#        SCRIPT_SELFTESTS=fail EXPIRED quarantine (fix the suite or re-justify ...)     rc=1
#   4. MALFORMED LEDGER — the ledger replaced with `{ not json`:
#        SCRIPT_SELFTESTS=fail reason=malformed-quarantine-ledger                       rc=1
#
# The unmutated tree is rc=0 with `SCRIPT_SELFTESTS suites=20 passed=18`.
#
# Usage:
#   scripts/check_script_selftests.sh            # run the suite
#   scripts/check_script_selftests.sh --list     # enumerate what it would run
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

QUARANTINE="data/script_selftest_quarantine.json"

PYTHON_BIN=""
for candidate in python3.14 python3.13 python3.12 python3.11 python3; do
  if command -v "$candidate" >/dev/null 2>&1; then PYTHON_BIN="$candidate"; break; fi
done
if [ -z "$PYTHON_BIN" ]; then
  echo "SCRIPT_SELFTESTS=fail reason=no-python3-on-PATH" >&2
  exit 1
fi

# Plain glob, not `mapfile`: macOS ships bash 3.2, which has neither `mapfile`
# nor `readarray`. A gate that only runs on the maintainer's Linux box is a gate
# that does not run.
SUITES=""
for suite in scripts/test_*.py scripts/test_*.sh; do
  [ -f "$suite" ] || continue
  SUITES="$SUITES$suite
"
done
SUITES="$(printf '%s' "$SUITES" | sort)"

if [ "${1:-}" = "--list" ]; then
  printf '%s\n' "$SUITES"
  exit 0
fi

if [ -z "$SUITES" ]; then
  echo "SCRIPT_SELFTESTS=fail reason=no-suites-found (an empty scripts/test_* glob is not a pass)" >&2
  exit 1
fi

# Read the quarantine ledger. Fail closed on an unreadable or malformed file:
# "could not read the exemptions" must never mean "there are none".
QUARANTINED="$("$PYTHON_BIN" - "$QUARANTINE" <<'PY'
import datetime, json, sys
from pathlib import Path
p = Path(sys.argv[1])
if not p.exists():
    raise SystemExit(0)          # no ledger == no quarantine, which is the strict case
try:
    doc = json.loads(p.read_text())
except (OSError, ValueError) as exc:
    print(f"MALFORMED {exc}")
    raise SystemExit(3)
today = datetime.date.today()
for row in doc.get("quarantined", []):
    suite = row.get("suite")
    expires = row.get("expires")
    if not suite or not expires:
        print(f"MALFORMED row missing suite/expires: {row}")
        raise SystemExit(3)
    try:
        exp = datetime.date.fromisoformat(expires)
    except ValueError:
        print(f"MALFORMED row bad expires {expires!r} for {suite}")
        raise SystemExit(3)
    state = "EXPIRED" if exp < today else "LIVE"
    print(f"{state} {suite} {expires}")
PY
)"
q_rc=$?
if [ "$q_rc" -eq 3 ]; then
  echo "SCRIPT_SELFTESTS=fail reason=malformed-quarantine-ledger ($QUARANTINE)" >&2
  printf '%s\n' "$QUARANTINED" >&2
  exit 1
fi

is_quarantined() { printf '%s\n' "$QUARANTINED" | grep -q "^LIVE $1 "; }
is_expired()     { printf '%s\n' "$QUARANTINED" | grep -q "^EXPIRED $1 "; }

TOTAL=0; PASSED=0
FAILURES=""; STALE=""; EXPIRED=""

while IFS= read -r suite; do
  [ -n "$suite" ] || continue
  TOTAL=$((TOTAL + 1))
  case "$suite" in
    *.py) runner=(env "PYTHONPATH=$REPO_ROOT" "$PYTHON_BIN" "$suite") ;;
    *)    runner=(bash "$suite") ;;
  esac
  if "${runner[@]}" >/dev/null 2>&1 </dev/null; then
    rc=0
  else
    rc=$?
  fi
  if is_expired "$suite"; then
    EXPIRED="$EXPIRED $suite"
    continue
  fi
  if [ "$rc" -eq 0 ]; then
    PASSED=$((PASSED + 1))
    if is_quarantined "$suite"; then
      STALE="$STALE $suite"
    fi
  else
    if is_quarantined "$suite"; then
      echo "  QUARANTINED-RED $suite (exit $rc)"
    else
      FAILURES="$FAILURES $suite(exit=$rc)"
    fi
  fi
done <<EOF
$SUITES
EOF

echo "SCRIPT_SELFTESTS suites=$TOTAL passed=$PASSED"

rc=0
if [ -n "$FAILURES" ]; then
  printf 'SCRIPT_SELFTESTS=fail unquarantined red:%s\n' "$FAILURES" >&2
  rc=1
fi
if [ -n "$STALE" ]; then
  printf 'SCRIPT_SELFTESTS=fail STALE quarantine (these now PASS; delete their rows in %s):%s\n' \
    "$QUARANTINE" "$STALE" >&2
  rc=1
fi
if [ -n "$EXPIRED" ]; then
  printf 'SCRIPT_SELFTESTS=fail EXPIRED quarantine (fix the suite or re-justify the row in %s):%s\n' \
    "$QUARANTINE" "$EXPIRED" >&2
  rc=1
fi
[ "$rc" -eq 0 ] && echo "SCRIPT_SELFTESTS=ok"
exit "$rc"
