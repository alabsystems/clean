#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Every `test_*.py` / `test_*.sh` under `scripts/` (nested directories
# included), as one gate.
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
# The DIRECTORY is the whole tree under `scripts/` (2026-11-10). The glob was
# `scripts/test_*` only, so the ten suites in `scripts/axiom_audit/`,
# `scripts/environment_dag_wire/`, `scripts/tactic_parity/` and
# `scripts/tests/` had no caller -- the gap docs/GATE_REGISTRY.md recorded for
# test_release_check_script.py on 2026-08-26, and the one that let a red
# environment_dag_wire/test_schema.py land in 8a237d625. Wired in, three were
# red, all from drift their callers never saw: test_release_check_script.py
# asserted a docs/RELEASE_READINESS.md sentence the Rust axiom-audit lane
# replaced; test_self_verify_crosscheck.py faked `rustc +trust` after the
# runner moved to `trustc` (75ab2ef31, 34 failures) and counted three
# `default_roots()` uses that 4e90bc81a moved into profile.rs; and
# test_generated_count_runner.py was a pytest module (no `__main__`, so run
# as a script it ran nothing) importing a PyYAML nothing here provides.
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
# FALSIFIED, not assumed
# -----------------------
# A gate nobody has seen fail is not a gate. Each arm was applied, run and
# reverted. HISTORY: arms 1-4 were measured on the real tree 2026-08-22 at
# 51c893ce5 (21 s per run) and arms 5-6 on 2026-09-15. Arm 1 prepended
# `sys.exit(1)` to scripts/test_merge_queue.py (appending it does NOT fail the
# suite: `unittest.main()` exits first), and arms 3 and 5 mutated the
# prove_theorem quarantine row (arm 5 lowered its cap 6 -> 5). That row was
# deleted 2026-10-28 with the ledger left empty (docs/DECISIONS.md R190), so on
# 2026-10-28 all seven were re-run on a SYNTHETIC tree: this script, a ledger,
# and stub suites (a passing .py, a passing .sh that prints the summary, a
# passing .sh that prints none, and for arm 5 a red .sh printing
# `=== Results: 1 passed, 2 failed ===`). Arms 3 and 5 name synthetic rows:
#
#   1. UNQUARANTINED RED — `sys.exit(1)` prepended to the passing .py stub:
#        SCRIPT_SELFTESTS=fail unquarantined red: scripts/test_stub_pass.py(exit=1)     rc=1
#   2. STALE QUARANTINE — a row added for that PASSING stub:
#        SCRIPT_SELFTESTS=fail STALE quarantine (these now PASS; ...)                   rc=1
#   3. EXPIRED QUARANTINE — a synthetic row for any suite, expiring 2026-01-01:
#        SCRIPT_SELFTESTS=fail EXPIRED quarantine (fix the suite or re-justify ...)     rc=1
#   4. MALFORMED LEDGER — the ledger replaced with `{ not json`:
#        SCRIPT_SELFTESTS=fail reason=malformed-quarantine-ledger                       rc=1
#   5. WIDENED QUARANTINE (added 2026-09-15) — the red stub (2 failed)
#      quarantined with max_failed 1; at max_failed 2 it is covered, rc=0:
#        SCRIPT_SELFTESTS=fail QUARANTINE WIDENED ... test_stub_red.sh:cap=1:measured=2  rc=1
#   6. UNCAPPED ROW — max_failed deleted from a row:
#        SCRIPT_SELFTESTS=fail reason=malformed-quarantine-ledger                       rc=1
#      (refused before a single suite runs, like every other ledger defect)
#   7. CRASH READ AS PASS (added 2026-10-28) — the summary-printing .sh stub
#      (`set -euo pipefail`) given an EXIT trap and an unbound variable before
#      its summary, so it exits 0 with no summary; also a summary of 0 passes, and one counting
#      failures, each with exit 0. And on a real suite: the mirror test with
#      its SUITE_DONE trap reverted and an unbound variable before Test 8,
#      which alone exits 0. The runner before this rule passed all four:
#        SCRIPT_SELFTESTS=fail exited 0 without its summary ...                         rc=1
#      The passing .sh stub that prints no summary passes throughout: the
#      rule holds only a suite whose source prints the summary.
#   8. NO DRIVER (added 2026-11-10) — a .py suite with its
#      `if __name__ == "__main__":` block deleted; it imports, defines its
#      tests, runs none and exits 0, which read as a pass before this rule
#      (test_generated_count_runner.py was exactly that shape):
#        SCRIPT_SELFTESTS=fail no __main__ driver ...                                 rc=1
#   9. NO TESTS RAN (added 2026-11-10) — `sys.exit(0)` prepended to a
#      unittest.main() suite (arm 1 prepends `sys.exit(1)`; exit 0 read as a
#      pass before this rule), and a suite whose TestCase lost every test
#      method under a Python older than 3.12 (which exits 0 on `Ran 0 tests`):
#        SCRIPT_SELFTESTS=fail exited 0 without running a test ...                    rc=1
#      A .py suite with its own driver (test_pre_push_checkout.py,
#      test_spine_set.py) is not held to unittest's summary; each checks its
#      own arm count.
#
# WHY THE CAP EXISTS (2026-09-15). Rules 1-4 above answer "is this suite
# quarantined, and is the row live". None of them asked HOW RED the suite is,
# so a quarantined suite could go from 6 failures to 10 and stay covered: a new
# regression inside it was invisible by construction. That is the file-level
# suppression this repo's own rule refuses — "a skip list that names a file is
# a suppression; a row that names a site, CAPS IT, and points at the comment is
# an account". The count was already in the ledger as PROSE in `observed`,
# parsed by nothing. `max_failed` is that number, enforced: MORE failures than
# the row records is a refusal, FEWER is progress and passes (the row is a cap,
# exactly like `occurrences` on a production_sites row). A quarantined suite
# whose output carries no readable count is REFUSED rather than assumed zero.
#
# A quarantined suite prints its measured count beside its cap on every run
# (`QUARANTINED-RED <suite> exit=1 failed=6 cap=6`), so the number a reviewer
# would have to take on trust is on screen instead. HISTORY: on 2026-09-15 the
# unmutated tree read `SCRIPT_SELFTESTS suites=26 passed=24`, its two
# quarantined suites at `failed=6 cap=6` and `failed=4 cap=4`. On 2026-10-28 it
# reads `suites=36 passed=36` with an empty ledger.
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

# `find` into a string, not `mapfile`: macOS ships bash 3.2, which has neither
# `mapfile` nor `readarray` nor `globstar`. A gate that only runs on the
# maintainer's Linux box is a gate that does not run. `-type f` skips links;
# scripts/check_gate_registry.py's `selftest_suite_files` mirrors this walk.
# The line protocol below cannot represent LF/CR in a discovered path. Keep
# names NUL-delimited until every path has been checked, before emitting lines.
# A failed traversal, validation or sort can still print a partial list. Refuse
# it before publishing the list or executing any suite from that set.
if ! SUITES="$(find scripts -type f \( -name 'test_*.py' -o -name 'test_*.sh' \) -print0 |
  "$PYTHON_BIN" -c '
import sys
raw = sys.stdin.buffer.read()
if raw and not raw.endswith(b"\0"):
    print("SCRIPT_SELFTESTS=fail reason=unframed-suite-path", file=sys.stderr)
    raise SystemExit(1)
paths = raw.split(b"\0")[:-1]
if any(b"\n" in path or b"\r" in path for path in paths):
    print("SCRIPT_SELFTESTS=fail reason=unrepresentable-suite-path", file=sys.stderr)
    raise SystemExit(1)
sys.stdout.buffer.write(b"".join(path + b"\n" for path in paths))
' | sort)"; then
  echo "SCRIPT_SELFTESTS=fail reason=suite-discovery-failed" >&2
  exit 1
fi

if [ "${1:-}" = "--list" ]; then
  printf '%s\n' "$SUITES"
  exit 0
fi

if [ -z "$SUITES" ]; then
  echo "SCRIPT_SELFTESTS=fail reason=no-suites-found (no test_* file under scripts/ is not a pass)" >&2
  exit 1
fi

# Read the quarantine ledger. Fail closed on an unreadable or malformed file:
# "could not read the exemptions" must never mean "there are none".
QUARANTINED="$("$PYTHON_BIN" - "$QUARANTINE" "$SUITES" <<'PY'
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
if not isinstance(doc, dict) or not isinstance(doc.get("quarantined", []), list):
    print("MALFORMED quarantine ledger needs an object and a quarantined array")
    raise SystemExit(3)
today = datetime.date.today()
discovered = set(sys.argv[2].split("\n"))
seen = set()
for row in doc.get("quarantined", []):
    if not isinstance(row, dict):
        print("MALFORMED quarantine row needs an object")
        raise SystemExit(3)
    suite = row.get("suite")
    if not isinstance(suite, str) or suite not in discovered or suite in seen:
        print(f"MALFORMED suite must name one unique discovered path: {suite!r}")
        raise SystemExit(3)
    seen.add(suite)
    expires = row.get("expires")
    if not suite or not expires:
        print(f"MALFORMED row missing suite/expires: {row}")
        raise SystemExit(3)
    try:
        exp = datetime.date.fromisoformat(expires)
    except ValueError:
        print(f"MALFORMED row bad expires {expires!r} for {suite}")
        raise SystemExit(3)
    # AUDIT r11 M11-9: unbounded above, so a quarantine dated 2999-12-31 read
    # as LIVE forever -- a permanent retirement of a suite selftest wearing a
    # date. Same 180-day horizon as the registry, the hook-coverage reader and
    # the source-elab exception, so "dated" means one thing in this repo.
    horizon = today + datetime.timedelta(days=180)
    if exp > horizon:
        print(f"BEYOND-HORIZON {suite} {expires} (max {horizon.isoformat()})")
        raise SystemExit(3)
    cap = row.get("max_failed")
    if not isinstance(cap, int) or isinstance(cap, bool) or cap < 0:
        print(f"MALFORMED row needs an integer max_failed for {suite}")
        raise SystemExit(3)
    state = "EXPIRED" if exp < today else "LIVE"
    print(f"{state} {suite} {expires} {cap}")
PY
)"
q_rc=$?
if [ "$q_rc" -ne 0 ]; then
  echo "SCRIPT_SELFTESTS=fail reason=malformed-quarantine-ledger ($QUARANTINE)" >&2
  printf '%s\n' "$QUARANTINED" >&2
  exit 1
fi

# Paths are literal identities, never regular expressions. Read the two
# space-free fields from the right so spaces in a suite path stay intact.
quarantine_cap_for_state() { # <suite> <LIVE|EXPIRED>
  local row cap prefix
  prefix="$2 "
  while IFS= read -r row; do
    case "$row" in
      "$prefix"*)
        cap="${row##* }"
        row="${row% *}"
        row="${row% *}"
        row="${row#"$prefix"}"
        if [ "$row" = "$1" ]; then printf '%s\n' "$cap"; return 0; fi
        ;;
    esac
  done <<EOF
$QUARANTINED
EOF
  return 1
}
is_quarantined() { quarantine_cap_for_state "$1" LIVE >/dev/null; }
is_expired()     { quarantine_cap_for_state "$1" EXPIRED >/dev/null; }
quarantine_cap() { quarantine_cap_for_state "$1" LIVE; }

# The measured failure count of a suite, read from its own summary line. Two
# shapes are understood: this repo's shell harnesses print
#   === Results: N passed, M failed ===
# and a Python unittest run prints
#   FAILED (failures=N, errors=M)
# Anything else prints NOTHING, and the caller REFUSES rather than reading an
# unreadable count as zero -- the same rule this file already applies to an
# unreadable ledger. sed and not a heredoc: a second heredoc inside this
# script tripped bash 3.2, which macOS ships and which the glob comment above
# already caters to.
measured_failures() { # <output-file>
  local n f e
  n="$(sed -n 's/.*=== Results: [0-9]* passed, \([0-9]*\) failed ===.*/\1/p' "$1" | tail -1)"
  if [ -n "$n" ]; then printf '%s\n' "$n"; return 0; fi
  f="$(sed -n 's/.*failures=\([0-9]*\).*/\1/p' "$1" | tail -1)"
  e="$(sed -n 's/.*errors=\([0-9]*\).*/\1/p' "$1" | tail -1)"
  if [ -n "$f" ] || [ -n "$e" ]; then printf '%s\n' "$(( ${f:-0} + ${e:-0} ))"; fi
}

TOTAL=0; PASSED=0
FAILURES=""; STALE=""; EXPIRED=""; WIDENED=""; UNREADABLE=""; NO_SUMMARY=""
NO_DRIVER=""; NO_TESTS_RAN=""

while IFS= read -r suite; do
  [ -n "$suite" ] || continue
  TOTAL=$((TOTAL + 1))
  case "$suite" in
    *.py) runner=(env "PYTHONPATH=$REPO_ROOT" "$PYTHON_BIN" "$suite") ;;
    *)    runner=(bash "$suite") ;;
  esac
  out_file="$(mktemp "${TMPDIR:-/tmp}/Clean-selftest-out.XXXXXX")"
  if "${runner[@]}" >"$out_file" 2>&1 </dev/null; then
    rc=0
  else
    rc=$?
  fi
  if is_expired "$suite"; then
    EXPIRED="$EXPIRED $suite"
    rm -f "$out_file"
    continue
  fi
  # An exit 0 from a shell suite that prints the harness summary counts only
  # with that summary, at least one pass and no failures. macOS /bin/bash 3.2,
  # which runs these, exits 0 when an expansion error (an unbound variable
  # under `set -u`, or `${X:?}`) aborts a `set -e` script that has an EXIT
  # trap, so a crash after the trap would read as a pass (2026-10-28, R190;
  # without `set -e` the same abort exits 1). The rule keys on the suite's own
  # source: one that never prints the summary is not held to it, and a suite
  # of that kind with such a trap guards itself (test_source_elab_gate.sh's
  # SUITE_DONE).
  is_sh=0
  case "$suite" in *.sh) is_sh=1 ;; esac
  if [ "$rc" -eq 0 ] && [ "$is_sh" -eq 1 ] && grep -q '=== Results: ' "$suite" &&
    ! grep -Eq '^=== Results: [1-9][0-9]* passed, 0 failed ===$' "$out_file"; then
    NO_SUMMARY="$NO_SUMMARY $suite"
    rm -f "$out_file"
    continue
  fi
  # A .py suite runs as a script, so one without a `__main__` driver (a pytest
  # module) defines its tests, runs none and exits 0. One that drives
  # unittest.main() passes only with a nonzero `Ran N tests`: `sys.exit(0)`
  # before it, or no test methods under Python < 3.12, also exits 0. A suite
  # with its own driver is not held to unittest's summary.
  if [ "$is_sh" -eq 0 ] && ! grep -Eq "^if __name__ *== *[\"']__main__[\"'] *:" "$suite"; then
    NO_DRIVER="$NO_DRIVER $suite"
    rm -f "$out_file"
    continue
  fi
  if [ "$rc" -eq 0 ] && [ "$is_sh" -eq 0 ] && grep -q 'unittest\.main(' "$suite" &&
    ! grep -Eq '^Ran [1-9][0-9]* tests? in ' "$out_file"; then
    NO_TESTS_RAN="$NO_TESTS_RAN $suite"
    rm -f "$out_file"
    continue
  fi
  if [ "$rc" -eq 0 ]; then
    PASSED=$((PASSED + 1))
    if is_quarantined "$suite"; then
      STALE="$STALE $suite"
    fi
  else
    if is_quarantined "$suite"; then
      cap="$(quarantine_cap "$suite")"
      got="$(measured_failures "$out_file")"
      if [ -z "$got" ]; then
        UNREADABLE="$UNREADABLE $suite"
      elif [ "$got" -gt "$cap" ]; then
        WIDENED="$WIDENED $suite:cap=$cap:measured=$got"
      fi
      echo "  QUARANTINED-RED $suite exit=$rc failed=${got:-unreadable} cap=$cap"
    else
      FAILURES="$FAILURES $suite(exit=$rc)"
    fi
  fi
  rm -f "$out_file"
done <<EOF
$SUITES
EOF

echo "SCRIPT_SELFTESTS suites=$TOTAL passed=$PASSED"

rc=0
if [ -n "$FAILURES" ]; then
  printf 'SCRIPT_SELFTESTS=fail unquarantined red:%s\n' "$FAILURES" >&2
  rc=1
fi
if [ -n "$NO_SUMMARY" ]; then
  printf 'SCRIPT_SELFTESTS=fail exited 0 without its summary -- each prints "=== Results: N passed, M failed ===" and did not print it with N>0 and M=0, so it stopped early (macOS bash 3.2 exits 0 when an unbound variable or ${X:?} aborts a set -e script that has an EXIT trap):%s\n' \
    "$NO_SUMMARY" >&2
  rc=1
fi
if [ -n "$NO_DRIVER" ]; then
  printf 'SCRIPT_SELFTESTS=fail no __main__ driver -- each .py suite runs as a script, and one without `if __name__ == "__main__":` runs no test; drive it with unittest.main():%s\n' \
    "$NO_DRIVER" >&2
  rc=1
fi
if [ -n "$NO_TESTS_RAN" ]; then
  printf 'SCRIPT_SELFTESTS=fail exited 0 without running a test -- each drives unittest.main() and printed no "Ran N tests" with N>0:%s\n' \
    "$NO_TESTS_RAN" >&2
  rc=1
fi
if [ -n "$STALE" ]; then
  printf 'SCRIPT_SELFTESTS=fail STALE quarantine (these now PASS; delete their rows in %s):%s\n' \
    "$QUARANTINE" "$STALE" >&2
  rc=1
fi
if [ -n "$WIDENED" ]; then
  printf 'SCRIPT_SELFTESTS=fail QUARANTINE WIDENED -- a quarantine covers the failures it RECORDED, never any future ones; fix the new breakage or re-justify and raise max_failed in %s:%s\n' \
    "$QUARANTINE" "$WIDENED" >&2
  rc=1
fi
if [ -n "$UNREADABLE" ]; then
  printf 'SCRIPT_SELFTESTS=fail a quarantined suite printed no readable failure count, so its cap could not be checked -- an uncountable suppression is not an account; teach measured_failures its summary shape:%s\n' \
    "$UNREADABLE" >&2
  rc=1
fi
if [ -n "$EXPIRED" ]; then
  printf 'SCRIPT_SELFTESTS=fail EXPIRED quarantine (fix the suite or re-justify the row in %s):%s\n' \
    "$QUARANTINE" "$EXPIRED" >&2
  rc=1
fi
[ "$rc" -eq 0 ] && echo "SCRIPT_SELFTESTS=ok"
exit "$rc"
