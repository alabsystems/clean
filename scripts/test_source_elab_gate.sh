#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Focused regression tests for scripts/source_elab_gate.sh.
#
# Deliberately corpus-free and binary-free: every test forces a deterministic
# path (CLEAN_BIN/CLEAN_MATHLIB_DIR overrides, --parse-report plumbing mode),
# so the suite passes on machines without a release build or a Mathlib
# checkout — exactly the environments where the gate's skip discipline and
# verdict-line contract matter most.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
GATE="${REPO_ROOT}/scripts/source_elab_gate.sh"
RATCHET="${REPO_ROOT}/data/source_elab_ratchet.json"

PASS=0
FAIL=0

pass() {
  PASS=$((PASS + 1))
  echo "  PASS: $1"
}

fail() {
  FAIL=$((FAIL + 1))
  echo "  FAIL: $1" >&2
}

TMP_DIR="$(mktemp -d -t source_elab_gate_test.XXXXXX)"
# macOS /bin/bash 3.2, which scripts/check_script_selftests.sh runs this under,
# exits 0 when an expansion error (an unbound variable under `set -u`, or
# `${X:?}`) aborts a `set -e` script that has an EXIT trap, so a crash after
# this line would read as a pass. Any exit before the summary is 70.
SUITE_DONE=0
on_exit() {
  rm -rf "$TMP_DIR"
  if [ "$SUITE_DONE" != 1 ]; then
    echo "  FAIL: the suite stopped before its summary line (exit 70)" >&2
    exit 70
  fi
}
trap on_exit EXIT

# --- 1. shell syntax -------------------------------------------------------
if bash -n "$GATE"; then
  pass "gate script parses (bash -n)"
else
  fail "gate script has a bash syntax error"
fi

# --- 2. committed ratchet artifact shape ----------------------------------
# ARMED 2026-08-23 at a86c5ffd6. This assertion used to pin the opposite
# ("armed is False, every baseline 0") because the ratchet had never been armed;
# an armed ratchet with a zero baseline enforces nothing, so the shape check
# flips with it rather than being deleted.
if python3 - "$RATCHET" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
assert d["schema_version"] == "Clean-srcelab-ratchet-v1", d.get("schema_version")
assert d["armed"] is True, "the committed ratchet is ARMED as of 2026-08-23"
assert d["counting_basis"] == "allow_sorry_success", d.get("counting_basis")
assert d.get("armed_commit"), "an armed baseline must record the commit it was measured at"
files = d["files"]
assert len(files) == 5, sorted(files)
for key, v in files.items():
    base = v.get("success_baseline")
    assert isinstance(base, int) and base > 0, (key, v)
    assert isinstance(v.get("decl_count"), int) and v["decl_count"] >= base, (key, v)
# No pinned file carries a line cap since 2026-08-23 (the Unique OOM that
# forced the 1-240 cap no longer reproduces: 2.97 GiB for the full file).
# The cap MACHINERY is still exercised, generically, by test 11b.
assert all("cap_lines" not in v for v in files.values()), files
assert "Mathlib/Order/Basic.lean" in files, sorted(files)
assert "sorry" in d["notes"], "notes must state the counting-basis caveat"
PY
then
  pass "ratchet artifact: ARMED, every baseline measured and > 0, 5 pinned keys, no caps"
else
  fail "ratchet artifact shape check"
fi

# --- 3. --parse-report extracts a Clean-check-report-v1 object ------------
FIX="$TMP_DIR/check_stdout.txt"
cat > "$FIX" <<'EOF'
warning: some non-JSON preamble line the parser must skip
{
  "schema_version": "Clean-check-report-v1",
  "command": "clean check",
  "file": "Mathlib/Logic/Basic.lean",
  "module": "Mathlib.Logic.Basic",
  "status": "fail",
  "decl_count": 257,
  "success_count": 86,
  "failed_count": 171,
  "trust_summary": { "sorry_axioms": 4, "kernel_check_failures": 0 },
  "errors": ["x: elaboration error"],
  "trust_failures": [],
  "kernel_failures": [],
  "proof_state_feedback": []
}
EOF
set +e
PARSED="$("$GATE" --parse-report "$FIX")"
rc=$?
set -e
if [ "$rc" -eq 0 ] && python3 -c '
import json, sys
d = json.loads(sys.argv[1])
assert d["success_count"] == 86, d
assert d["decl_count"] == 257, d
assert d["failed_count"] == 171, d
assert d["sorry_axioms"] == 4, d
assert d["kernel_check_failures"] == 0, d
assert d["status"] == "fail", d
' "$PARSED"; then
  pass "--parse-report extracts counters past leading non-JSON noise"
else
  fail "--parse-report extraction (rc=$rc, parsed=$PARSED)"
fi

# --- 4. --parse-report fail-closed on garbage and on wrong schema ---------
GARBAGE="$TMP_DIR/garbage.txt"
printf 'no json here at all\n' > "$GARBAGE"
set +e
"$GATE" --parse-report "$GARBAGE" >/dev/null 2>&1
rc=$?
set -e
if [ "$rc" -eq 2 ]; then
  pass "--parse-report exits 2 on a report with no JSON"
else
  fail "--parse-report garbage handling (rc=$rc, want 2)"
fi

WRONG="$TMP_DIR/wrong_schema.txt"
printf '{"schema_version": "something-else", "success_count": 9}\n' > "$WRONG"
set +e
"$GATE" --parse-report "$WRONG" >/dev/null 2>&1
rc=$?
set -e
if [ "$rc" -eq 3 ]; then
  pass "--parse-report exits 3 on a non-Clean-check-report-v1 schema"
else
  fail "--parse-report wrong-schema handling (rc=$rc, want 3)"
fi

# --- 4b. the THIRD verdict survives the parse, and a gap that nothing --------
#         explains is loud
#
# WHY THIS EXISTS. `clean check` grew a `diverged` verdict at 60e8747e7 -- a
# declaration that spends its whole per-declaration budget is neither a pass nor
# a failure -- and this gate's report parser predates it. Measured 2026-08-30
# through --parse-report on exactly the fixture below, the parser emitted only
# {decl_count, success_count, failed_count, sorry_axioms, kernel_check_failures,
# status}: the three diverged declarations VANISHED, leaving an artifact whose
# own counts did not add up and nothing in it to say why.
#
# The defect was INERT at the time it was found (0 diverged across all five
# pinned files in the last run), so no published number was wrong. It is pinned
# anyway, because a gate whose artifact can silently fail to account for its own
# denominator is the vacuous-gate shape this repo has now found six times.
#
# The invariant is deliberately ONE-SIDED, so all four directions are pinned
# below: a sum BELOW decl_count is a refusal, a sum ABOVE it is legitimate
# (file-level parser-recovery diagnostics are errors but not declarations).
srcelab_report_fixture() {
  # <dest> <decl> <success> <failed> <diverged|-> ; `-` omits the field entirely
  python3 - "$@" <<'PY'
import json, sys
o = {
    "schema_version": "Clean-check-report-v1",
    "command": "clean check",
    "file": "Mathlib/Logic/Basic.lean",
    "module": "Mathlib.Logic.Basic",
    "status": "fail",
    "decl_count": int(sys.argv[2]),
    "success_count": int(sys.argv[3]),
    "failed_count": int(sys.argv[4]),
    "trust_summary": {"sorry_axioms": 0, "kernel_check_failures": 0},
    "errors": [], "trust_failures": [], "kernel_failures": [],
    "proof_state_feedback": [],
}
if sys.argv[5] != "-":
    o["diverged_count"] = int(sys.argv[5])
    o["diverged"] = ["d{}: did not finish".format(i) for i in range(int(sys.argv[5]))]
with open(sys.argv[1], "w", encoding="utf-8") as f:
    json.dump(o, f, indent=2)
PY
}

# (i) the reported defect, verbatim: 10 counted, 4 pass, 3 fail, 3 diverged.
DIVERGED_FIX="$TMP_DIR/check_diverged.json"
srcelab_report_fixture "$DIVERGED_FIX" 10 4 3 3
set +e
PARSED="$("$GATE" --parse-report "$DIVERGED_FIX")"
rc=$?
set -e
if [ "$rc" -eq 0 ] && python3 -c '
import json, sys
d = json.loads(sys.argv[1])
assert d["diverged_count"] == 3, ("diverged_count dropped by the parser", d)
assert d["decl_count"] == 10 and d["success_count"] == 4 and d["failed_count"] == 3, d
# The whole point: the counts now ACCOUNT for the denominator.
assert d["accounted_count"] == 10, d
assert d["success_count"] + d["failed_count"] + d["diverged_count"] == d["decl_count"], d
' "$PARSED"; then
  pass "--parse-report carries diverged_count (3 diverged decls survive the parse)"
else
  fail "--parse-report diverged_count carry-through (rc=$rc, parsed=$PARSED)"
fi

# (ii) the same report with the diverged declarations UNACCOUNTED must refuse
# loudly -- exit 5, with the missing count named on stderr -- not exit 0 with a
# silent hole. This is the pre-fix behaviour turned into a hard failure.
GAP_FIX="$TMP_DIR/check_unaccounted.json"
srcelab_report_fixture "$GAP_FIX" 10 4 3 -
set +e
GAP_ERR="$("$GATE" --parse-report "$GAP_FIX" 2>&1 >/dev/null)"
rc=$?
set -e
if [ "$rc" -eq 5 ] \
   && printf '%s\n' "$GAP_ERR" | grep -q '10 declarations counted but only 7 accounted for' \
   && printf '%s\n' "$GAP_ERR" | grep -q '3 declaration(s) carry no verdict'; then
  pass "--parse-report exits 5 and names the hole when decl_count is unaccounted for"
else
  fail "--parse-report unaccounted-decl refusal (rc=$rc, want 5; stderr=$GAP_ERR)"
fi

# (iii) the OTHER direction is legitimate and must NOT be refused. failed_count
# includes file-level parser-recovery diagnostics, which are not declarations
# and so are absent from decl_count. Measured 2026-08-30 over every checked-in
# report row carrying per_error_class: the excess equals the parser-recovery
# count exactly, 37 of 37, and no row in the whole reports/source-elab/ history
# has ever gone the other way. Refusing this direction would fail the gate on
# every real run.
OVER_FIX="$TMP_DIR/check_overcount.json"
srcelab_report_fixture "$OVER_FIX" 10 4 8 -
set +e
PARSED="$("$GATE" --parse-report "$OVER_FIX")"
rc=$?
set -e
if [ "$rc" -eq 0 ] && python3 -c '
import json, sys
d = json.loads(sys.argv[1])
assert d["accounted_count"] == 12 and d["decl_count"] == 10, d
' "$PARSED"; then
  pass "--parse-report accepts failed_count above decl_count (parser-recovery diagnostics)"
else
  fail "--parse-report over-count acceptance (rc=$rc, parsed=$PARSED)"
fi

# (iv) reports minted before the diverged verdict existed carry no such field.
# Absence reads as 0 -- that binary had no per-declaration budget and could not
# diverge -- and must not become an error.
OLD_FIX="$TMP_DIR/check_prediverged.json"
srcelab_report_fixture "$OLD_FIX" 10 4 6 -
set +e
PARSED="$("$GATE" --parse-report "$OLD_FIX")"
rc=$?
set -e
if [ "$rc" -eq 0 ] && python3 -c '
import json, sys
d = json.loads(sys.argv[1])
assert d["diverged_count"] == 0, d
assert d["accounted_count"] == 10, d
' "$PARSED"; then
  pass "--parse-report reads an absent diverged_count as 0 (pre-60e8747e7 reports)"
else
  fail "--parse-report pre-diverged compatibility (rc=$rc, parsed=$PARSED)"
fi

# (v) a counter that is not a non-negative integer is a SCHEMA violation, not a
# zero. `"decl_count": null` defaulted to 0 would read a whole file as empty and
# call the run a pass.
NULL_FIX="$TMP_DIR/check_nullcount.json"
printf '{"schema_version":"Clean-check-report-v1","decl_count":null,"success_count":0,"failed_count":0}\n' > "$NULL_FIX"
set +e
"$GATE" --parse-report "$NULL_FIX" >/dev/null 2>&1
rc=$?
set -e
if [ "$rc" -eq 3 ]; then
  pass "--parse-report exits 3 on a malformed counter rather than defaulting it to 0"
else
  fail "--parse-report malformed-counter handling (rc=$rc, want 3)"
fi

# --- 5. skip discipline: no binary ----------------------------------------
set +e
OUT="$(CLEAN_BIN=/nonexistent/clean "$GATE" 2>/dev/null)"
rc=$?
set -e
if [ "$rc" -eq 0 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=skipped:no-binary$'; then
  pass "no-binary path: exit 0 + skipped:no-binary verdict"
else
  fail "no-binary path (rc=$rc, out=$OUT)"
fi
if [ "$(printf '%s\n' "$OUT" | grep -c '^SRCELAB_GATE=')" -eq 1 ]; then
  pass "no-binary path emits exactly one verdict line"
else
  fail "no-binary path verdict-line count"
fi

# --- 6. skip discipline: binary present, no corpus ------------------------
FAKE_BIN="$TMP_DIR/clean"
printf '#!/bin/sh\nexit 0\n' > "$FAKE_BIN"
chmod +x "$FAKE_BIN"
set +e
OUT="$(CLEAN_BIN="$FAKE_BIN" CLEAN_MATHLIB_DIR="$TMP_DIR/no-such-mathlib" "$GATE" 2>/dev/null)"
rc=$?
set -e
if [ "$rc" -eq 0 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=skipped:no-corpus$'; then
  pass "no-corpus path: exit 0 + skipped:no-corpus verdict (explicit env var authoritative)"
else
  fail "no-corpus path (rc=$rc, out=$OUT)"
fi

# --- 7. SRCELAB_GATE_REQUIRE_MEASURED turns a skip into a failure ---------
set +e
OUT="$(CLEAN_BIN="$FAKE_BIN" CLEAN_MATHLIB_DIR="$TMP_DIR/no-such-mathlib" \
       SRCELAB_GATE_REQUIRE_MEASURED=1 "$GATE" 2>/dev/null)"
rc=$?
set -e
if [ "$rc" -eq 1 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=skipped:no-corpus$'; then
  pass "REQUIRE_MEASURED: skip becomes exit 1, verdict still emitted"
else
  fail "REQUIRE_MEASURED skip handling (rc=$rc, out=$OUT)"
fi

# --- 8. verdict file mirror -----------------------------------------------
VFILE="$TMP_DIR/verdict.txt"
set +e
CLEAN_BIN=/nonexistent/clean SRCELAB_GATE_VERDICT_FILE="$VFILE" "$GATE" >/dev/null 2>&1
set -e
if [ -f "$VFILE" ] && grep -q '^SRCELAB_GATE=skipped:no-binary$' "$VFILE"; then
  pass "SRCELAB_GATE_VERDICT_FILE mirrors the verdict line"
else
  fail "verdict file mirror"
fi

# --- 9. a skipped --update run must not touch data/ -----------------------
BEFORE="$TMP_DIR/ratchet_before.json"
cp "$RATCHET" "$BEFORE"
set +e
CLEAN_BIN="$FAKE_BIN" CLEAN_MATHLIB_DIR="$TMP_DIR/no-such-mathlib" "$GATE" --update >/dev/null 2>&1
set -e
if cmp -s "$RATCHET" "$BEFORE"; then
  pass "skipped --update run leaves data/source_elab_ratchet.json untouched"
else
  fail "skipped --update run modified the ratchet artifact"
  cp "$BEFORE" "$RATCHET" # restore for later runs
fi

# --- 10. unknown argument fails closed with a verdict ---------------------
set +e
OUT="$(CLEAN_BIN=/nonexistent/clean "$GATE" --no-such-flag 2>/dev/null)"
rc=$?
set -e
if [ "$rc" -eq 1 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=failed:usage$'; then
  pass "unknown argument: exit 1 + failed:usage verdict"
else
  fail "unknown-argument handling (rc=$rc, out=$OUT)"
fi

# --- 11. end-to-end measured path with a fake corpus + fake binary --------
# A fake Mathlib tree (all five pinned files present, .lake/build marker dir)
# and a fake `clean` that always prints the fixture CheckReport and exits 1
# (the real check's exit contract when failed_count > 0). All artifact paths
# are redirected via the test/plumbing env overrides, so the committed
# data/ ratchet and reports/ tree stay untouched.
FAKE_ML="$TMP_DIR/mathlib"
mkdir -p "$FAKE_ML/.lake/build/lib/lean" \
         "$FAKE_ML/Mathlib/Logic/Function" "$FAKE_ML/Mathlib/Data" \
         "$FAKE_ML/Mathlib/Order"
for f in "Mathlib/Logic/Basic.lean" "Mathlib/Logic/Function/Basic.lean" \
         "Mathlib/Data/Subtype.lean" "Mathlib/Logic/Unique.lean" \
         "Mathlib/Order/Basic.lean"; do
  printf '%s\n' "-- fake pinned source ($f)" > "$FAKE_ML/$f"
done
# THE FAKE CORPUS CARRIES AN IDENTITY (2026-09-15), because the gate now
# refuses to arm baselines against a Mathlib it cannot name -- per-file counts
# are only comparable across the SAME corpus, so a baseline with no corpus is a
# count of nothing identifiable. A bare temp directory has no git rev and no
# lean-toolchain, so without this the harness would be exercising a path the
# real gate forbids.
printf '%s\n' "leanprover/lean4:v4.99.0-fake" > "$FAKE_ML/lean-toolchain"
(
  cd "$FAKE_ML"
  git init -q .
  git config user.email "selftest@example.invalid"
  git config user.name "srcelab selftest"
  git add -A
  git -c commit.gpgsign=false commit -q -m "fake corpus" >/dev/null 2>&1
) >/dev/null 2>&1
FAKE_ML_REV="$(git -C "$FAKE_ML" rev-parse HEAD 2>/dev/null || true)"
[ -n "$FAKE_ML_REV" ] || { echo "FATAL: fake corpus has no git rev; the harness cannot exercise the armed path" >&2; exit 1; }
FAKE_CHECK="$TMP_DIR/fake_check_clean"
{
  printf '#!/bin/sh\ncat <<"JSON"\n'
  # fixture minus the noise preamble line
  tail -n +2 "$FIX"
  printf 'JSON\nexit 1\n'
} > "$FAKE_CHECK"
chmod +x "$FAKE_CHECK"
# The e2e fixture ratchet is an explicitly UNARMED copy, derived from the
# committed one but with armed=false and zero baselines. It must NOT inherit
# the committed artifact's armed state: since 2026-08-23 the real ratchet
# carries measured baselines (151/77/13/8) that the 86-success fixture is below,
# which would make every e2e test below fail as a "regression" and say nothing
# about the paths they exist to cover. Test 13 arms this copy itself.
TEST_RATCHET="$TMP_DIR/ratchet.json"
python3 - "$RATCHET" "$TEST_RATCHET" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
d["armed"] = False
d.pop("armed_commit", None)
for v in d["files"].values():
    v["success_baseline"] = 0
    v.pop("decl_count", None)
    v.pop("sorry_axioms", None)
    # Nor may it inherit the committed PERFORMANCE baselines (armed 2026-09-25):
    # the fake `clean` here prints no `timing`, so every run re-armed from this
    # copy would fail perf-unmeasured and say nothing about the path under test.
    # Performance is scripts/srcelab_guard_demo.sh's subject.
    v.pop("perf_baseline", None)
json.dump(d, open(sys.argv[2], "w", encoding="utf-8"), indent=2)
PY
UNARMED_RATCHET="$TMP_DIR/ratchet_unarmed_seed.json"
cp "$TEST_RATCHET" "$UNARMED_RATCHET"
TEST_REPORTS="$TMP_DIR/reports"
run_gate_e2e() {
  CLEAN_BIN="$FAKE_CHECK" CLEAN_MATHLIB_DIR="$FAKE_ML" \
  SRCELAB_RATCHET="$TEST_RATCHET" SRCELAB_REPORT_DIR="$TEST_REPORTS" \
  SRCELAB_GATE_MEM_GIB_MIN=0 "$GATE" "$@"
}
set +e
OUT="$(run_gate_e2e 2>/dev/null)"
rc=$?
set -e
REPORT_FILE="$(ls "$TEST_REPORTS"/srcelab-*.json 2>/dev/null | head -1 || true)"
if [ "$rc" -eq 0 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=measured$' \
   && [ -n "$REPORT_FILE" ] && python3 - "$REPORT_FILE" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
assert d["schema_version"] == "Clean-srcelab-report-v1", d
assert len(d["files"]) == 5, [r["key"] for r in d["files"]]
assert d["totals"]["success_count"] == 5 * 86, d["totals"]
assert d["totals"]["sorry_axioms"] == 5 * 4, d["totals"]
assert d["counting_basis"] == "allow_sorry_success", d
assert d["ratchet"]["enforced"] is False, "unarmed ratchet must report enforced=false"
caps = {r["key"]: r["cap_lines"] for r in d["files"]}
assert set(caps.values()) == {None}, caps
PY
then
  pass "measured path: verdict=measured, dated report with totals, no capped file"
else
  fail "measured path (rc=$rc, report=$REPORT_FILE, out=$OUT)"
fi
LEFTOVER="$(find "$FAKE_ML" -name '*_srcelab_cap*_tmp.lean' 2>/dev/null | tr '\n' ' ')"
if [ -z "$LEFTOVER" ]; then
  pass "measured path leaves no line-cap temp copy anywhere in the corpus tree"
else
  fail "line-cap temp copies left behind in the corpus tree: $LEFTOVER"
fi

# --- 11b. the line-cap machinery still works, on a gate copy that uses it --
# WHY THIS EXISTS. Until 2026-08-23 the cap path was covered only because the
# real slice happened to pin Mathlib/Logic/Unique.lean:1-240. Retiring that cap
# (its OOM no longer reproduces -- 2.97 GiB for the full file, measured) would
# have silently deleted the coverage with it. `head -n <cap>` sibling copies,
# cap_lines in the report and cleanup on exit are all still LIVE code, so they
# are tested here against a throwaway copy of the gate whose pinned slice caps
# one file: no production seam, and the assertion is on the machinery rather
# than on which file happens to use it.
# The gate resolves its repo root as `dirname $0/..`, so the copy must sit in a
# `scripts/` dir with the modules it runs beside it: srcelab_classify.py, and
# (since 2026-09-24) the per-declaration guard and the performance leg.
CAPROOT="$TMP_DIR/gatecopy"
mkdir -p "$CAPROOT/scripts"
for _mod in srcelab_classify.py srcelab_decl_guard.py srcelab_perf.py; do
  cp "$REPO_ROOT/scripts/$_mod" "$CAPROOT/scripts/"
done
CAPGATE="$CAPROOT/scripts/gate_with_cap.sh"
python3 - "$GATE" "$CAPGATE" <<'CAPPATCH'
import sys
src, dst = sys.argv[1], sys.argv[2]
s = open(src, encoding="utf-8").read()
old = "Mathlib/Order/Basic.lean|Mathlib/Order/Basic.lean|\nPINNEDSLICE"
new = "Mathlib/Order/Basic.lean|Mathlib/Order/Basic.lean|17\nPINNEDSLICE"
assert s.count(old) == 1, "pinned-slice anchor moved; fix test 11b"
open(dst, "w", encoding="utf-8").write(s.replace(old, new))
CAPPATCH
chmod +x "$CAPGATE"
CAPRATCHET="$TMP_DIR/ratchet_cap.json"
cp "$UNARMED_RATCHET" "$CAPRATCHET"
# 40 lines of fake source, so a cap of 17 truncates something real
awk 'BEGIN { for (i = 1; i <= 40; i++) print "-- fake line " i }' \
  > "$FAKE_ML/Mathlib/Order/Basic.lean"
set +e
CLEAN_BIN="$FAKE_CHECK" CLEAN_MATHLIB_DIR="$FAKE_ML" SRCELAB_RATCHET="$CAPRATCHET" \
  SRCELAB_REPORT_DIR="$TMP_DIR/reports-cap" SRCELAB_GATE_MEM_GIB_MIN=0 \
  "$CAPGATE" >/dev/null 2>&1
rc=$?
set -e
CAPREPORT="$(ls -t "$TMP_DIR/reports-cap"/srcelab-*.json 2>/dev/null | head -1 || true)"
CAPLEFT="$(find "$FAKE_ML" -name '*_srcelab_cap*_tmp.lean' 2>/dev/null | tr '\n' ' ')"
CAPWC="$(wc -l < "$FAKE_ML/Mathlib/Order/Basic.lean" | tr -d ' ')"
if [ "$rc" -eq 0 ] && [ -n "$CAPREPORT" ] && [ -z "$CAPLEFT" ] && [ "$CAPWC" = 40 ] \
   && python3 - "$CAPREPORT" <<'CAPCHECK'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
caps = {r["key"]: r["cap_lines"] for r in d["files"]}
assert caps["Mathlib/Order/Basic.lean"] == 17, caps
assert set(v for k, v in caps.items() if k != "Mathlib/Order/Basic.lean") == {None}, caps
CAPCHECK
then
  pass "line-cap machinery: cap honoured, cap_lines recorded, temp copy cleaned up, original untouched"
else
  fail "line-cap machinery (rc=$rc, report=$CAPREPORT, leftover=$CAPLEFT, wc=$CAPWC)"
fi
# restore the one-line fake source the rest of the suite expects
printf '%s\n' "-- fake pinned source (Mathlib/Order/Basic.lean)" \
  > "$FAKE_ML/Mathlib/Order/Basic.lean"

# --- 12. --update arms the ratchet with measured baselines ----------------
set +e
OUT="$(run_gate_e2e --update 2>/dev/null)"
rc=$?
set -e
ARM_REPORT="$(ls -t "$TEST_REPORTS"/srcelab-*.json 2>/dev/null | head -1 || true)"
if [ "$rc" -eq 0 ] && python3 - "$TEST_RATCHET" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
assert d["armed"] is True, d
assert len(d["files"]) == 5, sorted(d["files"])
assert all(v["success_baseline"] == 86 for v in d["files"].values()), d["files"]
assert all("cap_lines" not in v for v in d["files"].values()), d["files"]
assert "armed_commit" in d, sorted(d)
PY
then
  pass "--update arms the ratchet with measured per-file baselines"
else
  fail "--update arming (rc=$rc, out=$OUT)"
fi

# The report of an ARMING run must not describe itself as unarmed. It is
# written before the arming (so a regression keeps its evidence) and then
# corrected; without the correction the artifact of the run that armed the
# ratchet reads `"armed": false`, which is exactly backwards.
if [ -n "$ARM_REPORT" ] && python3 - "$ARM_REPORT" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
r = d["ratchet"]
assert r["armed"] is True and r["enforced"] is True, r
assert r["armed_by_this_run"] is True, r
assert r["armed_state_before_this_run"] is False, r
PY
then
  pass "--update run's report records armed_by_this_run, not armed=false"
else
  fail "arming run report ratchet block (report=$ARM_REPORT)"
fi

# --- 13. armed ratchet catches a regression -------------------------------
python3 - "$TEST_RATCHET" <<'PY'
import json, sys
p = sys.argv[1]
d = json.load(open(p, encoding="utf-8"))
d["files"]["Mathlib/Logic/Basic.lean"]["success_baseline"] = 999
json.dump(d, open(p, "w", encoding="utf-8"), indent=2)
PY
set +e
OUT="$(run_gate_e2e 2>/dev/null)"
rc=$?
set -e
if [ "$rc" -eq 1 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=failed:ratchet-regression$'; then
  pass "armed ratchet: success below baseline fails with ratchet-regression verdict"
else
  fail "ratchet regression detection (rc=$rc, out=$OUT)"
fi

# --- 14. a crashed check (no JSON report) fails closed --------------------
FAKE_CRASH="$TMP_DIR/fake_crash_clean"
printf '#!/bin/sh\necho "boom" >&2\nexit 101\n' > "$FAKE_CRASH"
chmod +x "$FAKE_CRASH"
set +e
OUT="$(CLEAN_BIN="$FAKE_CRASH" CLEAN_MATHLIB_DIR="$FAKE_ML" \
       SRCELAB_RATCHET="$TEST_RATCHET" SRCELAB_REPORT_DIR="$TEST_REPORTS" \
       SRCELAB_GATE_MEM_GIB_MIN=0 "$GATE" 2>/dev/null)"
rc=$?
set -e
if [ "$rc" -eq 1 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=failed:check-no-report$'; then
  pass "crashed check with no JSON report fails closed (check-no-report)"
else
  fail "check-no-report handling (rc=$rc, out=$OUT)"
fi

# --- 14b. diverged declarations reach the DATED ARTIFACT, end to end -------
# Test 4b pins the parser; this pins the pipeline behind it. A verdict that
# survives the parse and then evaporates before the report is written would be
# the same defect one stage later.
fake_check_emitting() {  # <dest-script> <report-json>
  {
    printf '#!/bin/sh\ncat <<"JSON"\n'
    cat "$2"
    printf 'JSON\nexit 1\n'
  } > "$1"
  chmod +x "$1"
}

DIV_REPORTS="$TMP_DIR/reports_diverged"
DIV_RATCHET="$TMP_DIR/ratchet_diverged.json"
cp "$UNARMED_RATCHET" "$DIV_RATCHET"
FAKE_DIV="$TMP_DIR/fake_diverged_clean"
fake_check_emitting "$FAKE_DIV" "$DIVERGED_FIX"
set +e
OUT="$(CLEAN_BIN="$FAKE_DIV" CLEAN_MATHLIB_DIR="$FAKE_ML" \
       SRCELAB_RATCHET="$DIV_RATCHET" SRCELAB_REPORT_DIR="$DIV_REPORTS" \
       SRCELAB_GATE_MEM_GIB_MIN=0 "$GATE" 2>"$TMP_DIR/div.stderr")"
rc=$?
set -e
DIV_REPORT="$(ls "$DIV_REPORTS"/srcelab-*.json 2>/dev/null | head -1 || true)"
if [ "$rc" -eq 0 ] && [ -n "$DIV_REPORT" ] && python3 - "$DIV_REPORT" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
for r in d["files"]:
    assert r["diverged_count"] == 3, ("per-file diverged_count missing/wrong", r["key"], r)
    assert r["accounted_count"] == 10, r
assert d["totals"]["diverged_count"] == 5 * 3, d["totals"]
assert d["totals"]["accounted_count"] == 5 * 10, d["totals"]
assert d["totals"]["decl_count"] == 5 * 10, d["totals"]
# The artifact must EXPLAIN its own arithmetic, not merely contain it.
assert "accounting" in d, sorted(d)
assert "diverged_count >= decl_count" in d["accounting"]["invariant"], d["accounting"]
PY
then
  pass "e2e: diverged_count reaches the dated report per file, in totals, with an accounting block"
else
  fail "e2e diverged report plumbing (rc=$rc, report=$DIV_REPORT, out=$OUT)"
fi

# A verdict that means "no verdict" must be SAID, not merely serialised: 15
# declarations with no answer cannot scroll past as a silent 0.
if printf '%s\n' "$OUT" | grep -q 'diverged=3' \
   && grep -q 'NO VERDICT: 3 declaration(s)' "$TMP_DIR/div.stderr"; then
  pass "e2e: a nonzero diverged count is announced on the summary line and on stderr"
else
  fail "e2e diverged announcement (stdout=$OUT, stderr=$(cat "$TMP_DIR/div.stderr"))"
fi

# --- 14c. a report whose verdicts do not account for its own denominator ---
#          fails the WHOLE GATE, with its own reason
UNACC_REPORTS="$TMP_DIR/reports_unaccounted"
UNACC_RATCHET="$TMP_DIR/ratchet_unaccounted.json"
cp "$UNARMED_RATCHET" "$UNACC_RATCHET"
FAKE_UNACC="$TMP_DIR/fake_unaccounted_clean"
fake_check_emitting "$FAKE_UNACC" "$GAP_FIX"
set +e
OUT="$(CLEAN_BIN="$FAKE_UNACC" CLEAN_MATHLIB_DIR="$FAKE_ML" \
       SRCELAB_RATCHET="$UNACC_RATCHET" SRCELAB_REPORT_DIR="$UNACC_REPORTS" \
       SRCELAB_GATE_MEM_GIB_MIN=0 "$GATE" 2>"$TMP_DIR/unacc.stderr")"
rc=$?
set -e
# It must NOT be reported as check-no-report: the report is present and
# well-formed, it simply does not add up. Naming the wrong defect sends the next
# reader to the wrong half of the pipeline.
if [ "$rc" -eq 1 ] \
   && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=failed:check-unaccounted-decls$' \
   && grep -q 'carry no verdict at all' "$TMP_DIR/unacc.stderr"; then
  pass "e2e: an unaccounted-for decl_count fails the gate as check-unaccounted-decls"
else
  fail "e2e unaccounted-decl gate failure (rc=$rc, out=$OUT, stderr=$(cat "$TMP_DIR/unacc.stderr"))"
fi
if [ ! -f "$UNACC_REPORTS"/srcelab-*.json ] 2>/dev/null; then
  pass "e2e: no dated report is published from counts that do not add up"
else
  fail "e2e: a report was published despite unaccounted declarations"
fi

# --- 15. the classifier's own self-test ------------------------------------
if python3 "$REPO_ROOT/scripts/srcelab_classify.py" --self-test >/dev/null 2>&1; then
  pass "srcelab_classify.py self-test"
else
  fail "srcelab_classify.py self-test"
fi

# --- 16. the report carries a per-file failure-class histogram ------------
# The frontier map has to live in the gate's own artifact; before this it was
# recomputed by hand per lane and the one committed histogram was produced by
# an uncommitted classifier over strings that the artifact itself truncates.
cp "$UNARMED_RATCHET" "$TEST_RATCHET"
rm -rf "$TEST_REPORTS"
set +e
run_gate_e2e >/dev/null 2>&1
set -e
REPORT_FILE="$(ls "$TEST_REPORTS"/srcelab-*.json 2>/dev/null | head -1 || true)"
if [ -n "$REPORT_FILE" ] && python3 - "$REPORT_FILE" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
for r in d["files"]:
    assert r["failure_classes"] == {"other": 1}, r["failure_classes"]
    assert r["first_failure"]["class"] == "other", r["first_failure"]
    assert r["first_failure"]["decl"] == "x", r["first_failure"]
    assert r["per_error_class"][0]["class"] == "other", r["per_error_class"]
    assert isinstance(r["wall_seconds"], int), r
PY
then
  pass "report carries per-file failure_classes + first_failure + wall_seconds"
else
  fail "per-file failure-class histogram in the report (report=$REPORT_FILE)"
fi

# --- 17. --jobs N measures the same thing as --jobs 1 ---------------------
# Parallelism is a SCHEDULING change only: each pinned file is still its own
# `clean check` process with the identical invocation. Pin that by comparing
# every recorded counter, class and key between a serial and a parallel run.
SERIAL_REPORTS="$TMP_DIR/reports-serial"
PARALLEL_REPORTS="$TMP_DIR/reports-parallel"
set +e
CLEAN_BIN="$FAKE_CHECK" CLEAN_MATHLIB_DIR="$FAKE_ML" SRCELAB_RATCHET="$TEST_RATCHET" \
  SRCELAB_REPORT_DIR="$SERIAL_REPORTS" SRCELAB_GATE_MEM_GIB_MIN=0 "$GATE" --jobs 1 >/dev/null 2>&1
CLEAN_BIN="$FAKE_CHECK" CLEAN_MATHLIB_DIR="$FAKE_ML" SRCELAB_RATCHET="$TEST_RATCHET" \
  SRCELAB_REPORT_DIR="$PARALLEL_REPORTS" SRCELAB_GATE_MEM_GIB_MIN=0 "$GATE" --jobs 4 >/dev/null 2>&1
set -e
SER="$(ls "$SERIAL_REPORTS"/srcelab-*.json 2>/dev/null | head -1 || true)"
PAR="$(ls "$PARALLEL_REPORTS"/srcelab-*.json 2>/dev/null | head -1 || true)"
if [ -n "$SER" ] && [ -n "$PAR" ] && python3 - "$SER" "$PAR" <<'PY'
import json, sys
a = json.load(open(sys.argv[1], encoding="utf-8"))
b = json.load(open(sys.argv[2], encoding="utf-8"))
assert a["totals"] == b["totals"], (a["totals"], b["totals"])
# The fields parallelism is allowed to move are MEASUREMENTS of the process,
# never verdicts: its wall clock, and (since the 2026-09-24 performance leg)
# its peak RSS from /usr/bin/time, which differs by a page run to run even for
# the fake `clean` here -- measured 2026-09-25: 2,211,840 vs 2,228,224 bytes for
# the same file in a serial and a parallel run, one flake in four pairs.
drop = {"wall_seconds", "max_rss_bytes"}
fa = [{k: v for k, v in r.items() if k not in drop} for r in a["files"]]
fb = [{k: v for k, v in r.items() if k not in drop} for r in b["files"]]
assert fa == fb, "serial and parallel per-file records differ"
assert [r["key"] for r in b["files"]] == [r["key"] for r in a["files"]], "plan order not preserved"
PY
then
  pass "--jobs 4 records byte-identical per-file results, in plan order"
else
  fail "--jobs parallel/serial equivalence (serial=$SER parallel=$PAR)"
fi

# --- 18. --jobs validation fails closed -----------------------------------
set +e
OUT="$(CLEAN_BIN=/nonexistent/clean "$GATE" --jobs 0 2>/dev/null)"
rc=$?
OUT2="$(CLEAN_BIN=/nonexistent/clean "$GATE" --jobs banana 2>/dev/null)"
rc2=$?
set -e
if [ "$rc" -eq 1 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=failed:usage$' \
   && [ "$rc2" -eq 1 ] && printf '%s\n' "$OUT2" | grep -q '^SRCELAB_GATE=failed:usage$'; then
  pass "--jobs 0 and --jobs banana fail closed with failed:usage"
else
  fail "--jobs validation (rc=$rc/$rc2)"
fi

# --- 19. SRCELAB_KEEP_DIR preserves the untruncated stdout ----------------
KEEP="$TMP_DIR/keep"
set +e
CLEAN_BIN="$FAKE_CHECK" CLEAN_MATHLIB_DIR="$FAKE_ML" SRCELAB_RATCHET="$TEST_RATCHET" \
  SRCELAB_REPORT_DIR="$TMP_DIR/reports-keep" SRCELAB_GATE_MEM_GIB_MIN=0 \
  SRCELAB_KEEP_DIR="$KEEP" "$GATE" >/dev/null 2>&1
set -e
if [ -s "$KEEP/Mathlib_Logic_Basic.lean.stdout" ] \
   && [ -s "$KEEP/Mathlib_Logic_Unique.lean.stdout" ] \
   && [ -s "$KEEP/Mathlib_Order_Basic.lean.stdout" ] \
   && grep -q 'Clean-check-report-v1' "$KEEP/Mathlib_Data_Subtype.lean.stdout"; then
  pass "SRCELAB_KEEP_DIR keeps every pinned file's untruncated stdout"
else
  fail "SRCELAB_KEEP_DIR ($(ls "$KEEP" 2>/dev/null | tr '\n' ' '))"
fi

# --- 20. --check-artifact passes on the committed ratchet -----------------
set +e
OUT="$("$GATE" --check-artifact 2>&1)"
rc=$?
set -e
if [ "$rc" -eq 0 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=artifact-ok$'; then
  pass "--check-artifact: committed ratchet agrees with the pinned slice"
else
  fail "--check-artifact on the committed ratchet (rc=$rc, out=$OUT)"
fi

# --- 21. --check-artifact catches a pinned file with no ratchet entry -----
# THE HOLE THIS CLOSES: enforcement defaults a missing key to
# success_baseline=0, so a pinned file absent from the ratchet is measured
# against nothing and the gate still reports PASS.
HOLE="$TMP_DIR/ratchet_hole.json"
python3 - "$RATCHET" "$HOLE" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
del d["files"]["Mathlib/Data/Subtype.lean"]
json.dump(d, open(sys.argv[2], "w", encoding="utf-8"), indent=2)
PY
set +e
OUT="$(SRCELAB_RATCHET="$HOLE" "$GATE" --check-artifact 2>&1)"
rc=$?
set -e
if [ "$rc" -eq 1 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=failed:artifact-inconsistent$' \
   && printf '%s\n' "$OUT" | grep -q 'Mathlib/Data/Subtype.lean'; then
  pass "--check-artifact: a pinned file with no ratchet entry fails closed"
else
  fail "--check-artifact missing-key detection (rc=$rc, out=$OUT)"
fi

# --- 22. --check-artifact catches an armed zero baseline ------------------
ZEROED="$TMP_DIR/ratchet_armed_zero.json"
python3 - "$RATCHET" "$ZEROED" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
d["armed"] = True
d["armed_commit"] = "deadbeef1"
d["last_updated"] = "2026-08-22"
for k in d["files"]:
    d["files"][k]["success_baseline"] = 7
d["files"]["Mathlib/Logic/Unique.lean"]["success_baseline"] = 0
json.dump(d, open(sys.argv[2], "w", encoding="utf-8"), indent=2)
PY
set +e
OUT="$(SRCELAB_RATCHET="$ZEROED" "$GATE" --check-artifact 2>&1)"
rc=$?
set -e
if [ "$rc" -eq 1 ] && printf '%s\n' "$OUT" | grep -q 'ZERO baseline'; then
  pass "--check-artifact: an armed ratchet with a zero baseline fails closed"
else
  fail "--check-artifact armed-zero detection (rc=$rc, out=$OUT)"
fi

# --- 23. a measured run with an armed, unbaselined pinned file fails closed
UNBASE="$TMP_DIR/ratchet_unbaselined.json"
python3 - "$RATCHET" "$UNBASE" "$FAKE_ML_REV" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
d["armed"] = True
d["armed_commit"] = "deadbeef1"
# Re-pin to the FAKE corpus (2026-09-15). This ratchet is derived from the
# committed one, so it inherits the real corpus pin, and the gate now refuses
# to compare counts across corpora -- without this the arm below would exercise
# corpus-mismatch instead of the --update arming path it is written for.
d["corpus"] = {"rev": sys.argv[3], "toolchain": "leanprover/lean4:v4.99.0-fake"}
for k in d["files"]:
    d["files"][k]["success_baseline"] = 1
    # The fake `clean` prints no `timing`; an inherited perf_baseline would
    # turn this arm into perf-unmeasured (see TEST_RATCHET above).
    d["files"][k].pop("perf_baseline", None)
del d["files"]["Mathlib/Data/Subtype.lean"]
json.dump(d, open(sys.argv[2], "w", encoding="utf-8"), indent=2)
PY
set +e
OUT="$(CLEAN_BIN="$FAKE_CHECK" CLEAN_MATHLIB_DIR="$FAKE_ML" SRCELAB_RATCHET="$UNBASE" \
       SRCELAB_REPORT_DIR="$TMP_DIR/reports-unbase" SRCELAB_GATE_MEM_GIB_MIN=0 "$GATE" 2>/dev/null)"
rc=$?
set -e
if [ "$rc" -eq 1 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=failed:ratchet-missing-key$'; then
  pass "measured run: armed ratchet with an unbaselined pinned file fails closed"
else
  fail "ratchet-missing-key on a measured run (rc=$rc, out=$OUT)"
fi

# --- 23b. ... but --update ARMS that file instead of deadlocking -----------
# The fail-closed rule above, applied to --update too, made adding a file to the
# pinned slice impossible without first hand-typing a placeholder baseline --
# and a hand-typed baseline is the un-evidenced number --check-artifact's
# evidence binding exists to forbid. --update must therefore arm a new pinned
# file from its measurement, loudly, and leave every other file's baseline
# subject to the same monotonic-up rule.
UNBASE_UPD="$TMP_DIR/ratchet_unbaselined_update.json"
python3 - "$UNBASE" "$UNBASE_UPD" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
json.dump(d, open(sys.argv[2], "w", encoding="utf-8"), indent=2)
PY
set +e
OUT="$(CLEAN_BIN="$FAKE_CHECK" CLEAN_MATHLIB_DIR="$FAKE_ML" SRCELAB_RATCHET="$UNBASE_UPD" \
       SRCELAB_REPORT_DIR="$TMP_DIR/reports-unbase-upd" SRCELAB_GATE_MEM_GIB_MIN=0 \
       "$GATE" --update 2>&1)"
rc=$?
set -e
if [ "$rc" -eq 0 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=measured$' \
   && printf '%s\n' "$OUT" | grep -q 'NEW PINNED FILE Mathlib/Data/Subtype.lean' \
   && python3 - "$UNBASE_UPD" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
assert d["armed"] is True, d
assert len(d["files"]) == 5, sorted(d["files"])
e = d["files"]["Mathlib/Data/Subtype.lean"]
assert e["success_baseline"] == 86, e
assert e["decl_count"] == 257, e
PY
then
  pass "--update arms a newly pinned file from its measurement (no hand-typed placeholder)"
else
  fail "--update arming a new pinned file (rc=$rc, out=$OUT)"
fi

# --- 24. baselines are bound to their committed evidence ------------------
# `--update` writes baselines from a measured run, but nothing stopped a later
# hand edit from typing a number no report ever contained. When a dated report
# for the ratchet's armed_commit is checked in beside it, every baseline must
# EQUAL that report's counts.
BOUND="$TMP_DIR/ratchet_bound.json"
python3 - "$RATCHET" "$BOUND" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
k = sorted(d["files"])[0]
d["files"][k]["success_baseline"] = d["files"][k]["success_baseline"] + 1
json.dump(d, open(sys.argv[2], "w", encoding="utf-8"), indent=2)
PY
set +e
OUT="$(SRCELAB_RATCHET="$BOUND" "$GATE" --check-artifact 2>&1)"
rc=$?
set -e
if [ "$rc" -eq 1 ] && printf '%s\n' "$OUT" | grep -q 'a baseline must equal its evidence'; then
  pass "--check-artifact: a baseline that disagrees with its armed_commit report fails closed"
else
  fail "--check-artifact evidence binding (rc=$rc, out=$OUT)"
fi

# --- 25. the committed ratchet IS bound (its armed_commit report exists) ---
if python3 - "$RATCHET" <<'PY'
import glob, json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
c = d["armed_commit"]
m = sorted(glob.glob("reports/source-elab/srcelab-*-g{}.json".format(c)))
assert m, "no committed report for armed_commit {}".format(c)
rep = json.load(open(m[-1], encoding="utf-8"))
by = {r["key"]: r for r in rep["files"]}
for key, v in d["files"].items():
    r = by[key]
    assert v["success_baseline"] == r["success_count"], (key, v, r["success_count"])
    assert v["decl_count"] == r["decl_count"], (key, v, r["decl_count"])
PY
then
  pass "committed ratchet's baselines equal its armed_commit report, key for key"
else
  fail "committed ratchet is not bound to a committed report"
fi

# --- 30-33. the audit r8/r9 provenance refusals, DEMONSTRATED ------------
# THE HOLE THESE CLOSE: r8 added a reachability refusal for `armed_commit`
# AND a sanctioned exception that bypasses it, then moved the row's
# demonstration pin in the same commit -- so a refusal and its own bypass
# shipped with no arm of any kind (audit r9 M-3). Each arm below deletes or
# corrupts exactly one condition and requires the gate to refuse.

_mk() {  # _mk <outfile> <python-body-editing-d>
  python3 - "$RATCHET" "$1" "$2" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
exec(sys.argv[3])
json.dump(d, open(sys.argv[2], "w", encoding="utf-8"), indent=2)
PY
}
_expect_refusal() {  # _expect_refusal <file> <needle> <label>
  set +e
  OUT="$(SRCELAB_RATCHET="$1" "$GATE" --check-artifact 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq 1 ] && printf '%s\n' "$OUT" | grep -q "$2"; then
    pass "$3"
  else
    fail "$3 (rc=$rc, out=$OUT)"
  fi
}

# The three arms below pin their OWN armed_commit to a sha no ref reaches,
# and mint their own exception block, so they test exactly the condition
# they name whatever the committed ratchet says. Until 2026-09-20 they read
# the committed ratchet's state instead: they passed only while
# data/source_elab_ratchet.json happened to be armed at an unrecoverable sha
# WITH an exception block, and the re-arm at the reachable 5e2e6dc0e
# (36b98378c) turned arm 30 into a pass-through and arms 31-32 into a KeyError
# -- a red no pusher caused, on a plain (unratcheted) landing leg.
_UNREACH='d["armed_commit"] = "0123456789abcdef0123456789abcdef01234567"'
_EXC='import datetime; d["armed_commit_unrecoverable_exception"] = {"armed_commit": d["armed_commit"], "owner": "selftest fixture", "expires": (datetime.date.today() + datetime.timedelta(days=30)).isoformat(), "discharge": "selftest fixture"}'

# 30. an unreachable armed_commit with NO exception refuses
_mk "$TMP_DIR/r_noexc.json" "$_UNREACH; d.pop(\"armed_commit_unrecoverable_exception\", None)"
_expect_refusal "$TMP_DIR/r_noexc.json" "resolves to no commit reachable" \
  "--check-artifact: an unreachable armed_commit with no exception fails closed"

# 31. an exception naming a DIFFERENT sha does not excuse this one
_mk "$TMP_DIR/r_wrongsha.json" "$_UNREACH; $_EXC; d[\"armed_commit_unrecoverable_exception\"][\"armed_commit\"] = \"deadbeef1\""
_expect_refusal "$TMP_DIR/r_wrongsha.json" "resolves to no commit reachable" \
  "--check-artifact: an exception naming another sha does not excuse this one"

# 32. a non-date expiry (the `2026-9-01` typo class) does not make it permanent
_mk "$TMP_DIR/r_baddate.json" "$_UNREACH; $_EXC; d[\"armed_commit_unrecoverable_exception\"][\"expires\"] = \"9999\""
_expect_refusal "$TMP_DIR/r_baddate.json" "resolves to no commit reachable" \
  "--check-artifact: a non-date expiry refuses (string compare made it permanent)"

# 33. an armed ratchet whose armed_commit RESOLVES but has NO committed report
# refuses -- this was a NOTE that PASSED, i.e. a one-token disarm of the
# evidence binding.
#
# THE FIXTURE MUST RESOLVE. The first cut used a nonexistent sha, so the
# REACHABILITY refusal fired first and the arm passed without ever exercising
# the mechanism it names -- the mutation proof caught it (deleting the
# no-report branch left the suite green). It now uses a commit that is
# genuinely reachable, so the only refusal available is the one under test,
# and the needle is unique to that branch.
_mk "$TMP_DIR/r_norep.json" 'd["armed_commit"] = "c98f195da"; d.pop("armed_commit_unrecoverable_exception", None)'
_expect_refusal "$TMP_DIR/r_norep.json" "the baselines are bound to nothing" \
  "--check-artifact: a RESOLVING armed_commit with no committed report fails closed"

# 34-35. AUDIT r15 (adjudicated non-material, taken as free hardening): `armed`
# is the MASTER SWITCH -- every check above is conditioned on it -- and
# `--check-artifact` read it without ever asserting it, so one `"armed": false`
# switched off the zero-baseline rule, the armed_commit provenance and the
# report binding while this IN_HOOK mode still printed `artifact-ok`. This suite
# asserted `armed is True` on the COMMITTED artifact, which is a different
# question and is GATE-FULL-ONLY, so the hook had no cover.
_mk "$TMP_DIR/r_disarmed.json" 'd["armed"] = False'
_expect_refusal "$TMP_DIR/r_disarmed.json" "the ratchet is DISARMED" \
  "--check-artifact: a silently disarmed ratchet refuses"

_mk "$TMP_DIR/r_disarmed_expired.json" 'd["armed"] = False; d["disarmed_because"] = {"owner": "x", "expires": "2001-01-01", "reason": "lapsed"}'
_expect_refusal "$TMP_DIR/r_disarmed_expired.json" "account EXPIRED" \
  "--check-artifact: a disarm account past its expiry refuses"

# --- 36-42. CORPUS IDENTITY (2026-09-15) ----------------------------------
# WHY THESE ARMS EXIST. This ratchet compares per-file success counts against
# armed baselines, and those counts are only comparable against the SAME
# Mathlib. Until 2026-09-15 nothing recorded which corpus a run measured: the
# report had no corpus field and the ratchet pinned none, so whichever checkout
# the discovery glob found silently became the basis. The day the glob was
# fixed to honour $HOME, the gate measured a v4.28.0 corpus against baselines
# armed on v4.30.0-rc2 and reported SRCELAB_GATE=failed:ratchet-regression --
# a cross-corpus comparison presented as a code regression.
#
# BOTH DIRECTIONS ARE PINNED. A refusal arm on its own is passed by a guard
# that refuses everything, so the matching-corpus control below must stay green
# beside the mismatch refusal.
CORPUS_RATCHET="$TMP_DIR/r_corpus.json"
_mk_corpus() {  # _mk_corpus <outfile> <python-body>
  python3 - "$TEST_RATCHET" "$1" "$2" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
exec(sys.argv[3])
json.dump(d, open(sys.argv[2], "w", encoding="utf-8"), indent=2)
PY
}

run_corpus_gate() {  # run_corpus_gate <ratchet> [args...]
  _R="$1"; shift
  CLEAN_BIN="$FAKE_CHECK" CLEAN_MATHLIB_DIR="$FAKE_ML" \
  SRCELAB_RATCHET="$_R" SRCELAB_REPORT_DIR="$TMP_DIR/reports_corpus" \
  SRCELAB_GATE_MEM_GIB_MIN=0 "$GATE" "$@"
}

# 36. CONTROL: the corpus the ratchet is pinned to still measures and enforces.
_mk_corpus "$CORPUS_RATCHET" 'd["armed"] = True; d["armed_commit"] = "deadbeef"; d["corpus"] = {"rev": sys.argv and "'"$FAKE_ML_REV"'", "toolchain": "leanprover/lean4:v4.99.0-fake"}
for v in d["files"].values(): v["success_baseline"] = 1'
set +e
OUT="$(run_corpus_gate "$CORPUS_RATCHET" 2>&1)"; rc=$?
set -e
if [ "$rc" -eq 0 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=measured$'; then
  pass "corpus identity: the PINNED corpus measures and enforces (control)"
else
  fail "corpus identity control (rc=$rc, out=$OUT)"
fi

# 37. A different corpus REV does not enforce, and does not report a regression.
#     Baselines are set ABOVE the fixture's 86 so that, if the corpus check were
#     removed, this arm would fail ratchet-regression -- which is exactly the
#     defect being pinned. The needle distinguishes the two outcomes.
_mk_corpus "$TMP_DIR/r_corpus_rev.json" 'd["armed"] = True; d["armed_commit"] = "deadbeef"; d["corpus"] = {"rev": "0123456789abcdef0123456789abcdef01234567", "toolchain": "leanprover/lean4:v4.99.0-fake"}
for v in d["files"].values(): v["success_baseline"] = 9999'
set +e
OUT="$(run_corpus_gate "$TMP_DIR/r_corpus_rev.json" 2>&1)"; rc=$?
set -e
if [ "$rc" -eq 0 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=skipped:corpus-mismatch$' \
   && printf '%s\n' "$OUT" | grep -q 'CORPUS MISMATCH' \
   && ! printf '%s\n' "$OUT" | grep -q 'REGRESSION'; then
  pass "corpus identity: a different corpus REV skips and reports NO regression"
else
  fail "corpus rev mismatch (rc=$rc, out=$OUT)"
fi

# 38. Same rev, different TOOLCHAIN is also a different corpus.
_mk_corpus "$TMP_DIR/r_corpus_tc.json" 'd["armed"] = True; d["armed_commit"] = "deadbeef"; d["corpus"] = {"rev": "'"$FAKE_ML_REV"'", "toolchain": "leanprover/lean4:v4.30.0-rc2"}
for v in d["files"].values(): v["success_baseline"] = 9999'
set +e
OUT="$(run_corpus_gate "$TMP_DIR/r_corpus_tc.json" 2>&1)"; rc=$?
set -e
if [ "$rc" -eq 0 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=skipped:corpus-mismatch$'; then
  pass "corpus identity: same rev but a different TOOLCHAIN skips"
else
  fail "corpus toolchain mismatch (rc=$rc, out=$OUT)"
fi

# 39. An armed ratchet with NO corpus pin is a DEFECT, not a deferral: it cannot
#     say what its own baselines are counts of. Red, not skip.
_mk_corpus "$TMP_DIR/r_corpus_none.json" 'd["armed"] = True; d["armed_commit"] = "deadbeef"; d.pop("corpus", None)
for v in d["files"].values(): v["success_baseline"] = 1'
set +e
OUT="$(run_corpus_gate "$TMP_DIR/r_corpus_none.json" 2>&1)"; rc=$?
set -e
if [ "$rc" -eq 1 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=failed:corpus-unpinned$'; then
  pass "corpus identity: an armed ratchet with no corpus pin FAILS closed"
else
  fail "corpus-unpinned (rc=$rc, out=$OUT)"
fi

# 40. A mismatched corpus cannot LAUNDER a baseline through --update. This is
#     the spine_scoreboard lesson (2026-09-14): a generator that can move its
#     own basis checks nothing. Without --repin-corpus, --update on a foreign
#     corpus must refuse rather than re-arm.
set +e
OUT="$(run_corpus_gate "$TMP_DIR/r_corpus_rev.json" --update 2>&1)"; rc=$?
set -e
if [ "$rc" -eq 0 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=skipped:corpus-mismatch$' \
   && python3 - "$TMP_DIR/r_corpus_rev.json" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
assert d["corpus"]["rev"] == "0123456789abcdef0123456789abcdef01234567", d["corpus"]
assert all(v["success_baseline"] == 9999 for v in d["files"].values()), d["files"]
PY
then
  pass "corpus identity: --update on a foreign corpus re-arms NOTHING"
else
  fail "corpus laundering via --update (rc=$rc, out=$OUT)"
fi

# 41. --repin-corpus IS the deliberate act: it moves the pin, re-bases the
#     baselines (monotonic-up does not carry across corpora) and RECORDS the
#     move with its reason, so the discontinuity is on the record.
set +e
OUT="$(run_corpus_gate "$TMP_DIR/r_corpus_rev.json" --update --repin-corpus "moved to the v4.28 corpus for the portability probe" 2>&1)"; rc=$?
set -e
if [ "$rc" -eq 0 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=measured$' \
   && python3 - "$TMP_DIR/r_corpus_rev.json" "$FAKE_ML_REV" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
assert d["corpus"]["rev"] == sys.argv[2], d["corpus"]
assert d["corpus"]["toolchain"] == "leanprover/lean4:v4.99.0-fake", d["corpus"]
rows = d.get("corpus_repins")
assert isinstance(rows, list) and len(rows) == 1, rows
assert rows[0]["to"]["rev"] == sys.argv[2], rows
assert "portability probe" in rows[0]["reason"], rows
# the baselines were re-derived from THIS corpus, not defended against it
assert all(v["success_baseline"] == 86 for v in d["files"].values()), d["files"]
PY
then
  pass "corpus identity: --repin-corpus moves the pin, re-bases, and records the move"
else
  fail "--repin-corpus (rc=$rc, out=$OUT)"
fi

# 42. A re-pin needs a real reason. A one-word gesture is not an account.
set +e
OUT="$(run_corpus_gate "$TMP_DIR/r_corpus_tc.json" --update --repin-corpus "oops" 2>&1)"; rc=$?
set -e
if [ "$rc" -eq 1 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=failed:repin-corpus-usage$'; then
  pass "corpus identity: --repin-corpus refuses a reason under 12 characters"
else
  fail "--repin-corpus short reason (rc=$rc, out=$OUT)"
fi

# 43. --check-artifact guards the pin between the hours-long measured runs.
_mk "$TMP_DIR/r_art_nocorpus.json" 'd.pop("corpus", None)'
_expect_refusal "$TMP_DIR/r_art_nocorpus.json" "has no .corpus. pin" \
  "--check-artifact: an armed ratchet with no corpus pin refuses"

_mk "$TMP_DIR/r_art_shortrev.json" 'd["corpus"]["rev"] = "43ad"'
_expect_refusal "$TMP_DIR/r_art_shortrev.json" "too short to identify a commit" \
  "--check-artifact: a corpus.rev too short to identify a commit refuses"

# --- 44-45. THE MONOTONIC-UP RULE ITSELF, and the narrowness of the corpus
# exemption. Found 2026-09-15 while mutation-proving the corpus work: the
# `--update would LOWER an armed baseline` refusal -- the oldest rule this
# ratchet has -- had NO arm in this suite, so the corpus rebase exemption was
# being added to a rule nothing pinned. A mutation making `corpus_rebased`
# unconditionally true survived the whole suite, which is how the hole was
# found: a vacuous arm is a finding about the proof, not a proof.
_mk_corpus "$TMP_DIR/r_lower.json" 'd["armed"] = True; d["armed_commit"] = "deadbeef"; d["corpus"] = {"rev": "'"$FAKE_ML_REV"'", "toolchain": "leanprover/lean4:v4.99.0-fake"}
for v in d["files"].values(): v["success_baseline"] = 9999'
set +e
OUT="$(run_corpus_gate "$TMP_DIR/r_lower.json" --update 2>&1)"; rc=$?
set -e
if [ "$rc" -eq 1 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=failed:ratchet-regression$' \
   && python3 - "$TMP_DIR/r_lower.json" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
assert all(v["success_baseline"] == 9999 for v in d["files"].values()), d["files"]
PY
then
  pass "monotonic-up: --update on the PINNED corpus refuses to lower a baseline"
else
  fail "monotonic-up lowering refusal (rc=$rc, out=$OUT)"
fi

# 45. The corpus exemption must not leak onto the matching-corpus path: on the
#     PINNED corpus the baselines are still defended, and no corpus_repins row
#     is minted by an ordinary --update.
_mk_corpus "$TMP_DIR/r_noleak.json" 'd["armed"] = True; d["armed_commit"] = "deadbeef"; d["corpus"] = {"rev": "'"$FAKE_ML_REV"'", "toolchain": "leanprover/lean4:v4.99.0-fake"}
for v in d["files"].values(): v["success_baseline"] = 1'
set +e
OUT="$(run_corpus_gate "$TMP_DIR/r_noleak.json" --update 2>&1)"; rc=$?
set -e
if [ "$rc" -eq 0 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=measured$' \
   && python3 - "$TMP_DIR/r_noleak.json" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
assert "corpus_repins" not in d, "an ordinary --update must mint no rebase row"
assert all(v["success_baseline"] == 86 for v in d["files"].values()), d["files"]
PY
then
  pass "monotonic-up: an ordinary --update raises baselines and records NO rebase"
else
  fail "ordinary --update on the pinned corpus (rc=$rc, out=$OUT)"
fi

# --- 46. THE PRE-FLIGHT IS A SEPARATE TOOTH FROM THE VERDICT, and needs its
# own arm to be provable. The finalize check renders the same
# skipped:corpus-mismatch, so an arm that reads only the verdict cannot tell
# whether the refusal happened BEFORE the measurement or after it -- a mutation
# disabling the pre-flight survives such an arm untouched (measured: it did).
# What separates them is observable: the pre-flight refuses before any
# `clean check` is spawned, so it writes NO dated report and prints no per-file
# checking line. On the real corpus that difference is 32m44s of measurement and
# a heavy_gate reservation held for all of it.
# Its OWN ratchet, freshly minted: r_corpus_rev.json was RE-PINNED to this
# corpus by the --repin-corpus arm above, so reusing it here would silently
# test a corpus that now MATCHES -- the arm would pass while measuring nothing.
# (Measured: it did exactly that on the first run of this arm.)
_mk_corpus "$TMP_DIR/r_preflight.json" 'd["armed"] = True; d["armed_commit"] = "deadbeef"; d["corpus"] = {"rev": "fedcba9876543210fedcba9876543210fedcba98", "toolchain": "leanprover/lean4:v4.99.0-fake"}
for v in d["files"].values(): v["success_baseline"] = 9999'
rm -rf "$TMP_DIR/reports_preflight"
set +e
OUT="$(CLEAN_BIN="$FAKE_CHECK" CLEAN_MATHLIB_DIR="$FAKE_ML" \
       SRCELAB_RATCHET="$TMP_DIR/r_preflight.json" \
       SRCELAB_REPORT_DIR="$TMP_DIR/reports_preflight" \
       SRCELAB_GATE_MEM_GIB_MIN=0 "$GATE" 2>&1)"; rc=$?
set -e
# Counted with a glob, not `ls | wc -l`: this suite runs under `set -euo
# pipefail`, and when the pre-flight does its job there is NO report, so `ls`
# exits nonzero and pipefail aborts the whole suite -- the arm killed the run
# precisely WHEN THE MECHANISM WORKED, and the control read as an early exit
# with zero FAILs. Same pipe trap this repo records elsewhere, one layer up.
NREP=0
for _f in "$TMP_DIR/reports_preflight"/srcelab-*.json; do
  if [ -e "$_f" ]; then NREP=$((NREP + 1)); fi
done
if [ "$rc" -eq 0 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=skipped:corpus-mismatch$' \
   && printf '%s\n' "$OUT" | grep -q 'pre-flight' \
   && [ "$NREP" = "0" ] \
   && ! printf '%s\n' "$OUT" | grep -q 'checking Mathlib/Logic/Basic.lean'; then
  pass "corpus identity: the mismatch is refused BEFORE the measurement is spent"
else
  fail "corpus pre-flight fail-fast (rc=$rc, reports=$NREP, out=$OUT)"
fi

# --- per-declaration guard + performance leg (2026-09-24) ------------------
# Their modules' own self-tests, then the teeth end to end through the GATE
# (scripts/srcelab_guard_demo.sh -- the same script the registry arms drive):
# a newly failing named row with the count held, the ledger admitting only its
# own row, a tripled import phase, an armed metric left unmeasured, and the
# committed 4020124a1-vs-0093eeb47 replay naming dite_dite_comm.
for _mod in srcelab_decl_guard srcelab_perf; do
  set +e
  OUT="$(python3 "$REPO_ROOT/scripts/$_mod.py" --selftest 2>&1)"; rc=$?
  set -e
  if [ "$rc" -eq 0 ]; then
    pass "$_mod.py self-test"
  else
    fail "$_mod.py self-test (rc=$rc, out=$OUT)"
  fi
done
set +e
OUT="$(bash "$REPO_ROOT/scripts/srcelab_guard_demo.sh" 2>&1)"; rc=$?
set -e
if [ "$rc" -eq 0 ] && printf '%s\n' "$OUT" | grep -q '^SRCELAB_GUARD_DEMO=ok$'; then
  pass "per-declaration guard and performance leg: every tooth holds through the gate"
else
  fail "srcelab_guard_demo.sh (rc=$rc, out=$OUT)"
fi

SUITE_DONE=1
echo
echo "source_elab_gate tests: $PASS passed, $FAIL failed"
[ "$FAIL" -eq 0 ]
