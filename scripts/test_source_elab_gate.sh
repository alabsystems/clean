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
trap 'rm -rf "$TMP_DIR"' EXIT

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
# `scripts/` dir with srcelab_classify.py beside it.
CAPROOT="$TMP_DIR/gatecopy"
mkdir -p "$CAPROOT/scripts"
cp "$REPO_ROOT/scripts/srcelab_classify.py" "$CAPROOT/scripts/"
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
drop = {"wall_seconds"}  # the only field parallelism is allowed to move
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
python3 - "$RATCHET" "$UNBASE" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
d["armed"] = True
d["armed_commit"] = "deadbeef1"
for k in d["files"]:
    d["files"][k]["success_baseline"] = 1
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

echo
echo "source_elab_gate tests: $PASS passed, $FAIL failed"
[ "$FAIL" -eq 0 ]
