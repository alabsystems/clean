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
if python3 - "$RATCHET" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
assert d["schema_version"] == "Clean-srcelab-ratchet-v1", d.get("schema_version")
assert d["armed"] is False, "initial ratchet must be UNARMED"
assert d["counting_basis"] == "allow_sorry_success", d.get("counting_basis")
files = d["files"]
assert len(files) == 4, sorted(files)
assert all(v.get("success_baseline") == 0 for v in files.values()), files
assert files["Mathlib/Logic/Unique.lean:1-240"]["cap_lines"] == 240
assert "sorry" in d["notes"], "notes must state the counting-basis caveat"
PY
then
  pass "ratchet artifact: unarmed, all-zero baselines, 4 pinned keys, cap noted"
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
# A fake Mathlib tree (all four pinned files present, .lake/build marker dir)
# and a fake `clean` that always prints the fixture CheckReport and exits 1
# (the real check's exit contract when failed_count > 0). All artifact paths
# are redirected via the test/plumbing env overrides, so the committed
# data/ ratchet and reports/ tree stay untouched.
FAKE_ML="$TMP_DIR/mathlib"
mkdir -p "$FAKE_ML/.lake/build/lib/lean" \
         "$FAKE_ML/Mathlib/Logic/Function" "$FAKE_ML/Mathlib/Data"
for f in "Mathlib/Logic/Basic.lean" "Mathlib/Logic/Function/Basic.lean" \
         "Mathlib/Data/Subtype.lean" "Mathlib/Logic/Unique.lean"; do
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
TEST_RATCHET="$TMP_DIR/ratchet.json"
cp "$RATCHET" "$TEST_RATCHET"
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
assert len(d["files"]) == 4, [r["key"] for r in d["files"]]
assert d["totals"]["success_count"] == 4 * 86, d["totals"]
assert d["totals"]["sorry_axioms"] == 4 * 4, d["totals"]
assert d["counting_basis"] == "allow_sorry_success", d
assert d["ratchet"]["enforced"] is False, "unarmed ratchet must report enforced=false"
caps = {r["key"]: r["cap_lines"] for r in d["files"]}
assert caps["Mathlib/Logic/Unique.lean:1-240"] == 240, caps
PY
then
  pass "measured path: verdict=measured, dated report with totals + cap metadata"
else
  fail "measured path (rc=$rc, report=$REPORT_FILE, out=$OUT)"
fi
if [ ! -e "$FAKE_ML/Mathlib/Logic/Unique_srcelab_cap240_tmp.lean" ]; then
  pass "measured path removes the Unique line-cap temp copy from the corpus tree"
else
  fail "Unique cap temp copy left behind in the corpus tree"
fi

# --- 12. --update arms the ratchet with measured baselines ----------------
set +e
OUT="$(run_gate_e2e --update 2>/dev/null)"
rc=$?
set -e
if [ "$rc" -eq 0 ] && python3 - "$TEST_RATCHET" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
assert d["armed"] is True, d
assert len(d["files"]) == 4, sorted(d["files"])
assert all(v["success_baseline"] == 86 for v in d["files"].values()), d["files"]
assert d["files"]["Mathlib/Logic/Unique.lean:1-240"]["cap_lines"] == 240
assert "armed_commit" in d, sorted(d)
PY
then
  pass "--update arms the ratchet with measured per-file baselines"
else
  fail "--update arming (rc=$rc, out=$OUT)"
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

echo
echo "source_elab_gate tests: $PASS passed, $FAIL failed"
[ "$FAIL" -eq 0 ]
