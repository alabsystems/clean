#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# srcelab_guard_demo.sh — the PER-DECLARATION and PERFORMANCE teeth of
# scripts/source_elab_gate.sh, asserted directly against the gate in seconds.
#
# Same shape and same reason as scripts/srcelab_corpus_demo.sh: a registry arm
# that runs the whole 58-case suite per mutation cannot finish, so each arm in
# data/gate_demonstrations.json drives the GATE through this script — a fake
# corpus, a fake `clean` whose report the scenario picks, one gate invocation
# per property — and keys on the one message below that names the property it
# broke. Every property is asserted POSITIVELY; the script exits non-zero naming
# each one that no longer holds. Run it bare to check all of them.
#
# What it pins, and why each is a separate tooth:
#   control   an unchanged run measures and passes (without it, a guard that
#             refuses EVERYTHING would pass every arm below);
#   1         a declaration that passed in the armed_commit report and fails
#             now fails the gate although every per-file COUNT holds -- the
#             4020124a1 shape, where Logic/Basic went 221 -> 224 while
#             `dite_dite_comm` broke and the count-only gate said PASS;
#   2         the same row, listed in `decl_regression_ledger` with an owner and
#             an unexpired date, is admitted -- and only that row;
#   3         a tripled import phase (the per-module `env.clone()` shape that
#             took the Subtype import floor from ~175 s to ~290 s unnoticed) fails
#             the gate against the armed perf_baseline;
#   4         an armed metric the run could not measure (a binary whose report
#             has no `timing` block) fails closed, never rounds up to a pass;
#   5         the committed evidence replays: re-running the 4020124a1 arming
#             against the 0093eeb47 report fails and names dite_dite_comm;
#   6         an `--update` arming writes perf_baseline from its own
#             measurement, so the leg does not stay unarmed after one.
set -uo pipefail
# A fake corpus is `git init`ed and committed below. Inherited from a git hook
# or a lane committing over a temporary index, GIT_DIR / GIT_INDEX_FILE would
# point those calls at the REAL repository.
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_COMMON_DIR GIT_OBJECT_DIRECTORY

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
GATE="$ROOT/scripts/source_elab_gate.sh"
RATCHET="$ROOT/data/source_elab_ratchet.json"
TMP="$(mktemp -d -t srcelab_guard_demo.XXXXXX)"
trap 'rm -rf "$TMP"' EXIT
FAILED=0
note() { printf '  %s\n' "$1"; }
broke() { printf 'SRCELAB-GUARD-DEMO BROKEN: %s\n' "$1" >&2; FAILED=1; }

KEYS="Mathlib/Logic/Basic.lean Mathlib/Logic/Function/Basic.lean Mathlib/Data/Subtype.lean Mathlib/Logic/Unique.lean Mathlib/Order/Basic.lean"

# ---- a fake Mathlib corpus with an identity (rev + lean-toolchain) --------
ML="$TMP/mathlib"
mkdir -p "$ML/.lake/build/lib/lean" "$ML/Mathlib/Logic/Function" "$ML/Mathlib/Data" "$ML/Mathlib/Order"
for f in $KEYS; do printf -- '-- fake pinned source (%s)\n' "$f" > "$ML/$f"; done
printf 'leanprover/lean4:v4.99.0-fake\n' > "$ML/lean-toolchain"
(
  cd "$ML" && git init -q . && git add -A \
    && git -c user.email=demo@example.invalid -c user.name="srcelab guard demo" \
           -c commit.gpgsign=false commit -q -m "fake corpus"
) >/dev/null 2>&1
REV="$(git -C "$ML" rev-parse HEAD 2>/dev/null || true)"
[ -n "$REV" ] || { echo "FATAL: fake corpus has no git rev" >&2; exit 2; }

# ---- a fake `clean`: $FAKE_SCENARIO picks the report ----------------------
BIN="$TMP/fake_clean"
cat > "$BIN" <<'SH'
#!/bin/sh
ROW='a: elaboration error at line 3: boom'
IMPORT=100.0
TIMING=1
case "${FAKE_SCENARIO:-base}" in
  decl) ROW='b: elaboration error at line 7: boom' ;;
  perf) IMPORT=300.0 ;;
  notiming) TIMING=0 ;;
esac
printf '{"schema_version":"Clean-check-report-v1","command":"clean check","file":"f",'
printf '"module":"f","status":"fail","decl_count":3,"success_count":2,"failed_count":1,'
printf '"diverged_count":0,"trust_summary":{"sorry_axioms":0,"kernel_check_failures":0},'
printf '"errors":["%s"],"trust_failures":[],"kernel_failures":[],"proof_state_feedback":[]' "$ROW"
if [ "$TIMING" = 1 ]; then
  printf ',"timing":{"total_s":111.0,"setup_s":0.5,"parse_s":0.1,"import_s":%s,"elab_s":10.0,' "$IMPORT"
  printf '"per_declaration":[{"name":"a","line":3,"elapsed_ms":9000.0}]}'
fi
printf '}\n'
exit 1
SH
chmod +x "$BIN"

# ---- an ARMED ratchet on that corpus, and its armed_commit report ---------
mkratchet() {  # mkratchet <out> [ledger-json]
  python3 - "$RATCHET" "$1" "$REV" "${2:-}" "$KEYS" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
d["armed"] = True
d["armed_commit"] = "deadbeef"
d["corpus"] = {"rev": sys.argv[3], "toolchain": "leanprover/lean4:v4.99.0-fake"}
d["files"] = {k: {"success_baseline": 2, "decl_count": 3, "sorry_axioms": 0,
                  "perf_baseline": {"import_s": 100.0, "elab_s": 10.0, "max_rss_bytes": 50000000}}
              for k in sys.argv[5].split()}
d.pop("decl_regression_ledger", None)
if sys.argv[4]:
    d["decl_regression_ledger"] = json.loads(sys.argv[4])
json.dump(d, open(sys.argv[2], "w", encoding="utf-8"), indent=2)
PY
}

run() {  # run <ratchet> <reportdir> <scenario> [args...]; echoes the gate's output
  local r="$1" rd="$2" sc="$3"; shift 3
  rm -rf "$rd"
  mkdir -p "$rd"
  python3 - "$rd/srcelab-2026-01-01-gdeadbeef.json" "$KEYS" <<'PY'
import json, sys
files = [{"key": k, "path": k, "success_count": 2, "decl_count": 3, "diverged_count": 0,
          "per_error_class": [{"decl": "a", "class": "other",
                               "error": "a: elaboration error at line 3: boom"}]}
         for k in sys.argv[2].split()]
json.dump({"schema_version": "Clean-srcelab-report-v1", "files": files}, open(sys.argv[1], "w"))
PY
  FAKE_SCENARIO="$sc" CLEAN_BIN="$BIN" CLEAN_MATHLIB_DIR="$ML" SRCELAB_RATCHET="$r" \
  SRCELAB_REPORT_DIR="$rd" SRCELAB_GATE_MEM_GIB_MIN=0 \
  "$GATE" --jobs 5 "$@" 2>&1
}

has() { printf '%s\n' "$1" | grep -q -- "$2"; }

mkratchet "$TMP/r.json"

# ---- CONTROL ---------------------------------------------------------------
OUT="$(run "$TMP/r.json" "$TMP/rep_control" base)"
if has "$OUT" '^SRCELAB_GATE=measured$'; then
  note "control: an unchanged run measures, and the guard and the perf leg both pass it"
else
  broke "the control does not measure -- every arm below is vacuous: $(printf '%s' "$OUT" | tail -3)"
fi
# The report says how many checks ran at once: import_s / elab_s are wall times
# of concurrent processes, so a perf number without its --jobs is not
# comparable to one with a different --jobs.
JOBS_REC="$(python3 - "$TMP/rep_control" <<'PY'
import glob, json, sys
reps = [p for p in glob.glob(sys.argv[1] + "/srcelab-*.json") if not p.endswith("-gdeadbeef.json")]
print(json.load(open(reps[0], encoding="utf-8")).get("jobs") if len(reps) == 1 else "none")
PY
)"
if [ "$JOBS_REC" = 5 ]; then
  note "control: the dated report records --jobs 5 beside its timings"
else
  broke "the dated report does not record the --jobs its timings were measured at (got $JOBS_REC)"
fi

# ---- 1. a newly failing named row fails although the counts hold ----------
OUT="$(run "$TMP/r.json" "$TMP/rep_decl" decl)"
if has "$OUT" '^SRCELAB_GATE=failed:decl-regression$' && has "$OUT" 'NEW-FAIL Mathlib/Logic/Basic.lean :: b'; then
  note "1. a declaration that newly fails is refused by name while every count holds"
else
  broke "a newly failing declaration did not fail the gate while its file's count held"
fi

# ---- 2. the ledger admits exactly its own row -----------------------------
EXP="$(python3 -c 'import datetime;print((datetime.date.today()+datetime.timedelta(days=30)).isoformat())')"
LED="$(python3 - "$KEYS" "$EXP" <<'PY'
import json, sys
print(json.dumps([{"file": k, "decl": "b", "owner": "guard demo", "reason": "demonstration row",
                   "expires": sys.argv[2]} for k in sys.argv[1].split()]))
PY
)"
mkratchet "$TMP/r_led.json" "$LED"
OUT="$(run "$TMP/r_led.json" "$TMP/rep_led" decl)"
if has "$OUT" '^SRCELAB_GATE=measured$' && has "$OUT" 'LEDGERED Mathlib/Logic/Basic.lean :: b'; then
  note "2. a ledgered row (owner, unexpired date) is admitted and reported as LEDGERED"
else
  broke "the decl_regression_ledger did not admit its own dated, owned row"
fi

# ---- 3. a tripled import phase fails against the armed baseline -----------
OUT="$(run "$TMP/r.json" "$TMP/rep_perf" perf)"
if has "$OUT" '^SRCELAB_GATE=failed:perf-regression$' && has "$OUT" 'PERF-REGRESSION Mathlib/Logic/Basic.lean import_s'; then
  note "3. a tripled import_s fails the gate against perf_baseline"
else
  broke "a tripled import phase did not fail the gate against its armed perf_baseline"
fi

# ---- 4. an armed metric that was not measured fails closed ----------------
OUT="$(run "$TMP/r.json" "$TMP/rep_nt" notiming)"
if has "$OUT" '^SRCELAB_GATE=failed:perf-unmeasured$'; then
  note "4. an armed metric the run could not read fails closed"
else
  broke "an armed metric this run could not measure did not fail closed"
fi

# ---- 5. the committed 4020124a1 arming replays red, naming dite_dite_comm --
BASE="$ROOT/reports/source-elab/srcelab-2026-09-21-g0093eeb47.json"
MEAS="$ROOT/reports/source-elab/srcelab-2026-09-21-g4020124a1.json"
if [ -f "$BASE" ] && [ -f "$MEAS" ]; then
  OUT="$("$GATE" --decl-diff "$BASE" "$MEAS" 2>&1)"
  if has "$OUT" '^SRCELAB_GATE=failed:decl-regression$' && has "$OUT" 'NEW-FAIL Mathlib/Logic/Basic.lean :: dite_dite_comm'; then
    note "5. re-running the 4020124a1 arming against the 0093eeb47 report fails and names dite_dite_comm"
  else
    broke "the 4020124a1 replay against 0093eeb47 did not fail naming dite_dite_comm"
  fi
else
  broke "the committed 0093eeb47 / 4020124a1 reports are missing, so the replay cannot run"
fi

# ---- 6. an arming writes perf_baseline from its own measurement -----------
# The leg enforces nothing until an `--update` arms it, so the arming path is a
# tooth too: a ratchet with NO perf_baseline, armed by a run whose report reads
# import_s 100.0 / elab_s 10.0, must come out with exactly those baselines on
# every pinned file (and a max_rss_bytes wherever time(1) could read one).
python3 - "$TMP/r.json" "$TMP/r_arm.json" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
for v in d["files"].values():
    v.pop("perf_baseline", None)
json.dump(d, open(sys.argv[2], "w", encoding="utf-8"), indent=2)
PY
OUT="$(run "$TMP/r_arm.json" "$TMP/rep_arm" base --update)"
ARMED_OK="$(python3 - "$TMP/r_arm.json" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
pb = [v.get("perf_baseline") or {} for v in d["files"].values()]
print("yes" if len(pb) == 5 and all(p.get("import_s") == 100.0 and p.get("elab_s") == 10.0
                                     for p in pb) else "no")
PY
)"
if has "$OUT" '^SRCELAB_GATE=measured$' && [ "$ARMED_OK" = yes ]; then
  note "6. an --update arming writes perf_baseline from its own measurement on every pinned file"
else
  broke "an --update arming did not write perf_baseline from its measurement"
fi

if [ "$FAILED" -ne 0 ]; then
  echo "SRCELAB_GUARD_DEMO=broken"
  exit 1
fi
echo "SRCELAB_GUARD_DEMO=ok"
