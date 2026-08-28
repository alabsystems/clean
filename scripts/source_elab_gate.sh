#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Mathlib SOURCE-elaboration gate (SRCELAB).
#
# RE-MEASURES the five pinned Mathlib source files through Clean's own
# parser -> elaborator -> kernel (`clean check --imports-prefer-olean
# --allow-sorry --json`) and enforces, against the committed baseline in
# data/source_elab_ratchet.json, that per-file success counts never drop.
# This is the gate-owned successor to the HISTORICAL July-14 numbers in
# docs/plans/SOURCE_ELAB_IMPORTS_2026-07-13.md (Logic/Basic 86/257 etc.),
# which must never be quoted as current status.
#
# Pinned slice (fixed, deterministic, memory-bounded):
#   Mathlib/Logic/Basic.lean
#   Mathlib/Logic/Function/Basic.lean
#   Mathlib/Data/Subtype.lean
#   Mathlib/Logic/Unique.lean          — UNCAPPED since 2026-08-23; see below
#   Mathlib/Order/Basic.lean           — added 2026-08-23; see below
#
# ## Mathlib/Logic/Unique.lean: the line-240 cap is RETIRED (2026-08-23)
#
# It was pinned as `Mathlib/Logic/Unique.lean:1-240` because
# docs/plans/SOURCE_ELAB_IMPORTS_2026-07-13.md recorded the final section
# (lines 241-270: Unique.subtypeEq/subtypeEq' + Fin.instUnique) OOMing at
# ~19.5 GB, bisected there and attributed to a `congr`/`subst` blowup on the
# newly-defined `Unique` class. That OOM NO LONGER REPRODUCES. Measured at this
# commit with a 1 Hz RSS sampler and a hard 20 GiB kill cap:
#
#   full file (270 lines)   peak RSS 3.13 GiB   ran to completion, never capped
#   control  (239 lines)    peak RSS 3.04 GiB   ran to completion, never capped
#
# i.e. the tail the July note blamed costs +0.09 GiB, and the WHOLE FILE needs
# 6.2x less than the 19.5 GB that note recorded for the tail alone. (Peak RSS is
# the claim; wall is not — these ran against a loaded box and the full file
# clocked FASTER than its own prefix, which is contention, not work. An earlier
# same-day pair on a second binary agrees to 0.03 GiB.) The cause is
# visible in the tail's own diagnostics: `Unique.subtypeEq` and
# `subtypeEq'` now FAIL FAST inside `congr` ("goal mismatch: congr: functions
# on both sides must be equal" / "type check failed: TypeMismatch"), so the
# tactic refuses the goal instead of searching it. A cap that buys 0.07 GiB and
# costs SIX declarations of measured frontier (decl_count 35 capped -> 41
# uncapped, success unchanged at 8, so the retired key's baseline is preserved
# exactly while six more declarations are now measured) is not worth keeping,
# so the whole file is pinned.
#
# The cap was also cutting in the wrong place: line 240 is
# `attribute [local simp] eq_iff_true_of_subsingleton in`, whose `in` binds the
# declaration on line 241, so `head -n 240` produced a syntactically INCOMPLETE
# file and the old 8/35 was measured against that artefact. Evidence, with both
# RSS traces and the tail diagnostics:
# reports/source-elab/unique-oom-retraction-2026-08-23.json.
#
# The `head -n <cap>` machinery below stays (it is generic, and test 11b of
# scripts/test_source_elab_gate.sh drives it against a throwaway gate copy so
# retiring this cap did not delete its coverage), it simply has no user today.
#
# ## Mathlib/Order/Basic.lean: why THIS fifth file (2026-08-23)
#
# The other four are all Logic/Data foundations, chosen before the elaborator
# got fast. The fifth was picked on MEASURED class coverage, not on reading:
# both it and Mathlib/Algebra/Group/Defs.lean were checked end-to-end first
# (same invocation), and Order/Basic won on three counts.
#
#  1. It exercises a failure class the pinned four DO NOT. Over-application
#     against a `Sort` head ("Too many arguments: function type Sort(Param ..)
#     is not a function type") occurs 0 times in the four pinned files -- all
#     9 of their "Too many arguments" errors have an FVar/App head -- and 17
#     times here (62 in Group/Defs). That is the class-hierarchy frontier the
#     Logic/Data slice never touches.
#  2. It populates all ten classes at once, from order-theoretic sources: its
#     25 `instance synthesis` failures are order-class instances (heads LE 8,
#     LT 7, SDiff 3, Max 1, 6 unresolved), structurally different from the 28
#     that Function/Basic contributes.
#  3. It protects real ground: 58/212 succeed, and NONE of its 20 `unknown
#     identifier` failures is a cascade marker. Group/Defs measures 15/265 and
#     25 of its 48 `unknown identifier` failures are "attribute target ... not
#     found in environment", i.e. downstream of one early wall rather than
#     independent frontier, so it re-measures one wall where Order/Basic maps
#     five. Group/Defs is recorded as the recommended SIXTH file, measured and
#     ready, in the ratchet notes — not as a rejected one.
#
# ## Counting basis (honesty note)
#
# The check report (Clean-check-report-v1, crates/clean-cli/src/cmd_core.rs)
# has NO per-decl sorry-taint field: under --allow-sorry a sorry-tainted decl
# is folded into success_count, and sorry taint is only visible as the
# run-wide trust_summary.sorry_axioms counter. So the number this gate
# ratchets is counting_basis=allow_sorry_success ("elaborated AND
# kernel-registered, sorry ALLOWED"), matching the historical measurements;
# each per-file sorry_axioms counter is recorded alongside as taint evidence.
# A strict sorry-free per-decl basis needs a companion run WITHOUT
# --allow-sorry (sorry decls then surface individually in trust_failures) —
# tracked as a follow-up in the ratchet notes.
#
# ## The verdict line (why a green exit code is not evidence)
#
# Mirrors scripts/kv_ratchet_gate.sh: SKIP-green (exit 0) when the binary or
# the corpus is absent, so clones without Mathlib still pass, which means
# `exit 0` alone cannot distinguish a measurement from a deferral. Every run
# emits exactly one machine-readable verdict line on stdout:
#
#     SRCELAB_GATE=measured             the five files were actually re-checked
#     SRCELAB_GATE=skipped:<reason>     nothing was measured; <reason> says why
#     SRCELAB_GATE=failed:<reason>      a real regression / defect (exit 1)
#     SRCELAB_GATE=artifact-ok          --check-artifact only: the ratchet
#                                       artifact agrees with the pinned slice
#
# Set SRCELAB_GATE_VERDICT_FILE=<path> to also write that line to a file.
# Set SRCELAB_GATE_REQUIRE_MEASURED=1 to make every skip a FAILURE instead
# (mandatory for any run whose result will be published).
#
# ## Usage
#
#   scripts/source_elab_gate.sh              measure + enforce; writes a dated
#                                            report under reports/source-elab/
#                                            and touches NOTHING in data/
#   scripts/source_elab_gate.sh --update     additionally (re-)arm the ratchet:
#                                            write measured per-file baselines
#                                            into data/source_elab_ratchet.json
#                                            (monotonic-up; a regression still
#                                            fails first). This is also the ONLY
#                                            way to ADD a pinned file: a run
#                                            without --update fails closed on an
#                                            armed ratchet that has no entry for
#                                            a pinned file, while --update arms
#                                            that file from its measurement.
#   scripts/source_elab_gate.sh --jobs N      measure the N pinned files
#                                            CONCURRENTLY (default 1 = the
#                                            historical serial behaviour). Each
#                                            file is still its own `clean check`
#                                            process with the identical
#                                            invocation, so the measurement is
#                                            unchanged; only the scheduling is.
#                                            At --jobs 1 the five files take the
#                                            SUM of their wall times (measured
#                                            2026-08-22: Logic/Basic alone is
#                                            3 h 17 min), which is why the first
#                                            arming never happened in one
#                                            sitting. Raise it only with the
#                                            memory budget in hand: each process
#                                            holds a full olean closure.
#   scripts/source_elab_gate.sh --check-artifact
#                                            CHEAP (~50 ms, no binary, no
#                                            corpus, no measurement): assert
#                                            data/source_elab_ratchet.json still
#                                            agrees with the pinned slice below
#                                            — every pinned file has an entry
#                                            (a missing one silently enforces a
#                                            baseline of ZERO), no armed entry
#                                            is 0, caps match, armed implies
#                                            provenance. Verdict artifact-ok.
#                                            This is the leg that belongs in
#                                            scripts/local_gate.sh; the
#                                            measurement above is a suite row.
#   scripts/source_elab_gate.sh --parse-report <file>
#                                            plumbing/test mode: extract the
#                                            Clean-check-report-v1 JSON from a
#                                            captured stdout file and print the
#                                            parsed counters (no verdict line;
#                                            exit 2 = no JSON, 3 = wrong schema)
#
# ## Environment
#
#   CLEAN_BIN            override the binary; default target/release/clean
#                        ONLY (never cargo, never a stale PATH binary)
#   CLEAN_MATHLIB_DIR    Mathlib checkout root (authoritative when set — an
#                        invalid value SKIPS, it does not fall back). Default
#                        candidates, in order: data/raw/mathlib4 (the KV-gate
#                        corpus convention), then the glob $HOME/mathlib4-*
#                        — first candidate with .lake/build/lib/lean wins.
#   SRCELAB_RATCHET      test/plumbing override for the ratchet artifact path
#                        (default data/source_elab_ratchet.json)
#   SRCELAB_REPORT_DIR   test/plumbing override for the report directory
#                        (default reports/source-elab)
#   SRCELAB_GATE_MEM_GIB_MIN  free-RAM admission floor in GiB (default 8;
#                        0 disables — used by the deterministic test suite)
#   SRCELAB_GATE_JOBS    default for --jobs (default 1)
#   SRCELAB_KEEP_DIR     if set, every pinned file's UNTRUNCATED `clean check`
#                        stdout/stderr is copied there (<key-slug>.stdout /
#                        .stderr) before the temp dir is removed. The dated
#                        report only carries 400-char-truncated error text, so
#                        this is how a run keeps auditable originals.
#
# bash-3.2 safe.
set -uo pipefail
cd "$(cd "$(dirname "$0")/.." && pwd)" || exit 1

RATCHET="${SRCELAB_RATCHET:-data/source_elab_ratchet.json}"
REPORT_DIR="${SRCELAB_REPORT_DIR:-reports/source-elab}"
INVOCATION="check --imports-prefer-olean --allow-sorry --json"

REQUIRE_MEASURED="${SRCELAB_GATE_REQUIRE_MEASURED:-0}"
case "$REQUIRE_MEASURED" in 1|true|TRUE|yes|YES) REQUIRE_MEASURED=1;; *) REQUIRE_MEASURED=0;; esac

# verdict <line>: emit the single machine-readable result line (stdout, and the
# optional SRCELAB_GATE_VERDICT_FILE). Called exactly once per gate run, on
# every path. (--parse-report plumbing mode emits no verdict by design.)
verdict() {
  echo "SRCELAB_GATE=$1"
  [ -n "${SRCELAB_GATE_VERDICT_FILE:-}" ] && printf 'SRCELAB_GATE=%s\n' "$1" > "$SRCELAB_GATE_VERDICT_FILE"
  return 0
}

# skip <reason-slug> <human text>: nothing was measured. Green by default;
# RED under SRCELAB_GATE_REQUIRE_MEASURED.
skip() {
  if [ "$REQUIRE_MEASURED" = 1 ]; then
    echo "SRCELAB gate: FAIL — SRCELAB_GATE_REQUIRE_MEASURED is set but nothing was measured: $2." >&2
    verdict "skipped:$1"
    exit 1
  fi
  echo "SKIP: SRCELAB gate — $2."
  verdict "skipped:$1"
  exit 0
}

fail() { echo "SRCELAB gate: FAIL — $2" >&2; verdict "failed:$1"; exit 1; }

# errored <reason-slug> <human text>: the measurement could not be COMPLETED --
# distinct from `failed` (a real regression) and from `skip` (nothing was
# attempted). Exit 4, so a consumer can tell "we do not know" from "it broke".
#
# WHY THIS EXISTS. Before the per-file budget below, a runaway `clean check`
# wedged this gate FOREVER: the run loop backgrounded each check and `wait`ed
# with no deadline, so the suite row could never go GREEN and could never go
# RED -- it simply never answered. Measured 2026-08-23 (lane TYPEMM): one
# Logic/Basic check burned 10h37m wall / 9.95 CPU-hours at ~94% CPU and never
# finished, against that file's own recorded 13,932 s baseline, while nine lanes
# queued behind it. That lane declined to land its fix rather than risk wedging
# this row for everyone -- which is the correct call and the reason this verdict
# now exists.
#
# It must NOT be reported as 0 successes: a timed-out file with success_count 0
# reads as a catastrophic ratchet regression, i.e. a FALSE soundness-shaped
# alarm. Absence of a measurement is not a measurement of absence.
errored() { echo "SRCELAB gate: ERROR — $2" >&2; verdict "errored:$1"; exit 4; }

# The pinned slice, in one place: `key|relative path|line cap`. Both the
# measurement pre-flight and `--check-artifact` read it, so a file added here
# cannot drift away from data/source_elab_ratchet.json unnoticed.
pinned_plan() {
  cat <<'PINNEDSLICE'
Mathlib/Logic/Basic.lean|Mathlib/Logic/Basic.lean|
Mathlib/Logic/Function/Basic.lean|Mathlib/Logic/Function/Basic.lean|
Mathlib/Data/Subtype.lean|Mathlib/Data/Subtype.lean|
Mathlib/Logic/Unique.lean|Mathlib/Logic/Unique.lean|
Mathlib/Order/Basic.lean|Mathlib/Order/Basic.lean|
PINNEDSLICE
}

# srcelab_parse <captured-stdout-file>: extract the trailing pretty-printed
# Clean-check-report-v1 object (defensive against any leading non-JSON lines)
# and print the counters this gate consumes as a single JSON line.
# Exit 2 = no JSON object found; 3 = JSON present but not Clean-check-report-v1.
srcelab_parse() {
  python3 - "$1" <<'PY'
import json
import sys

data = open(sys.argv[1], encoding="utf-8", errors="replace").read()
i = data.find("{")
if i < 0:
    sys.exit(2)
try:
    obj, _ = json.JSONDecoder().raw_decode(data[i:])
except ValueError:
    sys.exit(2)
if obj.get("schema_version") != "Clean-check-report-v1":
    sys.exit(3)
ts = obj.get("trust_summary") or {}
print(json.dumps({
    "decl_count": obj.get("decl_count", 0),
    "success_count": obj.get("success_count", 0),
    "failed_count": obj.get("failed_count", 0),
    "sorry_axioms": ts.get("sorry_axioms", 0),
    "kernel_check_failures": ts.get("kernel_check_failures", 0),
    "status": obj.get("status", "unknown"),
}))
PY
}

UPDATE=0
PARSE_REPORT=""
CHECK_ARTIFACT=0
JOBS="${SRCELAB_GATE_JOBS:-1}"
# Per-file wall budget, seconds. 0 disables (the pre-2026-08-24 behaviour, which
# could wedge the row forever -- see errored()).
#
# THE NUMBER: the four pinned files' own recorded walls are Logic/Basic 13,932 s,
# Logic/Function/Basic 11,467 s, Data/Subtype 1,969 s, Logic/Unique:1-240 570 s.
# 36,000 s is ~2.6x the slowest of them. The box routinely runs 4-9 concurrent
# lanes and this gate is deliberately deferral-safe rather than fast, so a tight
# multiple would false-positive on load; 2.6x is loose enough to survive that and
# still catches the measured 10h37m runaway with hours to spare. Per FILE, not
# per run: a slow file cannot spend a fast file's budget.
PER_FILE_BUDGET="${SRCELAB_GATE_FILE_BUDGET_S:-36000}"
case "$PER_FILE_BUDGET" in ''|*[!0-9]*) PER_FILE_BUDGET=36000;; esac
while [ $# -gt 0 ]; do
  case "$1" in
    --update) UPDATE=1 ;;
    --jobs)
      shift
      [ $# -gt 0 ] || { echo "--jobs needs a positive integer" >&2; exit 2; }
      JOBS="$1"
      ;;
    --jobs=*) JOBS="${1#--jobs=}" ;;
    --check-artifact) CHECK_ARTIFACT=1 ;;
    --parse-report)
      shift
      [ $# -gt 0 ] || { echo "--parse-report needs a file argument" >&2; exit 2; }
      PARSE_REPORT="$1"
      ;;
    -h|--help)
      sed -n '5,90p' "$0" | sed 's/^# \{0,1\}//'
      exit 0
      ;;
    *) fail usage "unknown argument: $1 (see --help)" ;;
  esac
  shift
done

case "$JOBS" in ''|*[!0-9]*) fail usage "--jobs must be a positive integer, got '$JOBS'";; esac
[ "$JOBS" -ge 1 ] || fail usage "--jobs must be >= 1, got '$JOBS'"

if [ -n "$PARSE_REPORT" ]; then
  command -v python3 >/dev/null 2>&1 || { echo "python3 required" >&2; exit 2; }
  srcelab_parse "$PARSE_REPORT"
  exit $?
fi

# --- --check-artifact: the CHEAP leg (no binary, no corpus, no measurement)
#
# WHY IT IS SEPARATE. The measurement above is hours long, so it can only be a
# detached suite row; that leaves the ratchet ARTIFACT unguarded between those
# runs. The specific hole this closes: enforcement reads
# `baselines.get(key, {}).get("success_baseline", 0)`, so a pinned file with NO
# ratchet entry silently enforces a baseline of ZERO — add a fifth file to the
# pinned slice, forget the ratchet, and the gate reports PASS while measuring
# that file against nothing. This mode (and the armed-run check below) makes
# that combination fail closed, in ~50 ms, cheap enough for scripts/local_gate.sh.
if [ "$CHECK_ARTIFACT" = 1 ]; then
  command -v python3 >/dev/null 2>&1 || fail no-python3 "python3 is required for --check-artifact"
  [ -f "$RATCHET" ] || fail no-ratchet "committed ratchet artifact missing at $RATCHET"
  pinned_plan > "${TMPDIR:-/tmp}/srcelab_pinned.$$"
  SRCELAB_RATCHET_PATH="$RATCHET" SRCELAB_PINNED_FILE="${TMPDIR:-/tmp}/srcelab_pinned.$$" \
  python3 - <<'ARTIFACT'
import json
import os
import sys

ratchet_path = os.environ["SRCELAB_RATCHET_PATH"]
pinned = []
with open(os.environ["SRCELAB_PINNED_FILE"], encoding="utf-8") as f:
    for line in f:
        line = line.rstrip("\n")
        if not line:
            continue
        key, _rel, cap = line.split("|", 2)
        pinned.append((key, cap))

problems = []
try:
    with open(ratchet_path, encoding="utf-8") as f:
        d = json.load(f)
except (OSError, ValueError) as exc:
    print("SRCELAB artifact: unreadable ratchet {}: {}".format(ratchet_path, exc), file=sys.stderr)
    sys.exit(1)

if d.get("schema_version") != "Clean-srcelab-ratchet-v1":
    problems.append("schema_version is {!r}, expected 'Clean-srcelab-ratchet-v1'".format(d.get("schema_version")))
files = d.get("files")
if not isinstance(files, dict):
    problems.append("`files` is not an object")
    files = {}
armed = bool(d.get("armed"))

pinned_keys = [k for k, _ in pinned]
missing = [k for k in pinned_keys if k not in files]
extra = [k for k in files if k not in pinned_keys]
if missing:
    problems.append(
        "pinned files with NO ratchet entry (they would enforce a baseline of 0): "
        + ", ".join(sorted(missing))
    )
if extra:
    problems.append("ratchet entries for files that are no longer pinned: " + ", ".join(sorted(extra)))

for key, cap in pinned:
    entry = files.get(key)
    if not isinstance(entry, dict):
        continue
    base = entry.get("success_baseline")
    if not isinstance(base, int) or base < 0:
        problems.append("{}: success_baseline is {!r}, expected a non-negative integer".format(key, base))
    elif armed and base == 0:
        problems.append(
            "{}: armed ratchet with a ZERO baseline — arming records a MEASURED count, "
            "and a 0 enforces nothing".format(key)
        )
    if cap:
        if entry.get("cap_lines") != int(cap):
            problems.append("{}: cap_lines is {!r}, the pinned slice caps at {}".format(key, entry.get("cap_lines"), cap))

if armed and not d.get("armed_commit"):
    problems.append("armed ratchet has no `armed_commit` — an armed baseline with no provenance")
if armed and not d.get("last_updated"):
    problems.append("armed ratchet has no `last_updated`")

# BASELINES ARE BOUND TO THEIR EVIDENCE. `--update` writes them from a measured
# run, but nothing stopped a later hand edit from typing a number the reports
# never contained -- and a hand-typed baseline is exactly a trust claim with no
# measurement behind it. When a dated report for the ratchet's own armed_commit
# is checked in next to it, every baseline must EQUAL that report's counts.
# (No such report -- an older arming, or a clone without reports/ -- is not an
# error; there is simply nothing to bind against, and that is stated, not
# silently passed over.)
armed_commit = d.get("armed_commit") or ""
report_path = None
if armed and armed_commit:
    import glob as _glob
    matches = sorted(_glob.glob("reports/source-elab/srcelab-*-g{}.json".format(armed_commit)))
    if matches:
        report_path = matches[-1]
if report_path:
    try:
        with open(report_path, encoding="utf-8") as f:
            rep = json.load(f)
        by_key = {r["key"]: r for r in rep.get("files", [])}
    except (OSError, ValueError, KeyError, TypeError) as exc:
        problems.append("armed_commit report {} is unreadable: {}".format(report_path, exc))
        by_key = {}
    for key, entry in files.items():
        r = by_key.get(key)
        if r is None:
            problems.append(
                "{}: no entry in the armed_commit report {}".format(key, report_path))
            continue
        for field, rep_field in (("success_baseline", "success_count"),
                                 ("decl_count", "decl_count"),
                                 ("sorry_axioms", "sorry_axioms")):
            if field in entry and entry[field] != r.get(rep_field):
                problems.append(
                    "{}: {}={!r} but {} says {}={!r} — a baseline must equal its "
                    "evidence".format(key, field, entry[field], report_path,
                                      rep_field, r.get(rep_field)))
elif armed:
    print("  SRCELAB artifact: NOTE no reports/source-elab/srcelab-*-g{}.json "
          "next to the ratchet, so baselines are NOT bound to a committed "
          "measurement here.".format(armed_commit or "<unset>"))

if problems:
    for p in problems:
        print("  SRCELAB artifact: {}".format(p), file=sys.stderr)
    sys.exit(1)
print("  SRCELAB artifact: OK ({} pinned files, armed={}, ratchet={})".format(
    len(pinned), armed, ratchet_path))
ARTIFACT
  arc=$?
  rm -f "${TMPDIR:-/tmp}/srcelab_pinned.$$"
  [ "$arc" -eq 0 ] || fail artifact-inconsistent "data/source_elab_ratchet.json disagrees with the gate's pinned slice (see above)"
  verdict artifact-ok
  exit 0
fi

# (1) The binary under test. target/release/clean only — a debug or stale PATH
# binary would measure the wrong elaborator and mint a wrong baseline. Never
# builds anything itself. $CLEAN_BIN overrides for redirected-target worktrees.
CLEAN_BIN="${CLEAN_BIN:-}"
[ -z "$CLEAN_BIN" ] && [ -x target/release/clean ] && CLEAN_BIN=target/release/clean
{ [ -n "$CLEAN_BIN" ] && [ -x "$CLEAN_BIN" ]; } || skip no-binary "no release clean binary at target/release/clean (cargo build --locked --release --bin clean to enable)"

command -v python3 >/dev/null 2>&1 || skip no-python3 "python3 is required to parse check reports"
[ -f "$RATCHET" ] || fail no-ratchet "committed ratchet artifact missing at $RATCHET"

# (2) The Mathlib checkout. CLEAN_MATHLIB_DIR is authoritative when set.
ML=""
if [ -n "${CLEAN_MATHLIB_DIR:-}" ]; then
  if [ -d "$CLEAN_MATHLIB_DIR/.lake/build/lib/lean" ]; then
    ML="$CLEAN_MATHLIB_DIR"
  else
    skip no-corpus "CLEAN_MATHLIB_DIR=$CLEAN_MATHLIB_DIR has no .lake/build/lib/lean (explicit env var is authoritative; not falling back)"
  fi
else
  for c in data/raw/mathlib4 $HOME/mathlib4-*; do
    [ -d "$c/.lake/build/lib/lean" ] || continue
    ML="$c"
    break
  done
  [ -n "$ML" ] || skip no-corpus "no Mathlib checkout (set CLEAN_MATHLIB_DIR, or provide data/raw/mathlib4 or $HOME/mathlib4-* with .lake/build)"
fi
MLLIB="$ML/.lake/build/lib/lean"

# LEAN_PATH: Mathlib lib + the pinned toolchain core + every Lake package lib
# (same composition as scripts/kv_ratchet_gate.sh, so the check path's olean
# probe sees the full compiled dependency context).
LP="$MLLIB"
if [ -f "$ML/lean-toolchain" ]; then
  TC="$(tr -d ' \t\r\n' < "$ML/lean-toolchain" | sed 's#/#--#; s#:#---#')"
  CORE="$HOME/.elan/toolchains/$TC/lib/lean"
  [ -d "$CORE" ] && LP="$LP:$CORE"
fi
for p in "$ML"/.lake/packages/*/.lake/build/lib/lean; do
  [ -d "$p" ] && LP="$LP:$p"
done
export LEAN_PATH="$LP"

# Lightweight OOM admission, same rationale as kv_ratchet_gate.sh: refuse to
# pile a multi-GiB olean-closure load onto a box already under memory pressure
# (the Unique tail is the documented ~19.5 GB OOM; the cap plus this check keep
# the gate deferral-safe instead of OOM-killed).
MEM_MIN="${SRCELAB_GATE_MEM_GIB_MIN:-8}"
case "$MEM_MIN" in ''|*[!0-9]*) MEM_MIN=8;; esac
if [ "$MEM_MIN" -gt 0 ] && [ -r scripts/lib/stamp_mem_governor.sh ]; then
  # shellcheck source=/dev/null
  . scripts/lib/stamp_mem_governor.sh
  _avail="$(stamp_available_gib 2>/dev/null || echo 999)"
  case "$_avail" in ''|*[!0-9]*) _avail=999;; esac
  [ "$_avail" -lt "$MEM_MIN" ] && skip low-memory "only ${_avail}GiB free RAM (< ${MEM_MIN}GiB floor); deferring the source-elab measurement"
fi

OUT="$(mktemp -d "${TMPDIR:-/tmp}/source_elab_gate.XXXXXX")"
cleanup() {
  if [ -n "${OUT:-}" ] && [ -f "$OUT/capfiles.list" ]; then
    while IFS= read -r f; do [ -n "$f" ] && rm -f "$f"; done < "$OUT/capfiles.list"
  fi
  [ -n "${OUT:-}" ] && rm -rf "$OUT"
}
trap cleanup EXIT

# Pre-flight: resolve every pinned file (and create the Unique line-cap copy
# INSIDE the corpus tree so Lake-root/import discovery still works) before any
# long check runs, so partial-corpus is a clean pre-run skip.
: > "$OUT/capfiles.list"
: > "$OUT/plan.list"
while IFS='|' read -r key rel cap; do
  [ -n "$key" ] || continue
  src="$ML/$rel"
  [ -f "$src" ] || skip partial-corpus "pinned file missing from checkout: $rel"
  if [ -n "$cap" ]; then
    capfile="$ML/$(dirname "$rel")/$(basename "$rel" .lean)_srcelab_cap${cap}_tmp.lean"
    if ! head -n "$cap" "$src" > "$capfile" 2>/dev/null; then
      skip corpus-not-writable "cannot create line-cap copy $capfile (corpus tree not writable)"
    fi
    printf '%s\n' "$capfile" >> "$OUT/capfiles.list"
    src="$capfile"
  fi
  printf '%s|%s|%s|%s\n' "$key" "$src" "$cap" "$rel" >> "$OUT/plan.list"
done <<PINNED
$(pinned_plan)
PINNED

COMMIT="$(git rev-parse --short=9 HEAD 2>/dev/null || echo unknown)"
: > "$OUT/results.ndjson"

# --- measurement phase --------------------------------------------------
# Each pinned file is its own `clean check` process with the identical
# invocation; --jobs only controls how many run at once. Exit code, wall
# clock and both streams are recorded per file so the parse phase below is
# a pure function of what is on disk, in deterministic plan order, no
# matter what order the processes actually finished in.
#
# bash-3.2: no `wait -n`, so the slot loop polls with kill -0.
_running() {
  _n=0
  for _pf in "$OUT"/*.pid; do
    [ -f "$_pf" ] || continue
    [ -f "${_pf%.pid}.rc" ] && continue
    _p="$(cat "$_pf" 2>/dev/null)"
    [ -n "$_p" ] && kill -0 "$_p" 2>/dev/null && _n=$((_n + 1))
  done
  echo "$_n"
}

idx=0
while IFS='|' read -r key src cap rel; do
  [ -n "$key" ] || continue
  idx=$((idx + 1))
  while [ "$(_running)" -ge "$JOBS" ]; do sleep 5; done
  echo "  checking $key ... (job $idx, --jobs $JOBS)"
  date +%s > "$OUT/$idx.start"
  (
    # The check runs in ITS OWN background job so this subshell can hold a
    # deadline over it. `timeout(1)` is not on macOS base, and a bare `wait`
    # here is exactly the wedge this replaces.
    # shellcheck disable=SC2086
    "$CLEAN_BIN" $INVOCATION "$src" > "$OUT/$idx.stdout" 2> "$OUT/$idx.stderr" &
    _cp=$!
    _spent=0
    while kill -0 "$_cp" 2>/dev/null; do
      if [ "$PER_FILE_BUDGET" -gt 0 ] && [ "$_spent" -ge "$PER_FILE_BUDGET" ]; then
        # TERM first so the child can flush the partial report it has already
        # printed -- that partial output is the evidence the keep-dir phase
        # below preserves, and it is most wanted precisely when a file wedges.
        kill -TERM "$_cp" 2>/dev/null
        _grace=0
        while kill -0 "$_cp" 2>/dev/null && [ "$_grace" -lt 15 ]; do
          sleep 1; _grace=$((_grace + 1))
        done
        kill -KILL "$_cp" 2>/dev/null
        date +%s > "$OUT/$idx.end"
        printf '%s\n' "$_spent" > "$OUT/$idx.timeout"
        echo 254 > "$OUT/$idx.rc"
        exit 0
      fi
      sleep 5
      _spent=$((_spent + 5))
    done
    wait "$_cp"
    _rc=$?
    date +%s > "$OUT/$idx.end"
    echo "$_rc" > "$OUT/$idx.rc"
  ) &
  echo "$!" > "$OUT/$idx.pid"
done < "$OUT/plan.list"
wait

# --- evidence-keeping phase ---------------------------------------------
# BEFORE any parse, so a run that fails closed on file 1 still leaves the
# raw output of files 2..N on disk. A multi-hour measurement whose evidence
# is deleted by its own error path has to be run again from zero.
if [ -n "${SRCELAB_KEEP_DIR:-}" ]; then
  mkdir -p "$SRCELAB_KEEP_DIR" 2>/dev/null
  kdx=0
  while IFS='|' read -r key src cap rel; do
    [ -n "$key" ] || continue
    kdx=$((kdx + 1))
    slug="$(printf '%s' "$key" | tr '/:' '__')"
    cp "$OUT/$kdx.stdout" "$SRCELAB_KEEP_DIR/$slug.stdout" 2>/dev/null
    cp "$OUT/$kdx.stderr" "$SRCELAB_KEEP_DIR/$slug.stderr" 2>/dev/null
  done < "$OUT/plan.list"
fi

# --- parse + record phase (serial, plan order) --------------------------
jdx=0
while IFS='|' read -r key src cap rel; do
  [ -n "$key" ] || continue
  jdx=$((jdx + 1))
  rc="$(cat "$OUT/$jdx.rc" 2>/dev/null || echo 255)"
  wall=$(( $(cat "$OUT/$jdx.end" 2>/dev/null || echo 0) - $(cat "$OUT/$jdx.start" 2>/dev/null || echo 0) ))
  [ "$wall" -lt 0 ] && wall=0
  # A timed-out file is an ERROR, not a regression and not a pass. Checked
  # BEFORE the parse: a killed check has usually printed a PARTIAL report, and
  # parsing that would hand the ratchet a success_count lower than the baseline
  # -- reporting a fabricated regression for a file that was never measured.
  if [ -f "$OUT/$jdx.timeout" ]; then
    echo "  $key exceeded its ${PER_FILE_BUDGET}s per-file budget after $(cat "$OUT/$jdx.timeout" 2>/dev/null)s; stderr tail:" >&2
    tail -5 "$OUT/$jdx.stderr" >&2
    errored file-timeout "clean check on $key exceeded the ${PER_FILE_BUDGET}s per-file budget (SRCELAB_GATE_FILE_BUDGET_S); no measurement was produced for it, so the ratchet is NOT evaluated"
  fi
  # Nonzero exit is EXPECTED whenever failed_count > 0 (`clean check` bails
  # "check failed" after printing the JSON report); the gate's failure signal
  # is a MISSING/unparseable report (crash, OOM-kill, panic), never rc alone.
  if ! PARSED="$(srcelab_parse "$OUT/$jdx.stdout")"; then
    echo "  no Clean-check-report-v1 JSON from $key (clean check exit $rc); stderr tail:" >&2
    tail -5 "$OUT/$jdx.stderr" >&2
    fail check-no-report "clean check produced no parseable JSON report for $key"
  fi
  python3 scripts/srcelab_classify.py --report "$OUT/$jdx.stdout" --json \
    > "$OUT/$jdx.classes.json" \
    || fail classify-error "scripts/srcelab_classify.py failed on the report for $key"
  SRCELAB_REC_OUT="$OUT/results.ndjson" SRCELAB_REC_KEY="$key" SRCELAB_REC_PATH="$rel" \
  SRCELAB_REC_CAP="$cap" SRCELAB_REC_RC="$rc" SRCELAB_REC_PARSED="$PARSED" \
  SRCELAB_REC_WALL="$wall" SRCELAB_REC_CLASSES="$OUT/$jdx.classes.json" \
  python3 - <<'REC' || fail record-error "failed to record parsed result for $key"
import json
import os

rec = json.loads(os.environ["SRCELAB_REC_PARSED"])
with open(os.environ["SRCELAB_REC_CLASSES"], encoding="utf-8") as _cf:
    cls = json.load(_cf)
cap = os.environ["SRCELAB_REC_CAP"]
rec.update({
    "key": os.environ["SRCELAB_REC_KEY"],
    "path": os.environ["SRCELAB_REC_PATH"],
    "cap_lines": int(cap) if cap else None,
    "check_exit_code": int(os.environ["SRCELAB_REC_RC"]),
    "wall_seconds": int(os.environ["SRCELAB_REC_WALL"]),
    "failure_classes": cls["failure_classes"],
    "tactic_subclasses": cls["tactic_subclasses"],
    "first_failure": cls["first_failure"],
    "per_error_class": cls["per_error"],
})
with open(os.environ["SRCELAB_REC_OUT"], "a", encoding="utf-8") as f:
    f.write(json.dumps(rec) + "\n")
REC
done < "$OUT/plan.list"
idx="$jdx"

[ "$idx" -gt 0 ] || fail empty-plan "pinned-file plan resolved to zero files"

# (5) Dated report under reports/source-elab/ + ratchet enforcement.
# data/ is only written under an explicit --update (mirroring how the KV gate
# defers arming to `clean mathverse ratchet update`).
mkdir -p "$REPORT_DIR"
REPORT="$REPORT_DIR/srcelab-$(date +%Y-%m-%d)-g$COMMIT.json"
SRCELAB_RESULTS="$OUT/results.ndjson" SRCELAB_RATCHET="$RATCHET" SRCELAB_REPORT="$REPORT" \
SRCELAB_COMMIT="$COMMIT" SRCELAB_BIN="$CLEAN_BIN" SRCELAB_UPDATE="$UPDATE" \
SRCELAB_INVOCATION="clean $INVOCATION" \
python3 - <<'PY'
import datetime
import json
import os
import sys

recs = [json.loads(l) for l in open(os.environ["SRCELAB_RESULTS"], encoding="utf-8") if l.strip()]
ratchet_path = os.environ["SRCELAB_RATCHET"]
ratchet = json.load(open(ratchet_path, encoding="utf-8"))
armed = bool(ratchet.get("armed"))
baselines = ratchet.get("files", {})
today = datetime.date.today().isoformat()

report = {
    "schema_version": "Clean-srcelab-report-v1",
    "date": today,
    "commit": os.environ["SRCELAB_COMMIT"],
    "binary": os.environ["SRCELAB_BIN"],
    "invocation": os.environ["SRCELAB_INVOCATION"],
    "counting_basis": ratchet.get("counting_basis", "allow_sorry_success"),
    "counting_basis_note": (
        "success_count counts --allow-sorry passes: Clean-check-report-v1 has no "
        "per-decl sorry-taint field, so sorry-tainted decls are folded into "
        "success_count and taint is only visible as the run-wide "
        "trust_summary.sorry_axioms counter recorded per file below."
    ),
    "ratchet": {"path": ratchet_path, "armed": armed, "enforced": armed},
    "classifier": {
        "script": "scripts/srcelab_classify.py",
        "note": (
            "Per-file failure_classes / tactic_subclasses / first_failure below are "
            "computed by that script from the UNTRUNCATED check report; per_error_class "
            "carries the class of every error with its text truncated to 400 chars, so "
            "the histogram is auditable entry by entry from this artifact alone. The "
            "2026-08-22 evidence file reports/source-elab/srcelab-2026-08-22-Logic-Basic-"
            "g17f4682e6.json predates this script: its histogram came from an uncommitted "
            "ad-hoc classifier over strings the artifact itself truncates, and is NOT "
            "reproducible from it. Same nine class names, different (now written-down) "
            "rules; do not merge the two histograms."
        ),
    },
    "files": recs,
    "totals": {
        "decl_count": sum(r["decl_count"] for r in recs),
        "success_count": sum(r["success_count"] for r in recs),
        "failed_count": sum(r["failed_count"] for r in recs),
        "sorry_axioms": sum(r["sorry_axioms"] for r in recs),
        "kernel_check_failures": sum(r["kernel_check_failures"] for r in recs),
    },
}
with open(os.environ["SRCELAB_REPORT"], "w", encoding="utf-8") as f:
    json.dump(report, f, indent=2)
    f.write("\n")

for r in recs:
    print("  {}: success={}/{} (sorry_axioms={}, kernel_check_failures={}, check_exit={}, wall={}s)".format(
        r["key"], r["success_count"], r["decl_count"],
        r["sorry_axioms"], r["kernel_check_failures"], r["check_exit_code"],
        r.get("wall_seconds", 0)))
    for cls_name, n in (r.get("failure_classes") or {}).items():
        print("      {:4d}  {}".format(n, cls_name))
    ff = r.get("first_failure")
    if ff:
        print("      first failure [{}] {}".format(ff["class"], ff["error"][:160]))
print("  report: {}".format(os.environ["SRCELAB_REPORT"]))

# Ratchet enforcement (report is already on disk so regressions keep evidence).
#
# An ARMED ratchet with no entry for a pinned file is a DEFECT, not a pass:
# the old `.get(key, {}).get("success_baseline", 0)` default silently enforced
# zero, so adding a file to the pinned slice without arming it made the gate
# green on any number at all. Same fail-closed rule as --check-artifact.
#
# ONE exception, and only one: an explicit `--update` run. Arming IS the act of
# writing baselines, so refusing to arm a file because it has no baseline yet is
# a deadlock -- it made adding a file to the pinned slice impossible without
# first hand-typing a placeholder number into data/source_elab_ratchet.json, and
# a hand-typed baseline is exactly the un-evidenced trust claim that
# --check-artifact's evidence binding exists to forbid. So under --update a
# missing entry is ARMED FROM THIS RUN'S MEASUREMENT and said out loud; without
# --update it is still a hard, silent-zero-proof failure.
if armed:
    unbaselined = [r["key"] for r in recs if r["key"] not in baselines]
    if unbaselined and os.environ["SRCELAB_UPDATE"] != "1":
        for key in unbaselined:
            print(
                "  NO BASELINE {}: the ratchet is armed but has no entry for this pinned file"
                " (it would enforce 0)".format(key),
                file=sys.stderr,
            )
        sys.exit(5)
    for key in unbaselined:
        print(
            "  NEW PINNED FILE {}: no ratchet entry yet; this --update run arms it "
            "from its measured count".format(key)
        )

regressions = []
for r in recs:
    base = baselines.get(r["key"], {}).get("success_baseline", 0)
    if armed and r["success_count"] < base:
        regressions.append((r["key"], r["success_count"], base))
if regressions:
    for key, got, base in regressions:
        print("  REGRESSION {}: success {} < baseline {}".format(key, got, base), file=sys.stderr)
    sys.exit(3)

if os.environ["SRCELAB_UPDATE"] == "1":
    for r in recs:
        old = baselines.get(r["key"], {}).get("success_baseline", 0)
        if armed and r["success_count"] < old:
            sys.exit(4)  # defensive; the regression gate above already fired
    ratchet["files"] = {
        r["key"]: {
            "success_baseline": r["success_count"],
            "decl_count": r["decl_count"],
            "sorry_axioms": r["sorry_axioms"],
            **({"cap_lines": r["cap_lines"]} if r["cap_lines"] else {}),
        }
        for r in recs
    }
    ratchet["armed"] = True
    ratchet["last_updated"] = today
    ratchet["armed_commit"] = os.environ["SRCELAB_COMMIT"]
    with open(ratchet_path, "w", encoding="utf-8") as f:
        json.dump(ratchet, f, indent=2)
        f.write("\n")
    # The report on disk was written BEFORE this arming (deliberately: a
    # regression must leave its evidence even when the run then fails), so its
    # ratchet block describes the PRE-run state. Correct it now, and say
    # explicitly that this run is the one that armed it -- otherwise the
    # artifact of the arming run reads `armed: false`, which is exactly
    # backwards. (The 2026-08-23 report
    # reports/source-elab/srcelab-2026-08-23-ga86c5ffd6.json was produced
    # before this fix and still carries armed:false for that reason; it is
    # left as the run produced it rather than hand-edited.)
    report["ratchet"] = {
        "path": ratchet_path,
        "armed": True,
        "enforced": True,
        "armed_by_this_run": True,
        "armed_state_before_this_run": armed,
    }
    with open(os.environ["SRCELAB_REPORT"], "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)
        f.write("\n")
    print("  ratchet armed/updated: {}".format(ratchet_path))
elif not armed:
    print("  NOTE: ratchet is UNARMED (all-zero baselines) — this run enforced nothing;")
    print("        arm it with: scripts/source_elab_gate.sh --update")
PY
frc=$?
case "$frc" in
  0) ;;
  3) fail ratchet-regression "a pinned file's success count dropped below its armed baseline in $RATCHET (see report + stderr above)" ;;
  4) fail ratchet-lower "--update would LOWER an armed baseline; the ratchet is monotonic-up (a deliberate rebaseline needs a hand edit with justification)" ;;
  5) fail ratchet-missing-key "the ratchet is ARMED but has no baseline entry for a pinned file, which would enforce a baseline of 0; add it with --update (or fix the pinned slice)" ;;
  *) fail finalize-error "report/ratchet finalize step failed (exit $frc)" ;;
esac

echo "  SRCELAB gate: PASS ($idx pinned files re-measured; ratchet holds)."
verdict measured
