#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Mathlib SOURCE-elaboration gate (SRCELAB).
#
# RE-MEASURES the four pinned Mathlib source files through Clean's own
# parser -> elaborator -> kernel (`clean check --imports-prefer-olean
# --allow-sorry --json`) and enforces, against the committed baseline in
# data/source_elab_ratchet.json, that per-file success counts never drop.
# This is the gate-owned successor to the HISTORICAL July-14 numbers in
# docs/plans/SOURCE_ELAB_IMPORTS_2026-07-13.md (Logic/Basic 86/257 etc.),
# which must never be quoted as current status.
#
# Pinned slice (fixed, deterministic, OOM-safe):
#   Mathlib/Logic/Basic.lean
#   Mathlib/Logic/Function/Basic.lean
#   Mathlib/Data/Subtype.lean
#   Mathlib/Logic/Unique.lean capped at line 240 — the final section (lines
#   241-270: Unique.subtypeEq/subtypeEq' + Fin.instUnique) OOMs (~19.5 GB);
#   see docs/plans/SOURCE_ELAB_IMPORTS_2026-07-13.md ("measure Unique.lean
#   capped at line 240"). The cap is a `head -n 240` sibling copy inside the
#   corpus tree (so Lake-root/import discovery still works), removed on exit.
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
#     SRCELAB_GATE=measured             the four files were actually re-checked
#     SRCELAB_GATE=skipped:<reason>     nothing was measured; <reason> says why
#     SRCELAB_GATE=failed:<reason>      a real regression / defect (exit 1)
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
#                                            fails first)
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
while [ $# -gt 0 ]; do
  case "$1" in
    --update) UPDATE=1 ;;
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

if [ -n "$PARSE_REPORT" ]; then
  command -v python3 >/dev/null 2>&1 || { echo "python3 required" >&2; exit 2; }
  srcelab_parse "$PARSE_REPORT"
  exit $?
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
done <<'PINNED'
Mathlib/Logic/Basic.lean|Mathlib/Logic/Basic.lean|
Mathlib/Logic/Function/Basic.lean|Mathlib/Logic/Function/Basic.lean|
Mathlib/Data/Subtype.lean|Mathlib/Data/Subtype.lean|
Mathlib/Logic/Unique.lean:1-240|Mathlib/Logic/Unique.lean|240
PINNED

COMMIT="$(git rev-parse --short=9 HEAD 2>/dev/null || echo unknown)"
: > "$OUT/results.ndjson"
idx=0
while IFS='|' read -r key src cap rel; do
  [ -n "$key" ] || continue
  idx=$((idx + 1))
  echo "  checking $key ..."
  # shellcheck disable=SC2086
  "$CLEAN_BIN" $INVOCATION "$src" > "$OUT/$idx.stdout" 2> "$OUT/$idx.stderr"
  rc=$?
  # Nonzero exit is EXPECTED whenever failed_count > 0 (`clean check` bails
  # "check failed" after printing the JSON report); the gate's failure signal
  # is a MISSING/unparseable report (crash, OOM-kill, panic), never rc alone.
  if ! PARSED="$(srcelab_parse "$OUT/$idx.stdout")"; then
    echo "  no Clean-check-report-v1 JSON from $key (clean check exit $rc); stderr tail:" >&2
    tail -5 "$OUT/$idx.stderr" >&2
    fail check-no-report "clean check produced no parseable JSON report for $key"
  fi
  SRCELAB_REC_OUT="$OUT/results.ndjson" SRCELAB_REC_KEY="$key" SRCELAB_REC_PATH="$rel" \
  SRCELAB_REC_CAP="$cap" SRCELAB_REC_RC="$rc" SRCELAB_REC_PARSED="$PARSED" \
  python3 - <<'PY' || fail record-error "failed to record parsed result for $key"
import json
import os

rec = json.loads(os.environ["SRCELAB_REC_PARSED"])
cap = os.environ["SRCELAB_REC_CAP"]
rec.update({
    "key": os.environ["SRCELAB_REC_KEY"],
    "path": os.environ["SRCELAB_REC_PATH"],
    "cap_lines": int(cap) if cap else None,
    "check_exit_code": int(os.environ["SRCELAB_REC_RC"]),
})
with open(os.environ["SRCELAB_REC_OUT"], "a", encoding="utf-8") as f:
    f.write(json.dumps(rec) + "\n")
PY
done < "$OUT/plan.list"

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
    print("  {}: success={}/{} (sorry_axioms={}, kernel_check_failures={}, check_exit={})".format(
        r["key"], r["success_count"], r["decl_count"],
        r["sorry_axioms"], r["kernel_check_failures"], r["check_exit_code"]))
print("  report: {}".format(os.environ["SRCELAB_REPORT"]))

# Ratchet enforcement (report is already on disk so regressions keep evidence).
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
  *) fail finalize-error "report/ratchet finalize step failed (exit $frc)" ;;
esac

echo "  SRCELAB gate: PASS (four pinned files re-measured; ratchet holds)."
verdict measured
