#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# The frontend merge suite: every lib, bin, integration and doctest target of
# the frontend crates, through the memory gate, with a per-target verdict.
#
# WHY
# ---
# Measured by the 2026-09-24 process audit
# (reports/lean4-replacement-audit-2026-09-24/process.json): the regression net
# outside the five-file source-elab slice was lib suites run with name filters.
# The first all-targets run after the wave-3 merges found three RED
# integration targets (clean-elab structural_recursion_prefix_params,
# clean-parser no_silent_trees, clean-olean prelude_instance_priority_census)
# that run in 0.37 s, 0.06 s and 8.28 s -- and because `cargo test` stops at
# the first failing binary, 31 clean-elab, 6 clean-parser and 8 clean-olean
# targets sorted after them were never executed at all. This runs
#
#     targo --unverified test --locked --no-fail-fast \
#         -p clean-parser -p clean-olean -p clean-macro -p clean-elab
#
# as three gated legs -- BUILD (`--no-run`), RUN (lib + bins + integration
# tests) and DOC (`--doc`) -- so the compile reservation is released before the
# hour of test execution starts instead of being held through it. Nothing is
# filtered by name. The only exclusion is the PINNED slow-list
# (scripts/frontend_merge_suite_slow.txt), and a row there is refused unless it
# records a measurement over the budget: a slow-list row under budget is a
# suppression. Slow targets are printed as SLOW with their measurement and
# where they run instead, never silently dropped.
#
# The verdict is scripts/frontend_merge_suite_report.py's, one row per target:
# GREEN / EMPTY / RED / NOT_RUN / SLOW, plus a machine-readable summary.
# Exit 0 only with zero RED and zero NOT_RUN.
#
# USAGE
#   scripts/frontend_merge_suite.sh               # build, run, doc, report
#   scripts/frontend_merge_suite.sh --no-doc      # skip the doctest leg
#   scripts/frontend_merge_suite.sh --selftest    # the verdict logic's arms
#
# ENVIRONMENT
#   CARGO_TARGET_DIR    build directory (default: target/targo-merge-suite --
#                       targo's fingerprints never match cargo's, so it gets
#                       its own)
#   TARGO               the targo binary (default: `targo` on PATH)
#   FRONTEND_SUITE_OUT  where logs and summary.json go
#                       (default: $CARGO_TARGET_DIR/frontend-merge-suite)
#   FRONTEND_SUITE_BUDGET_S  per-target budget for the slow-list (default 600)
#   FRONTEND_SUITE_TARGET_TIMEOUT_S  the per-target GUARD (default 21600): a
#                       run-leg test binary still running after this many
#                       wall seconds is killed, with its whole process group,
#                       and reads RED/TIMEOUT -- see "THE PER-TARGET GUARD"
#   FRONTEND_SUITE_PYTHON    interpreter for the report (default: python3;
#                       the report is Python 3.9 compatible)
#   FRONTEND_SUITE_BUILD_GB / _RUN_GB / _DOC_GB   heavy_gate weight specs
#                       (a whole number of GB, or auto:<class>[:<fallback>])
#
# Every leg goes through scripts/heavy_gate.sh: this box took two kernel panics
# from concurrent compiles, and a suite that bypassed the gate would be the
# third. Run it DIRECTLY, never inside another heavy_gate reservation: each leg
# takes its own, and an outer hold larger than the budget minus a leg's weight
# would wait on itself forever.
#
# WEIGHTS. The RUN and DOC legs reserve `auto:frontend-suite-run` /
# `auto:frontend-suite-doc`: heavy_gate derives each from that class's own
# measured peaks (ceil(1.3 x the max over its last 10 completed runs), see
# scripts/heavy_gate_weights.sh), so the suite's reservation follows what the
# suite actually uses instead of a number typed once. Both are properties of
# the TESTS -- the run leg executes the same binaries, and rustdoc recompiles
# every doctest on every run -- so one class per leg measures one kind of job.
# The BUILD leg stays an explicit 12 GB, deliberately: its peak depends on how
# much of the tree is stale, from ~0 GB for a no-op to 8.64 GB measured cold
# (heavy_gate peak line `p0net-frontend-build`, 2026-09-24), and a window of
# no-op rebuilds would teach an auto class to under-reserve the next real one
# -- the direction that panicked this box. 12 = ceil(1.3 x 8.64).
#
# THE PER-TARGET GUARD. libtest has no timeout and cargo runs the binaries one
# after another, so one hung test held the whole run leg: on 2026-10-07 the
# suite could not finish at all because clean-elab's
# bitvec_multilimb_pipeline_e2e ran 53 CPU-minutes without finishing (fixed at
# the cause in the elaborator's unifier, `unify/unifier/proof_irrel.rs`). The
# run leg therefore names this repo's verdict script as cargo's target RUNNER
# (`--config target.<host>.runner=[...]`, run leg only): every test binary runs
# under `frontend_merge_suite_report.py run-target`, which kills it -- and
# everything it spawned -- once it outlives FRONTEND_SUITE_TARGET_TIMEOUT_S,
# and prints the TIMEOUT marker the report turns into a RED row. It is an
# additional guard, not a fix and not a waiver: a killed target is RED, and the
# suite still exits 1. The default is a hang detector, ~4x the slowest target
# measured: clean-olean native_fold_canon_lean, 4383/4408 s (2026-10-07) and
# 5231 s (2026-10-09, load 50-90) -- the first 5400 s default left 169 s.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPORT="$REPO_ROOT/scripts/frontend_merge_suite_report.py"
SLOW_LIST="$REPO_ROOT/scripts/frontend_merge_suite_slow.txt"
GATE="$REPO_ROOT/scripts/heavy_gate.sh"
PY="${FRONTEND_SUITE_PYTHON:-python3}"
PACKAGES=(clean-parser clean-olean clean-macro clean-elab)
BUDGET_S="${FRONTEND_SUITE_BUDGET_S:-600}"
TARGET_TIMEOUT_S="${FRONTEND_SUITE_TARGET_TIMEOUT_S:-21600}"

refuse() { echo "frontend-merge-suite: REFUSED: $1" >&2; exit 2; }

DOC=1
case "${1:-}" in
  --selftest) exec "$PY" "$REPORT" --selftest ;;
  --no-doc) DOC=0 ;;
  "") ;;
  *) echo "usage: $0 [--no-doc|--selftest]" >&2; exit 64 ;;
esac

# A surrounding hold waits on itself when a phase acquires its own memory.
# Refuse before compiler discovery, metadata, or a phase can start.
if [[ ${HEAVY_GATE_HELD+x} ]]; then
  refuse "run directly, outside a memory reservation; each phase acquires its own"
fi

if [[ -z "${TARGO:-}" ]]; then
  TARGO="$(command -v targo 2>/dev/null)" \
    || refuse "no \`targo\` on PATH; set TARGO=<path to targo>"
fi
[[ -x "$TARGO" ]] || refuse "TARGO=$TARGO is not an executable file"

[[ "$TARGET_TIMEOUT_S" =~ ^[1-9][0-9]*$ ]] \
  || refuse "FRONTEND_SUITE_TARGET_TIMEOUT_S=$TARGET_TIMEOUT_S is not a positive whole number of seconds"
# The guard's runner: an absolute interpreter and script, spelled as a TOML
# array (cargo splits an env-var runner on whitespace; an array survives any
# path), for the host triple the run leg's binaries are built for.
PY_ABS="$(command -v "$PY" 2>/dev/null)" || refuse "no \`$PY\` on PATH for the per-target guard"
# The host triple comes from the compiler targo drives -- $RUSTC when set,
# else the trustc installed beside targo -- never whatever `rustc` is first on
# PATH (a stock one would name its own host, not the build's).
HOST_RUSTC="${RUSTC:-$(dirname "$TARGO")/trustc}"
[[ -x "$HOST_RUSTC" ]] || refuse "no compiler at $HOST_RUSTC to read the host triple from; set RUSTC=<path to trustc>"
HOST_TRIPLE="$("$HOST_RUSTC" -vV 2>/dev/null | sed -n 's/^host: //p')"
[[ -n "$HOST_TRIPLE" ]] || refuse "cannot read the host triple from \`$HOST_RUSTC -vV\` for the per-target guard"
for part in "$PY_ABS" "$REPORT"; do
  case "$part" in *'"'*|*\\*) refuse "the per-target guard cannot quote \`$part\` into a TOML runner array" ;; esac
done
RUNNER_CFG="target.$HOST_TRIPLE.runner=[\"$PY_ABS\", \"$REPORT\", \"run-target\", \"--timeout\", \"$TARGET_TIMEOUT_S\", \"--\"]"

export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$REPO_ROOT/target/targo-merge-suite}"
OUT="${FRONTEND_SUITE_OUT:-$CARGO_TARGET_DIR/frontend-merge-suite}"
mkdir -p "$OUT" || refuse "cannot create $OUT"
cd "$REPO_ROOT" || refuse "cannot cd to $REPO_ROOT"

pkg_args=()
for p in "${PACKAGES[@]}"; do pkg_args+=(-p "$p"); done
pkg_csv="$(IFS=,; echo "${PACKAGES[*]}")"

# The target inventory comes from cargo's own metadata, not from a directory
# listing: autotests, [[test]] paths and required-features are cargo's to say.
"$TARGO" metadata --no-deps --format-version 1 --locked >"$OUT/metadata.json" 2>"$OUT/metadata.err" \
  || { cat "$OUT/metadata.err" >&2; refuse "targo metadata failed"; }
"$PY" "$REPORT" plan --metadata "$OUT/metadata.json" --packages "$pkg_csv" \
  --slow-list "$SLOW_LIST" --budget "$BUDGET_S" >"$OUT/plan.txt" \
  || refuse "the slow-list or the target inventory is inconsistent (named above)"
selection=()
while IFS= read -r arg; do [[ -n "$arg" ]] && selection+=("$arg"); done <"$OUT/plan.txt"

head_sha="$(git rev-parse HEAD 2>/dev/null || echo unknown)"
dirty=false
[[ -n "$(git status --porcelain --untracked-files=no 2>/dev/null)" ]] && dirty=true
echo "== frontend merge suite: ${PACKAGES[*]} at ${head_sha:0:12} (dirty=$dirty) =="
echo "   targo: $TARGO"
echo "   build dir: $CARGO_TARGET_DIR   logs: $OUT"
echo "   per-target guard: a run-leg binary still running after ${TARGET_TIMEOUT_S}s is killed and RED (TIMEOUT)"

# Echo the progress lines only; the full output is in the leg's log.
progress() { grep --line-buffered -E '^[[:space:]]+(Running|Doc-tests) |^test result: |^error: ' || true; }

# One gated leg. LEG_WALL counts the heavy_gate QUEUE as well; LEG_RAN starts
# after memory AND CPU admit the leg (a stamp the command writes first), so a
# cost quoted from a run is the leg's own and not the machine's load. Measured
# on the first run: the doc leg's wall was 1054 s, of which 14 s was doctests
# and the rest a queue behind other lanes' reservations.
run_leg() { # <name> <weight> <log> <cargo args...>
  local name=$1 weight=$2 log=$3 t0 t1 rc stamp admitted
  shift 3
  stamp="$OUT/$name.admitted"
  if ! rm -f "$stamp"; then
    echo "frontend-merge-suite: REFUSED: cannot clear $name phase-start receipt" >&2
    LEG_WALL=0; LEG_RAN=null; LEG_RC=75
    return
  fi
  t0=$(date +%s)
  "$GATE" run "$weight" "frontend-suite-$name" -- \
    build-slot --cpus 2 -- \
    sh -c 'date +%s >"$0" || exit 74; exec "$@"' "$stamp" "$TARGO" --unverified test --locked "$@" 2>&1 \
    | tee "$log" | progress
  rc=${PIPESTATUS[0]}
  t1=$(date +%s)
  LEG_WALL=$(( t1 - t0 ))
  LEG_RAN=null
  if admitted=$(cat "$stamp" 2>/dev/null) \
      && [[ "$admitted" =~ ^[1-9][0-9]*$ && ${#admitted} -le ${#t1} ]] \
      && (( admitted >= t0 && admitted <= t1 )); then
    LEG_RAN=$(( t1 - admitted ))
  else
    echo "frontend-merge-suite: REFUSED: $name has no valid phase-start receipt" >&2
    [[ $rc -ne 0 ]] || rc=75
  fi
  LEG_RC=$rc
  echo "   leg $name: exit $rc in ${LEG_WALL}s wall, ${LEG_RAN}s after admission"
}

run_leg build "${FRONTEND_SUITE_BUILD_GB:-12}" "$OUT/build.log" --no-run "${pkg_args[@]}" "${selection[@]}"
build_rc=$LEG_RC; build_wall=$LEG_WALL; build_ran=$LEG_RAN
run_rc=""; run_wall=0; run_ran=null; doc_rc=""; doc_wall=0; doc_ran=null
: >"$OUT/run.log"
if [[ $build_rc -eq 0 ]]; then
  run_leg run "${FRONTEND_SUITE_RUN_GB:-auto:frontend-suite-run:6}" "$OUT/run.log" --no-fail-fast \
    --config "$RUNNER_CFG" "${pkg_args[@]}" "${selection[@]}"
  run_rc=$LEG_RC; run_wall=$LEG_WALL; run_ran=$LEG_RAN
else
  echo "   the build leg failed: every target is NOT_RUN (see $OUT/build.log)"
fi
doc_args=()
if [[ $DOC -eq 1 ]]; then
  : >"$OUT/doc.log"
  if [[ $build_rc -eq 0 ]]; then
    run_leg doc "${FRONTEND_SUITE_DOC_GB:-auto:frontend-suite-doc:12}" "$OUT/doc.log" --no-fail-fast --doc "${pkg_args[@]}"
    doc_rc=$LEG_RC; doc_wall=$LEG_WALL; doc_ran=$LEG_RAN
  fi
  doc_args=(--doc-log "$OUT/doc.log")
  [[ -n "$doc_rc" ]] && doc_args+=(--doc-rc "$doc_rc")
fi
run_rc_args=()
[[ -n "$run_rc" ]] && run_rc_args=(--run-rc "$run_rc")

legs="{\"head\": \"$head_sha\", \"dirty\": $dirty, \"targo\": \"$TARGO\",\
 \"build\": {\"rc\": $build_rc, \"wall_s\": $build_wall, \"ran_s\": $build_ran},\
 \"run\": {\"rc\": ${run_rc:-null}, \"wall_s\": $run_wall, \"ran_s\": $run_ran},\
 \"doc\": {\"rc\": ${doc_rc:-null}, \"wall_s\": $doc_wall, \"ran_s\": $doc_ran, \"enabled\": $([[ $DOC -eq 1 ]] && echo true || echo false)}}"
echo "== frontend merge suite: per-target verdicts =="
"$PY" "$REPORT" report --metadata "$OUT/metadata.json" --packages "$pkg_csv" \
  --slow-list "$SLOW_LIST" --budget "$BUDGET_S" \
  --run-log "$OUT/run.log" ${doc_args[@]+"${doc_args[@]}"} --build-rc "$build_rc" \
  ${run_rc_args[@]+"${run_rc_args[@]}"} \
  --legs "$legs" --summary-out "$OUT/summary.json"
rc=$?
echo "   summary: $OUT/summary.json   wall: build ${build_wall}s, run ${run_wall}s, doc ${doc_wall}s (after admission: ${build_ran}s, ${run_ran}s, ${doc_ran}s)"
exit "$rc"
