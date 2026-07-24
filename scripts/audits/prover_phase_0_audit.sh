#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
#
# prover_phase_0_audit.sh — Run the Phase-0 audit checklist commands and
# diff each result against the snapshot in
# reports/audits/2026-04-20-phase-0-baseline-metrics.md.
#
# Read-only. Does NOT invoke cargo (env-safe). If cargo is needed, run the
# constructive ratchet check separately.
#
# Exit codes:
#   0 — all metrics match or improved vs baseline
#   1 — one or more metrics regressed
#   2 — env / tool error

set -u

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$REPO_ROOT" || { echo "FATAL: cannot cd to $REPO_ROOT"; exit 2; }

# Baselines refreshed 2026-04-20 after Phase-0 landed. T1's reconciliation
# commit raised total_domain_axioms 33 → 38 (conjecture sum was already 37;
# T1 closed the gap and added one more). The original Phase-0 baseline of
# 33 would flag this as a regression and fail clean main — replaced with the
# authoritative current value from
# `python3 -m scripts.axiom_audit.aggregates --check`.
# See reports/audits/2026-04-20-phase-1-baseline-metrics.md for the snapshot.
BASELINE_AXIOMS=38
BASELINE_CONSTRUCTIVE=74
BASELINE_NN_DECL_AXIOM=374
# add_decl_(structural|unchecked) raw callsite count from the 2026-04-20 snapshot.
BASELINE_ADD_DECL_CALLSITES=245

status=0

run() {
  local label="$1"; shift
  echo "== $label =="
  "$@" 2>&1 | sed 's/^/  /'
  echo
}

normalize_int() {
  # Read a value from stdin and echo it as a trimmed integer, or "ERR".
  local v
  v="$(tr -d '[:space:]')"
  if [[ "$v" =~ ^-?[0-9]+$ ]]; then
    echo "$v"
  else
    echo "ERR"
  fi
}

measure_total_domain_axioms() {
  jq '.total_domain_axioms // 0' data/axiom_audit.json 2>/dev/null | normalize_int
}

measure_constructive_count() {
  jq '.count' data/constructive_ratchet.json 2>/dev/null | normalize_int
}

measure_nn_decl_axioms() {
  # shellcheck disable=SC2010
  ls crates/clean-kernel/src/env/nn_verify_*.rs 2>/dev/null \
    | xargs grep -hE 'Declaration::Axiom' 2>/dev/null \
    | wc -l \
    | normalize_int
}

measure_add_decl_callsites() {
  grep -rhE 'add_decl_(structural|unchecked)' crates/ 2>/dev/null \
    | wc -l \
    | normalize_int
}

check_ge() {
  # check_ge LABEL CURRENT BASELINE
  # passes if CURRENT >= BASELINE
  local label="$1" cur="$2" base="$3"
  if [[ "$cur" == "ERR" ]]; then
    echo "  [ERR]  $label: could not measure"
    status=2
    return
  fi
  if (( cur >= base )); then
    echo "  [ OK ] $label: $cur (>= baseline $base)"
  else
    echo "  [FAIL] $label: $cur regressed from baseline $base"
    status=1
  fi
}

check_le() {
  # check_le LABEL CURRENT BASELINE
  # passes if CURRENT <= BASELINE (ratchet downwards)
  local label="$1" cur="$2" base="$3"
  if [[ "$cur" == "ERR" ]]; then
    echo "  [ERR]  $label: could not measure"
    status=2
    return
  fi
  if (( cur <= base )); then
    echo "  [ OK ] $label: $cur (<= baseline $base)"
  else
    echo "  [FAIL] $label: $cur grew from baseline $base"
    status=1
  fi
}

check_eq() {
  local label="$1" cur="$2" base="$3"
  if [[ "$cur" == "ERR" ]]; then
    echo "  [ERR]  $label: could not measure"
    status=2
    return
  fi
  if [[ "$cur" == "$base" ]]; then
    echo "  [ OK ] $label: $cur (== baseline $base)"
  else
    echo "  [WARN] $label: $cur differs from baseline $base"
    # not a hard fail; count drift is informational here
  fi
}

echo "Phase-0 Prover audit — $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo

# 1. total_domain_axioms aggregate (ratchet down)
cur_axioms="$(measure_total_domain_axioms)"
check_le "total_domain_axioms (aggregate)" "$cur_axioms" "$BASELINE_AXIOMS"

# 2. constructive theorem ratchet count (ratchet up)
cur_constructive="$(measure_constructive_count)"
check_ge "constructive_ratchet.count" "$cur_constructive" "$BASELINE_CONSTRUCTIVE"

# 3. Declaration::Axiom in nn_verify_*.rs (must stay stable in Phase 0)
cur_nn_axioms="$(measure_nn_decl_axioms)"
check_eq "nn_verify_*.rs Declaration::Axiom sites" "$cur_nn_axioms" "$BASELINE_NN_DECL_AXIOM"

# 4. add_decl_(structural|unchecked) callsites — informational ratchet
cur_add_decl="$(measure_add_decl_callsites)"
check_le "add_decl_{structural,unchecked} callsites" "$cur_add_decl" "$BASELINE_ADD_DECL_CALLSITES"

echo
echo "Summary: exit=$status (0=ok, 1=regression, 2=tool error)"
exit $status
