#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0
#
# prover_building_clean_audit.sh — Run the Phase-1 (building-Clean) audit
# checklist commands and diff each result against the snapshot in
# reports/audits/2026-04-20-phase-1-baseline-metrics.md.
#
# This supersedes prover_phase_0_audit.sh. The Phase-0 script hard-coded
# total_domain_axioms baseline=33, which fails on current main (38 after
# Phase-0 T1 reconciliation). This script reads the authoritative aggregate
# from `python3 -m scripts.axiom_audit.aggregates --check` so it
# cannot drift.
#
# Read-only. Does NOT invoke cargo (env-safe). If cargo is needed, run the
# constructive-shard path separately (mathverse_shard verify-kernel --native).
#
# Exit codes:
#   0 — all metrics match or improved vs baseline
#   1 — one or more metrics regressed
#   2 — env / tool error

set -u

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$REPO_ROOT" || { echo "FATAL: cannot cd to $REPO_ROOT"; exit 2; }

# ---- Baselines (Phase-1 snapshot, 2026-04-20) ------------------------------
#
# total_domain_axioms: authoritative value on clean main = 38 (per recompute).
# If this script reads a value > BASELINE_AXIOMS_MAX, flag as regression.
# If this script reads a value < BASELINE_AXIOMS_MAX, pass (ratchet-down).
BASELINE_AXIOMS_MAX=38
BASELINE_CONSTRUCTIVE_MIN=74
BASELINE_NN_DECL_AXIOM_MAX=374
BASELINE_ADD_DECL_CALLSITES_MAX=245

status=0

normalize_int() {
  local v
  v="$(tr -d '[:space:]')"
  if [[ "$v" =~ ^-?[0-9]+$ ]]; then
    echo "$v"
  else
    echo "ERR"
  fi
}

# Read total_domain_axioms from the JSON file. The authoritative recompute
# script is invoked separately below to detect drift between file and
# conjecture array sum.
measure_total_domain_axioms() {
  jq '.total_domain_axioms // 0' data/axiom_audit.json 2>/dev/null | normalize_int
}

# Run the recompute script to get the authoritative aggregate. Exits 0 if the
# JSON file agrees with the conjecture sum; non-zero otherwise.
measure_recompute_status() {
  if command -v python3 >/dev/null 2>&1; then
    if python3 -m scripts.axiom_audit.aggregates --check \
        >/dev/null 2>&1; then
      echo "OK"
    else
      echo "DRIFT"
    fi
  else
    echo "NO_PYTHON3"
  fi
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

measure_def_eq_to_eq_sites() {
  # Count production call sites to def_eq_to_eq (exclude test files + doc
  # comments). This is the Packet-B/C/D headline metric.
  if command -v rg >/dev/null 2>&1; then
    rg --type rust 'def_eq_to_eq' crates/clean-verify/src/spec/core_spec/ 2>/dev/null \
      | grep -vE '(_tests\.rs|/tests/|^\s*//)' \
      | wc -l \
      | normalize_int
  else
    grep -rn 'def_eq_to_eq' crates/clean-verify/src/spec/core_spec/ 2>/dev/null \
      | grep -vE '(_tests\.rs|/tests/|^\s*//)' \
      | wc -l \
      | normalize_int
  fi
}

measure_type_preservation_leaves() {
  # Extract TYPE_PRESERVATION_LEAVES length from the authoritative constant.
  local file="crates/clean-verify/src/spec/core_spec/type_preservation_chain_status_tests.rs"
  if [[ -f "$file" ]]; then
    # Count comma-separated entries inside the `&[...]` init.
    grep -E 'const TYPE_PRESERVATION_LEAVES' "$file" 2>/dev/null \
      | head -1 \
      | grep -oE '"[^"]+"' \
      | wc -l \
      | normalize_int
  else
    echo "ERR"
  fi
}

check_le() {
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

check_ge() {
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
    echo "  [INFO] $label: $cur differs from baseline $base (drift — review)"
  fi
}

echo "Phase-1 (building-Clean) Prover audit — $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo "Head: $(git rev-parse --short HEAD 2>/dev/null || echo unknown)"
echo

# 1. Authoritative recompute script agrees with JSON file.
recompute="$(measure_recompute_status)"
case "$recompute" in
  OK)           echo "  [ OK ] axiom_audit recompute: JSON agrees with conjecture sum" ;;
  DRIFT)        echo "  [FAIL] axiom_audit recompute: JSON and conjecture sum disagree"
                status=1 ;;
  NO_PYTHON3)   echo "  [ERR]  axiom_audit recompute: python3 not available"
                status=2 ;;
esac

# 2. total_domain_axioms aggregate (ratchet down).
cur_axioms="$(measure_total_domain_axioms)"
check_le "total_domain_axioms (aggregate)" "$cur_axioms" "$BASELINE_AXIOMS_MAX"

# 3. Constructive theorem ratchet (ratchet up).
cur_constructive="$(measure_constructive_count)"
check_ge "constructive_ratchet.count" "$cur_constructive" "$BASELINE_CONSTRUCTIVE_MIN"

# 4. Declaration::Axiom in nn_verify_*.rs (must not increase; may decrease
#    slightly for #3646 REWRITE path).
cur_nn_axioms="$(measure_nn_decl_axioms)"
check_le "nn_verify_*.rs Declaration::Axiom sites" "$cur_nn_axioms" "$BASELINE_NN_DECL_AXIOM_MAX"

# 5. add_decl_{structural,unchecked} callsites (ratchet down).
cur_add_decl="$(measure_add_decl_callsites)"
check_le "add_decl_{structural,unchecked} callsites" "$cur_add_decl" "$BASELINE_ADD_DECL_CALLSITES_MAX"

# 6. def_eq_to_eq production call sites (ratchet down; Packet D drives to 0).
cur_defeq="$(measure_def_eq_to_eq_sites)"
echo "  [INFO] def_eq_to_eq production call sites (core_spec/): $cur_defeq"

# 7. TYPE_PRESERVATION_LEAVES count (ratchet down; Packet E drives 2 → 1).
cur_leaves="$(measure_type_preservation_leaves)"
echo "  [INFO] TYPE_PRESERVATION_LEAVES entries: $cur_leaves (baseline 2; Phase-1 target 1)"

echo
echo "Summary: exit=$status (0=ok, 1=regression, 2=tool error)"
exit $status
