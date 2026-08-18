#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# parser_mathlib_sweep.sh — Mathlib parse-rate sweep (parser pillar artifact).
#
# Runs `clean check --parse-only --json` over the 40-module Mathlib KV
# cross-section SOURCE files and aggregates the per-declaration parse outcomes
# into reports/parser-mathlib-parse-rate.json. This converts the parser
# pillar's headline number from historical-single-file (95.8% on
# Mathlib/Logic/Basic.lean, 2026-07-13) to a measured broad sample.
#
# MEASUREMENT SEMANTICS (fail-closed): a `RawDecl` recovery placeholder is a
# parse FAILURE, never a parse — enforced inside `clean check --parse-only`
# (crates/clean-cli/src/cmd_core.rs, ParseOnlyCounts). A hard parser error
# aborts the file with zero per-declaration counts. Parser recovery
# diagnostics (tactic-block degradations to synthetic sorry) are reported
# separately as completeness debt; they do not subtract from parse_ok.
#
# ## The verdict line (same contract as kv_ratchet_gate.sh)
#
# Exit 0 alone is NOT evidence — the corpus or binary may simply be absent.
# Every run emits exactly one machine-readable verdict line on stdout:
#
#     PARSESWEEP=measured             the sweep ran and the artifact was written
#     PARSESWEEP=skipped:<reason>     nothing was measured; <reason> says why
#     PARSESWEEP=failed:<reason>      the sweep ran but aggregation failed (exit 1)
#
# Env:
#   CLEAN_MATHLIB_DIR  Mathlib SOURCE checkout root (contains Mathlib/*.lean).
#                      Falls back to MATHLIB_CHECKOUT, then data/raw/mathlib4,
#                      then /tmp/mathlib4 (the provisioning layout from
#                      docs/plans/MATHLIB_KV_MILESTONE_2026-07-12.md).
#   CLEAN_BIN          clean binary (default: target/release/clean, then
#                      target/debug/clean).
#
# bash-3.2 safe.
set -uo pipefail
cd "$(cd "$(dirname "$0")/.." && pwd)" || exit 1

REPORT=reports/parser-mathlib-parse-rate.json

# ---------------------------------------------------------------------------
# The 40-module Mathlib KV cross-section.
#
# Source: docs/plans/MATHLIB_KV_MILESTONE_2026-07-12.md ("Cross-section — 40
# modules, 8,908 constants"). The doc records the cross-section's domain
# spread (logic, order, algebra, data, real/complex analysis, topology,
# category theory, measure theory, number theory, set theory, computability)
# but NAMES only 15 of the 40 modules explicitly — the full list was not
# machine-recorded, so it is inlined here per the roadmap brick
# (docs/plans/ROADMAP_LEAN4_FULL_REPLACEMENT_2026-08-10.md, parse-rate row).
# The 15 doc-named modules come first; the remainder reconstructs the SAME
# documented domain spread with long-standing foundational Mathlib modules.
# Modules absent from the local checkout are recorded as "missing" in the
# artifact, never silently dropped or counted as parsed.
# ---------------------------------------------------------------------------
MODULES=(
  # --- named explicitly in MATHLIB_KV_MILESTONE_2026-07-12.md ---
  Mathlib.Logic.Basic
  Mathlib.Algebra.Group.Defs
  Mathlib.Order.Basic
  Mathlib.Algebra.Group.Basic
  Mathlib.Data.List.Basic
  Mathlib.Data.Real.Basic
  Mathlib.Data.Complex.Basic
  Mathlib.Topology.Basic
  Mathlib.Analysis.Normed.Group.Basic
  Mathlib.CategoryTheory.Category.Basic
  Mathlib.MeasureTheory.Measure.MeasureSpace
  Mathlib.SetTheory.Cardinal.Basic
  Mathlib.Computability.Halting
  Mathlib.NumberTheory.Divisors
  Mathlib.Computability.Primrec
  # --- reconstructed domain spread (same doc-described cross-section) ---
  Mathlib.Logic.Function.Basic
  Mathlib.Logic.Equiv.Basic
  Mathlib.Logic.Relation
  Mathlib.Order.Lattice
  Mathlib.Order.Bounds.Basic
  Mathlib.Order.Hom.Basic
  Mathlib.Algebra.GroupWithZero.Defs
  Mathlib.Algebra.Ring.Defs
  Mathlib.Algebra.Ring.Basic
  Mathlib.Algebra.Field.Basic
  Mathlib.Algebra.Order.Ring.Defs
  Mathlib.Data.Nat.Defs
  Mathlib.Data.Int.Defs
  Mathlib.Data.Rat.Defs
  Mathlib.Data.Option.Basic
  Mathlib.Data.Prod.Basic
  Mathlib.Data.Subtype
  Mathlib.Data.Bool.Basic
  Mathlib.Data.Set.Basic
  Mathlib.Data.Finset.Basic
  Mathlib.Topology.Bases
  Mathlib.Topology.Constructions
  Mathlib.Analysis.SpecificLimits.Basic
  Mathlib.CategoryTheory.Functor.Basic
  Mathlib.CategoryTheory.NatTrans
  Mathlib.MeasureTheory.OuterMeasure.Basic
  Mathlib.SetTheory.Ordinal.Basic
)

verdict() {
  echo "PARSESWEEP=$1"
  return 0
}

skip() {
  echo "SKIP: parser Mathlib sweep — $2."
  verdict "skipped:$1"
  exit 0
}

fail() {
  echo "parser Mathlib sweep: FAIL — $2" >&2
  verdict "failed:$1"
  exit 1
}

command -v python3 >/dev/null 2>&1 || skip no-python3 "python3 not found"

# --- clean binary -----------------------------------------------------------
CLEAN_BIN="${CLEAN_BIN:-}"
if [ -z "$CLEAN_BIN" ]; then
  for cand in target/release/clean target/debug/clean; do
    if [ -x "$cand" ]; then
      CLEAN_BIN="$cand"
      break
    fi
  done
fi
if [ -z "$CLEAN_BIN" ] || [ ! -x "$CLEAN_BIN" ]; then
  skip no-clean-binary "clean binary not found (build: cargo build --locked --release -p clean, or set CLEAN_BIN)"
fi
if ! "$CLEAN_BIN" check --help 2>/dev/null | grep -q -- "--parse-only"; then
  skip stale-clean-binary "$CLEAN_BIN does not support 'check --parse-only' (rebuild at HEAD)"
fi

# --- Mathlib SOURCE checkout ------------------------------------------------
ML="${CLEAN_MATHLIB_DIR:-${MATHLIB_CHECKOUT:-}}"
if [ -z "$ML" ]; then
  for cand in data/raw/mathlib4 /tmp/mathlib4; do
    if [ -f "$cand/Mathlib/Logic/Basic.lean" ]; then
      ML="$cand"
      break
    fi
  done
fi
if [ -z "$ML" ] || [ ! -f "$ML/Mathlib/Logic/Basic.lean" ]; then
  skip no-mathlib-source "Mathlib SOURCE checkout not found (set CLEAN_MATHLIB_DIR to a mathlib4 checkout containing Mathlib/*.lean)"
fi

TMP="$(mktemp -d)" || skip no-tmpdir "mktemp failed"
cleanup() { rm -rf "$TMP"; }
trap cleanup EXIT

# --- per-module parse-only runs --------------------------------------------
MEASURED=0
MISSING=0
i=0
: > "$TMP/modules.tsv"
for mod in "${MODULES[@]}"; do
  rel="$(printf '%s' "$mod" | tr '.' '/').lean"
  src="$ML/$rel"
  i=$((i + 1))
  if [ ! -f "$src" ]; then
    MISSING=$((MISSING + 1))
    printf '%s\t%s\tmissing\t\n' "$mod" "$rel" >> "$TMP/modules.tsv"
    continue
  fi
  out="$TMP/$i.json"
  # --parse-only exits nonzero when any declaration failed to parse; the JSON
  # report is always printed first, so tolerate the exit code and let the
  # aggregator validate the payload (schema check) instead.
  "$CLEAN_BIN" check --parse-only --json "$src" > "$out" 2> "$TMP/$i.stderr" || true
  if [ -s "$out" ]; then
    MEASURED=$((MEASURED + 1))
    printf '%s\t%s\tmeasured\t%s\n' "$mod" "$rel" "$out" >> "$TMP/modules.tsv"
  else
    printf '%s\t%s\terror\t\n' "$mod" "$rel" >> "$TMP/modules.tsv"
  fi
done

if [ "$MEASURED" -eq 0 ]; then
  skip modules-not-found "corpus at $ML but none of the ${#MODULES[@]} cross-section modules produced a parse report"
fi

# --- aggregate --------------------------------------------------------------
mkdir -p reports
if ! python3 - "$TMP/modules.tsv" "$REPORT" "$ML" <<'PY'
import json
import re
import subprocess
import sys
from collections import Counter
from datetime import datetime, timezone

tsv_path, report_path, ml_dir = sys.argv[1], sys.argv[2], sys.argv[3]

def git_head():
    try:
        out = subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            capture_output=True, text=True, check=False,
        ).stdout.strip()
        return out or "unknown"
    except OSError:
        return "unknown"

modules = []
totals = {
    "decls": 0,
    "parse_ok": 0,
    "rawdecl_recovered": 0,
    "hard_error": 0,
    "recovery_diagnostics": 0,
}
counts = {"measured": 0, "missing": 0, "error": 0}
signatures = Counter()

with open(tsv_path, encoding="utf-8") as fh:
    for line in fh:
        line = line.rstrip("\n")
        if not line:
            continue
        parts = line.split("\t")
        mod, rel, status = parts[0], parts[1], parts[2]
        out_path = parts[3] if len(parts) > 3 else ""
        entry = {"module": mod, "file": rel, "status": status}
        if status == "measured" and out_path:
            rep = None
            try:
                with open(out_path, encoding="utf-8") as jf:
                    rep = json.load(jf)
            except (OSError, json.JSONDecodeError):
                rep = None
            if (not isinstance(rep, dict)
                    or rep.get("schema_version") != "Clean-parse-only-report-v1"):
                entry["status"] = "error"
                counts["error"] += 1
            else:
                counts["measured"] += 1
                for key in totals:
                    entry[key] = int(rep.get(key, 0))
                    totals[key] += entry[key]
                entry["first_errors"] = rep.get("first_errors", [])
                for err in entry["first_errors"]:
                    # Signature: digits normalized so line/column and literal
                    # variation aggregate to one row.
                    signatures[re.sub(r"\d+", "N", err)[:120]] += 1
        elif status == "missing":
            counts["missing"] += 1
        else:
            counts["error"] += 1
        modules.append(entry)

parse_rate = round(totals["parse_ok"] / totals["decls"], 4) if totals["decls"] else None
report = {
    "schema": "Clean-parser-mathlib-parse-rate-v1",
    "generated_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
    "clean_git_head": git_head(),
    "mathlib_dir": ml_dir,
    "module_list_source": (
        "docs/plans/MATHLIB_KV_MILESTONE_2026-07-12.md (15 doc-named modules) "
        "+ reconstructed domain spread; full list inlined in "
        "scripts/parser_mathlib_sweep.sh"
    ),
    "semantics": (
        "per-declaration parse outcomes from `clean check --parse-only --json`; "
        "RawDecl recovery placeholders count as failures, never as parses; "
        "recovery_diagnostics are separate completeness debt"
    ),
    "modules_measured": counts["measured"],
    "modules_missing": counts["missing"],
    "modules_error": counts["error"],
    "totals": totals,
    "parse_rate": parse_rate,
    "top_error_signatures": [
        {"signature": sig, "count": n} for sig, n in signatures.most_common(15)
    ],
    "modules": modules,
}
with open(report_path, "w", encoding="utf-8") as fh:
    json.dump(report, fh, indent=2)
    fh.write("\n")
print(
    "parser Mathlib sweep: {m} measured, {miss} missing, {err} error; "
    "decls={d} parse_ok={ok} rawdecl={raw} hard={hard} rate={rate}".format(
        m=counts["measured"], miss=counts["missing"], err=counts["error"],
        d=totals["decls"], ok=totals["parse_ok"],
        raw=totals["rawdecl_recovered"], hard=totals["hard_error"],
        rate=parse_rate,
    )
)
if counts["measured"] == 0:
    sys.exit(3)
PY
then
  fail aggregate "aggregation into $REPORT failed"
fi

echo "wrote $REPORT ($MEASURED measured, $MISSING missing of ${#MODULES[@]} modules)"
verdict measured
