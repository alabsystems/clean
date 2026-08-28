#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Calibrate `clean check --decl-budget`.
#
# WHY THIS EXISTS. The ambient per-declaration budget only helps if its default
# is large enough that no declaration which currently finishes is turned into a
# `diverged` row. "Large enough" is a measurement, not a guess: this script
# measures it.
#
# HOW. `clean check` is run over a corpus with the budget set to `u64::MAX` —
# armed, so the counter runs, but unreachable, so nothing is ever cut off — and
# `CLEAN_CHECK_DECL_BUDGET_TRACE=1` prints the ticks each declaration actually
# spent. The maximum over the corpus is the floor any honest default must clear.
#
# OUTPUT: reports/decl-budget-calibration.json (max / p99 / total per file, plus
# the single heaviest declaration seen).
#
# USAGE:
#   scripts/decl_budget_calibrate.sh [extra .lean paths...]
#
# The corpus is the repo's own `demos/` and `tests/fixtures/` .lean files plus
# anything named on the command line — point it at a real Mathlib module to
# calibrate against a file that actually stresses the elaborator.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# `u64::MAX`: the budget is ARMED (so the counter decrements and
# `declaration_budget_used()` is meaningful) but unreachable (so no declaration
# can be cut off and the measurement cannot perturb the verdicts it measures).
UNREACHABLE_BUDGET=18446744073709551615

CLEAN_BIN="${CLEAN_BIN:-$ROOT/target/release/clean}"
# Extra flags handed to every `clean check`. A Mathlib SOURCE sweep needs
# `--imports-prefer-olean`, without which every module fails its fail-closed
# import check in milliseconds and contributes ZERO declarations to the census
# — measured 2026-08-27: `Mathlib/Logic/Basic.lean` was in the corpus and
# appears in no `per_file` row.
CHECK_FLAGS="${CHECK_FLAGS:-}"
OUT="${OUT:-$ROOT/reports/decl-budget-calibration.json}"
TRACE_DIR="$(mktemp -d)"
trap 'rm -rf "$TRACE_DIR"' EXIT

if [ ! -x "$CLEAN_BIN" ]; then
  echo "decl_budget_calibrate: no clean binary at $CLEAN_BIN" >&2
  echo "  build it first:  scripts/heavy_gate.sh run 14 clean-release -- cargo build --locked --release -p clean" >&2
  exit 1
fi

# `mapfile` is bash 4+; macOS ships bash 3.2 as /bin/bash, and this script is
# run there. Measured 2026-08-27: `mapfile: command not found`, exit 127, on
# the very first real run. Read the corpus with a portable while-read loop.

# Which trees to sweep. Overridable because the full default corpus is not
# always affordable: measured 2026-08-27, `demos tests/fixtures` is 125 files
# and did NOT finish inside a 900 s bound — some fixtures are deliberately
# pathological. Narrow it when you need an artifact in budget, and say in the
# report which roots you used (the script records `corpus_roots`).
CORPUS_ROOTS="${CORPUS_ROOTS:-demos tests/fixtures}"

CORPUS=()
while IFS= read -r f; do
  [ -n "$f" ] && CORPUS+=("$f")
done < <({ find $CORPUS_ROOTS -name '*.lean' -type f 2>/dev/null || true; } | sort)
for extra in "$@"; do
  CORPUS+=("$extra")
done

if [ "${#CORPUS[@]}" -eq 0 ]; then
  echo "decl_budget_calibrate: empty corpus" >&2
  exit 1
fi

echo "decl_budget_calibrate: ${#CORPUS[@]} file(s), budget=$UNREACHABLE_BUDGET (unreachable)" >&2

i=0
for f in "${CORPUS[@]}"; do
  i=$((i + 1))
  # A file may legitimately fail to check; we want its per-declaration tick
  # trace either way, so the exit code is not fatal here.
  CLEAN_CHECK_DECL_BUDGET_TRACE=1 \
    "$CLEAN_BIN" check $CHECK_FLAGS --decl-budget "$UNREACHABLE_BUDGET" "$f" \
    >/dev/null 2>"$TRACE_DIR/$i.trace" || true
  printf '%s\t%s\n' "$i" "$f" >>"$TRACE_DIR/index"
done

python3 - "$TRACE_DIR" "$OUT" "$UNREACHABLE_BUDGET" "$CORPUS_ROOTS" "$CHECK_FLAGS" <<'PY'
import json, os, subprocess, sys

trace_dir, out_path, budget = sys.argv[1], sys.argv[2], int(sys.argv[3])
corpus_roots = sys.argv[4] if len(sys.argv) > 4 else ""
check_flags = sys.argv[5] if len(sys.argv) > 5 else ""

index = {}
with open(os.path.join(trace_dir, "index")) as fh:
    for line in fh:
        idx, path = line.rstrip("\n").split("\t", 1)
        index[idx] = path

per_file = []
all_ticks = []
heaviest = None
for idx, path in sorted(index.items(), key=lambda kv: int(kv[0])):
    ticks = []
    trace = os.path.join(trace_dir, f"{idx}.trace")
    if os.path.exists(trace):
        with open(trace, errors="replace") as fh:
            for line in fh:
                if not line.startswith("decl-budget\t"):
                    continue
                parts = line.rstrip("\n").split("\t")
                if len(parts) != 4:
                    continue
                _, module, name, used = parts
                try:
                    used = int(used)
                except ValueError:
                    continue
                ticks.append(used)
                all_ticks.append(used)
                if heaviest is None or used > heaviest["ticks"]:
                    heaviest = {"file": path, "module": module,
                                "declaration": name, "ticks": used}
    if ticks:
        per_file.append({
            "file": path,
            "declarations": len(ticks),
            "max_ticks": max(ticks),
            "total_ticks": sum(ticks),
        })

all_ticks.sort()


def pct(p):
    if not all_ticks:
        return 0
    k = min(len(all_ticks) - 1, int(round(p * (len(all_ticks) - 1))))
    return all_ticks[k]


try:
    commit = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True,
                            text=True, check=True).stdout.strip()
except Exception:
    commit = "unknown"

report = {
    "schema": "decl-budget-calibration-v1",
    "generated_at_commit": commit,
    "generated_by": "scripts/decl_budget_calibrate.sh",
    "method": (
        "clean check run with --decl-budget u64::MAX (armed but unreachable) and "
        "CLEAN_CHECK_DECL_BUDGET_TRACE=1, which prints the ambient ticks each "
        "top-level declaration spent. No declaration can be cut off at this "
        "budget, so the measurement cannot perturb the verdicts it measures."
    ),
    "corpus_roots": corpus_roots,
    "check_flags": check_flags,
    "measurement_budget": budget,
    "files_measured": len(per_file),
    "declarations_measured": len(all_ticks),
    "max_ticks": all_ticks[-1] if all_ticks else 0,
    "p99_ticks": pct(0.99),
    "p50_ticks": pct(0.50),
    "heaviest_declaration": heaviest,
    "per_file": per_file,
}

os.makedirs(os.path.dirname(out_path), exist_ok=True)
with open(out_path, "w") as fh:
    json.dump(report, fh, indent=2)
    fh.write("\n")

print(f"decl_budget_calibrate: {len(all_ticks)} declarations over "
      f"{len(per_file)} file(s); max={report['max_ticks']} "
      f"p99={report['p99_ticks']} p50={report['p50_ticks']}", file=sys.stderr)
print(f"decl_budget_calibrate: wrote {out_path}", file=sys.stderr)
PY
