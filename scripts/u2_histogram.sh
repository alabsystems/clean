#!/usr/bin/env bash
# u2_histogram.sh — U2 rung 0b: the real-source level-constraint histogram
# (designs/2026-08-08-u2-universe-polymorphism-ladder.md, brick U0).
#
# Elaborates one (or more) universe-polymorphic Mathlib SOURCE file(s)
# with CLEAN_U2_HISTOGRAM=1 and aggregates every emitted `[u2hist]`
# event into a ranked per-class histogram — the artifact that sizes
# rung 3 (algebraic solver + postponement) and rung 4
# (levelMVarToParam) against real source instead of guesses.
#
# Classes (emitted by crates/clean-elab/src/u2_histogram.rs):
#   occurs-check             self-referential level equation (postponement lane)
#   algebraic-maximax        Max/IMax with no metavar head (rung 3 proper)
#   rigid-blocked            a rigid declared param blocks the arm
#   shape-residual           anything else with params (rung 3 postponement)
#   concrete-conflict        genuinely unequal ground levels (real errors)
#   algebraic-defeq-saved    solved ONLY by normalization (near-miss signal)
#   compound-legacy-only     assignment invisible to union-find (rung 1 debt)
#   generalized-fresh-param  fresh u_N survives onto a registered def (rung 4)
#
# Usage: scripts/u2_histogram.sh [--bin path] [file.lean ...]
# Default target: the checked-in Mathlib source probe list below.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${REPO_ROOT}/target/release/clean"
if [[ "${1:-}" == "--bin" ]]; then
  BIN="${2:?--bin requires a path argument}"; shift 2
fi
[[ -x "$BIN" ]] || { echo "[u2-hist] FAIL: no executable clean binary at $BIN" >&2; exit 1; }

FILES=("$@")
if [[ ${#FILES[@]} -eq 0 ]]; then
  # Default probes: dependency-light, universe-polymorphic Mathlib source.
  FILES=(
    "${REPO_ROOT}/data/raw/mathlib4/Mathlib/Logic/ExistsUnique.lean"
    "${REPO_ROOT}/data/raw/mathlib4/Mathlib/Logic/Nonempty.lean"
    "${REPO_ROOT}/data/raw/mathlib4/Mathlib/Logic/Function/Defs.lean"
  )
fi

OUT_JSON="${REPO_ROOT}/reports/u2-constraint-histogram.json"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

: > "$WORK/events.txt"
: > "$WORK/runs.txt"
for f in "${FILES[@]}"; do
  [[ -f "$f" ]] || { echo "[u2-hist] FAIL: no such file: $f" >&2; exit 1; }
  echo "[u2-hist] elaborating $f"
  rc=0
  # --imports-prefer-olean: imports load from prebuilt .oleans (Lean's own
  # import model); WITHOUT it a Mathlib source file recursively elaborates
  # its entire transitive SOURCE closure and stalls for hours in
  # regenerate_missing_no_confusion (measured 2026-08-08).
  CLEAN_U2_HISTOGRAM=1 "$BIN" check --prelude builtin --imports-prefer-olean "$f" \
    > "$WORK/stdout.txt" 2> "$WORK/stderr.txt" || rc=$?
  grep '^\[u2hist\]' "$WORK/stderr.txt" >> "$WORK/events.txt" || true
  summary="$(grep -E "passed, .* failed" "$WORK/stdout.txt" | tail -1 | sed 's/^ *//' || true)"
  echo "$f|rc=$rc|$summary" >> "$WORK/runs.txt"
  echo "[u2-hist]   rc=$rc ${summary:-<no summary>} ($(grep -c '^\[u2hist\]' "$WORK/stderr.txt" || true) events)"
done

python3 - "$OUT_JSON" "$WORK/events.txt" "$WORK/runs.txt" "$(git -C "$REPO_ROOT" rev-parse HEAD)" <<'PY'
import json, sys, re
from collections import Counter

out, events_path, runs_path, sha = sys.argv[1:5]
by_class, by_class_site, samples = Counter(), Counter(), {}
n = 0
for line in open(events_path):
    m = re.match(r"\[u2hist\] class=(\S+) site=(\S+) detail=(.*)", line.strip())
    if not m:
        continue
    n += 1
    cls, site, detail = m.groups()
    by_class[cls] += 1
    by_class_site[f"{cls}@{site}"] += 1
    samples.setdefault(cls, detail[:200])

runs = []
for line in open(runs_path):
    f, rc, summary = line.rstrip("\n").split("|", 2)
    runs.append({"file": f, "rc": int(rc.removeprefix("rc=")), "summary": summary})

report = {
    "schema": "u2-constraint-histogram-v1",
    "commit": sha,
    "gate_command": "scripts/u2_histogram.sh",
    "total_events": n,
    "ranked": [
        {"class": c, "count": k, "sample": samples[c]}
        for c, k in by_class.most_common()
    ],
    "by_class_site": dict(by_class_site.most_common()),
    "runs": runs,
    "note": "Sizes U2 rung 3 (algebraic-maximax + shape-residual + occurs-check), "
            "rung 4 (generalized-fresh-param), rung 1 (compound-legacy-only). "
            "concrete-conflict lines are genuine mismatches, not solver gaps. "
            "Counts are event-per-attempt, not per-declaration.",
}
json.dump(report, open(out, "w"), indent=2)
print(f"[u2-hist] wrote {out}: {n} events, "
      + ", ".join(f"{c}={k}" for c, k in by_class.most_common()))
PY
