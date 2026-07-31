#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# ============================================================================
# CANONICAL Mathlib KernelVerified rebuild driver.
# ============================================================================
#
# ONE portable entry point that re-checks every Mathlib proof term through
# Clean's kernel (`clean mathverse stamp-verified`) and stamps each constant the
# kernel genuinely accepts as `KernelVerified`. Replaces the former ad-hoc
# stamp_mathlib_{batched,kv,kv_rerun,singlepass,heavy,tail}.sh scripts (removed):
# it auto-detects the corpus (no hardcoded contributor paths), sources the shared
# OOM governor, and — critically — wires the two bounded-memory knobs the code
# already supports but NO previous script exported:
#
#   CLEAN_REQUIRE_BOUNDED           demand-paged, fail-closed loader (no silent
#                                   eager ~100GB fallback) — the parallel path.
#   CLEAN_KERNEL_HEARTBEAT_ESCALATE recoverable two-tier heartbeat: a slow proof
#                                   becomes axiom_fallback and the run CONTINUES
#                                   instead of dying on the wall-clock watchdog.
#
# Targets = Mathlib modules (their proofs are the goal). Lean core / Batteries /
# Aesop / etc. are the TRUSTED imported closure (loaded, never re-stamped).
#
# See docs/plans/REBUILD_MATHLIB_KV.md for the full runbook and knob reference.
#
# Usage:
#   scripts/rebuild_mathlib_kv.sh [--strategy chunked|parallel|single-pass]
#                                 [--chunks N] [--jobs N]
#                                 [--elide opaque-and-theorem|opaque|none]
#                                 [--out-dir DIR] [--gate] [--dry-run]
#
# Strategies:
#   chunked      (default) split modules into N governed chunks; per-chunk RSS/
#                timeout watchdog requeues a runaway instead of panicking. Proven.
#   parallel     one `stamp-verified --parallel` run: demand-paged bounded base
#                + heartbeat escalation + `--jobs`-way fan-out. Fastest; needs the
#                closure to fit under the bounded loader. Sets CLEAN_REQUIRE_BOUNDED=1.
#   single-pass  memory-ADAPTIVE: one persistent env per piece, auto-split a piece
#                that OOMs/times-out down to a floor. Best on a tight-RAM box.
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
# shellcheck source=scripts/lib/mathlib_rebuild_lib.sh
. "$SCRIPT_DIR/lib/mathlib_rebuild_lib.sh"
# shellcheck source=scripts/lib/stamp_mem_governor.sh
. "$SCRIPT_DIR/lib/stamp_mem_governor.sh"

# ----- defaults (every knob is env-overridable; an explicit flag wins) --------
STRATEGY="${STRATEGY:-chunked}"
NCHUNKS="${NCHUNKS:-8}"
JOBS="${JOBS:-}"                                        # empty => let the CLI pick
ELIDE="${CLOSURE_ELIDE:-opaque-and-theorem}"            # validated production default
OUT_BASE="${OUT:-$REPO_ROOT/data/mathverse-library/mathlib-kv}"
DRY_RUN=0
RUN_GATE=0

# Operational budgets (NOT trust boundaries — a bigger budget only lets a CORRECT
# kernel check finish; add_decl can never accept an invalid proof).
export CLEAN_KERNEL_HEARTBEAT="${CLEAN_KERNEL_HEARTBEAT:-50000000}"
export CLEAN_KERNEL_HEARTBEAT_ESCALATE="${CLEAN_KERNEL_HEARTBEAT_ESCALATE:-100000000}"
export CLEAN_MAX_CLOSURE_MODULES="${CLEAN_MAX_CLOSURE_MODULES:-9000}"
CHUNK_TIMEOUT_SECS="${CHUNK_TIMEOUT_SECS:-10800}"       # 3h per chunk/piece
BATCH="${BATCH:-600}"                                   # single-pass initial piece
FLOOR="${FLOOR:-90}"                                    # single-pass split floor

usage() { sed -n '2,60p' "$0" | sed 's/^# \{0,1\}//'; }

while [ $# -gt 0 ]; do
  case "$1" in
    --strategy) STRATEGY="${2:?}"; shift 2;;
    --chunks)   NCHUNKS="${2:?}"; shift 2;;
    --jobs)     JOBS="${2:?}"; shift 2;;
    --elide)    ELIDE="${2:?}"; shift 2;;
    --out-dir)  OUT_BASE="${2:?}"; shift 2;;
    --gate)     RUN_GATE=1; shift;;
    --dry-run)  DRY_RUN=1; shift;;
    -h|--help)  usage; exit 0;;
    *) echo "rebuild_mathlib_kv: unknown argument: $1" >&2; usage; exit 2;;
  esac
done

case "$STRATEGY" in chunked|parallel|single-pass) ;; *)
  echo "rebuild_mathlib_kv: --strategy must be chunked|parallel|single-pass (got '$STRATEGY')" >&2; exit 2;; esac
case "$ELIDE" in opaque-and-theorem|opaque|none) ;; *)
  echo "rebuild_mathlib_kv: --elide must be opaque-and-theorem|opaque|none (got '$ELIDE')" >&2; exit 2;; esac

# ----- resolve the environment (dry-run tolerant) ----------------------------
CLEAN_BIN="$(mlr_resolve_clean_bin || true)"
CHECKOUT="$(mlr_resolve_checkout || true)"
MLLIB=""; MLROOT=""; LEAN_PATH_ROOTS=0
if [ -n "$CHECKOUT" ]; then
  MLLIB="$(mlr_mllib "$CHECKOUT")"; MLROOT="$MLLIB/Mathlib"
  export LEAN_PATH="$(mlr_build_lean_path "$CHECKOUT")"
  LEAN_PATH_ROOTS="$(mlr_lean_path_roots "$LEAN_PATH")"
fi

# ----- plan (always printed; the whole of --dry-run) -------------------------
print_plan() {
  echo "=== rebuild_mathlib_kv plan ==================================================="
  echo "  strategy            : $STRATEGY"
  echo "  clean binary        : ${CLEAN_BIN:-<NOT FOUND — cargo build -p clean-cli --release --bin clean>}"
  echo "  mathlib checkout    : ${CHECKOUT:-<NOT FOUND — scripts/setup_mathlib_oleans.sh (or set MATHLIB_CHECKOUT)>}"
  echo "  closure-root        : ${MLLIB:-<n/a>}"
  echo "  LEAN_PATH roots     : $LEAN_PATH_ROOTS"
  echo "  out dir             : $OUT_BASE"
  echo "  closure elide       : $ELIDE"
  case "$STRATEGY" in
    chunked)     echo "  chunks              : $NCHUNKS   (per-chunk watchdog ${CHUNK_TIMEOUT_SECS}s)";;
    parallel)    echo "  jobs                : ${JOBS:-<cli default>}   CLEAN_REQUIRE_BOUNDED=${CLEAN_REQUIRE_BOUNDED:-1}";;
    single-pass) echo "  initial piece / floor: $BATCH / $FLOOR   (per-piece watchdog ${CHUNK_TIMEOUT_SECS}s)";;
  esac
  echo "  CLEAN_KERNEL_HEARTBEAT          : $CLEAN_KERNEL_HEARTBEAT"
  echo "  CLEAN_KERNEL_HEARTBEAT_ESCALATE : $CLEAN_KERNEL_HEARTBEAT_ESCALATE"
  echo "  CLEAN_MAX_CLOSURE_MODULES       : $CLEAN_MAX_CLOSURE_MODULES"
  echo "  run gate after      : $([ "$RUN_GATE" = 1 ] && echo yes || echo no)"
  echo "==============================================================================="
}

print_plan
if [ "$DRY_RUN" = 1 ]; then
  echo "[dry-run] plan only; nothing executed."
  exit 0
fi

# ----- preconditions for a real run ------------------------------------------
[ -n "$CLEAN_BIN" ] || { echo "ERROR: no clean binary; build it: cargo build -p clean-cli --release --bin clean" >&2; exit 1; }
[ -n "$CHECKOUT"  ] || { echo "ERROR: no Mathlib checkout; run scripts/setup_mathlib_oleans.sh (or set MATHLIB_CHECKOUT)" >&2; exit 1; }
[ -d "$MLROOT"    ] || { echo "ERROR: no Mathlib oleans under $MLROOT" >&2; exit 1; }

# One system-wide lock so two rebuild/stamp harnesses can never overcommit RAM
# (the 2026-06-22 concurrent-run OOM). Shared with the legacy stamp scripts.
stamp_acquire_global_lock || exit 1

mkdir -p "$OUT_BASE"
find "$MLROOT" -name '*.olean' | sort > "$OUT_BASE/all_oleans.txt"
TOTAL=$(wc -l < "$OUT_BASE/all_oleans.txt" | tr -d ' ')
echo "[rebuild] $TOTAL Mathlib oleans, strategy=$STRATEGY, elide=$ELIDE, out=$OUT_BASE"

# ----- strategy: chunked -----------------------------------------------------
run_chunked() {
  local per ci=0 chunk outd man log
  per=$(( (TOTAL + NCHUNKS - 1) / NCHUNKS ))
  rm -f "$OUT_BASE"/chunk_a* 2>/dev/null
  split -l "$per" "$OUT_BASE/all_oleans.txt" "$OUT_BASE/chunk_"
  for chunk in "$OUT_BASE"/chunk_*; do
    case "$chunk" in *.log|*.txt|*.json) continue;; esac
    ci=$((ci+1))
    outd="$OUT_BASE/shards_$(printf '%02d' "$ci")"
    man="$OUT_BASE/kv_$(printf '%02d' "$ci").json"
    log="$OUT_BASE/chunk_$(printf '%02d' "$ci").log"
    mkdir -p "$outd"
    echo "[rebuild] chunk $ci/$NCHUNKS -> $outd ($(wc -l < "$chunk" | tr -d ' ') modules) $(date +%H:%M:%S)"
    stamp_wait_for_free_ram
    # shellcheck disable=SC2046
    stamp_run_governed_chunk "$log" "$CHUNK_TIMEOUT_SECS" -- \
        "$CLEAN_BIN" mathverse stamp-verified $(cat "$chunk") \
        --out-dir "$outd" --closure-root "$MLLIB" --closure-elide "$ELIDE" \
        --manifest "$man" --json
    echo "[rebuild] chunk $ci done (status=$STAMP_LAST_STATUS, peak=$((STAMP_LAST_PEAK_KB/1048576))GiB) $(date +%H:%M:%S)"
    [ "$STAMP_LAST_STATUS" = "ok" ] || echo "$chunk" >> "$OUT_BASE/requeue.txt"
  done
}

# ----- strategy: parallel (bounded, fail-closed) -----------------------------
run_parallel() {
  local outd="$OUT_BASE/shards_parallel" man="$OUT_BASE/kv_parallel.json" log="$OUT_BASE/parallel.log"
  local jobs_flag=""
  [ -n "$JOBS" ] && jobs_flag="--jobs $JOBS"
  # Fail-closed on the bounded loader: refuse to silently re-inflate to the eager
  # ~100GB base if demand-paging can't cover the closure. Operator can override
  # by exporting CLEAN_REQUIRE_BOUNDED=0 before invoking.
  export CLEAN_REQUIRE_BOUNDED="${CLEAN_REQUIRE_BOUNDED:-1}"
  mkdir -p "$outd"
  echo "[rebuild] parallel run (bounded=$CLEAN_REQUIRE_BOUNDED, jobs=${JOBS:-cli-default}, escalate=$CLEAN_KERNEL_HEARTBEAT_ESCALATE)"
  stamp_wait_for_free_ram
  # shellcheck disable=SC2046
  stamp_run_governed_chunk "$log" "$CHUNK_TIMEOUT_SECS" -- \
      "$CLEAN_BIN" mathverse stamp-verified $(cat "$OUT_BASE/all_oleans.txt") \
      --out-dir "$outd" --closure-root "$MLLIB" --closure-elide "$ELIDE" \
      --parallel $jobs_flag --incremental --manifest "$man" --json
  echo "[rebuild] parallel done (status=$STAMP_LAST_STATUS, peak=$((STAMP_LAST_PEAK_KB/1048576))GiB)"
}

# ----- strategy: single-pass (memory-adaptive split) -------------------------
run_piece() {
  local pf="$1" n h od log mid
  n=$(wc -l < "$pf" | tr -d ' ')
  h=$(md5 -q "$pf" 2>/dev/null || md5sum "$pf" | cut -d' ' -f1)
  od="$OUT_BASE/pieces/p_${h}"; log="$od.log"
  grep -q '"kernel_verified"' "$log" 2>/dev/null && { echo "[sp] skip(done) $n mods $h"; return 0; }
  mkdir -p "$od"
  echo "[sp] run $n mods $h"
  stamp_wait_for_free_ram
  # shellcheck disable=SC2046
  stamp_run_governed_chunk "$log" "$CHUNK_TIMEOUT_SECS" -- \
      "$CLEAN_BIN" mathverse stamp-verified $(cat "$pf") \
      --out-dir "$od" --closure-root "$MLLIB" --closure-elide "$ELIDE" \
      --single-pass --manifest "$od.json" --json
  if grep -q '"kernel_verified"' "$log" 2>/dev/null; then return 0; fi
  if [ "$n" -le "$FLOOR" ]; then
    echo "[sp]   DIED at floor ($n mods) — recording uncovered $h"
    printf '{"kernel_verified":0,"total":%s,"axiom_fallback":0,"failed":%s,"uncovered":true}\n' "$n" "$n" >> "$log"
    return 0
  fi
  echo "[sp]   DIED ($n mods) — splitting in half"
  mid=$(( (n + 1) / 2 ))
  split -l "$mid" "$pf" "$pf.s"
  for half in "$pf".s*; do run_piece "$half"; done
}
run_single_pass() {
  mkdir -p "$OUT_BASE/pieces"
  rm -f "$OUT_BASE"/seed_* 2>/dev/null
  split -l "$BATCH" "$OUT_BASE/all_oleans.txt" "$OUT_BASE/seed_"
  local sf
  for sf in "$OUT_BASE"/seed_*; do run_piece "$sf"; done
}

case "$STRATEGY" in
  chunked)     run_chunked;;
  parallel)    run_parallel;;
  single-pass) run_single_pass;;
esac

# ----- aggregate (strategy-agnostic: any *.log under OUT_BASE with a summary) -
echo "[rebuild] aggregating $(date +%H:%M:%S)"
python3 - "$OUT_BASE" <<'PY'
import json, os, sys
base = sys.argv[1]
agg = dict(total=0, kernel_verified=0, axiom_accepted=0, axiom_fallback=0,
           failed=0, stored_kernel_verified=0, uncovered=0, pieces=0)

def summaries(txt):
    """Yield every top-level {...} block via brace-depth scan (handles the
    nested summary object; the governor also appends small {...} fragments)."""
    depth = 0; start = -1
    for i, ch in enumerate(txt):
        if ch == '{':
            if depth == 0:
                start = i
            depth += 1
        elif ch == '}' and depth > 0:
            depth -= 1
            if depth == 0 and start >= 0:
                yield txt[start:i + 1]

for root, _, files in os.walk(base):
    for fn in files:
        if not fn.endswith('.log'):
            continue
        try:
            txt = open(os.path.join(root, fn), errors='ignore').read()
        except OSError:
            continue
        # The LAST parseable block carrying 'kernel_verified' is the run summary
        # (later governor fragments like {"timed_out":true} lack that key).
        d = None
        for blk in summaries(txt):
            try:
                cand = json.loads(blk)
            except ValueError:
                continue
            if isinstance(cand, dict) and 'kernel_verified' in cand:
                d = cand
        if d is None:
            continue
        agg['pieces'] += 1
        for k in ('total', 'kernel_verified', 'axiom_accepted', 'axiom_fallback',
                  'failed', 'stored_kernel_verified'):
            agg[k] += d.get(k, 0) or 0
        if d.get('uncovered'):
            agg['uncovered'] += d.get('total', 0) or 0
t = agg['total'] or 1
agg['kernel_verified_pct'] = round(100 * agg['kernel_verified'] / t, 2)
print("=== AGGREGATE MATHLIB KERNEL-VERIFICATION ===")
print(json.dumps(agg, indent=2))
print(f"kernel_verified rate: {agg['kernel_verified_pct']}%  "
      f"(KernelVerified = Clean's kernel re-checked the proof term; "
      f"axiom_fallback/failed are NOT verified)")
open(os.path.join(base, 'AGGREGATE.json'), 'w').write(json.dumps(agg, indent=2))
PY

# ----- optional: run the committed non-vacuous KV gate -----------------------
if [ "$RUN_GATE" = 1 ]; then
  echo "[rebuild] running KV ratchet gate (re-stamps the pinned slice)…"
  # The gate takes the heavy global lock's counterpart via a light admission
  # check; release ours first so it does not perma-skip on our own lock.
  rm -rf "${STAMP_LOCK_DIR:-${TMPDIR:-/tmp}/clean-stamp-verified.lock}" 2>/dev/null
  # --gate is an EXPLICIT request to gate, so a skip is a failure here: the gate
  # has six skip-green paths (no binary / no corpus / partial corpus / empty
  # slice / low RAM) and two of them fire routinely. Without this, `--gate` could
  # report success having measured nothing — precisely the failure mode the
  # KV_GATE=<verdict> line exists to make impossible. Override with
  # KV_GATE_REQUIRE_MEASURED=0 if you deliberately want a best-effort run.
  KV_GATE_REQUIRE_MEASURED="${KV_GATE_REQUIRE_MEASURED:-1}" \
    "$SCRIPT_DIR/kv_ratchet_gate.sh"
fi

echo "[rebuild] DONE. Aggregate: $OUT_BASE/AGGREGATE.json"
echo "[rebuild] To ARM the committed ratchet from a full-corpus summary, see"
echo "          docs/plans/REBUILD_MATHLIB_KV.md ('Arming the ratchet')."
