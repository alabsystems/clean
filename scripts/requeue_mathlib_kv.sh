#!/usr/bin/env bash
# Requeue pass for scripts/rebuild_mathlib_kv.sh --strategy chunked.
#
# The chunked strategy records RAM/timeout-killed chunks in
# $OUT/requeue.txt and moves on. This driver re-runs EXACTLY those
# modules through the memory-adaptive single-pass discipline (halve the
# piece on death, down to a floor), then reports what to re-aggregate.
# Chunks of ~1000 modules routinely die at a ~24GiB RSS ceiling; pieces
# of a few hundred survive — measured 2026-08-08 (chunks 2,3,4,5,7 of 8
# died; 1,6,8 completed).
#
# Usage: scripts/requeue_mathlib_kv.sh [--out DIR] [--batch N] [--floor N]
#   --out    the rebuild OUT_BASE holding requeue.txt (default: the
#            standard data/mathverse-library/mathlib-kv)
#   --batch  initial piece size (default 300 — deliberately below the
#            measured death threshold, unlike the fresh-run default 600)
#   --floor  don't split below this many modules (default 60)
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=lib/mathlib_rebuild_lib.sh
source "$REPO_ROOT/scripts/lib/mathlib_rebuild_lib.sh"
# shellcheck source=lib/stamp_mem_governor.sh
source "$REPO_ROOT/scripts/lib/stamp_mem_governor.sh"

OUT_BASE="$REPO_ROOT/data/mathverse-library/mathlib-kv"
BATCH=300
FLOOR=60
TIMEOUT="${CHUNK_TIMEOUT_SECS:-10800}"
ELIDE="${ELIDE:-opaque-and-theorem}"
# The requeued chunks are the DEEP end of Mathlib: their import closures
# exceed the default 1500-module single-pass cap (measured: TrivSqZeroExt
# needs more; rc=1 at 1GiB, NOT a memory kill). Raise the cap and let the
# RSS governor + halving own the memory risk instead.
export CLEAN_MAX_CLOSURE_MODULES="${CLEAN_MAX_CLOSURE_MODULES:-9000}"
while [ $# -gt 0 ]; do
  case "$1" in
    --out)   OUT_BASE="${2:?}"; shift 2;;
    --batch) BATCH="${2:?}"; shift 2;;
    --floor) FLOOR="${2:?}"; shift 2;;
    *) echo "requeue_mathlib_kv: unknown arg $1" >&2; exit 2;;
  esac
done

REQ="$OUT_BASE/requeue.txt"
[ -s "$REQ" ] || { echo "[requeue] nothing to do: $REQ absent or empty"; exit 0; }

# Single-instance lock: a concurrent driver's startup seed re-split deletes
# the running driver's fragment files mid-walk (measured: crossed relaunches
# wiped each other, EXIT:66). PID-stamped; a stale lock from a dead driver
# is reclaimed.
LOCK="$OUT_BASE/requeue.lock"
if [ -f "$LOCK" ]; then
  oldpid="$(cat "$LOCK" 2>/dev/null || true)"
  if [ -n "$oldpid" ] && kill -0 "$oldpid" 2>/dev/null; then
    echo "[requeue] another driver is running (pid $oldpid) — refusing" >&2
    exit 3
  fi
  echo "[requeue] reclaiming stale lock (pid ${oldpid:-?})"
fi
echo $$ > "$LOCK"
trap 'rm -f "$LOCK"' EXIT

# Resolution is dry-run tolerant (the lib resolves relative to its own dir;
# set CLEAN_BIN / MATHLIB_CHECKOUT env pins when auto-resolution misses —
# same contract as rebuild_mathlib_kv.sh).
CLEAN_BIN="${CLEAN_BIN:-$(mlr_resolve_clean_bin || true)}"
CHECKOUT="$(mlr_resolve_checkout || true)"
MLLIB=""
[ -n "$CHECKOUT" ] && MLLIB="$(mlr_mllib "$CHECKOUT")"
[ -n "$CLEAN_BIN" ] && [ -x "$CLEAN_BIN" ]   || { echo "[requeue] no clean binary (set CLEAN_BIN)" >&2; exit 1; }
[ -n "$MLLIB" ] && [ -d "$MLLIB" ]   || { echo "[requeue] no Mathlib closure root (set MATHLIB_CHECKOUT)" >&2; exit 1; }

RQDIR="$OUT_BASE/requeue_pieces"
mkdir -p "$RQDIR"
ALL="$RQDIR/modules.txt"
# The requeue entries are chunk FILES (module lists); concatenate them.
: > "$ALL"
while IFS= read -r chunk; do
  [ -f "$chunk" ] && cat "$chunk" >> "$ALL"
done < "$REQ"
sort -u "$ALL" -o "$ALL"
TOTAL=$(wc -l < "$ALL" | tr -d ' ')
echo "[requeue] $TOTAL modules from $(wc -l < "$REQ" | tr -d ' ') requeued chunks; batch=$BATCH floor=$FLOOR"

run_piece() {
  local pf="$1" n h od log
  n=$(wc -l < "$pf" | tr -d ' ')
  h=$(md5 -q "$pf" 2>/dev/null || md5sum "$pf" | cut -d' ' -f1)
  od="$RQDIR/p_${h}"; log="$od.log"
  grep -q '"kernel_verified"' "$log" 2>/dev/null && { echo "[requeue] skip(done) $n mods $h"; return 0; }
  mkdir -p "$od"
  echo "[requeue] run $n mods $h $(date +%H:%M:%S)"
  # The governor lib is written for a NON-strict caller: its poll loop uses
  # bare `[ -n "$rss" ] && [ ... ]` lists whose benign-false evaluations
  # abort a `set -e` script (observed: instant empty-log death on the first
  # poll tick). Run it in a relaxed section; run_piece judges success by
  # the log content, not the return code.
  set +e
  stamp_wait_for_free_ram
  # shellcheck disable=SC2046
  stamp_run_governed_chunk "$log" "$TIMEOUT" -- \
      "$CLEAN_BIN" mathverse stamp-verified $(cat "$pf") \
      --out-dir "$od" --closure-root "$MLLIB" --closure-elide "$ELIDE" \
      --single-pass --manifest "$od.json" --json
  set -e
  if grep -q '"kernel_verified"' "$log" 2>/dev/null; then return 0; fi
  if [ "$n" -le "$FLOOR" ]; then
    # Floor-size piece died (eager closure of the DEEPEST modules exceeds
    # the RSS ceiling at any piece size). Retry ONCE with the demand-paged
    # lazy closure (CLEAN_LAZY_CLOSURE=1) — scripts/kv_invariance_gate.sh
    # proves the KernelVerified name set identical between the two loaders,
    # so this changes memory behavior only.
    echo "[requeue]   floor piece died — LAZY-closure retry ($n mods) $h"
    set +e
    stamp_wait_for_free_ram
    # shellcheck disable=SC2046
    CLEAN_LAZY_CLOSURE=1 CLEAN_BUILD_CLOSURE_CACHE=1 \
        stamp_run_governed_chunk "$log.lazy" "$TIMEOUT" -- \
        "$CLEAN_BIN" mathverse stamp-verified $(cat "$pf") \
        --out-dir "$od" --closure-root "$MLLIB" --closure-elide "$ELIDE" \
        --single-pass --manifest "$od.json" --json
    set -e
    if grep -q '"kernel_verified"' "$log.lazy" 2>/dev/null; then
      cat "$log.lazy" >> "$log"
      return 0
    fi
    echo "[requeue]   DIED at floor ($n mods) — recording uncovered $h"
    printf '{"kernel_verified":0,"total":%s,"axiom_fallback":0,"failed":%s,"uncovered":true}\n' "$n" "$n" >> "$log"
    return 0
  fi
  echo "[requeue]   DIED ($n mods) — splitting in half"
  local mid=$(( (n + 1) / 2 ))
  split -l "$mid" "$pf" "$pf.s"
  local half
  for half in "$pf".s*; do
    # bash passes the literal pattern through when no fragment matched
    # (nullglob unset) — and a resumed run may find stale/partial splits.
    [ -f "$half" ] || continue
    run_piece "$half"
  done
}

rm -f "$RQDIR"/seed_* 2>/dev/null
split -l "$BATCH" "$ALL" "$RQDIR/seed_"
for sf in "$RQDIR"/seed_*; do
  case "$sf" in *.s*) continue;; esac
  run_piece "$sf"
done

echo "[requeue] DONE. Piece manifests under $RQDIR/*.json — re-aggregate with"
echo "          the AGGREGATE step in docs/plans/REBUILD_MATHLIB_KV.md."
