#!/bin/sh
# Stamp the chunks that mathlib_stamp_chunked.sh could not, by SPLITTING THEM
# UNTIL THEY FIT.
#
#   scripts/mathlib_stamp_rescue.sh [--work <dir>] [--floor <n>] [--jobs <n>]
#                                   [--min-free-gb <n>] [--dry-run]
#
# WHY THIS EXISTS. `--chunk N` picks ONE size for the whole library, and Mathlib
# is not uniform: chunk_ac carries 30 `Algebra/Category/*` modules whose closure
# needed ~28 GB against 36 GB physical, and it was SIGKILLed by jetsam three
# times at 100 modules while its neighbours finished in 13 minutes. A single
# global chunk size is therefore always wrong somewhere — too big for the
# CategoryTheory-shaped subtrees, needlessly small everywhere else.
#
# A failed chunk is not a rounding error. The goal is that EVERY Mathlib module
# is citable; 100 modules lost to an OOM is 100 modules a proof cannot cite. The
# main script already re-runs failed chunks under `--resume`, but re-running the
# same 100 modules at the same size just reproduces the same OOM. This retries
# them SMALLER: halve, stamp the halves, and recurse on whichever half still
# fails, down to `--floor` modules. Peak RSS is dominated by the closure, which
# shrinks with the target set, so halving is the lever that actually moves it.
#
# WHAT COUNTS AS DONE. A chunk's `done_` mark is written only when EVERY one of
# its sub-splits succeeded, and it records the summed KV so the main script's
# accounting is unchanged. A partially-rescued chunk stays un-marked and is
# retried next time — never silently counted.
#
# ONE HEAVY JOB AT A TIME. This refuses to start while a chunked stamp is
# running. Two memory-hungry stamps on one machine is how the 2026-08-01 run
# lost chunks in the first place: the second job's pages evict the first's into
# the compressor, and the evicted one thrashes at ~4% CPU until something dies.
set -eu

REPO="${CLEAN_REPO:-$HOME/clean}"
MLROOT="${MLROOT:-$HOME/mathlib4}"
MLLIB="$MLROOT/.lake/build/lib/lean"
WORK="${WORK:-$HOME/ml-full}"
FLOOR=13
JOBS=2
MIN_FREE_GB=10
DRY=0

while [ $# -gt 0 ]; do
  case "$1" in
    --work)  WORK="$2"; shift 2 ;;
    --floor) FLOOR="$2"; shift 2 ;;
    --jobs)  JOBS="$2"; shift 2 ;;
    --min-free-gb) MIN_FREE_GB="$2"; shift 2 ;;
    --dry-run) DRY=1; shift ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done

SHARDS="$WORK/shards"; EVID="$WORK/evidence"
CLEAN_BIN="$REPO/target/release/clean"
[ -x "$CLEAN_BIN" ] || { echo "FAIL  no $CLEAN_BIN" >&2; exit 1; }
[ -d "$EVID" ] || { echo "FAIL  no evidence dir at $EVID" >&2; exit 1; }

if pgrep -f "mathlib_stamp_chunked" >/dev/null 2>&1; then
  echo "FAIL  a chunked stamp is running. Rescue is memory-hungry and must not"
  echo "      share the machine with it — wait for it to finish, then re-run."
  exit 1
fi

TCLIB=$(ls -d "$HOME"/.elan/toolchains/*/lib/lean 2>/dev/null | head -1)
PKGS=""
for d in "$MLROOT"/.lake/packages/*/.lake/build/lib/lean; do
  [ -d "$d" ] && PKGS="$PKGS:$d"
done
export LEAN_PATH="$MLLIB:$TCLIB$PKGS"
export CLEAN_MAX_CLOSURE_MODULES="${CLEAN_MAX_CLOSURE_MODULES:-9000}"

free_gb() {
  ps=$(vm_stat | sed -n '1s/.*page size of \([0-9]*\).*/\1/p'); [ -n "$ps" ] || ps=16384
  vm_stat | awk -v ps="$ps" '
    /Pages free/{gsub(/\./,"",$3);f=$3} /Pages inactive/{gsub(/\./,"",$3);i=$3}
    /Pages speculative/{gsub(/\./,"",$3);s=$3} /Pages purgeable/{gsub(/\./,"",$3);p=$3}
    END{printf "%d",(f+i+s+p)*ps/1073741824}'
}

# Stamp one module set. Returns 0 and echoes KV on success; returns 1 on failure.
# `label` names BOTH the output dir and the evidence files, so every invocation
# gets a disjoint shard namespace — required, because stamp-verified
# disambiguates same-basename shards only within one invocation.
stamp_set() {
  label="$1"; list="$2"
  n=$(wc -l < "$list" | tr -d ' ')
  fg=$(free_gb)
  if [ "$fg" -lt "$MIN_FREE_GB" ]; then
    echo "      ABORT  ${fg} GB free (floor ${MIN_FREE_GB}) — stopping rather than thrash" >&2
    return 2
  fi
  echo "      [$label] $n modules, ${fg} GB free — stamping" >&2
  if [ "$DRY" = 1 ]; then echo 0; return 0; fi
  cdir="$SHARDS/$label"; rm -rf "$cdir"; mkdir -p "$cdir"
  t0=$(date +%s)
  # shellcheck disable=SC2046
  if "$CLEAN_BIN" mathverse stamp-verified $(cat "$list") \
        --out-dir "$cdir" --manifest "$EVID/kv_$label.json" \
        --closure-root "$MLLIB" --closure-elide opaque \
        --parallel --jobs "$JOBS" --json \
        > "$EVID/out_$label.json" 2> "$EVID/err_$label.log"; then
    kv=$(python3 -c "
import json
try: print(json.load(open('$EVID/out_$label.json')).get('kernel_verified',0))
except Exception: print(0)")
    echo "      [$label] ok KV=$kv $(( $(date +%s) - t0 ))s" >&2
    echo "$kv"; return 0
  fi
  echo "      [$label] FAILED after $(( $(date +%s) - t0 ))s" >&2
  rm -rf "$cdir" "$EVID/kv_$label.json"   # never leave shards with no manifest
  return 1
}

# Stamp `list`, halving on failure until it fits or hits --floor.
# Echoes total KV on full success; returns 1 if any leaf could not be stamped.
stamp_adaptive() {
  label="$1"; list="$2"
  # NOT `if kv=$(...); then ... fi` followed by `rc=$?`: after a `fi` whose
  # condition failed and which has no else, `$?` is the IF's status (0), not the
  # command's — so the memory-abort code 2 would read as success and the whole
  # library would keep splitting into a machine that is already out of RAM. An
  # AND-list preserves the real status, and is exempt from `set -e`.
  kv=$(stamp_set "$label" "$list") && { echo "$kv"; return 0; }
  rc=$?
  [ "$rc" = 2 ] && return 2
  n=$(wc -l < "$list" | tr -d ' ')
  if [ "$n" -le "$FLOOR" ]; then
    echo "      [$label] IRREDUCIBLE at $n modules (floor $FLOOR) — needs more RAM" >&2
    return 1
  fi
  half=$(( (n + 1) / 2 ))
  echo "      [$label] splitting $n -> $half + $(( n - half ))" >&2
  head -n "$half" "$list" > "$list.L"; tail -n +"$((half+1))" "$list" > "$list.R"
  total=0
  for side in L R; do
    if kv=$(stamp_adaptive "${label}_$side" "$list.$side"); then
      total=$(( total + kv ))
    else
      rc=$?; [ "$rc" = 2 ] && return 2
      return 1
    fi
  done
  echo "$total"; return 0
}

echo "== rescue =="
echo "   work $WORK   floor $FLOOR   jobs $JOBS"
pending=""
for c in "$EVID"/chunk_*; do
  b=$(basename "$c")
  case "$b" in done_*|kv_*|out_*|err_*) continue ;; esac
  [ -f "$EVID/done_$b" ] || pending="$pending $b"
done
[ -n "$pending" ] || { echo "   nothing pending — every chunk has a done mark"; exit 0; }
echo "   pending:$pending"

rescued=0; failed=0
for b in $pending; do
  echo "   --- $b ---"
  if kv=$(stamp_adaptive "$b" "$EVID/$b"); then
    echo "$kv" > "$EVID/done_$b"
    echo "   $b RESCUED, KV=$kv"
    rescued=$((rescued+1))
  else
    rc=$?
    [ "$rc" = 2 ] && { echo "   stopping: memory floor hit"; break; }
    echo "   $b STILL FAILING — left unmarked for a future retry"
    failed=$((failed+1))
  fi
done
rm -f "$EVID"/chunk_*.L "$EVID"/chunk_*.R
echo "== done: $rescued rescued, $failed still failing =="
