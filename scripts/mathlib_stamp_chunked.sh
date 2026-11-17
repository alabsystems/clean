#!/bin/sh
# Stamp Mathlib into .mathverse shards in MEMORY-BOUNDED CHUNKS, then union them
# into one manifest a Clean proof can cite from at TrustGate::Strict.
#
#   scripts/mathlib_stamp_chunked.sh [--modules <file>] [--chunk <n>] [--work <dir>]
#                                    [--elide opaque|opaque-and-theorem|none]
#                                    [--limit <n>] [--resume] [--jobs <n>]
#
# WHY CHUNKED. `stamp-verified` loads each target's TRANSITIVE IMPORT CLOSURE into
# one kernel Environment before re-checking. For Mathlib that closure is 10^3-10^4
# modules; a single whole-library invocation was projected at ~46 GB against 36 GB
# physical. Chunking bounds the resident set per invocation: each chunk pays for
# its own closure and exits, so peak RSS is per-chunk rather than per-library.
# Shards accumulate in one directory and are unioned at the end, because the
# loader takes coverage from the manifest's base_shards list, not from one file.
#
# MEMORY IS THE BINDING CONSTRAINT, NOT TIME. Check free memory before starting
# and do NOT run this alongside another large job (an Isabelle grand regen holds
# 6-13 GB for ~38 h). The script refuses to start below --min-free-gb.
#
# SOUNDNESS. `--closure-elide opaque` (the default) is statically sound: the
# kernel never delta-unfolds an `Opaque` value, so no verdict can change.
# `opaque-and-theorem` is NOT statically sound for this kernel and is accepted
# here ONLY so it can be validated against an unchanged-KV-count gate — if you
# pass it, this script records the count so the comparison is possible, and says
# so in the summary. It does not decide for you that the win is safe.
# P6 slice 1a: blocked until the reference producer (slice 1b); see scripts/lib/p6_blocked.sh.
# shellcheck source=scripts/lib/p6_blocked.sh
. "$(cd "$(dirname "$0")" && pwd)/lib/p6_blocked.sh" && p6_blocked "scripts/mathlib_stamp_chunked.sh"
set -eu

REPO="${CLEAN_REPO:-$HOME/clean}"
MLROOT="${MLROOT:-$HOME/mathlib4}"
MLLIB="$MLROOT/.lake/build/lib/lean"
# NOT /tmp. macOS wipes /tmp at boot, and on 2026-08-01 a watchdog panic +
# reboot destroyed a /tmp work dir mid-run: 83 chunks of shards, the evidence,
# and every `done_chunk_*` mark that makes --resume work — ~35 h, unrecoverable.
# A multi-day job's state does not belong on a volume the OS clears.
WORK="${WORK:-$HOME/mathlib-chunked}"
CHUNK=200
# PARAGON workers per chunk. PASSED EXPLICITLY, because the built-in default
# over-provisions: `ram_aware_default_jobs()` computes `total_ram_gib /
# PER_WORKER_GIB`, which on this 36 GiB host is 36/12 = 3 — i.e. 3 x 12 GiB =
# 100% of physical RAM, with nothing left for the OS or for the shared base the
# module's own peak-RSS model (`base + jobs * ...`) says is there. On 2026-08-01
# that killed chunks ac and ag with SIGKILL (jetsam) mid-run. Budget against
# what is actually free, not against the nameplate.
JOBS=2
ELIDE=opaque
LIMIT=0
RESUME=0
MODULES=""
MIN_FREE_GB=12

while [ $# -gt 0 ]; do
  case "$1" in
    --modules) MODULES="$2"; shift 2 ;;
    --chunk)   CHUNK="$2"; shift 2 ;;
    --work)    WORK="$2"; shift 2 ;;
    --elide)   ELIDE="$2"; shift 2 ;;
    --limit)   LIMIT="$2"; shift 2 ;;
    --jobs)    JOBS="$2"; shift 2 ;;
    --min-free-gb) MIN_FREE_GB="$2"; shift 2 ;;
    --resume)  RESUME=1; shift ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done

SHARDS="$WORK/shards"; EVID="$WORK/evidence"
mkdir -p "$SHARDS" "$EVID"

# --- toolchain env (all three load-bearing; see scripts/mathlib_via_mathverse.sh)
#
# PIN THE TOOLCHAIN TO THE ONE MATHLIB WAS BUILT WITH. This was
# `ls -d ...toolchains/*/lib/lean | head -1` — whichever sorted first. With two
# toolchains installed on 2026-08-02 that selected v4.30.0-rc2 while
# `mathlib4/lean-toolchain` pinned v4.32.0-rc1, so LEAN_PATH resolved Lean CORE
# from a different Lean version than the Mathlib oleans were compiled against.
# Core constants are the closure floor of every Mathlib declaration, so a
# version skew there is not cosmetic. Read the pin and fail loudly if its
# toolchain is absent, rather than silently stamping against whatever is on disk.
TCPIN=$(tr -d ' \t\r\n' < "$MLROOT/lean-toolchain" 2>/dev/null)
if [ -n "$TCPIN" ]; then
  # `leanprover/lean4:v4.32.0-rc1` -> `leanprover--lean4---v4.32.0-rc1`
  TCDIR=$(printf '%s' "$TCPIN" | sed 's|/|--|g; s|:|---|g')
  TCLIB="$HOME/.elan/toolchains/$TCDIR/lib/lean"
  [ -d "$TCLIB" ] || {
    echo "FAIL  $MLROOT/lean-toolchain pins '$TCPIN' but $TCLIB is missing." >&2
    echo "      Refusing to stamp against a different Lean core than Mathlib was built with." >&2
    exit 1
  }
else
  TCLIB=$(ls -d "$HOME"/.elan/toolchains/*/lib/lean 2>/dev/null | head -1)
  echo "WARN  no $MLROOT/lean-toolchain pin; falling back to $TCLIB" >&2
fi
PKGS=""
for d in "$MLROOT"/.lake/packages/*/.lake/build/lib/lean; do
  [ -d "$d" ] && PKGS="$PKGS:$d"
done
export LEAN_PATH="$MLLIB:$TCLIB$PKGS"
export CLEAN_MAX_CLOSURE_MODULES="${CLEAN_MAX_CLOSURE_MODULES:-9000}"

CLEAN_BIN="$REPO/target/release/clean"
[ -x "$CLEAN_BIN" ] || { echo "FAIL  no $CLEAN_BIN — cargo build --release -p clean --bin clean" >&2; exit 1; }

# --- refuse to start under memory pressure -----------------------------------
# AVAILABLE memory, not `Pages free`.
#
# On macOS `Pages free` is nearly always ~0 even on an idle machine, because the
# kernel keeps freed pages as INACTIVE (file cache) and hands them back on demand.
# An earlier version of this guard read `Pages free` alone and refused to start at
# "0 GB" while 6.5 GB was genuinely reclaimable — a guard that blocks all real
# work is worse than no guard, because it teaches you to pass --min-free-gb 0.
#
# Available = free + inactive + speculative + purgeable, which is what the system
# will actually surrender under pressure.
free_gb() {
  # Portable: BSD awk has no 3-arg match(), so pull the page size with sed.
  ps=$(vm_stat | sed -n '1s/.*page size of \([0-9]*\).*/\1/p')
  [ -n "$ps" ] || ps=16384
  vm_stat | awk -v ps="$ps" '
    /Pages free/        { gsub(/\./,"",$3); f = $3 }
    /Pages inactive/    { gsub(/\./,"",$3); i = $3 }
    /Pages speculative/ { gsub(/\./,"",$3); s = $3 }
    /Pages purgeable/   { gsub(/\./,"",$3); p = $3 }
    END { printf "%d", (f + i + s + p) * ps / 1073741824 }'
}
FG=$(free_gb)
echo "== preflight =="
echo "   free memory: ${FG} GB (floor ${MIN_FREE_GB} GB)"
if [ "$FG" -lt "$MIN_FREE_GB" ]; then
  echo "FAIL  only ${FG} GB free; refusing to start."
  echo "      Chunked stamping is memory-bound. Running it under pressure risks"
  echo "      OOM-killing whatever else is resident — including a multi-day job."
  echo "      Wait, lower --chunk, or raise --min-free-gb deliberately."
  exit 1
fi

# --- module list --------------------------------------------------------------
LIST="$EVID/modules.txt"
if [ -n "$MODULES" ]; then
  cp "$MODULES" "$LIST"
else
  find "$MLLIB/Mathlib" -name '*.olean' | sort > "$LIST"
fi
[ "$LIMIT" -gt 0 ] && head -n "$LIMIT" "$LIST" > "$LIST.tmp" && mv "$LIST.tmp" "$LIST"
TOTAL=$(wc -l < "$LIST" | tr -d ' ')
echo "   modules to stamp: $TOTAL   chunk size: $CHUNK   elide: $ELIDE"
[ "$ELIDE" = "opaque-and-theorem" ] && \
  echo "   NOTE  --elide opaque-and-theorem is NOT statically sound; the KV count below" && \
  echo "         must be compared against an 'opaque' run before the win is accepted."

# --- chunk loop ---------------------------------------------------------------
split -l "$CHUNK" "$LIST" "$EVID/chunk_"
NCHUNK=$(ls "$EVID"/chunk_* | wc -l | tr -d ' ')
echo "   chunks: $NCHUNK"
i=0; KV_TOTAL=0; FAILED=0
for c in "$EVID"/chunk_*; do
  i=$((i+1))
  MARK="$EVID/done_$(basename "$c")"
  if [ "$RESUME" = 1 ] && [ -f "$MARK" ]; then
    echo "   [$i/$NCHUNK] skip (done)"; KV_TOTAL=$((KV_TOTAL + $(cat "$MARK"))); continue
  fi
  T0=$(date +%s)
  # shellcheck disable=SC2046
  # PER-CHUNK OUTPUT DIR — do not share one.
  #
  # `stamp-verified` names each shard after the module's BASENAME and
  # disambiguates collisions only WITHIN a single invocation (Basic, Basic-1).
  # Mathlib has 4 `Basic.olean` in `Logic/` alone, so a shared --out-dir lets a
  # later chunk's `Basic.mathverse` silently overwrite an earlier chunk's, and
  # coverage vanishes with no error and no failed exit. Measured: 12 modules
  # produced 10 shards. Per-chunk dirs make the namespace disjoint; the union
  # step below walks them all.
  CDIR="$SHARDS/$(basename "$c")"
  mkdir -p "$CDIR"
  if "$CLEAN_BIN" mathverse stamp-verified $(cat "$c") \
        --out-dir "$CDIR" \
        --manifest "$EVID/kv_$(basename "$c").json" \
        --closure-root "$MLLIB" --closure-elide "$ELIDE" \
        --parallel --jobs "$JOBS" --json > "$EVID/out_$(basename "$c").json" 2> "$EVID/err_$(basename "$c").log"; then
    KV=$(python3 -c "
import json,sys
try:
    d=json.load(open('$EVID/out_$(basename "$c").json'))
    print(d.get('kernel_verified') or d.get('kernelVerified') or 0)
except Exception: print(0)")
    echo "$KV" > "$MARK"
    KV_TOTAL=$((KV_TOTAL + KV))
    echo "   [$i/$NCHUNK] ok  KV=$KV  $(( $(date +%s) - T0 ))s"
  else
    FAILED=$((FAILED+1))
    echo "   [$i/$NCHUNK] FAIL (see $EVID/err_$(basename "$c").log)"
  fi
  FG=$(free_gb)
  if [ "$FG" -lt 4 ]; then
    echo "ABORT  free memory fell to ${FG} GB mid-run; stopping before something gets OOM-killed."
    echo "       Re-run with --resume and a smaller --chunk."
    break
  fi
done

# --- union manifest -----------------------------------------------------------
python3 - "$SHARDS" "$LIST" <<'PY'
import struct, json, os, sys, glob
d, listfile = sys.argv[1], sys.argv[2]
# Walk per-chunk subdirs; `path` stays relative to the manifest's own dir, which
# is what LibraryLoader::load_shard resolves against (root.join(entry.path)).
shards = []
for p in sorted(glob.glob(os.path.join(d, "**", "*.mathverse"), recursive=True)):
    h = struct.unpack_from('<12I', open(p, 'rb').read(64), 0)
    shards.append({"path": os.path.relpath(p, d), "content_hash": "local-not-verified",
                   "constant_count": h[7], "expr_count": 0, "source": "lean4"})
json.dump({"version": 1, "base_shards": shards, "delta_shards": [],
           "total_constants": sum(s["constant_count"] for s in shards),
           "total_exprs": 0},
          open(os.path.join(d, "manifest.json"), "w"), indent=2)
n_mod = sum(1 for _ in open(listfile))
print(f"   union manifest: {len(shards)} shards, "
      f"{sum(s['constant_count'] for s in shards):,} constants")
# Coverage check: one shard per module, or something was silently dropped.
if len(shards) != n_mod:
    print(f"   WARNING  {n_mod} modules but {len(shards)} shards — "
          f"{n_mod - len(shards)} lost to filename collision or a failed chunk")
    sys.exit(3)
PY

echo
echo "== summary =="
echo "   modules stamped : $TOTAL (chunks: $NCHUNK, failed: $FAILED)"
echo "   KernelVerified  : $KV_TOTAL   <- a MINTING count, not a usage count"
echo "   shard dir       : $SHARDS"
echo
echo "   Measure USAGE (goals actually closed) — the number that matters:"
echo "     MATHVERSE_BY_NAME=1 MATHVERSE_PROBE_NAME=<thm> MATHVERSE_SHARD_DIR=$SHARDS \\"
echo "       $REPO/target/release/examples/mathverse_mathlib_citation"
[ "$FAILED" -gt 0 ] && echo "   SOME CHUNKS FAILED — coverage is incomplete." && exit 1
exit 0
