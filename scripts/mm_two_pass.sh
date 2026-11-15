#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# TWO-PASS PARALLEL Metamath kernel-verifier driver.
#
# Splits the first N `$p` theorems of a set.mm database into NWORKERS disjoint
# provable-ordinal ranges and launches one `mm_verify_range` process per range
# in parallel. Each worker runs the two-pass verifier (PASS 1 registers every
# theorem's type as an axiom; PASS 2 proof-checks only its range), prints its
# verified labels, and the driver UNIONS them into a single sorted label set.
#
# Usage:
#   scripts/mm_two_pass.sh <set.mm> <N> [NWORKERS] [OUTDIR]
#
#   <set.mm>    path to the Metamath database
#   <N>         number of leading $p theorems to verify (provable ordinals [0,N))
#   NWORKERS    number of parallel workers (default: number of CPUs)
#   OUTDIR      where per-worker logs + the unioned label set are written
#               (default: a fresh mktemp dir, path printed at the end)
#
# Output:
#   $OUTDIR/range_<start>_<end>.out   per-worker stdout (VERIFIED_FORMAT/COUNT,
#                                     `V <label>`, and `G <label>` for the
#                                     GROUND-ONLY subset)
#   $OUTDIR/range_<start>_<end>.err   per-worker stderr (timing + any FAILs)
#   $OUTDIR/verified_union.txt        sorted union, in the same VERIFIED_FORMAT 2
#                                     shape — feed it straight to `mm_gate`
#
# R1-MM: the union MUST carry the `G <label>` marking. A theorem that verified only
# on the GROUND fallback is verified but NOT reusable, and `mm_gate` has to drop its
# dependents to reproduce the sequential verifier's set (issue
# docs/issues/2026-08-23-r1-mm-two-pass-theorem.md). The `VERIFIED_FORMAT 2` stamp is
# written only if EVERY worker's output carried it, so a stale `mm_verify_range`
# binary produces an unstamped union that `mm_gate` REFUSES — never a silently
# all-reusable one.
#
# Each worker's PASS 1 traverses [0, end) to build dependency-type axioms, so
# every worker pays the (cheap) type-registration cost for its prefix; only its
# assigned PASS-2 range pays the expensive proof checks. This is the practical
# win on deep proofs: the proof-checking work is partitioned across cores.

set -euo pipefail

if [[ $# -lt 2 ]]; then
  echo "usage: $0 <set.mm> <N> [NWORKERS] [OUTDIR]" >&2
  exit 2
fi

SETMM="$1"
N="$2"
NWORKERS="${3:-}"
OUTDIR="${4:-}"

if [[ ! -f "$SETMM" ]]; then
  echo "error: set.mm not found: $SETMM" >&2
  exit 2
fi
if ! [[ "$N" =~ ^[0-9]+$ ]] || [[ "$N" -eq 0 ]]; then
  echo "error: N must be a positive integer (got '$N')" >&2
  exit 2
fi

# Default worker count = memory-aware (NOT CPU-aware).
#
# 2026-06-26: each worker's PASS 1 builds the full dependency-type env (observed
# 6-16 GB resident per worker). Sizing by CPU count caused a WindowServer-watchdog
# kernel panic — ~12 workers x ~13 GB ~= 163 GB on a 24 GB machine, saturating the
# compressor/swap until WindowServer missed its watchdog and the kernel panicked.
# Size by reclaimable RAM, capped by CPU count, floored at 1.
#   MM_WORKER_GB        estimated peak GiB per worker (default 12)
#   MM_MEM_HEADROOM_GB  GiB to leave for the OS/GUI (default 6)
if [[ -z "$NWORKERS" ]]; then
  if command -v nproc >/dev/null 2>&1; then
    cpu="$(nproc)"
  elif command -v sysctl >/dev/null 2>&1; then
    cpu="$(sysctl -n hw.ncpu)"
  else
    cpu=4
  fi
  if command -v vm_stat >/dev/null 2>&1; then
    psz="$(sysctl -n hw.pagesize 2>/dev/null || echo 16384)"
    avail_gb="$(vm_stat | awk -v p="$psz" '
      /Pages free:/       {f=$NF}
      /Pages inactive:/   {i=$NF}
      /Pages speculative:/{s=$NF}
      END {gsub(/\./,"",f); gsub(/\./,"",i); gsub(/\./,"",s);
           printf "%d", ((f+i+s)*p)/1073741824}')"
  elif [[ -r /proc/meminfo ]]; then
    avail_gb="$(awk '/MemAvailable/{printf "%d",$2/1048576}' /proc/meminfo)"
  else
    avail_gb=8
  fi
  worker_gb="${MM_WORKER_GB:-12}"
  headroom_gb="${MM_MEM_HEADROOM_GB:-6}"
  mem_workers=$(( (avail_gb - headroom_gb) / worker_gb ))
  [[ "$mem_workers" -lt 1 ]] && mem_workers=1
  NWORKERS="$mem_workers"
  [[ "$NWORKERS" -gt "$cpu" ]] && NWORKERS="$cpu"
  if [[ "$mem_workers" -lt "$cpu" ]]; then
    echo "note: memory-bounded to $NWORKERS worker(s) (~${avail_gb}GiB avail, ~${worker_gb}GiB/worker)." >&2
    echo "      For large N, run on a high-RAM host (see ~/remote-server) — not this machine." >&2
  fi
fi
# Never spawn more workers than theorems.
if [[ "$NWORKERS" -gt "$N" ]]; then
  NWORKERS="$N"
fi

if [[ -z "$OUTDIR" ]]; then
  OUTDIR="$(mktemp -d "${TMPDIR:-/tmp}/mm_two_pass.XXXXXX")"
else
  mkdir -p "$OUTDIR"
fi

# Locate the release binary (build it if absent).
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="$REPO_ROOT/target/release/mm_verify_range"
if [[ ! -x "$BIN" ]]; then
  echo "building mm_verify_range (release)..." >&2
  ( cd "$REPO_ROOT" && targo --unverified build --offline --release -p clean-olean --bin mm_verify_range )
fi

echo "two-pass: $SETMM  N=$N  workers=$NWORKERS  outdir=$OUTDIR" >&2

# Compute disjoint ranges [start,end) that partition [0, N) as evenly as possible.
declare -a STARTS ENDS
base=$(( N / NWORKERS ))
rem=$(( N % NWORKERS ))
cur=0
for (( w = 0; w < NWORKERS; w++ )); do
  len=$base
  if [[ "$w" -lt "$rem" ]]; then
    len=$(( len + 1 ))
  fi
  start=$cur
  end=$(( cur + len ))
  cur=$end
  STARTS[$w]=$start
  ENDS[$w]=$end
done

# Per-worker address-space backstop. Even with the memory-aware NWORKERS above,
# cap each worker via `ulimit -v` so a single runaway cannot exhaust the machine
# and trigger a WindowServer-watchdog panic. Sized from physical RAM / workers,
# leaving OS/GUI headroom. macOS only partially enforces RLIMIT_AS, so this is a
# backstop on top of NWORKERS, not the primary guard. Override MM_ULIMIT_V_KB;
# set it to 0 to disable.
if [[ -z "${MM_ULIMIT_V_KB:-}" ]]; then
  if [[ "$(uname -s)" == "Darwin" ]]; then
    # macOS RLIMIT_AS counts VIRTUAL address space, which Rust over-reserves by
    # tens of GB, so a physical-RAM-sized `ulimit -v` kills healthy workers at
    # startup (empty output, instant exit). Disable on macOS and rely on the
    # memory-aware NWORKERS above; for a hard cap on macOS use the governor's
    # RSS watchdog (scripts/lib/stamp_mem_governor.sh). Override to force a value.
    MM_ULIMIT_V_KB=0
  else
    if [[ -r /proc/meminfo ]]; then
      total_kb="$(awk '/MemTotal/{print $2; exit}' /proc/meminfo)"
    elif command -v sysctl >/dev/null 2>&1 && sysctl -n hw.memsize >/dev/null 2>&1; then
      total_kb=$(( $(sysctl -n hw.memsize) / 1024 ))
    else
      total_kb=0
    fi
    headroom_kb=$(( ${MM_MEM_HEADROOM_GB:-6} * 1024 * 1024 ))
    if [[ "$total_kb" -gt "$headroom_kb" ]]; then
      MM_ULIMIT_V_KB=$(( (total_kb - headroom_kb) / NWORKERS ))
    else
      MM_ULIMIT_V_KB=0
    fi
  fi
fi
[[ "${MM_ULIMIT_V_KB:-0}" -gt 0 ]] && \
  echo "per-worker ulimit -v: $(( MM_ULIMIT_V_KB / 1048576 )) GiB" >&2

# Launch all workers in parallel.
declare -a PIDS
for (( w = 0; w < NWORKERS; w++ )); do
  s="${STARTS[$w]}"
  e="${ENDS[$w]}"
  if [[ "$s" -ge "$e" ]]; then
    continue
  fi
  out="$OUTDIR/range_${s}_${e}.out"
  err="$OUTDIR/range_${s}_${e}.err"
  echo "  worker $w: range [$s,$e)" >&2
  if [[ "${MM_ULIMIT_V_KB:-0}" -gt 0 ]]; then
    ( ulimit -v "$MM_ULIMIT_V_KB" 2>/dev/null; exec "$BIN" "$SETMM" "$s" "$e" ) >"$out" 2>"$err" &
  else
    "$BIN" "$SETMM" "$s" "$e" >"$out" 2>"$err" &
  fi
  PIDS+=($!)
done

# Wait for every worker; fail if any worker exits non-zero.
fail=0
for pid in "${PIDS[@]}"; do
  if ! wait "$pid"; then
    fail=1
  fi
done

# Union the verified labels across all workers, PRESERVING the ground-only marking.
#
# `V <label>` = verified; `G <label>` = verified only on the GROUND (non-reusable)
# fallback. `G` is STICKY across workers: ranges are disjoint so exactly one worker
# owns each label, but a sticky union is fail-closed under any re-partitioning.
# The `VERIFIED_FORMAT 2` stamp is emitted only when every worker output had it.
UNION="$OUTDIR/verified_union.txt"
# bash 3.2 (the macOS system shell) has no `mapfile`, so collect with a glob loop.
WORKER_OUTS=()
for f in "$OUTDIR"/range_*.out; do
  if [[ -f "$f" ]]; then
    WORKER_OUTS+=("$f")
  fi
done
n_outs="${#WORKER_OUTS[@]}"
stamped=0
for f in ${WORKER_OUTS+"${WORKER_OUTS[@]}"}; do
  if grep -q '^VERIFIED_FORMAT 2' "$f"; then
    stamped=$(( stamped + 1 ))
  fi
done
if [[ "$n_outs" -gt 0 && "$stamped" -eq "$n_outs" ]]; then
  echo "VERIFIED_FORMAT 2" > "$UNION"
else
  : > "$UNION"
  echo "WARNING: $stamped/$n_outs worker outputs carry the VERIFIED_FORMAT 2 stamp." >&2
  echo "         The union is written UNSTAMPED and mm_gate will REFUSE it (fail-closed)." >&2
  echo "         Rebuild mm_verify_range (rm -f '$BIN') and re-run — see R1-MM." >&2
  fail=1
fi
# `G` wins over `V` for the same label (sticky, order-independent). Both lines are
# emitted for a ground-only label so a v1 `/^V /` reader still sees every label.
cat ${WORKER_OUTS+"${WORKER_OUTS[@]}"} 2>/dev/null \
  | awk '/^V /{v[$2]=1} /^G /{g[$2]=1; v[$2]=1}
         END {for (l in v) {print "V " l; if (l in g) print "G " l}}' \
  | sort -u >> "$UNION"

union_count="$(awk '/^V /{n++} END{print n+0}' "$UNION")"
ground_count="$(awk '/^G /{n++} END{print n+0}' "$UNION")"
echo "===============================================" >&2
echo "two-pass UNION verified labels: $union_count ($ground_count ground-only)" >&2
echo "union written to: $UNION" >&2
echo "next: mm_gate <set.mm> $UNION   # drops dependents of unverified AND of" >&2
echo "      ground-only \$p-deps — this is what makes the set equal sequential" >&2
if grep -rq "    FAIL " "$OUTDIR"/range_*.err 2>/dev/null; then
  echo "WARNING: at least one worker reported a FAIL (soundness alarm) — see *.err" >&2
  fail=1
fi

# Echo the union count on stdout for easy capture.
echo "$union_count"
exit "$fail"
