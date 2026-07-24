# shellcheck shell=bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Memory governor for the Mathlib kernel-verification stamping harness.
#
# WHY THIS EXISTS — 2026-06-22 watchdog-timeout kernel panic (OOM).
# Six concurrent `clean mathverse stamp-verified` processes (RSS 129.8 / 114.9 /
# 98.1 / 81.8 / 13.4 / 9.7 GB) demanded ~448 GB on a 128 GB machine, pinned the
# compressor at ~73 GB, drove free RAM to ~14 MB, and starved `watchdogd` for
# 93 s -> kernel panic. Each `stamp-verified` chunk loads the full transitive
# import closure of every target olean into ONE kernel Environment (the union
# closure); even in the sound `--closure-elide opaque` mode this is a large
# per-process working set, and NOTHING stopped several of them from running at
# once. The stamping scripts are individually sequential, but neither held a
# single-instance lock, so overlapping invocations overcommitted RAM.
#
# This library provides harness-only guards (no kernel/soundness impact):
#   1. stamp_acquire_global_lock   — atomic, system-wide single-instance lock so
#                                     two stamp-verified harnesses can never run
#                                     at once (macOS has no flock -> mkdir lock).
#   2. stamp_wait_for_free_ram     — admission gate: block a new chunk until the
#                                     OS reports enough reclaimable RAM, so the
#                                     harness self-throttles even against load it
#                                     did not launch.
#   3. stamp_run_governed_chunk    — launch a chunk under a `ulimit -v` address-
#                                     space backstop and poll it: kill+record on
#                                     wall-clock timeout, on per-process RSS over
#                                     a ceiling, OR on a system-wide low-RAM
#                                     abort — converting a would-be OS panic into
#                                     one recoverable, requeueable chunk failure.
#
# All thresholds are env-overridable so an operator can tune them to the host.
# Defaults below target a 128 GB box and leave generous headroom for the
# compressor; they are conservative on purpose — throughput loss is acceptable,
# a second kernel panic is not.

# ----- tunables (override via env) -------------------------------------------
# Defaults AUTO-SCALE to the machine's physical RAM so the governor protects
# small machines (e.g. 24 GB) as well as 128 GB+ boxes, instead of hardcoding
# 128 GB-box values (the prior defaults assumed ~128 GB and would refuse to
# admit ANY chunk on a 24 GB machine, since the 28 GiB floor exceeds total RAM).
# At ~128 GB these formulas reproduce the original values; any explicit env
# override still wins.
if command -v sysctl >/dev/null 2>&1 && sysctl -n hw.memsize >/dev/null 2>&1; then
  _stamp_total_gib=$(( $(sysctl -n hw.memsize) / 1073741824 ))
elif [ -r /proc/meminfo ]; then
  _stamp_total_gib=$(awk '/MemTotal/{printf "%d",$2/1048576; exit}' /proc/meminfo)
else
  _stamp_total_gib=128
fi
[ "${_stamp_total_gib:-0}" -lt 1 ] && _stamp_total_gib=128

# Refuse to LAUNCH a new chunk unless at least this much RAM is reclaimable (~20% of RAM, min 2).
: "${STAMP_MIN_FREE_GIB:=$(( _stamp_total_gib / 5 > 2 ? _stamp_total_gib / 5 : 2 ))}"
# Kill the RUNNING chunk if system-wide reclaimable RAM falls below this (last
# resort to protect the machine; smaller than the admission floor by design; ~1/16 RAM, min 1).
: "${STAMP_ABORT_FREE_GIB:=$(( _stamp_total_gib / 16 > 1 ? _stamp_total_gib / 16 : 1 ))}"
# Kill the running chunk if its own resident set exceeds this many KiB (~75% of
# RAM): far above the expected legitimate working set, so it only fires on a
# genuine runaway, while still leaving the box alive.
: "${STAMP_RSS_CEIL_KB:=$(( _stamp_total_gib * 786432 ))}"
# Per-process address-space ceiling (KiB) applied via `ulimit -v` (~85% of RAM).
# macOS only partially enforces RLIMIT_AS, so this is a backstop paired with the
# RSS watchdog, not the primary guard. Set to 0 to disable.
: "${STAMP_ULIMIT_V_KB:=$(( _stamp_total_gib * 891289 ))}"
# How often (seconds) the watchdog samples RSS + free RAM.
: "${STAMP_POLL_SECS:=15}"
# If 1, stamp_acquire_global_lock waits for the lock instead of refusing.
: "${STAMP_LOCK_WAIT:=0}"
# System-wide lock path (shared by ALL stamp harnesses so they mutually exclude).
: "${STAMP_LOCK_DIR:=${TMPDIR:-/tmp}/clean-stamp-verified.lock}"

# Set by stamp_run_governed_chunk for the caller to inspect.
STAMP_LAST_STATUS=""   # ok | timeout | rss_kill | lowram_kill | spawn_fail
STAMP_LAST_PEAK_KB=0

# ----- memory probing (macOS vm_stat; Linux /proc/meminfo) -------------------
# Echo system-wide reclaimable memory in whole GiB (free + inactive +
# speculative + purgeable on macOS; MemAvailable on Linux).
stamp_available_gib() {
  if command -v vm_stat >/dev/null 2>&1; then
    vm_stat | awk '
      /page size of/ { for (i=1;i<=NF;i++) if ($i ~ /^[0-9]+$/) ps=$i }
      /Pages free/        { gsub(/[ .]/,"",$3); free=$3 }
      /Pages inactive/    { gsub(/[ .]/,"",$3); inact=$3 }
      /Pages speculative/ { gsub(/[ .]/,"",$3); spec=$3 }
      /Pages purgeable/   { gsub(/[ .]/,"",$3); purg=$3 }
      END {
        if (ps=="") ps=16384
        bytes=(free+inact+spec+purg)*ps
        printf "%d", bytes/1073741824
      }'
  elif [ -r /proc/meminfo ]; then
    awk '/MemAvailable/ { printf "%d", $2/1048576 }' /proc/meminfo
  else
    echo 999   # unknown host: do not block
  fi
}

# ----- single-instance lock (atomic mkdir; stale-PID aware) ------------------
stamp_acquire_global_lock() {
  local me=$$
  while :; do
    if mkdir "$STAMP_LOCK_DIR" 2>/dev/null; then
      echo "$me" > "$STAMP_LOCK_DIR/pid"
      # Release on any exit of THIS shell.
      # shellcheck disable=SC2064
      trap "rm -rf '$STAMP_LOCK_DIR'" EXIT INT TERM
      echo "[gov] acquired stamp lock ($STAMP_LOCK_DIR)"
      return 0
    fi
    # Lock exists — is the holder still alive?
    local holder=""
    holder=$(cat "$STAMP_LOCK_DIR/pid" 2>/dev/null || echo "")
    if [ -n "$holder" ] && ! kill -0 "$holder" 2>/dev/null; then
      echo "[gov] stale stamp lock from dead pid $holder — reclaiming"
      rm -rf "$STAMP_LOCK_DIR"
      continue
    fi
    if [ "$STAMP_LOCK_WAIT" = "1" ]; then
      echo "[gov] another stamp harness holds the lock (pid ${holder:-?}); waiting…"
      sleep "$STAMP_POLL_SECS"
      continue
    fi
    echo "[gov] REFUSING to start: another stamp harness holds $STAMP_LOCK_DIR (pid ${holder:-?})." >&2
    echo "[gov] This guard prevents the 2026-06-22 OOM (concurrent stamp-verified runs). " >&2
    echo "[gov] Set STAMP_LOCK_WAIT=1 to queue instead of refusing." >&2
    return 1
  done
}

# ----- admission gate --------------------------------------------------------
stamp_wait_for_free_ram() {
  local need="${1:-$STAMP_MIN_FREE_GIB}" avail
  while :; do
    avail=$(stamp_available_gib)
    if [ "${avail:-0}" -ge "$need" ]; then
      return 0
    fi
    echo "[gov] waiting for RAM: ${avail}GiB reclaimable < ${need}GiB floor…"
    sleep "$STAMP_POLL_SECS"
  done
}

# ----- governed chunk launcher ----------------------------------------------
# Usage: stamp_run_governed_chunk <log> <timeout_secs> -- <command...>
# Launches <command...> with stdout+stderr -> <log>, under a ulimit -v backstop,
# and polls it. Sets STAMP_LAST_STATUS / STAMP_LAST_PEAK_KB. Returns 0 iff the
# command exited on its own before any guard fired.
stamp_run_governed_chunk() {
  local log="$1" timeout_secs="$2"; shift 2
  [ "$1" = "--" ] && shift
  STAMP_LAST_STATUS=""; STAMP_LAST_PEAK_KB=0

  # ulimit -v backstop in a subshell so it does not affect the harness shell.
  if [ "${STAMP_ULIMIT_V_KB:-0}" -gt 0 ]; then
    ( ulimit -v "$STAMP_ULIMIT_V_KB" 2>/dev/null; exec "$@" ) > "$log" 2>&1 &
  else
    ( exec "$@" ) > "$log" 2>&1 &
  fi
  local pid=$! waited=0 rss avail
  while kill -0 "$pid" 2>/dev/null; do
    # Track peak RSS (KiB) for observability — the per-chunk RSS logs from the
    # crashed run were lost, so we record it going forward.
    rss=$(ps -o rss= -p "$pid" 2>/dev/null | tr -d ' ')
    if [ -n "$rss" ] && [ "$rss" -gt "$STAMP_LAST_PEAK_KB" ]; then
      STAMP_LAST_PEAK_KB="$rss"
    fi
    # Guard 1: per-process RSS ceiling.
    if [ -n "$rss" ] && [ "$rss" -gt "$STAMP_RSS_CEIL_KB" ]; then
      echo "[gov] RSS ${rss}KiB > ceiling ${STAMP_RSS_CEIL_KB}KiB — killing pid $pid" | tee -a "$log"
      pkill -P "$pid" 2>/dev/null; kill -9 "$pid" 2>/dev/null
      echo "{\"oom_guard\":\"rss_kill\",\"rss_kb\":$rss}" >> "$log"
      STAMP_LAST_STATUS="rss_kill"; wait "$pid" 2>/dev/null; return 1
    fi
    # Guard 2: system-wide low-RAM abort.
    avail=$(stamp_available_gib)
    if [ "${avail:-999}" -lt "$STAMP_ABORT_FREE_GIB" ]; then
      echo "[gov] system reclaimable RAM ${avail}GiB < ${STAMP_ABORT_FREE_GIB}GiB — killing pid $pid to protect host" | tee -a "$log"
      pkill -P "$pid" 2>/dev/null; kill -9 "$pid" 2>/dev/null
      echo "{\"oom_guard\":\"lowram_kill\",\"avail_gib\":$avail}" >> "$log"
      STAMP_LAST_STATUS="lowram_kill"; wait "$pid" 2>/dev/null; return 1
    fi
    # Guard 3: wall-clock timeout (one pathological module can't hang the run).
    if [ "$waited" -ge "$timeout_secs" ]; then
      echo "[gov] TIMEOUT after ${waited}s — killing pid $pid" | tee -a "$log"
      pkill -P "$pid" 2>/dev/null; kill -9 "$pid" 2>/dev/null
      echo "{\"timed_out\":true}" >> "$log"
      STAMP_LAST_STATUS="timeout"; wait "$pid" 2>/dev/null; return 1
    fi
    sleep "$STAMP_POLL_SECS"; waited=$((waited + STAMP_POLL_SECS))
  done
  wait "$pid" 2>/dev/null; local rc=$?
  if [ "$rc" -ne 0 ]; then
    # The process exited NONZERO without tripping a governor guard above — almost
    # always an OS OOM-kill (SIGKILL=9 => rc 137) the 15s poll missed, or another
    # signal/crash. The original design set STAMP_LAST_STATUS only from its OWN
    # guards, so such a kill was recorded as `ok`: the harness then skipped the
    # requeue and silently lost the chunk's summary + manifest (observed
    # 2026-06-24: a 104GiB chunk jetsam-killed on a 128GB box, logged status=ok,
    # produced partial shards and no KV data). Treat any nonzero exit as FAILED so
    # the chunk is requeued, not silently dropped.
    STAMP_LAST_STATUS="proc_fail"
    echo "[gov] chunk process exited NONZERO (rc=$rc; 137=SIGKILL/OS-OOM) at peak RSS $((STAMP_LAST_PEAK_KB/1048576))GiB — FAILED, requeue" | tee -a "$log"
    echo "{\"proc_fail\":true,\"rc\":$rc,\"peak_kb\":$STAMP_LAST_PEAK_KB}" >> "$log"
    return 1
  fi
  STAMP_LAST_STATUS="ok"
  echo "[gov] chunk completed; peak RSS ${STAMP_LAST_PEAK_KB}KiB ($((STAMP_LAST_PEAK_KB/1048576))GiB)"
  return 0
}
