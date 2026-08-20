#!/bin/bash
# Machine-wide admission gate for memory-heavy build/test jobs.
#
# WHY THIS EXISTS. On 2026-08-19 this machine took a kernel panic:
#
#   panic(cpu 14): watchdog timeout: no checkins from watchdogd in 90 seconds
#   Compressor Info: 44% of compressed pages limit (OK)
#                    100% of SEGMENTS limit (BAD) with 82 swapfiles
#
# Note WHICH limit: compressed *pages* were fine at 44%. The compressor ran out
# of SEGMENTS. Once those are gone it cannot accept another compression however
# much page budget is left, so every allocation stalls kernel-wide, watchdogd
# misses its checkin, and the kernel panics on purpose.
#
# Segment exhaustion is caused by MANY medium-large processes holding fragmented
# anonymous memory -- not by one big process. That is precisely a fleet of
# concurrent rustc/cargo jobs. Measured peaks in this repo: a clean-verify spec
# binary is ~8.8 GB RSS; a trustc driver build is multi-GB; whole-crate compiles
# run several at once. Independently-scheduled lanes had no idea about each
# other, so demand was unbounded by construction.
#
# So the gate counts GIGABYTES IN FLIGHT, machine-wide, across every lane and
# every process -- including jobs detached with fork()+setsid(), which outlive
# the lane that started them and were the invisible accumulator.
#
# USAGE
#   heavy_gate.sh acquire <gb> <label>   # blocks until <gb> is available; prints a token
#   heavy_gate.sh release <token>        # gives it back
#   heavy_gate.sh run <gb> <label> -- cmd...   # acquire, run, release even on failure
#   heavy_gate.sh status                 # what is in flight
#   heavy_gate.sh reap                   # drop tokens whose owner PID is gone
#
# A token records its owner PID. `reap` (run automatically on every acquire)
# drops tokens whose owner is dead, so a crashed or killed lane cannot wedge the
# gate permanently.

set -uo pipefail

GATE_DIR="${HEAVY_GATE_DIR:-/private/tmp/heavy_gate}"
TOKENS="$GATE_DIR/tokens"
LOCKD="$GATE_DIR/lock.d"

# Budget: physical RAM minus headroom for the OS, Spotlight and the editor.
# 128 GB machine -> 96 GB budget. Override with HEAVY_GATE_BUDGET_GB.
_phys_gb=$(( $(sysctl -n hw.memsize) / 1073741824 ))
_headroom=$(( _phys_gb / 4 ))
[ "$_headroom" -lt 8 ] && _headroom=8
BUDGET=${HEAVY_GATE_BUDGET_GB:-$(( _phys_gb - _headroom ))}

mkdir -p "$TOKENS"

# Portable mutex. macOS has no flock(1), so use mkdir, which is atomic on POSIX.
# A lock older than 60 s is assumed abandoned and is broken -- the critical
# section is a few file reads, so 60 s can only mean the holder died.
_lock() {
  local waited=0
  while ! mkdir "$LOCKD" 2>/dev/null; do
    if [ -d "$LOCKD" ]; then
      local age
      age=$(( $(date +%s) - $(stat -f %m "$LOCKD" 2>/dev/null || date +%s) ))
      [ "$age" -gt 60 ] && rmdir "$LOCKD" 2>/dev/null && continue
    fi
    sleep 0.2; waited=$((waited+1))
    [ "$waited" -gt 900 ] && { echo "heavy_gate: lock stuck >180s" >&2; return 1; }
  done
  echo $$ > "$LOCKD/owner" 2>/dev/null
  return 0
}
_unlock() { rm -f "$LOCKD/owner" 2>/dev/null; rmdir "$LOCKD" 2>/dev/null; }

_reap() {
  local f pid
  for f in "$TOKENS"/*; do
    [ -e "$f" ] || continue
    pid=$(awk 'NR==1{print $1}' "$f" 2>/dev/null)
    if [ -z "$pid" ] || ! kill -0 "$pid" 2>/dev/null; then rm -f "$f"; fi
  done
}

_inflight() {
  local total=0 g
  for f in "$TOKENS"/*; do
    [ -e "$f" ] || continue
    g=$(awk 'NR==1{print $2}' "$f" 2>/dev/null); total=$(( total + ${g:-0} ))
  done
  echo "$total"
}

cmd=${1:-status}
case "$cmd" in
  acquire)
    gb=${2:?need gb}; label=${3:-unnamed}; owner=${HEAVY_GATE_OWNER_PID:-$PPID}
    if [ "$gb" -gt "$BUDGET" ]; then
      echo "heavy_gate: refusing: $gb GB exceeds the whole budget of $BUDGET GB" >&2; exit 2
    fi
    while :; do
      _lock || exit 3
      _reap
      if [ $(( $(_inflight) + gb )) -le "$BUDGET" ]; then
        tok="$TOKENS/$(date +%s)-$$-$RANDOM"
        printf '%s %s %s %s\n' "$owner" "$gb" "$label" "$(date -u +%FT%TZ)" > "$tok"
        _unlock
        echo "$tok"; exit 0
      fi
      _unlock
      sleep 20
    done ;;
  release) rm -f "${2:?need token}" ;;
  run)
    gb=${2:?need gb}; label=${3:?need label}; shift 3
    [ "${1:-}" = "--" ] && shift
    tok=$("$0" acquire "$gb" "$label") || exit $?
    trap 'rm -f "$tok"' EXIT INT TERM
    "$@"; rc=$?
    rm -f "$tok"; trap - EXIT INT TERM; exit $rc ;;
  status)
    _reap
    echo "budget ${BUDGET} GB   in flight $(_inflight) GB"
    for f in "$TOKENS"/*; do
      [ -e "$f" ] || continue
      awk '{printf "  pid %-8s %3s GB  %-28s %s\n", $1, $2, $3, $4}' "$f"
    done ;;
  reap) _reap; echo "reaped; in flight now $(_inflight) GB" ;;
  *) echo "usage: $0 {acquire <gb> <label>|release <token>|run <gb> <label> -- cmd...|status|reap}" >&2; exit 64 ;;
esac
