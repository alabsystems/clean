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
QUEUE="$GATE_DIR/queue"
LOCKD="$GATE_DIR/lock.d"

# Budget: physical RAM minus headroom for the OS, Spotlight and the editor.
# 128 GB machine -> 96 GB budget. Override with HEAVY_GATE_BUDGET_GB.
_phys_gb=$(( $(sysctl -n hw.memsize) / 1073741824 ))
_headroom=$(( _phys_gb / 4 ))
[ "$_headroom" -lt 8 ] && _headroom=8
BUDGET=${HEAVY_GATE_BUDGET_GB:-$(( _phys_gb - _headroom ))}

mkdir -p "$TOKENS" "$QUEUE"

# Portable mutex. macOS has no flock(1), so use mkdir, which is atomic on POSIX.
# A lock older than 60 s is assumed abandoned and is broken -- the critical
# section is a few file reads, so 60 s can only mean the holder died.
_lock() {
  local waited=0
  while ! mkdir "$LOCKD" 2>/dev/null; do
    if [ -d "$LOCKD" ]; then
      local age
      age=$(( $(date +%s) - $(stat -f %m "$LOCKD" 2>/dev/null || date +%s) ))
      # MEASURED 2026-08-20: this breaker could never fire. `_lock` writes
      # `$LOCKD/owner` the instant it takes the lock, so `$LOCKD` is NEVER empty
      # while held and `rmdir` ALWAYS fails -- the `&& continue` was unreachable
      # for every real abandoned lock. Observed: lock.d held by DEAD pid 20854
      # for 280 s while five lanes' queue tickets hit the 180 s "lock stuck"
      # bail and their jobs exited. Remove the owner file first, then rmdir.
      if [ "$age" -gt 60 ]; then
        rm -f "$LOCKD/owner" 2>/dev/null
        rmdir "$LOCKD" 2>/dev/null && continue
      fi
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

# ---------------------------------------------------------------- the queue
# Without a queue this was a pure spin-retry: a 24 GB request loses every race
# to a 12 GB one, so a lane cycling small builds starves a large one for as long
# as it keeps cycling. That is not hypothetical -- it cost one lane 1h30m and
# denied another a slot entirely.
#
# Fix: FIFO by enqueue time, with EASY backfill. The OLDEST waiter holds a
# reservation on capacity as it frees; a younger waiter may still be admitted,
# but only out of the capacity left OVER that reservation. So the head of line
# always makes progress, and capacity is never idled waiting for it.
_qreap() {
  local f pid
  for f in "$QUEUE"/*; do
    [ -e "$f" ] || continue
    pid=$(awk 'NR==1{print $1}' "$f" 2>/dev/null)
    if [ -z "$pid" ] || ! kill -0 "$pid" 2>/dev/null; then rm -f "$f"; fi
  done
}

# Oldest ticket ahead of mine: its requested GB count, or empty when my ticket
# is the head of line. Ticket basenames start with a zero-padded enqueue epoch,
# so lexical sort IS time order.
_qhead() {
  local mine=$1 f best=""
  for f in $(ls "$QUEUE" 2>/dev/null | sort); do
    # Ticket basenames are lexically time-ordered, so the FIRST one is the head
    # of line. If it is mine I reserve nothing -- which is exactly what the
    # acquire loop's comment already claims ("I am the head of line if nothing
    # older is waiting; then I need only fit").
    #
    # MEASURED 2026-08-20: this used to `continue` past my own ticket and return
    # the SECOND oldest, so the head of line reserved capacity for the waiter
    # BEHIND it and could not start until budget - (its own gb) - (the next
    # waiter's gb) was free. With a 24 GB head and a 24 GB follower on a 96 GB
    # budget that means the head waits for in-flight <= 48 instead of <= 72 --
    # i.e. the anti-starvation device starved the largest job in the queue,
    # which is the exact failure this queue was written to prevent.
    [ "$QUEUE/$f" = "$mine" ] && break
    best="$QUEUE/$f"; break
  done
  [ -n "$best" ] && awk 'NR==1{print $2}' "$best" 2>/dev/null
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
    # Enqueue FIRST, so position is by arrival, not by who wins a race.
    _lock || exit 3
    myq="$QUEUE/$(printf '%012d' "$(date +%s)")-$$-$RANDOM"
    printf '%s %s %s %s\n' "$owner" "$gb" "$label" "$(date -u +%FT%TZ)" > "$myq"
    _unlock
    # Never leave a ticket behind: a stale one would reserve capacity forever.
    trap 'rm -f "$myq" 2>/dev/null' EXIT INT TERM
    while :; do
      _lock || { rm -f "$myq"; exit 3; }
      _reap; _qreap
      head_gb=$(_qhead "$myq")
      # I am the head of line if nothing older is waiting; then I need only fit.
      # Otherwise I must fit while LEAVING ROOM for the head's reservation.
      if [ -z "$head_gb" ]; then reserve=0; else reserve=$head_gb; fi
      if [ $(( $(_inflight) + gb + reserve )) -le "$BUDGET" ]; then
        tok="$TOKENS/$(date +%s)-$$-$RANDOM"
        printf '%s %s %s %s\n' "$owner" "$gb" "$label" "$(date -u +%FT%TZ)" > "$tok"
        rm -f "$myq"
        _unlock
        trap - EXIT INT TERM
        echo "$tok"; exit 0
      fi
      _unlock
      sleep $(( 3 + RANDOM % 5 ))
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
    _reap; _qreap
    echo "budget ${BUDGET} GB   in flight $(_inflight) GB"
    for f in "$TOKENS"/*; do
      [ -e "$f" ] || continue
      awk '{printf "  pid %-8s %3s GB  %-28s %s\n", $1, $2, $3, $4}' "$f"
    done
    # The queue is shown in arrival order: the top row is the head of line and
    # holds a reservation, so a lane that looks stuck can be SEEN to be next
    # rather than starved.
    _qn=$(ls "$QUEUE" 2>/dev/null | wc -l | tr -d ' ')
    if [ "${_qn:-0}" -gt 0 ]; then
      echo "waiting ($_qn, oldest first — the head holds a reservation):"
      for f in $(ls "$QUEUE" 2>/dev/null | sort); do
        awk '{printf "  pid %-8s %3s GB  %-28s queued %s\n", $1, $2, $3, $4}' "$QUEUE/$f"
      done
    fi ;;
  reap) _reap; echo "reaped; in flight now $(_inflight) GB" ;;
  *) echo "usage: $0 {acquire <gb> <label>|release <token>|run <gb> <label> -- cmd...|status|reap}" >&2; exit 64 ;;
esac
