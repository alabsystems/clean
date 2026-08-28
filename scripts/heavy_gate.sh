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

# `/tmp/heavy_gate`, not `/private/tmp/heavy_gate`: on macOS `/tmp` IS a symlink
# to `/private/tmp`, so this names the identical directory there and keeps the
# gate machine-wide, while on Linux `/private` does not exist and the old path
# could not even be created. Deliberately NOT `$TMPDIR` — that is per-user on
# macOS, and a per-user directory would silently split one machine-wide mutex
# into several.
GATE_DIR="${HEAVY_GATE_DIR:-/tmp/heavy_gate}"
TOKENS="$GATE_DIR/tokens"
QUEUE="$GATE_DIR/queue"
LOCKD="$GATE_DIR/lock.d"

# Budget: physical RAM minus headroom for the OS, Spotlight and the editor.
# 128 GB machine -> 96 GB budget. Override with HEAVY_GATE_BUDGET_GB.
# HEAVY_GATE_PHYS_GB is a TEST SEAM (selftest only): it fakes the physical-RAM
# reading so both machine classes can be exercised on one box. Real callers
# never set it.
# Physical RAM, portably. `sysctl -n hw.memsize` is macOS-only: on Linux it
# prints nothing and the old arithmetic expanded to `$(( / 1073741824 ))`, a
# syntax error that left `_phys_gb` unbound and killed the script on the next
# line under `set -u`. Any gate sourcing this then died with a message about
# `_phys_gb` rather than about memory — measured 2026-08-25, that is what made
# ay's trust-verification ratchet report "dependency build failed".
_heavy_gate_phys_gb() {
  local raw
  if raw=$(sysctl -n hw.memsize 2>/dev/null) && [ -n "$raw" ]; then
    printf '%s' "$(( raw / 1073741824 ))"; return 0            # macOS, bytes
  fi
  if [ -r /proc/meminfo ]; then
    raw=$(awk '/^MemTotal:/ { print $2; exit }' /proc/meminfo 2>/dev/null)
    if [ -n "${raw:-}" ]; then
      printf '%s' "$(( raw / 1048576 ))"; return 0             # Linux, kB
    fi
  fi
  local pages page
  pages=$(getconf _PHYS_PAGES 2>/dev/null) || pages=""
  page=$(getconf PAGE_SIZE 2>/dev/null) || page=""
  if [ -n "$pages" ] && [ -n "$page" ]; then
    printf '%s' "$(( pages * page / 1073741824 ))"; return 0   # POSIX fallback
  fi
  return 1
}

if [ -n "${HEAVY_GATE_PHYS_GB:-}" ]; then
  _phys_gb=$HEAVY_GATE_PHYS_GB
elif _phys_gb=$(_heavy_gate_phys_gb); then
  :
else
  # Fail CLOSED and SAY SO. A gate that cannot size the machine must not guess
  # a budget; the previous behaviour was to die with an unbound-variable error
  # that named the wrong problem.
  echo "heavy_gate: FATAL — cannot read physical memory on this platform." >&2
  echo "            Tried: sysctl hw.memsize, /proc/meminfo, getconf _PHYS_PAGES." >&2
  echo "            Set HEAVY_GATE_PHYS_GB=<gb> to state it explicitly." >&2
  exit 1
fi
_headroom=$(( _phys_gb / 4 ))
[ "$_headroom" -lt 8 ] && _headroom=8
_arith_budget=$(( _phys_gb - _headroom ))

# SMALL-BOX MODE (2026-08-24). This gate was designed on and for the 128 GB
# build machines; an 8 GB laptop was never its design target. MEASURED on such
# a box on 2026-08-24 (docs/analysis/evalir-completion-plan-2026-08-24.md §6):
# the arithmetic above yields BUDGET = 8 - max(8/4, 8) = 0, every positive
# request then takes the exclusive clamp below to req=0, and the whole-machine
# hog check runs with HOG_GB = BUDGET/2 = 0 -- so EVERY process on the box
# counts as a hog and the acquire loop never converges: a ~35-minute
# unadmitted wait with 0 GB in flight. Fix, fail-closed in both directions:
# when the arithmetic budget falls below MIN_BUDGET, floor the budget at
# phys/2 so SOME work admits (a measured ~1.4 GB `cargo check` must not need a
# bypass), and -- in `acquire` below -- REFUSE, rather than admit
# "exclusively", anything bigger than that budget: on this machine class a job
# that cannot fit in the budget cannot fit in the machine either, and running
# it alone would just recreate the panic this gate exists to prevent. So on an
# 8 GB box a weight-24 spec binary is refused (exit 75) and a weight-4 check
# queues normally.
MIN_BUDGET=${HEAVY_GATE_MIN_BUDGET_GB:-4}
SMALL_BOX=0
if [ "$_arith_budget" -lt "$MIN_BUDGET" ]; then
  SMALL_BOX=1
  _arith_budget=$(( _phys_gb / 2 ))
  [ "$_arith_budget" -lt 1 ] && _arith_budget=1
fi
BUDGET=${HEAVY_GATE_BUDGET_GB:-$_arith_budget}

mkdir -p "$TOKENS" "$QUEUE"

# Portable mtime in epoch seconds; empty when it cannot be read.
#
# `stat -f %m` is BSD/macOS. On Linux `-f` means "filesystem status", so GNU
# stat SUCCEEDS on it and prints a multi-line report whose `  File: ...` line
# then landed inside the arithmetic below — the `|| date +%s` fallback could
# never fire, because stat did not fail. GNU first, BSD second: each errors
# cleanly on the other's flag.
_mtime() {
  stat -c %Y "$1" 2>/dev/null || stat -f %m "$1" 2>/dev/null
}

# Portable mutex. macOS has no flock(1), so use mkdir, which is atomic on POSIX.
# A lock older than 60 s is assumed abandoned and is broken -- the critical
# section is a few file reads, so 60 s can only mean the holder died.
_lock() {
  local waited=0
  while ! mkdir "$LOCKD" 2>/dev/null; do
    if [ -d "$LOCKD" ]; then
      local age
      local lock_mtime
      lock_mtime=$(_mtime "$LOCKD"); [ -n "${lock_mtime:-}" ] || lock_mtime=$(date +%s)
      age=$(( $(date +%s) - lock_mtime ))
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
# A waiting ticket is dropped when its OWNER is dead -- and also when it has
# gone STALE, i.e. the acquire loop that owns it has not touched it recently.
#
# MEASURED 2026-08-24 (lane STAGE1): owner-liveness alone is not enough. The
# owner recorded on a ticket is the CALLER (`$PPID` / HEAVY_GATE_OWNER_PID),
# not the `acquire` process itself. Kill an acquire -- SIGKILL runs no trap, so
# its EXIT handler never removes the ticket -- while the caller lives on, and
# the ticket becomes an IMMORTAL head-of-line reservation: `_qhead` keeps
# handing every other lane a phantom waiter to reserve capacity for. Seven such
# 44 GB tickets from one pid stacked up and taxed every other lane 44 GB until
# that pid happened to exit.
#
# The acquire loop re-stamps its own ticket on every poll (it wakes every 3-8 s),
# so a ticket untouched for TICKET_STALE_S has no live acquire behind it
# whatever its owner is doing. 120 s is >15x the slowest poll -- long enough
# that a loaded box cannot false-positive, short enough that a wedged
# reservation clears in about the time one poll cycle used to waste.
TICKET_STALE_S=${HEAVY_GATE_TICKET_STALE_S:-120}

_qreap() {
  local f pid now age
  now=$(date +%s)
  for f in "$QUEUE"/*; do
    [ -e "$f" ] || continue
    pid=$(awk 'NR==1{print $1}' "$f" 2>/dev/null)
    if [ -z "$pid" ] || ! kill -0 "$pid" 2>/dev/null; then rm -f "$f"; continue; fi
    f_mtime=$(_mtime "$f"); [ -n "${f_mtime:-}" ] || f_mtime=$now
    age=$(( now - f_mtime ))
    if [ "$age" -gt "$TICKET_STALE_S" ]; then rm -f "$f"; fi
  done
}

# Oldest waiting ticket, excluding my own: "<gb> <ticket>". Empty if none.
# Ticket basenames start with a zero-padded enqueue epoch, so lexical sort IS
# time order.
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

# The largest process the LEDGER DOES NOT KNOW ABOUT, if it is big enough to
# matter. Consulted only when a job needs the whole machine (see `acquire`).
# Reports GB, pid and command so a human has something to act on.
HOG_GB=${HEAVY_GATE_HOG_GB:-$(( BUDGET / 2 ))}
_biggest_other() {
  ps -axo rss=,pid=,comm= | awk -v lim=$(( HOG_GB * 1048576 )) '
    $1 > lim { if ($1 > m) { m = $1; p = $2; c = $3 } }
    END { if (m) printf "%.1f GB (pid %s %s)", m/1048576, p, c }'
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
    req=$gb
    # A job BIGGER THAN THE MACHINE is admitted EXCLUSIVELY, never refused.
    # Refusing it does not make it smaller -- it makes it INVISIBLE. Measured
    # 2026-08-24: 31 suite targets weigh more than this budget, the gate
    # refused each one, verify_runner ran them anyway (its refusal path was
    # fail-open) TWO AT A TIME, and the box took a watchdog panic with two
    # 23 GB spec binaries alive at once. Clamping the reservation to the whole
    # budget makes the existing FIFO arithmetic do the right thing with no new
    # logic: `in_flight + BUDGET + reserve <= BUDGET` holds only when nothing
    # else is in flight AND this ticket is head of line, so an oversize job
    # waits for the machine, runs ALONE, and the next one queues BEHIND it.
    if [ "$gb" -gt "$BUDGET" ]; then
      if [ "$SMALL_BOX" -eq 1 ]; then
        # Small-box refusal (2026-08-24): see SMALL-BOX MODE above. Exclusive
        # admission is a big-box device -- here "the whole machine" is smaller
        # than the job, so the only honest answer is no, and promptly.
        echo "heavy_gate: REFUSED: $label wants ${gb} GB but this is a small box (${_phys_gb} GB physical, budget ${BUDGET} GB) -- this job cannot fit here at all; run it on a big machine" >&2
        exit 75
      fi
      echo "heavy_gate: $label wants ${gb} GB > budget ${BUDGET} GB: admitting EXCLUSIVELY (alone)" >&2
      req=$BUDGET; label="$label(x${gb})"
    fi
    # Enqueue FIRST, so position is by arrival, not by who wins a race.
    _lock || exit 3
    myq="$QUEUE/$(printf '%012d' "$(date +%s)")-$$-$RANDOM"
    printf '%s %s %s %s\n' "$owner" "$req" "$label" "$(date -u +%FT%TZ)" > "$myq"
    _unlock
    # Never leave a ticket behind: a stale one would reserve capacity forever.
    # INT/TERM must EXIT after the cleanup, not merely run it: MEASURED
    # 2026-08-24 -- a bare cleanup trap meant a TERM'd acquire deleted its
    # ticket and then kept spinning FOREVER, invisible to the queue, ready to
    # print a token to a caller that was long gone. (SIGKILL still runs no
    # trap; that path is what the _qreap staleness sweep is for.)
    # If the signal lands inside the lock's critical section, release the
    # mutex too -- but only if THIS process holds it (owner file says $$),
    # never someone else's.
    _bail() { rm -f "$myq" 2>/dev/null
              [ "$(cat "$LOCKD/owner" 2>/dev/null)" = "$$" ] && _unlock
              trap - EXIT; exit "$1"; }
    trap 'rm -f "$myq" 2>/dev/null' EXIT
    trap '_bail 130' INT
    trap '_bail 143' TERM
    while :; do
      _lock || { rm -f "$myq"; exit 3; }
      # Prove this ticket still has a live acquire behind it (see _qreap).
      touch "$myq" 2>/dev/null
      _reap; _qreap
      head_gb=$(_qhead "$myq")
      # I am the head of line if nothing older is waiting; then I need only fit.
      # Otherwise I must fit while LEAVING ROOM for the head's reservation.
      if [ -z "$head_gb" ]; then reserve=0; else reserve=$head_gb; fi
      if [ $(( $(_inflight) + req + reserve )) -le "$BUDGET" ]; then
        # A whole-machine job must also clear processes the LEDGER CANNOT SEE.
        # The gate is an honour-system ledger; at the 2026-08-24 panic a
        # runaway `rapportd` held 16.96 GB with no token -- 24% of everything
        # in flight. Admitting a whole-machine job on top of that still
        # panics the box. This check runs ONLY on the exclusive path -- and
        # never in small-box mode (2026-08-24): there oversize is refused
        # outright above, so a budget-sized job is a normal job, and the
        # HOG_GB = BUDGET/2 threshold degenerates at this scale anyway
        # (measured: at budget 0 it matched every process on the box).
        if [ "$SMALL_BOX" -eq 0 ] && [ "$req" -ge "$BUDGET" ]; then
          hog=$(_biggest_other)
          if [ -n "$hog" ]; then
            echo "heavy_gate: $label needs the WHOLE machine but $hog is held by a process the gate does not know about; waiting" >&2
            _unlock; sleep $(( 3 + RANDOM % 5 )); continue
          fi
        fi
        tok="$TOKENS/$(date +%s)-$$-$RANDOM"
        printf '%s %s %s %s\n' "$owner" "$req" "$label" "$(date -u +%FT%TZ)" > "$tok"
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
    if [ "$SMALL_BOX" -eq 1 ]; then
      echo "budget ${BUDGET} GB (small-box mode: ${_phys_gb} GB physical; oversize requests are REFUSED, exit 75)   in flight $(_inflight) GB"
    else
      echo "budget ${BUDGET} GB   in flight $(_inflight) GB"
    fi
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
  selftest)
    # Mutation-tests the small-box fix in BOTH directions, plus big-box
    # regression, in isolated gate dirs with the physical-RAM test seam.
    # Added 2026-08-24 with SMALL-BOX MODE (see the budget block above).
    fails=0
    td=$(mktemp -d "${TMPDIR:-/tmp}/heavy_gate_selftest.XXXXXX") || exit 1
    _st() { # _st <name> <expected_rc> <cmd...>
      local name=$1 want=$2 got; shift 2
      "$@" >/dev/null 2>&1; got=$?
      if [ "$got" -eq "$want" ]; then echo "  selftest ok: $name (exit $got)"
      else echo "  selftest FAILED: $name (want exit $want, got $got)"; fails=$((fails+1)); fi
    }
    # 8 GB box: budget floors at phys/2 = 4, small-box mode on.
    st_out=$(HEAVY_GATE_DIR="$td/s" HEAVY_GATE_PHYS_GB=8 "$0" status)
    case "$st_out" in
      "budget 4 GB (small-box"*) echo "  selftest ok: 8 GB box floors budget at 4 GB, small-box mode on" ;;
      *) echo "  selftest FAILED: 8 GB box status: $st_out"; fails=$((fails+1)) ;;
    esac
    # Direction 1: a weight-24 request on 8 GB still refuses (prompt, exit 75).
    _st "8 GB box REFUSES weight 24" 75 \
      env HEAVY_GATE_DIR="$td/s" HEAVY_GATE_PHYS_GB=8 "$0" run 24 st-oversize -- true
    # Direction 2: a weight-4 request admits and the wrapped command runs.
    _st "8 GB box ADMITS weight 4" 0 \
      env HEAVY_GATE_DIR="$td/s" HEAVY_GATE_PHYS_GB=8 "$0" run 4 st-fits -- true
    # Capacity accounting stays fail-closed: with 4 GB in flight on a 4 GB
    # budget, a second 4 GB request must wait, not be admitted.
    tok=$(HEAVY_GATE_DIR="$td/s" HEAVY_GATE_PHYS_GB=8 "$0" acquire 4 st-holder)
    HEAVY_GATE_DIR="$td/s" HEAVY_GATE_PHYS_GB=8 "$0" acquire 4 st-second >"$td/second.out" 2>/dev/null &
    w2=$!
    sleep 6
    if kill -0 "$w2" 2>/dev/null && [ ! -s "$td/second.out" ]; then
      echo "  selftest ok: second 4 GB request WAITS while 4 GB is in flight"
    else
      echo "  selftest FAILED: second 4 GB request admitted over a 4 GB budget"; fails=$((fails+1))
    fi
    kill "$w2" 2>/dev/null; wait "$w2" 2>/dev/null
    HEAVY_GATE_DIR="$td/s" HEAVY_GATE_PHYS_GB=8 "$0" release "$tok"
    # Big-box regression: the arithmetic and exclusive admission are unchanged.
    st_out=$(HEAVY_GATE_DIR="$td/b" HEAVY_GATE_PHYS_GB=128 "$0" status)
    case "$st_out" in
      "budget 96 GB "*) echo "  selftest ok: 128 GB box budget still 96 GB" ;;
      *) echo "  selftest FAILED: 128 GB box status: $st_out"; fails=$((fails+1)) ;;
    esac
    _st "128 GB box admits weight 24" 0 \
      env HEAVY_GATE_DIR="$td/b" HEAVY_GATE_PHYS_GB=128 "$0" run 24 st-big -- true
    # Oversize on a big box still admits EXCLUSIVELY. The hog threshold is
    # pinned out of the way: this arm tests the clamp arithmetic, not the live
    # ps scan (which is nondeterministic on a loaded box).
    _st "128 GB box admits weight 200 EXCLUSIVELY" 0 \
      env HEAVY_GATE_DIR="$td/b" HEAVY_GATE_PHYS_GB=128 HEAVY_GATE_HOG_GB=4096 "$0" run 200 st-huge -- true
    rm -rf "$td"
    if [ "$fails" -gt 0 ]; then echo "selftest: $fails arm(s) FAILED"; exit 1; fi
    echo "selftest: all arms green"; exit 0 ;;
  *) echo "usage: $0 {acquire <gb> <label>|release <token>|run <gb> <label> -- cmd...|status|reap|selftest}" >&2; exit 64 ;;
esac
