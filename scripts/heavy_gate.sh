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
#   heavy_gate.sh run auto:<class>[:<fallback-gb>] <label> -- cmd...
#                                        # weight DERIVED from <class>'s measured peaks
#   heavy_gate.sh weight auto:<class>[:<fallback-gb>]   # what `auto:` would reserve, and why
#   heavy_gate.sh weight <gb> <label>    # what an explicit <gb> becomes under the floor
#                                        # An explicit <gb> (run/acquire) is RAISED, loudly, to
#                                        # ceil(1.3 x the label class's completed peak) when it
#                                        # is below it (heavy_gate_weights.sh, _apply_reservation_floor)
#   heavy_gate.sh status                 # what is in flight
#   heavy_gate.sh peaks [n]              # what past jobs RESERVED vs what they USED
#   heavy_gate.sh reap                   # drop tokens whose owner PID is gone
#   heavy_gate.sh selftest-auto          # the derived-weight arms alone (seconds)
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

# A process is GONE only when the kernel says it does not exist. `kill -0`
# also fails with EPERM for a live process this shell may not signal (a
# sandboxed agent's shell cannot signal processes outside its sandbox, and
# nobody may signal launchd), and reading that as death deleted live tickets
# and tokens out from under other sessions' jobs (measured 2026-10-05).
_pid_gone() {
  local err
  err=$(kill -0 "$1" 2>&1) && return 1
  case "$err" in *[Nn]ot\ permitted*) return 1 ;; esac
  return 0
}

_reap() {
  local f pid
  for f in "$TOKENS"/*; do
    [ -e "$f" ] || continue
    pid=$(awk 'NR==1{print $1}' "$f" 2>/dev/null)
    if [ -z "$pid" ] || _pid_gone "$pid"; then
      rm -f "$f" "$PEAKD/${f##*/}" 2>/dev/null
    fi
  done
  # Sidecar high-water marks outlive nothing: a mark whose token is gone is
  # dead weight, and -- since token names embed an epoch, a pid and $RANDOM --
  # could only ever be resurrected by a name collision that cannot happen.
  for f in "$PEAKD"/*; do
    [ -e "$f" ] || continue
    [ -e "$TOKENS/${f##*/}" ] || rm -f "$f" 2>/dev/null
  done
}

# ---------------------------------------------------------------- the queue
# Without a queue this was a pure spin-retry: a 24 GB request loses every race
# to a 12 GB one, so a lane cycling small builds starves a large one for as long
# as it keeps cycling. That is not hypothetical -- it cost one lane 1h30m and
# denied another a slot entirely.
#
# FIFO by enqueue time, with backfill that cannot postpone the oldest waiter.
# A younger request may use free capacity only if the head will still fit after
# EVERY subset of current holders whose completion would have made it fit.
# This needs no runtime predictions and never exceeds the memory budget.
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
    if [ -z "$pid" ] || _pid_gone "$pid"; then rm -f "$f"; continue; fi
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

# Backfill cannot delay the head after any combination of current completions.
# Let S = budget - head, and M be the greatest sum of token weights <= S.
# Remaining holders that would permit the head weigh at most M, so any younger
# request <= S-M preserves that opportunity. Check current capacity separately.
# Releases may race this snapshot: they only remove holders, so keeping their
# old weights in the subset set can only make this bound MORE conservative.
_backfill_room() {
  local head=$1 f
  {
    for f in "$TOKENS"/*; do
      [ -e "$f" ] || continue
      awk 'NR==1{print $2}' "$f" || { [ ! -e "$f" ] || return 3; }
    done
  } | awk -v budget="$BUDGET" -v head="$head" '
    BEGIN { slack = budget-head; reachable[0] = 1 }
    {
      weight = $1
      if (weight > 0 && weight <= slack)
        for (sum = slack; sum >= weight; sum--)
          if (reachable[sum-weight]) reachable[sum] = 1
    }
    END {
      if (slack < 0) { print 0; exit }
      for (sum = slack; sum > 0 && !reachable[sum]; sum--) {}
      print slack-sum
    }'
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

# ------------------------------------------- observed peak vs the reservation
#
# WHY. Everything above guards ONE direction: a weight smaller than the job.
# That is the direction that panicked this machine (2026-08-24: 31 targets
# weighed more than the budget, the gate refused them, and they ran anyway).
#
# The OPPOSITE error had no guard at all, and it is not benign. A weight LARGER
# than the job is silently converted by the arithmetic above into exclusive
# admission -- `req=$BUDGET` -- so ONE over-weighted job turns a shared,
# backfilling machine into a single-lane one for as long as it runs, and every
# part of the gate still looks like it is working. MEASURED 2026-08-28:
# `clean-verify::test::axiom_ratchet` reserved the whole 27 GB budget at
# weight 44 (derived from a 28.87 GB recording), ran at a 9.11 GB peak, held
# the machine 6h14m -- of which 2h41m was OTHER lanes' jobs queued behind it --
# and nothing anywhere printed a number a reader could have doubted.
#
# So `run` now MEASURES what the job actually used and says so at exit. It is a
# REPORT, not a policy: admission is untouched, no request is resized, and a
# job whose peak is unknown (too short to sample) is never warned about. The
# number is also appended to a machine-wide log so a stale weight is visible to
# the next lane and not only to the one that happened to be watching stderr.
#
# The measurement is a sampled sum of RSS over this script's descendant tree.
# Two known biases, both stated rather than corrected: summing RSS across a
# process tree DOUBLE-COUNTS pages shared between its processes (a group sum can
# therefore exceed physical RAM -- `kernel_core_red_env_fidelity` has a recorded
# 57.26 GB peak on this 36 GB box), and a peak between two samples is missed.
# Both bias the observed peak in directions that make this report CONSERVATIVE
# about crying over-reservation, which is the safe way round for a report whose
# only failure mode would be talking someone into a weight that is too small.
PEAK_SAMPLE_S=${HEAVY_GATE_SAMPLE_S:-5}
# Below this reservation the absolute waste is too small to be worth a line.
PEAK_MIN_REPORT_GB=${HEAVY_GATE_PEAK_MIN_GB:-4}
# An observed peak under this percentage of the reservation is called out.
PEAK_LOW_PCT=${HEAVY_GATE_PEAK_LOW_PCT:-40}
PEAKLOG="$GATE_DIR/peaks.log"

# Sum of RSS (KB) over the descendants of $1, excluding the subtree rooted at $2.
# Excluding the sampler's own subtree keeps the sampler from measuring itself;
# it is a few MB, but a measurement that includes its own instrument is one more
# thing a reader has to discount.
_tree_rss_kb() {
  ps -axo pid=,ppid=,rss= 2>/dev/null | awk -v root="$1" -v skip="${2:-0}" '
    { pid[NR]=$1+0; par[NR]=$2+0; rss[NR]=$3+0; n=NR }
    END {
      # `ps` does not emit parents before children, so both closures are taken
      # to a fixed point rather than in one pass.
      skipm[skip]=1; changed=1
      while (changed) { changed=0
        for (i=1;i<=n;i++) if (!skipm[pid[i]] && skipm[par[i]]) { skipm[pid[i]]=1; changed=1 } }
      mark[root]=1; changed=1
      while (changed) { changed=0
        for (i=1;i<=n;i++)
          if (!mark[pid[i]] && !skipm[pid[i]] && mark[par[i]]) { mark[pid[i]]=1; changed=1 } }
      t=0
      for (i=1;i<=n;i++) if (mark[pid[i]] && pid[i]!=root && !skipm[pid[i]]) t+=rss[i]
      printf "%d", t
    }'
}

# One line per gated job, plus a warning when the reservation and the job
# disagree -- in EITHER direction.
#
# The line ends ` rc=<exit>` (every `run` since 2026-09-24) and, for a job
# admitted through `auto:<class>`, ` class=<class>`: those two fields are what
# `_auto_weight` below reads back, and the leading fields are unchanged so
# every older reader of this log still parses it.
_peak_report() {   # <reserved_gb> <label> <peakfile> <elapsed_s> [<rc> [<class>]]
  local gb=$1 label=$2 pf=$3 secs=$4 rc=${5:-} cls=${6:-} kb line tail=""
  [ -n "$pf" ] && [ -s "$pf" ] || return 0     # never sampled: say nothing
  kb=$(awk 'NR==1{print $1+0}' "$pf" 2>/dev/null)
  [ -n "${kb:-}" ] && [ "$kb" -gt 0 ] || return 0
  line=$(awk -v kb="$kb" -v gb="$gb" -v secs="$secs" -v lbl="$label" \
             -v lowpct="$PEAK_LOW_PCT" -v minrep="$PEAK_MIN_REPORT_GB" '
    BEGIN {
      peak = kb / 1048576.0
      pct  = (gb > 0) ? peak * 100.0 / gb : 0
      h = int(secs/3600); m = int((secs%3600)/60)
      dur = (h > 0) ? sprintf("%dh%02dm", h, m) : sprintf("%dm%02ds", m, secs%60)
      printf "%s|%.2f|%.0f|%s|%d", lbl, peak, pct, dur,
             (pct < lowpct && gb >= minrep) ? 1 : (peak > gb ? 2 : 0)
    }')
  local lbl peak pct dur verdict
  IFS='|' read -r lbl peak pct dur verdict <<EOF
$line
EOF
  mkdir -p "$GATE_DIR" 2>/dev/null
  [ -n "$rc" ] && tail=" rc=$rc"
  [ -n "$cls" ] && tail="$tail class=$cls"
  printf '%s %s reserved=%s peak_gb=%s pct=%s dur=%s%s\n' \
    "$(date -u +%FT%TZ)" "$lbl" "$gb" "$peak" "$pct" "$dur" "$tail" >> "$PEAKLOG" 2>/dev/null
  [ -n "${HEAVY_GATE_QUIET:-}" ] || \
    echo "heavy_gate: $lbl reserved ${gb} GB, observed peak ${peak} GB (${pct}% of it) over $dur" >&2
  case "$verdict" in
    1) # A refusal/failure only measured its executed prefix, not a completed
       # workload. Keep the raw row, but never recommend lowering from it.
       [ "$rc" = 0 ] || return 0
       echo "heavy_gate: OVER-RESERVED — $lbl held ${gb} GB and never used more than ${peak} GB." >&2
       if [ "$gb" -gt "$BUDGET" ]; then
         echo "            ${gb} GB is above the ${BUDGET} GB budget, so this job was admitted" >&2
         echo "            EXCLUSIVELY: it held the WHOLE machine and every other lane queued" >&2
         echo "            behind it for $dur. An over-sized weight makes this a single-lane box." >&2
       else
         echo "            That is ${gb} GB of a ${BUDGET} GB budget denied to other lanes for $dur." >&2
       fi
       if [ -n "$cls" ]; then
         echo "            The next \`auto:$cls\` run re-derives its weight from this measurement." >&2
       else
         echo "            Re-derive the weight from this measurement: peak x1.5 = $(awk -v p="$peak" \
                'BEGIN{w=int(p*1.5); if (w<p*1.5) w++; if (w<1) w=1; printf "%d", w}') GB." >&2
       fi ;;
    2) echo "heavy_gate: UNDER-RESERVED — $lbl reserved ${gb} GB and peaked at ${peak} GB." >&2
       echo "            The ledger under-counted this job; that is the direction that panicked this" >&2
       if [ -n "$cls" ]; then
         echo "            box on 2026-08-19 and 2026-08-24. The next \`auto:$cls\` run reserves from" >&2
         echo "            this peak; if the class mixes jobs of different sizes, split it." >&2
       else
         echo "            box on 2026-08-19 and 2026-08-24. Raise the weight before running it again." >&2
       fi ;;
  esac
}

# Weights DERIVED from the peak log above (`run auto:<class>`): the resolver
# lives beside this file. Refuse to start without it -- a gate that silently
# lost its resolver would turn every auto: request into a usage error at best.
_HG_WEIGHTS="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")" && pwd)/heavy_gate_weights.sh"
[ -r "$_HG_WEIGHTS" ] || { echo "heavy_gate: FATAL — $_HG_WEIGHTS is missing" >&2; exit 1; }
# shellcheck source=scripts/heavy_gate_weights.sh
. "$_HG_WEIGHTS"

# --------------------------------- what the HOLDERS are using, right now
#
# `run` reports peak-vs-reservation AT EXIT. Measured 2026-08-30, that is both
# the wrong moment and the wrong caller for the failure it exists to catch:
#
#   * WRONG CALLER. `verify_runner.py` -- the only thing on this machine that
#     ever reserves 44 GB -- uses `acquire`/`release`, never `run`. So
#     `_peak_report` has never once run on a suite target: all 39 rows of
#     peaks.log at the time of writing are hand-run lane jobs, and `heavy_gate
#     peaks` is blind to precisely the class the report was written for.
#   * WRONG MOMENT. On 2026-08-28 `clean-verify::test::axiom_ratchet` held the
#     whole 27 GB budget for 3h33m of execution (plus 2h41m of its own gate
#     wait) with six lanes queued behind it. A line printed when that job
#     finally exits helps nobody who is blocked while it runs.
#
# So `status` -- the command a queued lane actually runs -- now says what each
# holder is USING against what it RESERVED. One `ps` pass, no admission change,
# no request resized, and SILENCE whenever the answer is unknown.
#
# ATTRIBUTION. A token records its OWNER pid (the caller), so usage is the RSS
# of that owner's descendant closure, owner included. One owner may hold
# SEVERAL tokens (a `--jobs N` runner does); those are summed and the row says
# so, because billing one worker's whole tree to one of its N tokens would be a
# number wrong in an unstated direction. An oversize job is by construction its
# owner's only token -- nothing else fits beside it -- which is exactly the case
# this report exists for.
#
# Summing RSS over a tree DOUBLE-COUNTS shared pages, so `using` is an
# OVER-estimate. This is live telemetry, not a completed-workload sizing bound.
#
# A HIGH-WATER MARK, NOT AN INSTANT. One `ps` sample would libel a job caught
# between two rustc spikes -- a cargo build is a sawtooth, and the number a
# weight must be derived from is its PEAK. So each `status` merges what it sees
# into a per-token high-water file. The mark only ever rises; a later phase may
# still exceed every observation made so far.
#
# THE TWO DIRECTIONS ARE NOT SYMMETRIC. One observation ABOVE a reservation is already proof of an
# under-reservation -- the memory was there, the ledger did not know about it,
# and that is the direction that panicked this box twice -- so UNDER fires on
# sample one. Observations BELOW cannot establish a completed peak, even after
# many samples: a later build/test phase may need more. Lower reservations are
# derived from completed runs; status never recommends them from live prefixes.
PEAKD="$GATE_DIR/peaks.d"

_status_holders() {
  local toks="" f snap any=0 base
  mkdir -p "$PEAKD" 2>/dev/null
  for f in "$TOKENS"/*; do
    [ -e "$f" ] || continue
    any=1
    base=${f##*/}
    toks="$toks$(awk -v tok="$base" 'NR==1{printf "T %s %s %s %s %s", tok, $1, $2, $3, $4}' "$f" 2>/dev/null)
"
    if [ -s "$PEAKD/$base" ]; then
      toks="$toks$(awk -v tok="$base" 'NR==1{printf "H %s %s %s", tok, $1+0, $2+0}' "$PEAKD/$base" 2>/dev/null)
"
    fi
  done
  [ "$any" -eq 1 ] || return 0
  snap=$(ps -axo pid=,ppid=,rss= 2>/dev/null | awk 'NF>=3 {printf "P %d %d %d\n", $1, $2, $3}')
  printf '%s%s\n' "$toks" "$snap" | awk -v peakd="$PEAKD" '
    function treekb(root,   i, changed, t) {
      # Descendant closure of `root`, root included. `ps` does not emit parents
      # before children, so this is a fixed point rather than one pass.
      split("", mk); mk[root] = 1; changed = 1
      while (changed) { changed = 0
        for (i = 1; i <= n; i++)
          if (!mk[pid[i]] && mk[par[i]]) { mk[pid[i]] = 1; changed = 1 } }
      t = 0
      for (i = 1; i <= n; i++) if (mk[pid[i]]) t += rss[i]
      return t
    }
    $1 == "T" { m++; tok[m] = $2; own[m] = $3 + 0; gb[m] = $4 + 0
                lbl[m] = $5; ts[m] = $6
                ogb[own[m]] += gb[m]; ocnt[own[m]]++; next }
    $1 == "H" { histkb[$2] = $3 + 0; histn[$2] = $4 + 0; next }
    $1 == "P" { n++; pid[n] = $2 + 0; par[n] = $3 + 0; rss[n] = $4 + 0
                live[pid[n]] = 1; next }
    END {
      # This sample, then the owner high-water across every sample ever taken
      # of any of that owner s tokens.
      for (o in ogb) if (live[o]) okb[o] = treekb(o)
      for (i = 1; i <= m; i++) {
        o = own[i]
        if (histkb[tok[i]] > opeak[o]) opeak[o] = histkb[tok[i]]
        if (histn[tok[i]] > oseen[o]) oseen[o] = histn[tok[i]]
      }
      for (o in ogb) if (live[o]) {
        if (okb[o] > opeak[o]) opeak[o] = okb[o]
        oseen[o]++
      }
      for (i = 1; i <= m; i++) {
        o = own[i]
        if (!live[o]) {
          # Never guess. An owner ps cannot see is an owner whose usage is
          # UNKNOWN, and an unknown must not print as a small number: that is
          # how a real weight gets cut.
          use = "peak ? (owner not visible to ps)"
        } else {
          g = opeak[o] / 1048576.0
          pct = (ogb[o] > 0) ? g * 100.0 / ogb[o] : 0
          # Keep every ternary on ONE line: the BWK awk macOS ships parses a
          # `?:` split across a continuation as a syntax error and aborts the
          # WHOLE program, which prints no rows at all.
          sfx = (oseen[o] == 1) ? "" : "s"
          if (ocnt[o] > 1)
            use = sprintf("peak %.2f GB across %d tokens (%.0f%% of %d GB, %d sample%s)", g, ocnt[o], pct, ogb[o], oseen[o], sfx)
          else
            use = sprintf("peak %.2f GB (%.0f%%, %d sample%s)", g, pct, oseen[o], sfx)
          if (g > ogb[o]) { use = use "  UNDER-RESERVED"; flag[o] = "under" }
          # Persist live telemetry without treating a partial peak as a bound
          # on the completed workload.
          pf = peakd "/" tok[i]
          printf "%d %d\n", opeak[o], oseen[o] > pf
          close(pf)
        }
        printf "  pid %-8s %3s GB  %-28s %s  %s\n", o, gb[i], lbl[i], ts[i], use
        ownerlbl[o] = ownerlbl[o] (ownerlbl[o] ? ", " : "") lbl[i]
      }
      for (o in flag) {
        g = opeak[o] / 1048576.0
        printf "UNDER-RESERVED: pid %s holds %d GB for %s and has peaked at %.2f GB.\n",
               o, ogb[o], ownerlbl[o], g
        printf "  The ledger is under-counting a LIVE job; that is the direction that panicked this box.\n"
      }
      if (m > 0) print "  Live peaks are partial observations; lower weights require completed-run evidence."
    }'
}

cmd=${1:-status}
case "$cmd" in
  acquire)
    label=${3:-unnamed}; owner=${HEAVY_GATE_OWNER_PID:-$PPID}
    _resolve_weight "${2:?need gb}" "$label"; gb=$GB
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
      # Prove this ticket still has a live acquire behind it (see _qreap), and
      # RESTORE it, contents and all, if something removed it. A bare `touch`
      # recreated a removed ticket EMPTY, `_qreap` then deleted it at once (no
      # owner pid), and the job waited invisible to `status` and to every other
      # waiter's head-of-line arithmetic -- measured 2026-10-05, twice (1 h 40 min
      # and 40+ min). The name carries the enqueue epoch, so FIFO order survives.
      if [ -s "$myq" ]; then
        touch "$myq" 2>/dev/null
      else
        printf '%s %s %s %s\n' "$owner" "$req" "$label" "$(date -u +%FT%TZ)" > "$myq"
      fi
      _reap; _qreap
      head_gb=$(_qhead "$myq")
      # The head needs only fit. A younger request must also preserve every
      # completion opportunity of the head. Keep the two bounds separate:
      # releases need no mutex, so current usage may fall after the snapshot.
      if [ -z "$head_gb" ]; then backfill_room=$BUDGET
      else backfill_room=$(_backfill_room "$head_gb") || { _unlock; exit 3; }; fi
      if [ "$req" -le "$backfill_room" ] && [ $(( $(_inflight) + req )) -le "$BUDGET" ]; then
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
  release) _rel=${2:?need token}; rm -f "$_rel" "$PEAKD/${_rel##*/}" 2>/dev/null ;;
  run)
    label=${3:?need label}
    _resolve_weight "${2-}" "$label"; gb=$GB; cls=$CLASS
    shift 3
    [ "${1:-}" = "--" ] && shift
    # The RESOLVED number goes to acquire, so the admission and the peak line
    # both carry the weight that was actually reserved.
    tok=$("$0" acquire "$gb" "$label") || exit $?
    peakf=""; spid=""
    # The sampler runs as a separate invocation of this script, not as a `( ) &`
    # subshell: this is bash 3.2 (macOS ships no newer /bin/bash), where a
    # subshell's `$$` is still the PARENT's pid, so a subshell could not tell
    # `_tree_rss_kb` which subtree to exclude -- itself.
    peakf=$(mktemp "${TMPDIR:-/tmp}/heavy_gate_peak.XXXXXX" 2>/dev/null) || peakf=""
    trap 'rm -f "$tok" ${peakf:+"$peakf"} 2>/dev/null; [ -n "${spid:-}" ] && kill "$spid" 2>/dev/null' EXIT INT TERM
    if [ -n "$peakf" ]; then
      "$0" __peak_watch $$ "$peakf" >/dev/null 2>&1 &
      spid=$!
    fi
    _t0=$(date +%s)
    # The wrapped command still runs in the FOREGROUND of this script, exactly
    # as before: measuring a job must not change how it is executed (stdin,
    # process group and signal delivery all stay put).
    # HEAVY_GATE_HELD tells the command it already runs inside a reservation, so
    # a runner it starts (check_gate_registry.py's demonstrations) runs under
    # this one instead of waiting on a second reservation this one may block.
    HEAVY_GATE_HELD="${gb}:${label}" "$@"; rc=$?
    _t1=$(date +%s)
    if [ -n "$spid" ]; then kill "$spid" 2>/dev/null; wait "$spid" 2>/dev/null; fi
    _peak_report "$gb" "$label" "$peakf" $(( _t1 - _t0 )) "$rc" "$cls"
    rm -f "$tok" ${peakf:+"$peakf"} 2>/dev/null
    trap - EXIT INT TERM; exit $rc ;;
  weight)
    # Read-only: what `run auto:<class>` would reserve right now, and why.
    # Prints "<gb>\t<basis>" so a caller can read the number off field 1.
    # With a <label>, an explicit weight is floored exactly as `run`/`acquire`
    # floor it (`_apply_reservation_floor`).
    _parse_weight "${2:?need a weight spec}" || { echo "heavy_gate: malformed weight '$2'" >&2; exit 64; }
    if [ -z "$W_CLASS" ]; then
      GB=$W_GB; _apply_reservation_floor "${3:-}" 2>/dev/null
      if [ "$GB" -gt "$W_GB" ]; then printf '%s\texplicit weight %s raised to its label class floor\n' "$GB" "$W_GB"
      else printf '%s\texplicit weight\n' "$GB"; fi
      exit 0
    fi
    _w=$(_auto_weight "$W_CLASS" "$W_FALLBACK")
    printf '%s\t%s\n' "${_w%%|*}" "${_w#*|}"; exit 0 ;;
  selftest-auto)
    "$0" __selftest_auto; exit $? ;;
  __selftest_auto)
    exec bash "$(cd "$(dirname "$0")" && pwd)/test_heavy_gate_auto.sh" ;;
  __peak_watch)
    # INTERNAL (used by `run`): track the peak RSS of <root>'s descendant tree
    # into <outfile> until <root> goes away. Never fails the job it watches.
    _pw_root=${2:?need root pid}; _pw_out=${3:?need outfile}; _pw_best=0
    while kill -0 "$_pw_root" 2>/dev/null; do
      _pw_kb=$(_tree_rss_kb "$_pw_root" $$)
      if [ -n "${_pw_kb:-}" ] && [ "$_pw_kb" -gt "$_pw_best" ]; then
        _pw_best=$_pw_kb; echo "$_pw_best" > "$_pw_out" 2>/dev/null
      fi
      sleep "$PEAK_SAMPLE_S"
    done
    exit 0 ;;
  peaks)
    # What every gated job on this machine actually used against what it
    # reserved. `status` answers "what is in flight"; this answers "were those
    # numbers right", which is the question a stale weight hides.
    if [ -s "$PEAKLOG" ]; then tail -n "${2:-40}" "$PEAKLOG"
    else echo "no peak measurements recorded yet ($PEAKLOG)"; fi ;;
  status)
    _reap; _qreap
    if [ "$SMALL_BOX" -eq 1 ]; then
      echo "budget ${BUDGET} GB (small-box mode: ${_phys_gb} GB physical; oversize requests are REFUSED, exit 75)   in flight $(_inflight) GB"
    else
      echo "budget ${BUDGET} GB   in flight $(_inflight) GB"
    fi
    # Each holder row carries what that job is USING against what it reserved,
    # as partial telemetry; it cannot establish a lower completed-run weight.
    # See _status_holders.
    _status_holders
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
    # A waiter whose ticket is removed from under it restores the ticket WITH
    # its contents (2026-10-05): an empty restore was reaped at once, leaving
    # the waiter invisible to the queue for as long as it waited.
    rm -f "${td:?}/s/queue/"* 2>/dev/null
    sleep 9
    if grep -qs " st-second " "$td/s/queue/"* 2>/dev/null; then
      echo "  selftest ok: a waiter restores its removed ticket, contents and all"
    else
      echo "  selftest FAILED: a removed ticket stayed gone (the waiter is invisible)"; fails=$((fails+1))
    fi
    kill "$w2" 2>/dev/null; wait "$w2" 2>/dev/null
    HEAVY_GATE_DIR="$td/s" HEAVY_GATE_PHYS_GB=8 "$0" release "$tok"
    # A token whose owner this shell may not signal (EPERM: pid 1) is alive,
    # not reaped; a token whose owner does not exist is reaped.
    mkdir -p "$td/p/tokens"
    printf '1 2 st-eperm %s\n' "$(date -u +%FT%TZ)" > "$td/p/tokens/1-1-1"
    printf '999999999 2 st-dead %s\n' "$(date -u +%FT%TZ)" > "$td/p/tokens/1-2-2"
    HEAVY_GATE_DIR="$td/p" HEAVY_GATE_PHYS_GB=128 "$0" status >/dev/null
    if [ -e "$td/p/tokens/1-1-1" ] && [ ! -e "$td/p/tokens/1-2-2" ]; then
      echo "  selftest ok: an unsignalable (EPERM) owner is alive; a missing owner is reaped"
    else
      echo "  selftest FAILED: EPERM owner reaped, or missing owner kept"; fails=$((fails+1))
    fi
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

    # ---- the peak-vs-reservation report (2026-08-28) --------------------
    # These arms run REAL jobs with REAL memory and read the REAL sampler:
    # nothing here injects a peak, because a report that can only be proved
    # through a test seam has not been shown to work on a job.
    _stg() {   # _stg <name> <expect|no:expect> <cmd...>
      local name=$1 want=$2 err; shift 2
      err=$("$@" 2>&1 >/dev/null)
      case "$want" in
        no:*) if printf '%s' "$err" | grep -q "${want#no:}"; then
                echo "  selftest FAILED: $name (unexpected '${want#no:}'): $err"; fails=$((fails+1))
              else echo "  selftest ok: $name"; fi ;;
        *)    if printf '%s' "$err" | grep -q "$want"; then echo "  selftest ok: $name"
              else echo "  selftest FAILED: $name (no '$want'): $err"; fails=$((fails+1)); fi ;;
      esac
    }
    _pk="env HEAVY_GATE_DIR=$td/b HEAVY_GATE_PHYS_GB=128 HEAVY_GATE_SAMPLE_S=2"
    # 1. A tiny job holding a big reservation IS called out. This is the
    #    2026-08-28 axiom_ratchet shape: weight 44, peak 9.11 GB, 6h12m of
    #    exclusive hold, and not one line of output saying so.
    _stg "over-reservation is REPORTED" "OVER-RESERVED" \
      $_pk "$0" run 8 st-overres -- sleep 7
    # 2. ... and a right-sized reservation is NOT, or the report is noise
    #    everyone learns to ignore. Same job, threshold moved under it.
    _stg "right-sized reservation is SILENT" "no:OVER-RESERVED" \
      $_pk HEAVY_GATE_PEAK_LOW_PCT=0 "$0" run 8 st-rightsized -- sleep 7
    # 3. The other direction -- the one that panicked this box -- is reported
    #    too: a real 1.5 GB allocation against a 1 GB reservation.
    _stg "under-reservation is REPORTED" "UNDER-RESERVED" \
      $_pk "$0" run 1 st-underres -- python3 -c \
      'import time
b = bytearray(1610612736)
for i in range(0, len(b), 4096): b[i] = 1
time.sleep(8)'
    # 4. A job too short to sample says NOTHING. An unmeasured peak must never
    #    be reported as a small one -- that is how a real weight gets cut.
    _stg "an unsampled job is not reported" "no:observed peak" \
      $_pk "$0" run 8 st-short -- true
    # 4a. A GRANDCHILD's memory counts. Cargo trees are deep -- cargo spawns
    #     rustc spawns its codegen workers -- so a measurement that stopped at
    #     the direct child would read ~0 on every job this gate exists for.
    #     The parent here is a small python that merely WAITS: all 1 GiB is in
    #     the grandchild, so only a transitive closure can see it. (Do not
    #     write this arm with nested `sh -c`: a single-command `sh -c` execs
    #     rather than forks, the chain collapses to one direct child, and the
    #     arm passes against a direct-children-only measurement -- measured
    #     2026-08-28 by planting exactly that mutation.)
    _stg "a GRANDCHILD's memory IS counted" "UNDER-RESERVED" \
      $_pk "$0" run 1 st-deep -- python3 -c 'import subprocess, sys
child = subprocess.Popen([sys.executable, "-c", """
import time
b = bytearray(1073741824)
for i in range(0, len(b), 4096): b[i] = 1
time.sleep(9)
"""])
child.wait()'
    # 4b. ... and a process OUTSIDE the job's tree does not. This is the arm
    #     that fails if `_tree_rss_kb` is ever 'simplified' to a process-GROUP
    #     sum: without job control every sibling this shell started shares the
    #     group, so a co-tenant's 1.5 GB would be billed to a `sleep`.
    python3 -c 'import time
b = bytearray(1610612736)
for i in range(0, len(b), 4096): b[i] = 1
time.sleep(30)' & _sib=$!
    sleep 4
    _stg "a sibling process is NOT counted" "no:UNDER-RESERVED" \
      $_pk "$0" run 1 st-isolation -- sleep 9
    kill "$_sib" 2>/dev/null; wait "$_sib" 2>/dev/null
    # 5. The wrapper still passes the job's exit code through untouched. The
    #    sampler is bookkeeping around `"$@"`, and must stay that way.
    _st "run passes a nonzero exit code through" 7 \
      env HEAVY_GATE_DIR="$td/b" HEAVY_GATE_PHYS_GB=128 "$0" run 4 st-rc -- sh -c 'exit 7'

    # ---- the LIVE holder report in `status` (2026-08-30) ----------------
    # Arms 1-5 above only ever exercise `run`. Nothing on this machine that
    # reserves 44 GB CALLS `run` -- verify_runner uses acquire/release -- so
    # these arms drive `status` itself, against real processes holding real
    # tokens in an isolated gate dir. Nothing injects a usage figure: a report
    # provable only through a seam has not been shown to work on a job.
    _lv="$td/live"
    # <owner_pid> <gb> <label> <status_passes> [extra env...] -> status output
    _live() {
      local owner=$1 gb=$2 label=$3 passes=$4; shift 4
      local tok out="" i=0
      tok=$(env HEAVY_GATE_DIR="$_lv" HEAVY_GATE_PHYS_GB=128 \
                HEAVY_GATE_OWNER_PID="$owner" "$@" "$0" acquire "$gb" "$label") || return 1
      while [ "$i" -lt "$passes" ]; do
        out=$(env HEAVY_GATE_DIR="$_lv" HEAVY_GATE_PHYS_GB=128 "$@" "$0" status)
        i=$((i + 1))
      done
      env HEAVY_GATE_DIR="$_lv" HEAVY_GATE_PHYS_GB=128 "$@" "$0" release "$tok"
      printf '%s' "$out"
    }
    # EVERY arm below FIRST proves the holder row is on screen. A `no:` arm
    # that only greps for the absence of a verdict passes when the token was
    # never minted at all -- measured 2026-08-30, and it is how the first cut
    # of these arms reported three greens against a gate holding nothing. The
    # owner-liveness trap that caused it is in _stl_owner below.
    _stl() {   # _stl <name> <expect|no:expect> <owner_pid> <gb> <label> <passes> [env...]
      local name=$1 want=$2 out; shift 2
      out=$(_live "$@")
      if ! printf '%s' "$out" | grep -q "  $3 "; then
        echo "  selftest FAILED: $name (no holder row for '$3' -- the arm is VACUOUS): $out"
        fails=$((fails+1)); return
      fi
      case "$want" in
        no:*) if printf '%s' "$out" | grep -q "${want#no:}"; then
                echo "  selftest FAILED: $name (unexpected '${want#no:}'): $out"; fails=$((fails+1))
              else echo "  selftest ok: $name"; fi ;;
        *)    if printf '%s' "$out" | grep -q "$want"; then echo "  selftest ok: $name"
              else echo "  selftest FAILED: $name (no '$want'): $out"; fails=$((fails+1)); fi ;;
      esac
    }
    # The owner must be backgrounded in THIS shell, never through a helper
    # function called in `$(...)`: measured 2026-08-30, a `sleep 45 & echo $!`
    # inside a command substitution returns a pid that is already dead by the
    # time the caller reads it, `_reap` then correctly drops the token, and
    # every live arm runs against an empty gate.
    _alloc_src='import time
b = bytearray(1610612736)
for i in range(0, len(b), 4096): b[i] = 1
time.sleep(60)'
    # L1. The 2026-08-28 shape, seen WHILE it is happening: a token held by a
    #     process that is using nothing. This is the line the six starved lanes
    #     had no way to read.
    sleep 60 & _o=$!
    _stl "live peaks do not justify downsizing after 3 samples" "no:OVER-RESERVED" "$_o" 8 st-live-over 3
    kill "$_o" 2>/dev/null; wait "$_o" 2>/dev/null
    # L2. Two samples also remain a prefix, not completed-workload evidence.
    sleep 60 & _o=$!
    _stl "live peaks do not justify downsizing after 2 samples" "no:OVER-RESERVED" "$_o" 8 st-live-early 2
    kill "$_o" 2>/dev/null; wait "$_o" 2>/dev/null
    # L3. Further samples still cannot justify a lower completed-run weight.
    sleep 60 & _o=$!
    _stl "live peaks do not justify downsizing after 4 samples" "no:OVER-RESERVED" "$_o" 8 st-live-right 4
    kill "$_o" 2>/dev/null; wait "$_o" 2>/dev/null
    # L4. The panic direction is NOT sample-floored: one observation above the
    #     reservation is already proof, so it fires on the FIRST pass. An arm
    #     given three passes would not catch a floor applied to both directions.
    python3 -c "$_alloc_src" & _o=$!
    sleep 5
    _stl "status REPORTS an under-reservation on ONE sample" "UNDER-RESERVED" "$_o" 1 st-live-under 1
    kill "$_o" 2>/dev/null; wait "$_o" 2>/dev/null
    # L5. A GRANDCHILD's memory counts: the owner recorded on a token is the
    #     CALLER (verify_runner's python, a lane's shell), and every byte that
    #     matters is two or more levels below it.
    # The fixture owner must terminate AND reap its own allocation when the
    # shell ends it. Killing only the parent leaves 1.5 GiB alive for a minute.
    python3 -c 'import signal, subprocess, sys

def stop(signum, _frame):
    raise SystemExit(128 + signum)

signal.signal(signal.SIGTERM, stop)
child = None
try:
    child = subprocess.Popen([sys.executable, "-c", """
import time
b = bytearray(1610612736)
for i in range(0, len(b), 4096): b[i] = 1
time.sleep(60)
"""])
    with open(sys.argv[1], "w") as ready:
        ready.write(str(child.pid) + "\n")
    child.wait()
finally:
    if child is not None:
        child.terminate()
        child.wait()' "$td/live-child.pid" & _o=$!
    sleep 6
    _live_child=""; _live_child_ready=0
    if read -r _live_child < "$td/live-child.pid" && [[ "$_live_child" =~ ^[0-9]+$ ]] && kill -0 "$_live_child" 2>/dev/null; then
      _live_child_ready=1
    else
      echo "  selftest FAILED: grandchild cleanup control has no live child"; fails=$((fails+1))
    fi
    _stl "a GRANDCHILD's memory IS counted by status" "UNDER-RESERVED" "$_o" 1 st-live-deep 1
    kill "$_o" 2>/dev/null; wait "$_o" 2>/dev/null
    if [ "$_live_child_ready" -eq 1 ]; then
      if kill -0 "$_live_child" 2>/dev/null; then
        echo "  selftest FAILED: grandchild allocation outlived its fixture owner"; fails=$((fails+1))
      else
        echo "  selftest ok: grandchild allocation is reaped before its fixture owner exits"
      fi
    fi
    # L6. ... and a process OUTSIDE the owner's tree is not. THE arm that fails
    #     if this report is ever 'simplified' to a machine-wide RSS sum: with a
    #     1.5 GB co-tenant alive, an idle owner must still read as idle.
    python3 -c "$_alloc_src" & _sib=$!
    sleep 60 & _o=$!
    sleep 5
    _stl "a co-tenant is NOT billed to a holder" "no:UNDER-RESERVED" "$_o" 1 st-live-isolation 3
    kill "$_o" "$_sib" 2>/dev/null; wait "$_o" 2>/dev/null; wait "$_sib" 2>/dev/null
    # L7. Small reservations also receive no premature downsizing advice.
    sleep 60 & _o=$!
    _stl "a small live reservation receives no downsizing advice" "no:OVER-RESERVED" "$_o" 2 st-live-small 4
    kill "$_o" 2>/dev/null; wait "$_o" 2>/dev/null
    rm -rf "$td"
    # ---- weights derived from measurement (2026-09-24) -------------------
    "$0" __selftest_auto || fails=$((fails+1))
    if [ "$fails" -gt 0 ]; then echo "selftest: $fails arm(s) FAILED"; exit 1; fi
    echo "selftest: all arms green"; exit 0 ;;
  *) echo "usage: $0 {acquire <weight> <label>|release <token>|run <weight> <label> -- cmd...|weight <weight>|status|peaks [n]|reap|selftest|selftest-auto}" >&2
     echo "       <weight> is a whole number of GB, or auto:<class>[:<fallback-gb>] (derived from <class>'s measured peaks)" >&2
     exit 64 ;;
esac
