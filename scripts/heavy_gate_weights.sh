#!/bin/bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# SOURCED by scripts/heavy_gate.sh -- not a command. It defines the resolver
# behind `heavy_gate.sh run auto:<class>`: weights DERIVED from the machine's
# own peak log instead of typed by hand. It lives in its own file only to keep
# heavy_gate.sh under the repo's 1000-line organisational limit; it reads the
# gate's PEAKLOG and nothing else, and the gate refuses to start without it.
#
# ------------------------------------------- weights DERIVED from measurement
#
# WHY. Every weight in this repo used to be typed by hand, per job, and the
# process audit of 2026-09-24 measured what that costs in BOTH directions over
# 927 gated jobs (reports/lean4-replacement-audit-2026-09-24/process.json):
#   * starvation -- in busy minutes ~22 of the 27 GB budget was reserved while
#     the jobs holding it peaked at ~13.5 GB summed, and a 1-second job waited
#     13.5 minutes behind reservations nobody was using;
#   * the panic direction -- 17 jobs were UNDER-reserved, the srcelab gate at
#     24.10 GB peak on a 14 GB reservation and a test run at 9.39 GB on 3.
# The peak log below already held the measurement that would have sized every
# one of them; the OVER/UNDER lines above only ever PRINTED it.
#
# `auto:<class>[:<fallback>]` reserves
#
#     max(FLOOR, ceil(FACTOR x P))     P = the largest peak over the last WINDOW
#                                          COMPLETED runs of <class>, and over
#                                          every KILLED run newer than the oldest
#                                          of those
#
# with FACTOR 1.3 and WINDOW 10 (the audit's derivation) and FLOOR 1 GB. Three
# rules keep it on the safe side of the two failures above:
#   * A COMPLETED run (the command exited 0) may LOWER a class's weight as it
#     ages out of the window -- that is the learning loop. A KILLED run (rc >=
#     128: a signal, a timeout, an abort) measured only the part that ran, and
#     so did a FAILED one (any other nonzero exit), so either's peak may RAISE
#     the weight and never lower it: the rule verify_runner's
#     `_prior_peak_rss_gb` already applies to suite rows ("a run that executed
#     no test measured no test"). Until 2026-09-29 a failed run counted as
#     completed, and it bit on its first use: a gate demonstration refused at
#     its first step (a PATH problem, rc 1, 8 s, 0.06 GB) taught its class a
#     1 GB weight for a job whose replays peaked at 8.71 GB.
#   * The weight is never below the peak of any run it read, whatever FACTOR
#     says -- a factor under 1 is refused by construction, not by convention.
#   * A class with no completed run reserves <fallback> (default 12 GB), and a
#     killed-only history can raise that fallback but never lower it.
# A class must name ONE kind of job. A cold build and a warm rebuild of the
# same crates differ by an order of magnitude; filed under one class, ten warm
# rebuilds age the cold build out of the window and the next cold one is
# under-reserved (the UNDER line above then says so, and the run after it
# reserves from that peak). Name them apart: `frontend-suite-build-cold`.
AUTO_WINDOW=${HEAVY_GATE_AUTO_WINDOW:-10}
AUTO_FACTOR=${HEAVY_GATE_AUTO_FACTOR:-1.3}
AUTO_FLOOR=${HEAVY_GATE_AUTO_FLOOR_GB:-1}
AUTO_FALLBACK=${HEAVY_GATE_AUTO_FALLBACK_GB:-12}

# Parse a weight argument. Sets W_GB (numeric requests) or W_CLASS/W_FALLBACK
# (auto requests). Exit status 0 = ok, 64 = malformed (the caller exits 64).
_parse_weight() {  # <spec>
  W_GB=""; W_CLASS=""; W_FALLBACK=""
  case "$1" in
    auto:*)
      local rest=${1#auto:}
      W_CLASS=${rest%%:*}
      if [ "$W_CLASS" != "$rest" ]; then W_FALLBACK=${rest#*:}; else W_FALLBACK=$AUTO_FALLBACK; fi
      case "$W_CLASS" in ""|*[!A-Za-z0-9_.-]*) return 64 ;; esac
      case "$W_FALLBACK" in ""|*[!0-9]*) return 64 ;; esac
      return 0 ;;
    ""|*[!0-9]*) return 64 ;;
    *) W_GB=$1; return 0 ;;
  esac
}

# Resolve an auto class to "<gb>|<basis>" from the peak log. Pure: reads only.
_auto_weight() {  # <class> <fallback_gb>
  local cls=$1 fb=$2
  if [ ! -r "$PEAKLOG" ]; then
    printf '%s|unseen class %s (no peak log at %s): fallback %s GB\n' "$fb" "$cls" "$PEAKLOG" "$fb"
    return 0
  fi
  awk -v cls="$cls" -v n="$AUTO_WINDOW" -v factor="$AUTO_FACTOR" -v floor="$AUTO_FLOOR" \
      -v fb="$fb" '
    # An epsilon, because 1.1 x 50 is 55.00000000000001 in binary floating
    # point and a naive ceil would reserve 56 (measured; see the selftest).
    function ceil(x,   y) { y = int(x); return (x - y > 1e-9) ? y + 1 : y }
    {
      c = ""; p = ""; rc = ""
      for (i = 3; i <= NF; i++) {
        if ($i ~ /^class=/) c = substr($i, 7)
        else if ($i ~ /^peak_gb=/) p = substr($i, 9)
        else if ($i ~ /^rc=/) rc = substr($i, 4)
      }
      if (c != cls || p == "") next
      k++; peak[k] = p + 0
      completed[k] = (rc ~ /^[0-9]+$/ && rc + 0 == 0) ? 1 : 0
    }
    END {
      # The window: the last n COMPLETED runs, newest first.
      oldest = 0; nc = 0; pc = 0
      for (i = k; i >= 1 && nc < n; i--) if (completed[i]) {
        nc++; oldest = i; if (peak[i] > pc) pc = peak[i]
      }
      # Killed runs newer than the window start may raise, never lower.
      np = 0; pp = 0
      for (i = (nc ? oldest : 1); i <= k; i++) if (!completed[i]) {
        np++; if (peak[i] > pp) pp = peak[i]
      }
      if (nc == 0 && np == 0) {
        printf "%d|unseen class %s: no measured run yet, fallback %d GB\n", fb, cls, fb
        exit
      }
      if (nc == 0) {
        w = ceil(factor * pp); if (w < ceil(pp)) w = ceil(pp); if (w < fb) w = fb
        printf "%d|class %s: no completed run; %d killed run(s) peaked at %.2f GB, which may raise the %d GB fallback and never lower it\n", w, cls, np, pp, fb
        exit
      }
      top = (pp > pc) ? pp : pc
      w = ceil(factor * top)
      if (w < floor) w = floor
      if (w < ceil(top)) w = ceil(top)
      extra = np ? sprintf(" and %d newer killed run(s)", np) : ""
      printf "%d|class %s: max peak %.2f GB over the last %d completed run(s)%s; ceil(%s x %.2f) = %d GB (floor %d)\n", w, cls, top, nc, extra, factor, top, w, floor
    }' "$PEAKLOG"
}

# ------------------------------- the FLOOR under an explicit (typed) weight
#
# WHY. The UNDER-RESERVED line in `_peak_report` and the `auto:` resolver above
# both depend on the caller reading and acting, and they did not: from
# 2026-09-29 to 2026-10-01 the peak log recorded 25 runs that peaked above
# their own reservation, the worst at 230%. That is the direction that
# panicked this box twice. So an EXPLICIT weight is now raised, mechanically
# and loudly, to what the log says that kind of job needs:
#
#     floor = ceil(FACTOR x P), never below ceil(P)
#     P     = the largest peak over the last WINDOW COMPLETED runs (rc=0) of
#             the job's LABEL CLASS -- the same factor, window and completed-run
#             rule as `auto:` (a killed or failed run measured only part of a
#             job and never sets the floor).
#
# The LABEL CLASS is the label with trailing run decorations stripped: digits,
# and `-rN` / `-vN` / `-dN` style suffixes (`f1-build-r2` -> `f1-build`,
# `kernel-lib2` -> `kernel-lib`). A logged run belongs to a class through its
# label or through its `class=` field (a run admitted as `auto:<class>`).
# RAISING, not refusing: an exit 75 only makes the caller retry with another
# small number. A raised run says so on stderr with the requested weight, the
# class peak and the raised weight. If a run is genuinely smaller than its
# class (a warm rebuild filed under a cold build's label), give it a label of
# its own. `auto:` requests are not floored here: their weight is already
# derived from the class's completed peaks by the same rule.
_HG_LCLASS_AWK='
function lclass(s,   prev) {
  prev = ""
  while (s != prev) {
    prev = s
    sub(/[-_.]?[rvdRVD]?[0-9]+$/, "", s)
    sub(/[-_.]+$/, "", s)
  }
  return s
}'

_label_class() {  # <label> -> its class (the label itself if stripping empties it)
  awk -v l="$1" "$_HG_LCLASS_AWK"'
    BEGIN { c = lclass(l); print (c == "" ? l : c) }'
}

# "<floor_gb>|<peak_gb>|<completed_runs>" for a label class, or nothing when the
# log holds no completed run of it. Pure: reads only.
_class_floor() {  # <class>
  [ -r "$PEAKLOG" ] || return 0
  awk -v cls="$1" -v n="$AUTO_WINDOW" -v factor="$AUTO_FACTOR" "$_HG_LCLASS_AWK"'
    function ceil(x,   y) { y = int(x); return (x - y > 1e-9) ? y + 1 : y }
    {
      c = ""; p = ""; rc = ""
      for (i = 3; i <= NF; i++) {
        if ($i ~ /^class=/) c = substr($i, 7)
        else if ($i ~ /^peak_gb=/) p = substr($i, 9)
        else if ($i ~ /^rc=/) rc = substr($i, 4)
      }
      if (p == "" || !(rc ~ /^[0-9]+$/ && rc + 0 == 0)) next
      lc = lclass($2); if (lc == "") lc = $2
      if (lc != cls && c != cls) next
      k++; peak[k] = p + 0
    }
    END {
      if (k == 0) exit
      top = 0; nc = 0
      for (i = k; i >= 1 && nc < n; i--) { nc++; if (peak[i] > top) top = peak[i] }
      w = ceil(factor * top); if (w < ceil(top)) w = ceil(top)
      printf "%d|%.2f|%d\n", w, top, nc
    }' "$PEAKLOG"
}

# Raise GB to its label class's floor, loudly. A no-op when GB is already at or
# above it, or when the class has no completed run on record.
_apply_reservation_floor() {  # <label>
  local cls line fl rest pk nc
  [ -n "${1:-}" ] || return 0
  cls=$(_label_class "$1")
  line=$(_class_floor "$cls")
  [ -n "$line" ] || return 0
  fl=${line%%|*}; rest=${line#*|}; pk=${rest%%|*}; nc=${rest#*|}
  case "$fl" in ""|*[!0-9]*) return 0 ;; esac
  if [ "$GB" -lt "$fl" ]; then
    echo "heavy_gate: RAISED $1: requested ${GB} GB, but the last ${nc} completed run(s) of class '$cls' peaked at ${pk} GB -- reserving ceil(${AUTO_FACTOR} x ${pk}) = ${fl} GB. A request under a recorded peak is the direction that panicked this box; if this run is genuinely smaller, give it a label of its own." >&2
    GB=$fl
  fi
}

# Resolve a weight spec for a caller. Sets GB and CLASS; prints the basis of an
# auto weight to stderr, and RAISES an explicit weight that sits below its
# label class's recorded completed peak (`_apply_reservation_floor`). Exits 64
# on a malformed spec.
_resolve_weight() {  # <spec> <label>
  local basis line
  if ! _parse_weight "$1"; then
    echo "heavy_gate: malformed weight '$1': want a whole number of GB, or auto:<class>[:<fallback-gb>] with <class> in [A-Za-z0-9_.-]" >&2
    exit 64
  fi
  CLASS=$W_CLASS
  if [ -z "$W_CLASS" ]; then GB=$W_GB; _apply_reservation_floor "${2:-}"; return 0; fi
  line=$(_auto_weight "$W_CLASS" "$W_FALLBACK")
  GB=${line%%|*}; basis=${line#*|}
  case "$GB" in ""|*[!0-9]*) echo "heavy_gate: internal: auto weight for '$1' did not resolve ('$line')" >&2; exit 70 ;; esac
  [ -n "${HEAVY_GATE_QUIET:-}" ] || echo "heavy_gate: ${2:-job}: auto:$W_CLASS -> ${GB} GB ($basis)" >&2
}

