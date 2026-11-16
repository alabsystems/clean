#!/bin/bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Self-test for heavy_gate.sh's DERIVED weights (`run auto:<class>`,
# scripts/heavy_gate_weights.sh). Runs in an isolated gate dir with the
# physical-RAM test seam, so it never touches the machine-wide queue.
# Invoked by `heavy_gate.sh selftest-auto`, by `heavy_gate.sh selftest`, and --
# as a scripts/test_*.sh suite -- by scripts/check_script_selftests.sh, which is
# the full local gate's runner for these.
set -uo pipefail
GATE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/heavy_gate.sh"
# The derived-weight arms (2026-09-24), in an isolated gate dir, over
# synthetic peak logs plus ONE real job whose measured peak must come back
# as the next reservation. Seconds, not minutes, so a runner can afford it.
fails=0
td=$(mktemp -d "${TMPDIR:-/tmp}/heavy_gate_auto.XXXXXX") || exit 1
_aw() {  # _aw <name> <expected-gb> <spec> <log-lines...>: seed a log, resolve, compare
  local name=$1 want=$2 spec=$3 got d; shift 3
  d="$td/$name"; d=${d// /_}; mkdir -p "$d"
  printf '%s\n' "$@" >"$d/peaks.log"
  got=$(HEAVY_GATE_DIR="$d" HEAVY_GATE_PHYS_GB=128 HEAVY_GATE_AUTO_WINDOW="${AW_WINDOW:-10}" HEAVY_GATE_AUTO_FACTOR="${AW_FACTOR:-1.3}" \
          "$GATE" weight "$spec" | cut -f1)
  if [ "$got" = "$want" ]; then echo "  selftest ok: $name (-> $got GB)"
  else echo "  selftest FAILED: $name (want $want GB, got '$got')"; fails=$((fails+1)); fi
}
L='2026-09-24T00:00:00Z lbl reserved=4 pct=0 dur=0m10s'
_aw "an unseen class reserves the explicit fallback" 7 auto:never:7 "${L/pct/peak_gb=3.00 pct} rc=0 class=other"
_aw "an unseen class with no fallback reserves the default" 12 auto:never "${L/pct/peak_gb=3.00 pct} rc=0 class=other"
_aw "the weight is ceil(1.3 x the max completed peak)" 8 auto:c:12 \
  "${L/pct/peak_gb=2.00 pct} rc=0 class=c" "${L/pct/peak_gb=5.50 pct} rc=101 class=c" \
  "${L/pct/peak_gb=3.00 pct} rc=0 class=c"
# 1.1 x 50 is 55.00000000000001 in binary floating point; a naive ceil
# reserves 56. (1.3 x any two-decimal peak happens to round exactly, so the
# default factor cannot show it.)
AW_FACTOR=1.1
_aw "1.1 x 50 is 55, not 56 (float ceil)" 55 auto:c:4 "${L/pct/peak_gb=50.00 pct} rc=0 class=c"
AW_FACTOR=1.3
_aw "a completed run LOWERS the weight once older peaks age out of the window" 6 auto:c:12 \
  "${L/pct/peak_gb=20.00 pct} rc=0 class=c" "${L/pct/peak_gb=19.00 pct} rc=0 class=c" \
  "${L/pct/peak_gb=4.00 pct} rc=0 class=c" "${L/pct/peak_gb=1.00 pct} rc=0 class=c" \
  "${L/pct/peak_gb=1.00 pct} rc=0 class=c" "${L/pct/peak_gb=1.00 pct} rc=0 class=c" \
  "${L/pct/peak_gb=1.00 pct} rc=0 class=c" "${L/pct/peak_gb=1.00 pct} rc=0 class=c" \
  "${L/pct/peak_gb=1.00 pct} rc=0 class=c" "${L/pct/peak_gb=1.00 pct} rc=0 class=c" \
  "${L/pct/peak_gb=1.00 pct} rc=0 class=c" "${L/pct/peak_gb=1.00 pct} rc=0 class=c"
_aw "a KILLED run newer than the window RAISES the weight" 12 auto:c:2 \
  "${L/pct/peak_gb=4.00 pct} rc=0 class=c" "${L/pct/peak_gb=9.00 pct} rc=143 class=c"
# At WINDOW 1 a killed run read as a completion would be the whole window and
# cut 11 GB to 1 -- the verify_runner 2026-08-30 shape (44 GB cut to 2).
AW_WINDOW=1
_aw "a KILLED run never LOWERS it, even as the newest row of a 1-run window" 11 auto:c:2 \
  "${L/pct/peak_gb=8.00 pct} rc=0 class=c" "${L/pct/peak_gb=0.50 pct} rc=137 class=c"
_aw "a run with no recorded rc is read as killed, never as a completion" 11 auto:c:2 \
  "${L/pct/peak_gb=8.00 pct} rc=0 class=c" "${L/pct/peak_gb=0.50 pct} class=c"
_aw "a FAILED run (rc 1) never LOWERS it either: it may have stopped at its first step" 11 auto:c:2 \
  "${L/pct/peak_gb=8.00 pct} rc=0 class=c" "${L/pct/peak_gb=0.06 pct} rc=1 class=c"
AW_WINDOW=10
_aw "a failed-only history never lowers the fallback (2026-09-29: rc 1 at 0.06 GB)" 12 auto:c:12 \
  "${L/pct/peak_gb=0.06 pct} rc=1 class=c"
_aw "a killed-only history raises the fallback" 10 auto:c:4 "${L/pct/peak_gb=7.10 pct} rc=130 class=c"
_aw "a killed-only history never lowers the fallback" 9 auto:c:9 "${L/pct/peak_gb=0.40 pct} rc=130 class=c"
_aw "the floor holds under a tiny peak" 1 auto:c:12 "${L/pct/peak_gb=0.01 pct} rc=0 class=c"
# The local gate scopes these existing auto classes to a conservative minimum.
# Synthetic rows qualify resolver behavior only, never a real workload peak.
HEAVY_GATE_AUTO_FLOOR_GB=47 _aw "frontend warm run cannot lower the compiler floor" 47 auto:frontend-suite-run:47 \
  "${L/pct/peak_gb=0.01 pct} rc=0 class=frontend-suite-run"
HEAVY_GATE_AUTO_FLOOR_GB=47 _aw "frontend high partial peak still raises above47" 65 auto:frontend-suite-run:47 \
  "${L/pct/peak_gb=3.00 pct} rc=0 class=frontend-suite-run" \
  "${L/pct/peak_gb=50.00 pct} rc=130 class=frontend-suite-run"
HEAVY_GATE_AUTO_FLOOR_GB=96 _aw "frontend higher valid auto floor is preserved" 96 auto:frontend-suite-doc:47 \
  "${L/pct/peak_gb=0.01 pct} rc=0 class=frontend-suite-doc"
mkdir -p "$td/factor"; printf '%s\n' "${L/pct/peak_gb=7.20 pct} rc=0 class=c" >"$td/factor/peaks.log"
_fw=$(HEAVY_GATE_DIR="$td/factor" HEAVY_GATE_PHYS_GB=128 HEAVY_GATE_AUTO_FACTOR=0.5 "$GATE" weight auto:c:12 | cut -f1)
if [ "$_fw" = 8 ]; then echo "  selftest ok: never below an observed peak at factor 0.5 (-> 8 GB)"
else echo "  selftest FAILED: at factor 0.5 a 7.20 GB peak resolved to '$_fw' GB (want 8)"; fails=$((fails+1)); fi
_aw "classes do not leak: another class, a legacy line and a prefix class are ignored" 3 auto:build:12 \
  "${L/pct/peak_gb=2.00 pct} rc=0 class=build" "${L/pct/peak_gb=30.00 pct} rc=0 class=build-cold" \
  "${L/pct/peak_gb=25.00 pct}" "2026-09-24T00:00:00Z build reserved=4 peak_gb=26.00 pct=0 dur=0m10s"
for bad in auto: "auto:bad class" auto:x:abc auto:x: 12x ""; do
  if HEAVY_GATE_DIR="$td/bad" HEAVY_GATE_PHYS_GB=128 "$GATE" run "$bad" st-bad -- true >/dev/null 2>&1; then
    echo "  selftest FAILED: malformed weight '$bad' was ADMITTED"; fails=$((fails+1))
  else rc=$?; [ "$rc" -eq 64 ] && echo "  selftest ok: malformed weight '$bad' refused (exit 64)" \
    || { echo "  selftest FAILED: malformed weight '$bad' exited $rc, want 64"; fails=$((fails+1)); }
  fi
done
_st_rc=0
HEAVY_GATE_DIR="$td/num" HEAVY_GATE_PHYS_GB=128 "$GATE" run 3 st-numeric -- sh -c 'exit 5' >/dev/null 2>&1 || _st_rc=$?
if [ "$_st_rc" -eq 5 ]; then echo "  selftest ok: an explicit numeric weight still runs and passes its exit code"
else echo "  selftest FAILED: explicit numeric weight run exited $_st_rc, want 5"; fails=$((fails+1)); fi
# The loop closes through a REAL job: its measured peak and exit code are
# recorded under its class, and the next resolution reserves from them.
HEAVY_GATE_DIR="$td/e2e" HEAVY_GATE_PHYS_GB=128 HEAVY_GATE_SAMPLE_S=1 "$GATE" run auto:st-e2e:1 st-e2e -- \
  python3 -c 'import time
b = bytearray(1073741824)
for i in range(0, len(b), 4096): b[i] = 1
time.sleep(4)' >/dev/null 2>&1
_e2e_line=$(grep ' class=st-e2e$' "$td/e2e/peaks.log" 2>/dev/null | tail -1)
_e2e_w=$(HEAVY_GATE_DIR="$td/e2e" HEAVY_GATE_PHYS_GB=128 "$GATE" weight auto:st-e2e:1 | cut -f1)
case "$_e2e_line" in
  *" rc=0 class=st-e2e") ;;
  *) echo "  selftest FAILED: a real auto run left no 'rc=0 class=st-e2e' peak line: '$_e2e_line'"; fails=$((fails+1)) ;;
esac
if [ -n "$_e2e_w" ] && [ "$_e2e_w" -ge 2 ]; then
  echo "  selftest ok: a real 1 GiB job's peak sizes the next auto:st-e2e reservation (-> $_e2e_w GB)"
else
  echo "  selftest FAILED: after a 1 GiB job, auto:st-e2e resolved to '$_e2e_w' GB (want >= 2)"; fails=$((fails+1))
fi
# ---- the FLOOR under an explicit weight (2026-10-01). Every arm below that
# expects a RAISE is RED under the old rule, which reserved the typed number.
_fw() {  # _fw <name> <expected-gb> <gb> <label> <log-lines...>
  local name=$1 want=$2 gb=$3 lbl=$4 got d; shift 4
  d="$td/floor-$name"; d=${d// /_}; mkdir -p "$d"
  printf '%s\n' "$@" >"$d/peaks.log"
  got=$(HEAVY_GATE_DIR="$d" HEAVY_GATE_PHYS_GB=128 HEAVY_GATE_AUTO_WINDOW="${AW_WINDOW:-10}" \
          "$GATE" weight "$gb" "$lbl" | cut -f1)
  if [ "$got" = "$want" ]; then echo "  selftest ok: $name (-> $got GB)"
  else echo "  selftest FAILED: $name (want $want GB, got '$got')"; fails=$((fails+1)); fi
}
_ln() {  # _ln <label> <peak_gb> [<tail>]: one peak-log line
  printf '2026-10-01T00:00:00Z %s reserved=1 peak_gb=%s pct=0 dur=0m10s%s' "$1" "$2" "${3:+ $3}"
}
_fw "an explicit weight under ceil(1.3 x its label class's completed peak) is RAISED" 10 4 job-r3 \
  "$(_ln job-r1 7.00 rc=0)"
_fw "trailing digits and -vN/-dN decorations share one class" 4 2 job-v4 "$(_ln job2 3.00 rc=0)"
_fw "a -dN label reads the same class" 4 2 job-d1 "$(_ln job 3.00 rc=0)"
_fw "a weight at or above the floor is kept" 16 16 job-r3 "$(_ln job-r1 7.00 rc=0)"
_fw "killed, failed and rc-less runs never set the floor" 4 4 job-r3 \
  "$(_ln job-r1 9.00 rc=137)" "$(_ln job-r2 9.00 rc=1)" "$(_ln job-r4 9.00)"
_fw "a run filed under auto:<class> sets that class's floor" 10 4 job-r5 \
  "$(_ln someone-else 7.00 'rc=0 class=job')"
_fw "other classes do not leak (a longer name, a prefix, another auto class)" 4 4 job-r1 \
  "$(_ln job-cold 30.00 rc=0)" "$(_ln jobs 30.00 rc=0)" "$(_ln x 30.00 'rc=0 class=jobx')"
AW_WINDOW=2
_fw "the floor reads only the last WINDOW completed runs" 3 1 job-r9 \
  "$(_ln job-r1 20.00 rc=0)" "$(_ln job-r2 2.00 rc=0)" "$(_ln job-r3 2.00 rc=0)"
AW_WINDOW=10
# Through `run`: the RESERVATION itself is raised, and the caller is told.
mkdir -p "$td/floor-run"; _ln st-floor-r1 3.00 rc=0 >"$td/floor-run/peaks.log"; echo >>"$td/floor-run/peaks.log"
# A sampled job (an unsampled one leaves no peak line to read the reservation from).
_fr_err=$(HEAVY_GATE_DIR="$td/floor-run" HEAVY_GATE_PHYS_GB=128 HEAVY_GATE_SAMPLE_S=1 \
            "$GATE" run 1 st-floor-r2 -- sleep 2 2>&1 >/dev/null)
_fr_line=$(grep ' st-floor-r2 ' "$td/floor-run/peaks.log" | tail -1)
case "$_fr_line" in
  *" reserved=4 "*) echo "  selftest ok: run 1 under a 3.00 GB class peak reserved 4 GB" ;;
  *) echo "  selftest FAILED: run 1 under a 3.00 GB class peak recorded '$_fr_line' (want reserved=4)"; fails=$((fails+1)) ;;
esac
case "$_fr_err" in
  *"RAISED st-floor-r2: requested 1 GB"*"peaked at 3.00 GB"*"= 4 GB"*) echo "  selftest ok: the raise is printed with the requested weight, the class peak and the raised weight" ;;
  *) echo "  selftest FAILED: no loud RAISED line on stderr: '$_fr_err'"; fails=$((fails+1)) ;;
esac
# Through a direct `acquire` (verify_runner's path): the TOKEN carries the raised weight.
_fa_tok=$(HEAVY_GATE_DIR="$td/floor-run" HEAVY_GATE_PHYS_GB=128 HEAVY_GATE_OWNER_PID=$$ \
            "$GATE" acquire 1 st-floor-r3 2>/dev/null)
_fa_req=$(awk '{print $2}' "$_fa_tok" 2>/dev/null)
HEAVY_GATE_DIR="$td/floor-run" HEAVY_GATE_PHYS_GB=128 "$GATE" release "$_fa_tok" >/dev/null 2>&1
if [ "$_fa_req" = 4 ]; then echo "  selftest ok: acquire 1 under a 3.00 GB class peak holds a 4 GB token"
else echo "  selftest FAILED: acquire 1 under a 3.00 GB class peak holds '$_fa_req' GB (want 4)"; fails=$((fails+1)); fi
# A waiting acquire whose ticket another process reaped (2026-10-05: an unfair
# lock kept one waiter out past TICKET_STALE_S) must restore it, with its
# owner, under the same name. Under the old `touch` re-stamp the ticket came
# back EMPTY and the next reap removed it for good.
_tk="$td/ticket"; mkdir -p "$_tk/tokens" "$_tk/queue"
printf '%s 10 st-ticket-holder %s\n' "$$" "$(date -u +%FT%TZ)" >"$_tk/tokens/0-$$-holder"
HEAVY_GATE_DIR="$_tk" HEAVY_GATE_PHYS_GB=128 HEAVY_GATE_BUDGET_GB=10 HEAVY_GATE_OWNER_PID=$$ \
  "$GATE" acquire 4 st-ticket-waiter >/dev/null 2>&1 &
_tk_pid=$!
_tk_name=""
for _ in $(seq 50); do _tk_name=$(ls "$_tk/queue" 2>/dev/null | head -1); [ -n "$_tk_name" ] && break; sleep 0.2; done
_tk_back=""
if [ -n "$_tk_name" ]; then
  rm -f "$_tk/queue/$_tk_name"   # the false-stale reap
  for _ in $(seq 60); do
    [ -s "$_tk/queue/$_tk_name" ] && { _tk_back=$(awk 'NR==1{print $1" "$3}' "$_tk/queue/$_tk_name"); break; }
    sleep 0.2
  done
fi
kill -TERM "$_tk_pid" 2>/dev/null; wait "$_tk_pid" 2>/dev/null
if [ "$_tk_back" = "$$ st-ticket-waiter" ]; then echo "  selftest ok: a waiting acquire restores its reaped ticket with its owner and position"
else echo "  selftest FAILED: reaped ticket '${_tk_name:-<never queued>}' came back as '$_tk_back' (want '$$ st-ticket-waiter')"; fails=$((fails+1)); fi
# Backfill admission is part of the same resource manager whose current
# source is qualified by this registry replay entry point. Keep its independent
# completion-subset oracle and real queue controls in that qualification.
python3 "$(dirname "$GATE")/test_heavy_gate_backfill.py" || fails=$((fails+1))
# Peak-report advice is part of the same tool: failed prefixes must never teach
# a smaller reservation, while successful and under-reserved runs retain their
# existing recommendations. Keep the focused synthetic regression in this
# registry replay entry point rather than leaving it as an unwired test file.
bash "$(dirname "$GATE")/test_heavy_gate_peak_report.sh" || fails=$((fails+1))
rm -rf "$td"
if [ "$fails" -gt 0 ]; then echo "selftest-auto: $fails arm(s) FAILED"; exit 1; fi
echo "selftest-auto: all arms green"; exit 0
