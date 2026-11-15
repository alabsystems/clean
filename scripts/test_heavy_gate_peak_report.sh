#!/bin/bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
# Deterministic reporting regression: synthetic peaks, isolated ledger, no jobs.
set -euo pipefail
GATE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/heavy_gate.sh"
td=$(mktemp -d "${TMPDIR:-/tmp}/heavy_gate_report.XXXXXX")
trap 'rm -rf "$td"' EXIT
export HEAVY_GATE_DIR="$td/ledger" HEAVY_GATE_PHYS_GB=128 HEAVY_GATE_QUIET=1
# Source the real reporting/resolver functions through its ordinary read-only
# status entry. The explicit private directory never touches the machine ledger.
. "$GATE" status >/dev/null
printf '32768\n' > "$td/peak"
_peak_report 39 completed "$td/peak" 2 0 >"$td/ok" 2>&1
grep -q 'OVER-RESERVED' "$td/ok"
grep -q 'Re-derive the weight' "$td/ok"
for rc in 75 1 143 ''; do
    _peak_report 39 incomplete "$td/peak" 2 "$rc" incomplete >"$td/incomplete" 2>&1
    if grep -Eq 'OVER-RESERVED|Re-derive|re-derives' "$td/incomplete"; then
        echo "failed/unknown rc=$rc recommended a smaller reservation" >&2
        exit 1
    fi
done
# Refusals are retained as losses; they do not teach the auto resolver a 1 GB
# reservation in place of its unchanged 39 GB fallback.
grep -q 'reserved=39 .*rc=75 class=incomplete' "$PEAKLOG"
case "$(_auto_weight incomplete 39)" in
    39'|'*) ;;
    *) echo 'failed-only observations lowered the auto reservation' >&2; exit 1 ;;
esac
# A failed prefix can still demonstrate TOO LITTLE memory. Preserve that warning.
printf '2097152\n' > "$td/peak"
_peak_report 1 under "$td/peak" 2 75 >"$td/under" 2>&1
grep -q 'UNDER-RESERVED' "$td/under"
grep -q 'Raise the weight' "$td/under"
# A live owner remains incomplete however many small high-water observations
# exist. Keep telemetry, but do not recommend a smaller future reservation.
mkdir -p "$TOKENS" "$PEAKD"
printf '%s 39 live-reporting 2026-11-15T00:00:00Z\n' "$$" > "$TOKENS/live"
cp "$TOKENS/live" "$td/token-before"
cp "$PEAKLOG" "$td/log-before"
for samples in 3 100; do
    printf '32768 %s\n' "$samples" > "$PEAKD/live"
    "$GATE" status > "$td/live-status"
    grep -q 'live-reporting.*peak ' "$td/live-status"
    if grep -Eq 'OVER-RESERVED|Re-derive it|x1.5 =' "$td/live-status"; then
        echo "unfinished live owner recommended downsizing after $samples samples" >&2
        exit 1
    fi
    cmp "$TOKENS/live" "$td/token-before"
    cmp "$PEAKLOG" "$td/log-before"
done
# A high observed peak can still establish an under-reservation immediately.
printf '%s 1 live-under 2026-11-15T00:00:00Z\n' "$$" > "$TOKENS/live"
printf '2097152 0\n' > "$PEAKD/live"
"$GATE" status > "$td/live-under"
grep -q 'live-under.*UNDER-RESERVED' "$td/live-under"
grep -q 'UNDER-RESERVED: pid' "$td/live-under"
echo 'peak reporting: completed, failed, unknown, live partial and under-reservation controls passed'
