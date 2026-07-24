#!/bin/bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Run tactic tests with sorry location tracking and report census.
# Compares against scripts/sorry_baseline.json if it exists.
#
# Usage:
#   ./scripts/sorry_census.sh          # Run census, compare against baseline
#   ./scripts/sorry_census.sh --update  # Run census, update baseline file
#
# Part of #1144

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BASELINE_FILE="$PROJECT_ROOT/scripts/sorry_baseline.json"

export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"

UPDATE_BASELINE=false
if [[ "${1:-}" == "--update" ]]; then
    UPDATE_BASELINE=true
fi

echo "=== Sorry Census ==="
echo "Running tactic tests with sorry tracking..."

# Run the sorry census test which reports cumulative sorry count.
# We run the full tactic test suite first (to accumulate sorry terms),
# then the census test reads the cumulative count.
output_file="$(mktemp "${TMPDIR:-/tmp}/Clean-sorry-census.XXXXXX")"
trap 'rm -f "$output_file"' EXIT

CARGO_ALLOW_FULL_SUITE=1 cargo test --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-elab --lib -- tactic --nocapture >"$output_file" 2>&1 || true

# Extract the sorry count from census output
census_line=$(grep "Cumulative sorry terms" "$output_file" | tail -1 || true)
if [[ -n "$census_line" ]]; then
    current_count=$(printf '%s\n' "$census_line" | grep -o '[0-9]*$')
    echo "Current sorry count: $current_count"
else
    echo "WARNING: Could not extract sorry count from test output"
    echo "--- cargo output tail ---"
    tail -200 "$output_file" || true
    echo "--- end cargo output tail ---"
    echo "Debug with: debug_log=\"\${TMPDIR:-/tmp}/Clean-sorry-census-debug.log\"; cargo test --locked --message-format=short -j \"\$CARGO_BUILD_JOBS\" -p clean-elab --lib -- sorry_census --nocapture >\"\$debug_log\" 2>&1; tail -200 \"\$debug_log\""
    exit 1
fi

# Compare against baseline
if [[ -f "$BASELINE_FILE" ]]; then
    baseline=$(jq -r '.sorry_count_baseline' "$BASELINE_FILE")
    echo "Baseline: $baseline"

    if [[ "$current_count" -gt "$baseline" ]]; then
        echo ""
        echo "FAIL: Sorry count increased from $baseline to $current_count"
        echo "Proof reconstruction regressed. Fix the regression or update baseline with justification."
        exit 1
    elif [[ "$current_count" -lt "$baseline" ]]; then
        echo "IMPROVEMENT: Sorry count decreased from $baseline to $current_count"
        if $UPDATE_BASELINE; then
            echo "Updating baseline..."
        fi
    else
        echo "OK: Sorry count matches baseline ($baseline)"
    fi
else
    echo "No baseline file found at $BASELINE_FILE"
fi

# Update baseline if requested
if $UPDATE_BASELINE; then
    mkdir -p "$(dirname "$BASELINE_FILE")"
    cat >"$BASELINE_FILE" <<BASELINE_EOF
{
    "sorry_count_baseline": $current_count,
    "date": "$(date +%Y-%m-%d)",
    "note": "Ratchet: new tests must not increase sorry count"
}
BASELINE_EOF
    echo "Updated baseline to $current_count"
fi

echo "=== End Sorry Census ==="
