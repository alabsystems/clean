#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# Benchmark regression detection for Clean
# Tracking: #1485
#
# Usage:
#   ./scripts/bench_regression.sh [--baseline] [--compare] [--package PKG]
#
# Modes:
#   --baseline  Run benchmarks and save as new baseline
#   --compare   Run benchmarks and compare against saved baseline (default)
#   --package   Run only benchmarks for a specific package (clean-kernel, clean-server)
#
# Output:
#   metrics/benchmarks/baseline.json     Current baseline results
#   metrics/benchmarks/candidate.json    Latest run results
#   metrics/benchmarks/regression.json   Comparison report (on --compare)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BENCHMARKS_DIR="$REPO_ROOT/metrics/benchmarks"
BASELINE_FILE="$BENCHMARKS_DIR/baseline.json"
CANDIDATE_FILE="$BENCHMARKS_DIR/candidate.json"
REGRESSION_FILE="$BENCHMARKS_DIR/regression.json"
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"

# Regression threshold: flag if >10% slower
REGRESSION_THRESHOLD="${BENCH_REGRESSION_THRESHOLD:-10}"

if ! [[ "$REGRESSION_THRESHOLD" =~ ^[0-9]+$ ]]; then
    echo "error: BENCH_REGRESSION_THRESHOLD must be a non-negative integer" >&2
    exit 2
fi

MODE="compare"
PACKAGE=""

while [[ $# -gt 0 ]]; do
    case "$1" in
    --baseline)
        MODE="baseline"
        shift
        ;;
    --compare)
        MODE="compare"
        shift
        ;;
    --package)
        PACKAGE="$2"
        shift 2
        ;;
    -h | --help)
        echo "Usage: $0 [--baseline] [--compare] [--package PKG]"
        echo ""
        echo "Modes:"
        echo "  --baseline  Run benchmarks and save as new baseline"
        echo "  --compare   Run benchmarks and compare against baseline (default)"
        echo "  --package   Restrict to one package (clean-kernel or clean-server)"
        exit 0
        ;;
    *)
        echo "Unknown option: $1"
        exit 1
        ;;
    esac
done

case "$PACKAGE" in
"" | clean-kernel | clean-server) ;;
*)
    echo "error: --package must be one of: clean-kernel, clean-server" >&2
    exit 2
    ;;
esac

mkdir -p "$BENCHMARKS_DIR"

# Build package list
PACKAGES=("clean-kernel" "clean-server")
if [[ -n "$PACKAGE" ]]; then
    PACKAGES=("$PACKAGE")
fi

# Run criterion benchmarks and extract JSON estimates
run_benchmarks() {
    local output_file="$1"
    local results="{}"
    local git_commit
    git_commit="$(git -C "$REPO_ROOT" rev-parse --short HEAD)"
    local timestamp
    timestamp="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

    for pkg in "${PACKAGES[@]}"; do
        echo "[bench] Running benchmarks for $pkg..."

        # Run criterion benchmarks and parse bencher format output.
        # Keep the full benchmark name intact so names with spaces do not collide.
        local bench_output
        bench_output="$(cargo bench --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p "$pkg" -- --output-format=bencher 2>/dev/null)"
        while IFS= read -r line; do
            # Parse: "test <name> ... bench: <ns> ns/iter (+/- <variance>)"
            if [[ "$line" =~ ^test\ (.+)\ \.\.\.\ bench:\ +([0-9,]+)\ ns/iter ]]; then
                local name="${BASH_REMATCH[1]}"
                local ns="${BASH_REMATCH[2]//,/}"
                local key
                key="${pkg}::$(printf '%s' "$name" | tr '/' '_' | tr ' ' '_')"
                results="$(jq -cn \
                    --argjson current "$results" \
                    --arg k "$key" \
                    --argjson ns "$ns" \
                    --arg pkg "$pkg" \
                    '$current + {($k): {"ns_per_iter": $ns, "package": $pkg}}')"
            fi
        done <<<"$bench_output"
    done

    # Wrap results with metadata using jq
    jq -n --arg commit "$git_commit" --arg ts "$timestamp" \
        --arg jobs "$CARGO_BUILD_JOBS" \
        --arg command 'cargo bench --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p "$pkg" -- --output-format=bencher' \
        --argjson threshold "$REGRESSION_THRESHOLD" --argjson benchmarks "$results" \
        '{git_commit: $commit, timestamp: $ts, cargo_build_jobs: $jobs, cargo_command: $command, threshold_pct: $threshold, benchmarks: $benchmarks}' \
        >"$output_file"

    echo "[bench] Results written to $output_file"
}

# Compare candidate against baseline using bench_compare.py
compare_results() {
    if [[ ! -f "$BASELINE_FILE" ]]; then
        echo "[bench] No baseline found at $BASELINE_FILE"
        echo "[bench] Run with --baseline first to create one."
        exit 1
    fi

    if [[ ! -f "$CANDIDATE_FILE" ]]; then
        echo "[bench] No candidate found at $CANDIDATE_FILE"
        echo "[bench] Running benchmarks first..."
        run_benchmarks "$CANDIDATE_FILE"
    fi

    python3 "$SCRIPT_DIR/bench_compare.py" \
        "$BASELINE_FILE" "$CANDIDATE_FILE" "$REGRESSION_FILE" "$REGRESSION_THRESHOLD"
}

case "$MODE" in
baseline)
    echo "[bench] Creating baseline..."
    run_benchmarks "$BASELINE_FILE"
    echo "[bench] Baseline saved to $BASELINE_FILE"
    ;;
compare)
    echo "[bench] Running candidate benchmarks..."
    run_benchmarks "$CANDIDATE_FILE"
    echo "[bench] Comparing against baseline..."
    compare_results
    ;;
esac
