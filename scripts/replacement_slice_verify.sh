#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Run the fast Lean4-replacement evidence gates without flooding the terminal.
#
# The replacement epic needs frequent verification while the workspace still has
# many unrelated Rust warnings. This wrapper keeps cargo jobs bounded, captures
# full logs under target/, and runs replacement reports from the already-built
# binary so operators can inspect failures without pushing huge warning output
# through agent sessions.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
LOG_DIR="${CLEAN_REPLACEMENT_LOG_DIR:-$REPO_ROOT/target/replacement-slice-verify}"
TAIL_LINES="${CLEAN_REPLACEMENT_TAIL_LINES:-120}"

export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"

mkdir -p "$LOG_DIR"
cd "$REPO_ROOT"

log_path() {
    local name="$1"
    printf "%s/%s.log" "$LOG_DIR" "$name"
}

run_logged() {
    local name="$1"
    shift

    local log
    log="$(log_path "$name")"
    printf "replacement_slice_verify: running %s\n" "$name"
    if "$@" >"$log" 2>&1; then
        printf "replacement_slice_verify: PASS %s (log: %s)\n" "$name" "$log"
        return 0
    fi

    printf "replacement_slice_verify: FAIL %s (log: %s)\n" "$name" "$log" >&2
    printf "replacement_slice_verify: last %s log lines:\n" "$TAIL_LINES" >&2
    tail -n "$TAIL_LINES" "$log" >&2
    return 1
}

run_json_report() {
    local name="$1"
    shift

    local json
    json="$LOG_DIR/$name.json"
    printf "replacement_slice_verify: running %s\n" "$name"
    if "$@" >"$json"; then
        python3 -m json.tool "$json" >/dev/null
        printf "replacement_slice_verify: PASS %s (json: %s)\n" "$name" "$json"
        return 0
    fi

    printf "replacement_slice_verify: FAIL %s (json: %s)\n" "$name" "$json" >&2
    return 1
}

TARGET_DIR="${CARGO_TARGET_DIR:-$REPO_ROOT/target}"
if [[ "$TARGET_DIR" != /* ]]; then
    TARGET_DIR="$REPO_ROOT/$TARGET_DIR"
fi

if [[ -n "${CARGO_BUILD_TARGET:-}" ]]; then
    CLEAN_BIN="$TARGET_DIR/$CARGO_BUILD_TARGET/debug/clean"
else
    CLEAN_BIN="$TARGET_DIR/debug/clean"
fi

run_logged cargo-build-clean cargo build --quiet --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean --bin clean
run_logged cli-replacement-unit cargo test --quiet --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-cli cmd_replacement --lib
run_logged cli-docs-drift cargo test --quiet --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-cli --test docs_drift
run_logged cli-feature-coverage cargo test --quiet --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-cli --test feature_coverage
run_logged cli-lake-delegation cargo test --quiet --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-cli --test lake_replacement_delegation
run_logged mathverse-native-gate cargo test --quiet --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-mathverse --test native_gate_integration

run_json_report replacement-status "$CLEAN_BIN" replacement status --json
run_json_report replacement-tactic-parity "$CLEAN_BIN" replacement tactic-parity --json
run_json_report replacement-trust-core-evidence "$CLEAN_BIN" replacement trust-core-evidence --json

printf "replacement_slice_verify: PASS all gates (logs: %s)\n" "$LOG_DIR"
