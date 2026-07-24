#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

set -euo pipefail

INCLUDE_OLEAN_TEST_WRITE=0
MAX_OLEAN_TEST_WRITE_RERUNS=1
ONLY_CRATE="all"
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"

usage() {
    cat <<'USAGE'
Usage: scripts/run_build_regression_gate.sh [options]

Run the #1412 build-regression command policy for routine gates.

Options:
  --include-olean-test-write   Run isolated slow lane: cargo test --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-olean test_write
  --max-reruns N               Max reruns for slow lane (default: 1, must be >= 0)
  --only TARGET                all | clean-olean | clean-auto | clean-lake (default: all)
  -h, --help                   Show this help message
USAGE
}

timestamp() {
    date -u +"%Y-%m-%dT%H:%M:%SZ"
}

log() {
    echo "[build-regression][$(timestamp)] $*"
}

run_cmd() {
    local label="$1"
    shift
    log "$label: $*"
    "$@"
}

run_doc_metrics_check_in_head_snapshot() {
    local snapshot_dir
    local status=0

    snapshot_dir="$(mktemp -d "${TMPDIR:-/tmp}/Clean-doc-sync.XXXXXX")"
    if ! git archive HEAD | tar -x -C "$snapshot_dir" >/dev/null 2>&1; then
        rm -rf "$snapshot_dir"
        log "doc-sync check: failed to export HEAD snapshot"
        return 1
    fi

    log "doc-sync check: running in HEAD snapshot $snapshot_dir"
    (
        cd "$snapshot_dir" || exit 1
        python3 scripts/sync_readme_metrics.py --check
    ) || status=$?

    rm -rf "$snapshot_dir"
    return "$status"
}

run_clean_olean_test_write_lane() {
    local attempt=0
    while true; do
        log "clean-olean slow lane attempt=${attempt}: cargo test --locked --message-format=short -j $CARGO_BUILD_JOBS -p clean-olean test_write"
        if CLEAN_OLEAN_TEST_WRITE_LANE=1 \
            CLEAN_OLEAN_TEST_WRITE_RERUN="${attempt}" \
            cargo test --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-olean test_write; then
            log "clean-olean slow lane passed on attempt=${attempt}"
            return 0
        fi

        if ((attempt >= MAX_OLEAN_TEST_WRITE_RERUNS)); then
            log "clean-olean slow lane failed after ${attempt} reruns"
            return 1
        fi

        attempt=$((attempt + 1))
        log "rerunning clean-olean slow lane (rerun ${attempt}/${MAX_OLEAN_TEST_WRITE_RERUNS})"
    done
}

while [[ $# -gt 0 ]]; do
    case "$1" in
    --include-olean-test-write)
        INCLUDE_OLEAN_TEST_WRITE=1
        shift
        ;;
    --max-reruns)
        if [[ $# -lt 2 ]]; then
            echo "error: --max-reruns requires a value" >&2
            usage
            exit 2
        fi
        MAX_OLEAN_TEST_WRITE_RERUNS="$2"
        shift 2
        ;;
    --only)
        if [[ $# -lt 2 ]]; then
            echo "error: --only requires a value" >&2
            usage
            exit 2
        fi
        ONLY_CRATE="$2"
        shift 2
        ;;
    -h | --help)
        usage
        exit 0
        ;;
    *)
        echo "error: unknown option: $1" >&2
        usage
        exit 2
        ;;
    esac
done

case "$ONLY_CRATE" in
all | clean-olean | clean-auto | clean-lake) ;;
*)
    echo "error: --only must be one of: all, clean-olean, clean-auto, clean-lake" >&2
    exit 2
    ;;
esac

if ! [[ "$MAX_OLEAN_TEST_WRITE_RERUNS" =~ ^[0-9]+$ ]]; then
    echo "error: --max-reruns must be a non-negative integer" >&2
    exit 2
fi

# Doc-metrics staleness check (runs early, fast, unconditional for --only all)
if [[ "$ONLY_CRATE" == "all" ]]; then
    run_doc_metrics_check_in_head_snapshot
fi

if [[ "$ONLY_CRATE" == "all" || "$ONLY_CRATE" == "clean-olean" ]]; then
    run_cmd "routine gate" cargo check --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-olean --tests
fi

if [[ "$ONLY_CRATE" == "all" || "$ONLY_CRATE" == "clean-auto" ]]; then
    run_cmd "routine gate" cargo check --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-auto
    # ay-smt gate removed: ay-smt is now a default feature (#2402)
fi

if [[ "$ONLY_CRATE" == "all" || "$ONLY_CRATE" == "clean-lake" ]]; then
    run_cmd "routine gate" cargo check --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-lake --tests
fi

if ((INCLUDE_OLEAN_TEST_WRITE == 1)) && [[ "$ONLY_CRATE" != "clean-auto" && "$ONLY_CRATE" != "clean-lake" ]]; then
    run_clean_olean_test_write_lane
fi

log "build-regression gate completed"
