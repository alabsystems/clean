#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Project Maintainers
# SPDX-License-Identifier: Apache-2.0
#
# Run one clean-elab frontend integration test through a bounded Cargo lane.
#
# The clean-elab integration binary can consume very large memory when launched
# with a broad substring filter. Require a fully qualified test path and pass
# --exact so replacement/frontend validation does not accidentally fan into the
# full integration corpus.

set -euo pipefail

export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"
TAIL_LINES="${FRONTEND_INTEGRATION_TAIL_LINES:-120}"
FILTER=""
NOCAPTURE=false

usage() {
    cat <<'EOF'
Usage: ./scripts/run_frontend_integration_exact.sh --filter <module::test> [--nocapture]

Runs:
  cargo test --locked --message-format=short -j "$CARGO_BUILD_JOBS" \
    -p clean-elab --test integration -- <module::test> --exact

Examples:
  ./scripts/run_frontend_integration_exact.sh --filter lean4_phase1_compat::lean4_phase1_compat

Environment:
  CARGO_BUILD_JOBS defaults to 1.
  FRONTEND_INTEGRATION_TAIL_LINES defaults to 120 for failure summaries.
  FRONTEND_INTEGRATION_LOG overrides the temporary log path.
EOF
}

while [ "$#" -gt 0 ]; do
    case "$1" in
    --filter)
        if [ "$#" -lt 2 ] || [ -z "$2" ]; then
            echo "ERROR: --filter requires a fully qualified test path" >&2
            exit 2
        fi
        FILTER="$2"
        shift 2
        ;;
    --nocapture)
        NOCAPTURE=true
        shift
        ;;
    -h | --help)
        usage
        exit 0
        ;;
    *)
        echo "ERROR: unknown argument: $1" >&2
        usage >&2
        exit 2
        ;;
    esac
done

if [ -z "$FILTER" ]; then
    echo "ERROR: pass --filter <module::test>; broad frontend integration runs are blocked" >&2
    exit 2
fi

if [[ "$FILTER" != *::* ]]; then
    echo "ERROR: frontend integration filter must be fully qualified, for example lean4_phase1_compat::lean4_phase1_compat" >&2
    exit 2
fi

if ! [[ "$TAIL_LINES" =~ ^[0-9]+$ ]] || [ "$TAIL_LINES" -lt 1 ]; then
    echo "ERROR: FRONTEND_INTEGRATION_TAIL_LINES must be a positive integer" >&2
    exit 2
fi

LOG_PATH="${FRONTEND_INTEGRATION_LOG:-}"
if [ -z "$LOG_PATH" ]; then
    LOG_PATH="$(mktemp -t Clean-frontend-integration.XXXXXX.log)"
fi

cargo_cmd=(
    cargo test --locked --message-format=short -j "$CARGO_BUILD_JOBS"
    -p clean-elab --test integration -- "$FILTER" --exact
)

if [ "$NOCAPTURE" = true ]; then
    cargo_cmd+=("--nocapture")
fi

echo "Running bounded frontend integration test: $FILTER"
echo "Cargo output: $LOG_PATH"

if "${cargo_cmd[@]}" >"$LOG_PATH" 2>&1; then
    echo "PASS: $FILTER"
else
    status=$?
    echo "ERROR: frontend integration test failed: $FILTER" >&2
    echo "Showing last $TAIL_LINES lines from $LOG_PATH" >&2
    tail -n "$TAIL_LINES" "$LOG_PATH" >&2 || true
    exit "$status"
fi
