#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Differential conformance test runner for SAT/SMT proof checkers.
#
# Usage:
#   ./scripts/run_conformance.sh [--sat | --smt] [--external] [--verbose] [--nocapture] [--help]
#
# Modes:
#   Default:    Runs SAT + SMT internal conformance tests via
#               cargo test --locked --message-format=short -j "$CARGO_BUILD_JOBS"
#   --sat:      Runs only SAT conformance tests
#   --smt:      Runs only SMT/Alethe conformance tests
#   Selectors:  --sat and --smt are mutually exclusive; omit both to run both
#               families
#   --external: Also runs the currently supported SAT external checker
#               comparison path via `clean kernel lrat-conform`. SMT external
#               comparison remains unimplemented and is reported as skipped.
#   --verbose:  Shows resolved command/status details without streaming test bodies
#   --nocapture: Also forwards --nocapture to cargo test for focused debugging
#
# External SAT oracles currently wired by --external:
#   - ay-lrat-check: https://github.com/Z3Prover/z3
#   - cake_lpr:      https://github.com/tanyongkiam/cake_lpr
#
# The internal tests exercise the same proof corpus against Clean's native
# DRAT, LRAT, FRAT, and Alethe checkers. Cross-format consistency is
# verified by checking that the same UNSAT formula yields identical verdicts
# across all proof formats. Broader differential coverage against drat-trim
# and Carcara remains separate.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

EXTERNAL=false
SAT=false
SMT=false
VERBOSE=false
NOCAPTURE=false
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"

usage() {
    cat <<'EOF'
Differential conformance test runner for SAT/SMT proof checkers.

Usage:
  ./scripts/run_conformance.sh [--sat | --smt] [--external] [--verbose] [--nocapture] [--help]

Modes:
  Default:    Runs SAT + SMT internal conformance tests via
              cargo test --locked --message-format=short -j "$CARGO_BUILD_JOBS"
  --sat:      Runs only SAT conformance tests
  --smt:      Runs only SMT/Alethe conformance tests
  Selectors:  --sat and --smt are mutually exclusive; omit both to run both
              families
  --external: Also runs the currently supported SAT external checker
              comparison path via `clean kernel lrat-conform`. SMT external
              comparison remains unimplemented and is reported as skipped.
  --verbose:  Shows resolved command/status details without streaming test bodies
  --nocapture: Also forwards --nocapture to cargo test for focused debugging

External SAT oracles currently wired by --external:
  - ay-lrat-check: https://github.com/Z3Prover/z3
  - cake_lpr:      https://github.com/tanyongkiam/cake_lpr

The internal tests exercise the same proof corpus against Clean's native
DRAT, LRAT, FRAT, and Alethe checkers. Cross-format consistency is
verified by checking that the same UNSAT formula yields identical verdicts
across all proof formats. Broader differential coverage against drat-trim
and Carcara remains separate.
EOF
}

usage_error() {
    echo "$1" >&2
    echo >&2
    usage >&2
    exit 1
}

declare -a SAT_EXTERNAL_ARGS=()
declare -a SAT_EXTERNAL_TOOLS=()

resolve_tool_path() {
    local tool="$1"
    if command -v "$tool" >/dev/null 2>&1; then
        command -v "$tool"
    fi
}

resolve_sat_external_oracles() {
    SAT_EXTERNAL_ARGS=()
    SAT_EXTERNAL_TOOLS=()

    local ay_path=""
    ay_path="$(resolve_tool_path ay-lrat-check)"
    if [ -n "$ay_path" ]; then
        SAT_EXTERNAL_ARGS+=("--ay-lrat-check" "$ay_path")
        SAT_EXTERNAL_TOOLS+=("ay-lrat-check")
    fi

    local cake_path=""
    cake_path="$(resolve_tool_path cake_lpr)"
    if [ -n "$cake_path" ]; then
        SAT_EXTERNAL_ARGS+=("--cake-lpr" "$cake_path")
        SAT_EXTERNAL_TOOLS+=("cake_lpr")
    fi
}

run_sat_external_comparison() {
    resolve_sat_external_oracles
    if [ "${#SAT_EXTERNAL_ARGS[@]}" -eq 0 ]; then
        echo "WARNING: No supported SAT external oracles found (looked for ay-lrat-check and cake_lpr)."
        echo "[2/2] External checker comparison: SKIPPED (missing SAT oracles)"
        return 0
    fi

    echo "Running SAT external checker comparison via clean kernel lrat-conform..."
    local tool
    for tool in "${SAT_EXTERNAL_TOOLS[@]}"; do
        echo "  using $tool"
    done

    local external_cmd=(cargo run --locked -q --message-format=short -j "$CARGO_BUILD_JOBS" -p clean --bin clean -- kernel lrat-conform)
    external_cmd+=("${SAT_EXTERNAL_ARGS[@]}")
    "${external_cmd[@]}"
    echo "[2/2] SAT external checker comparison: PASSED"
}

for arg in "$@"; do
    case "$arg" in
    --sat) SAT=true ;;
    --smt) SMT=true ;;
    --external) EXTERNAL=true ;;
    --verbose) VERBOSE=true ;;
    --nocapture) NOCAPTURE=true ;;
    --help | -h)
        usage
        exit 0
        ;;
    *)
        echo "Unknown argument: $arg" >&2
        exit 1
        ;;
    esac
done

if [ "$SAT" = true ] && [ "$SMT" = true ]; then
    usage_error "Conflicting selectors: --sat and --smt cannot be used together. Omit both flags to run SAT + SMT."
fi

echo "=== Clean conformance tests ==="
echo ""

# --- Internal conformance tests (always run) ---
INTERNAL_SCOPE="SAT + SMT"
FILTER="conformance"

if [ "$SAT" = true ] && [ "$SMT" = false ]; then
    INTERNAL_SCOPE="SAT only"
    FILTER="sat_verify::conformance_tests::"
elif [ "$SAT" = false ] && [ "$SMT" = true ]; then
    INTERNAL_SCOPE="SMT only"
    FILTER="smt_verify::conformance_tests::"
fi

echo "[1/2] Running internal conformance tests ($INTERNAL_SCOPE)..."
cd "$REPO_ROOT"
cargo_cmd=(cargo test --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-verify --lib -- "$FILTER")
if [ "$VERBOSE" = true ]; then
    printf 'cargo:'
    printf ' %q' "${cargo_cmd[@]}"
    printf '\n'
fi
if [ "$NOCAPTURE" = true ]; then
    cargo_cmd+=("--nocapture")
fi
"${cargo_cmd[@]}"
echo ""
echo "[1/2] Internal conformance tests ($INTERNAL_SCOPE): PASSED"

# --- External checker comparison (opt-in) ---
if [ "$EXTERNAL" = true ]; then
    echo ""
    echo "[2/2] External checker comparison..."

    if [ "$SAT" = false ] && [ "$SMT" = true ]; then
        echo "SMT external checker comparison is not implemented yet."
        echo "[2/2] External checker comparison: SKIPPED (SMT external comparison not implemented)"
    else
        run_sat_external_comparison
        if [ "$SAT" = false ] && [ "$SMT" = false ]; then
            echo "[2/2] SMT external checker comparison: SKIPPED (not implemented)"
        fi
    fi
else
    echo "[2/2] External checker comparison: SKIPPED (use --external to enable)"
fi

echo ""
echo "=== Done ==="
