#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Gamma-Crown Formal Proof Reproduction Script — paper artifact for all 15
# gamma-crown conjectures (C001-C030). Builds Clean, runs kernel
# type-checking, cross-checks data/axiom_audit.json, emits reports.
#
# Exit codes: 0 success | 1 verification failure | 2 prerequisites/build |
# 3 integrity/cross-check failure.
#
# Requirements: Rust >= 1.75 (rustc, cargo), jq (recommended for integrity
# gate), ~2GB disk. See --help for usage. Part of #3380.

set -euo pipefail

# --- Configuration -----------------------------------------------------------

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
AXIOM_AUDIT="${REPO_ROOT}/data/axiom_audit.json"

# Target A conjectures that must pass kernel verification.
# Expansion of EXPECTED_CONSTRUCTIVE happens at runtime from axiom_audit.json.
TARGET_A_CONJECTURES=("C001" "C002" "C004" "C006" "C008")

# Minimum Rust version required.
MIN_RUST_VERSION="1.75.0"

# Cargo features needed for the verification binary.
CARGO_FEATURES="test-utils,math-overlays"

export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"

# --- Argument parsing --------------------------------------------------------

OUTPUT_DIR=""
JSON_ONLY=false
SKIP_BUILD=false
RELEASE_MODE=true

usage() {
    cat <<'USAGE'
Usage: ./scripts/reproduce_gamma_crown.sh [OPTIONS]

Options:
  --output-dir DIR   Write all report formats (human, JSON, CSV, LaTeX) to DIR
  --json-only        Print only JSON report to stdout (for piping)
  --skip-build       Skip cargo build step (reuse previous build)
  --debug            Build in debug mode (faster compile, slower execution)
  --help             Show this help message

Examples:
  # Full verification with human-readable output
  ./scripts/reproduce_gamma_crown.sh

  # Save all artifacts for paper submission
  ./scripts/reproduce_gamma_crown.sh --output-dir artifact/

  # Pipe JSON into jq for custom analysis
  ./scripts/reproduce_gamma_crown.sh --json-only | jq '.conjectures[] | select(.constructive)'
USAGE
    exit 0
}

while [[ $# -gt 0 ]]; do
    case "$1" in
    --output-dir)
        OUTPUT_DIR="$2"
        shift 2
        ;;
    --json-only)
        JSON_ONLY=true
        shift
        ;;
    --skip-build)
        SKIP_BUILD=true
        shift
        ;;
    --debug)
        RELEASE_MODE=false
        shift
        ;;
    --help | -h)
        usage
        ;;
    *)
        echo "Error: unknown option '$1'" >&2
        echo "Run with --help for usage." >&2
        exit 2
        ;;
    esac
done

# --- Helper functions --------------------------------------------------------

log() {
    if [ "$JSON_ONLY" = false ]; then
        echo "$@"
    fi
}

log_err() {
    echo "$@" >&2
}

# Compare semantic versions. Returns 0 if $1 >= $2.
version_ge() {
    local IFS=.
    local i
    local -a ver1 ver2
    read -r -a ver1 <<<"$1"
    read -r -a ver2 <<<"$2"
    for ((i = 0; i < ${#ver2[@]}; i++)); do
        local v1="${ver1[i]:-0}"
        local v2="${ver2[i]:-0}"
        if ((v1 > v2)); then return 0; fi
        if ((v1 < v2)); then return 1; fi
    done
    return 0
}

# Locate jq binary. jq is preferred over inline python3 because AI-template
# environments intercept `python3 -c ...` invocations (rule #1987) and the
# interception mangles inline json filtering. jq is also more portable for
# external reviewers.
JQ_BIN=""
if command -v jq &>/dev/null; then
    JQ_BIN="$(command -v jq)"
fi

# Extract a jq expression from the live JSON report.
# Usage: jq_live '<expression>'
# Returns the value or "?" if jq is unavailable or the field is missing.
jq_live() {
    local expr="$1"
    if [ -z "${JSON_OUTPUT:-}" ] || [ -z "$JQ_BIN" ]; then
        echo "?"
        return
    fi
    local out
    out="$(printf '%s' "$JSON_OUTPUT" | "$JQ_BIN" -r "$expr" 2>/dev/null || echo "?")"
    if [ -z "$out" ] || [ "$out" = "null" ]; then
        echo "?"
    else
        echo "$out"
    fi
}

# Extract a jq expression from axiom_audit.json.
# Usage: jq_audit '<expression>'
jq_audit() {
    local expr="$1"
    if [ ! -f "$AXIOM_AUDIT" ] || [ -z "$JQ_BIN" ]; then
        echo "?"
        return
    fi
    local out
    out="$("$JQ_BIN" -r "$expr" "$AXIOM_AUDIT" 2>/dev/null || echo "?")"
    if [ -z "$out" ] || [ "$out" = "null" ]; then
        echo "?"
    else
        echo "$out"
    fi
}

# --- Step 1: Validate prerequisites -----------------------------------------

log "=================================================================="
log "  Gamma-Crown Formal Proof Reproduction"
log "  Clean kernel — kernel type-checked verification"
log "=================================================================="
log ""

# Check Rust toolchain
if ! command -v rustc &>/dev/null; then
    log_err "ERROR: rustc not found. Install Rust: https://rustup.rs/"
    exit 2
fi
if ! command -v cargo &>/dev/null; then
    log_err "ERROR: cargo not found. Install Rust: https://rustup.rs/"
    exit 2
fi

RUSTC_VERSION="$(rustc --version | sed 's/rustc \([0-9.]*\).*/\1/')"
if ! version_ge "$RUSTC_VERSION" "$MIN_RUST_VERSION"; then
    log_err "ERROR: Rust >= $MIN_RUST_VERSION required, found $RUSTC_VERSION"
    log_err "       Run: rustup update stable"
    exit 2
fi

# Check that we are in the repo root
if [ ! -f "${REPO_ROOT}/Cargo.toml" ]; then
    log_err "ERROR: Cannot find Cargo.toml at repo root: $REPO_ROOT"
    exit 2
fi

# --- Step 2: Record build environment ---------------------------------------

cd "$REPO_ROOT"

GIT_HASH="$(git rev-parse --short HEAD 2>/dev/null || echo 'unknown')"
GIT_SUBJECT="$(git log -1 --format='%s' HEAD 2>/dev/null | head -c 72 || echo 'unknown')"
GIT_DIRTY=""
if ! git diff --quiet HEAD 2>/dev/null; then
    GIT_DIRTY=" (dirty)"
fi
OS_INFO="$(uname -srm)"
TIMESTAMP="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"

log "-- Environment ---------------------------------------------------"
log "  Timestamp:      $TIMESTAMP"
log "  Git commit:     ${GIT_HASH}${GIT_DIRTY}"
log "  Commit subject: $GIT_SUBJECT"
log "  Rust version:   $(rustc --version)"
log "  Cargo version:  $(cargo --version)"
log "  OS:             $OS_INFO"
log "  Repo root:      $REPO_ROOT"
log ""

# --- Step 3: Build from source ----------------------------------------------

BUILD_FLAGS=(--locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-kernel --features "${CARGO_FEATURES}" --bin verify_gamma_crown)
if [ "$RELEASE_MODE" = true ]; then
    BUILD_FLAGS+=(--release)
fi

if [ "$SKIP_BUILD" = false ]; then
    log "-- Building verify_gamma_crown binary ----------------------------"
    log "  cargo build ${BUILD_FLAGS[*]}"
    log ""

    BUILD_START="$(date +%s)"
    if ! cargo build "${BUILD_FLAGS[@]}"; then
        log_err "ERROR: Build failed. See output above."
        exit 2
    fi
    BUILD_END="$(date +%s)"
    BUILD_SECS=$((BUILD_END - BUILD_START))
    log ""
    log "  Build completed in ${BUILD_SECS}s"
    log ""
else
    log "-- Skipping build (--skip-build) ---------------------------------"
    log ""
fi

# --- Step 4: Run verification -----------------------------------------------

log "-- Running kernel type-check verification ------------------------"
log ""

RUN_FLAGS=(--locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean-kernel --features "${CARGO_FEATURES}" --bin verify_gamma_crown)
if [ "$RELEASE_MODE" = true ]; then
    RUN_FLAGS+=(--release)
fi

# Always capture JSON for cross-checking, regardless of output mode.
# Temporarily allow non-zero exit (set -e would abort before we can report).
VERIFY_EXIT=0
JSON_OUTPUT="$(cargo run "${RUN_FLAGS[@]}" -- --json 2>/dev/null)" || VERIFY_EXIT=$?

# If verification binary returned nonzero, report and exit
if [ $VERIFY_EXIT -ne 0 ]; then
    log_err "ERROR: Verification binary exited with code $VERIFY_EXIT"
    log_err "One or more conjectures failed kernel verification."
    if [ "$JSON_ONLY" = true ]; then
        echo "$JSON_OUTPUT"
    fi
    exit 1
fi

# --- Step 5: Cross-check against axiom_audit.json ---------------------------

CROSS_CHECK_OK=true
INTEGRITY_OK=true

if [ -z "$JQ_BIN" ]; then
    log ""
    log "-- Skipping cross-check (jq not found) --------------------------"
    log "  Install jq to enable the integrity gate (recommended):"
    log "    macOS:  brew install jq"
    log "    Linux:  apt-get install jq  (or equivalent)"
    log ""
    # Continue without cross-check. Live verification alone is still
    # meaningful — jq-dependent gate is strictly additive.
fi

# Dynamically derive the list of conjectures claimed constructive in
# axiom_audit.json. This keeps the script in sync with the audit file
# without requiring manual updates here.
EXPECTED_CONSTRUCTIVE=()
if [ -f "$AXIOM_AUDIT" ] && [ -n "$JQ_BIN" ]; then
    while IFS= read -r cid; do
        [ -n "$cid" ] && EXPECTED_CONSTRUCTIVE+=("$cid")
    done < <("$JQ_BIN" -r \
        '.conjectures | to_entries[] | select(.value.constructive == true) | .key' \
        "$AXIOM_AUDIT" 2>/dev/null | sort)
fi

if [ -f "$AXIOM_AUDIT" ] && [ -n "$JQ_BIN" ]; then
    log "-- Cross-checking against data/axiom_audit.json -----------------"
    log ""
    log "  Audit claims ${#EXPECTED_CONSTRUCTIVE[@]} conjectures constructive: ${EXPECTED_CONSTRUCTIVE[*]}"
    log ""

    # Integrity check: zero live axioms + proof_mechanism parity with
    # data/axiom_audit.json. 'constructive: true' in the audit INCLUDES
    # sorry-inhabited scaffolds; proof_mechanism is the honest field.
    log "  Integrity check: audit-constructive conjectures must have 0 live domain axioms"
    log "                   (NOTE: 'constructive: true' in audit includes sorry-inhabited;"
    log "                    proof_mechanism is the reviewer-safe honesty field.)"
    for cid in "${EXPECTED_CONSTRUCTIVE[@]}"; do
        is_constructive="$(jq_live ".conjectures[] | select(.id==\"$cid\") | .constructive")"
        live_axioms="$(jq_live ".conjectures[] | select(.id==\"$cid\") | .domain_axioms")"
        live_mechanism="$(jq_live ".conjectures[] | select(.id==\"$cid\") | .proof_mechanism")"
        audit_mechanism="$(jq_audit ".conjectures.\"$cid\".proof_mechanism // \"n/a\"")"

        if [ "$is_constructive" = "true" ] && [ "$live_axioms" = "0" ]; then
            if [ "$live_mechanism" = "$audit_mechanism" ]; then
                log "    $cid: 0 domain axioms, mechanism=$live_mechanism -- OK"
            else
                log_err "    $cid: MECHANISM MISMATCH -- audit=$audit_mechanism, live=$live_mechanism"
                CROSS_CHECK_OK=false
            fi
        elif [ "$is_constructive" = "false" ] || [ "$live_axioms" != "0" ]; then
            log_err "    $cid: INTEGRITY VIOLATION -- audit claims constructive but live shows"
            log_err "          constructive=$is_constructive, domain_axioms=$live_axioms"
            INTEGRITY_OK=false
            CROSS_CHECK_OK=false
        else
            log_err "    $cid: could not determine status (jq extraction failed)"
            CROSS_CHECK_OK=false
        fi
    done

    # Check 2: Target A conjectures must all pass kernel type checking
    log ""
    log "  Target A kernel type-check (C001, C002, C004, C006, C008):"
    for cid in "${TARGET_A_CONJECTURES[@]}"; do
        tc_verified="$(jq_live ".conjectures[] | select(.id==\"$cid\") | .tc_verified")"

        if [ "$tc_verified" = "true" ]; then
            log "    $cid: kernel type-checked -- OK"
        elif [ "$tc_verified" = "false" ]; then
            log_err "    $cid: FAILED kernel type checking -- Target A violation"
            CROSS_CHECK_OK=false
        else
            log_err "    $cid: could not determine status"
            CROSS_CHECK_OK=false
        fi
    done

    # Check 3: axiom-count parity (live vs audit) — for all conjectures,
    # reports in deterministic (sorted) order.
    log ""
    log "  Axiom count parity (live vs audit, all conjectures):"
    ALL_IDS="$(jq_live '.conjectures[].id' | sort)"
    for cid in $ALL_IDS; do
        audit_axioms="$(jq_audit ".conjectures.\"$cid\".axioms // \"n/a\"")"
        live_axioms="$(jq_live ".conjectures[] | select(.id==\"$cid\") | .domain_axioms")"
        if [ "$audit_axioms" = "$live_axioms" ]; then
            log "    $cid: live=$live_axioms, audit=$audit_axioms -- MATCH"
        elif [ "$audit_axioms" = "n/a" ]; then
            log "    $cid: live=$live_axioms, audit=n/a -- (not in audit)"
        else
            log_err "    $cid: live=$live_axioms, audit=$audit_axioms -- MISMATCH"
            CROSS_CHECK_OK=false
        fi
    done
    log ""
elif [ ! -f "$AXIOM_AUDIT" ]; then
    log "  (data/axiom_audit.json not found, skipping cross-check)"
    log ""
fi

# --- Step 6: Produce output -------------------------------------------------

if [ "$JSON_ONLY" = true ]; then
    echo "$JSON_OUTPUT"
elif [ -n "$OUTPUT_DIR" ]; then
    # Write all report formats to the output directory
    mkdir -p "$OUTPUT_DIR"

    echo "$JSON_OUTPUT" >"${OUTPUT_DIR}/verification_report.json"
    log "  Wrote ${OUTPUT_DIR}/verification_report.json"

    cargo run "${RUN_FLAGS[@]}" -- 2>/dev/null >"${OUTPUT_DIR}/verification_report.txt"
    log "  Wrote ${OUTPUT_DIR}/verification_report.txt"

    cargo run "${RUN_FLAGS[@]}" -- --csv 2>/dev/null >"${OUTPUT_DIR}/verification_report.csv"
    log "  Wrote ${OUTPUT_DIR}/verification_report.csv"

    cargo run "${RUN_FLAGS[@]}" -- --latex 2>/dev/null >"${OUTPUT_DIR}/verification_report.tex"
    log "  Wrote ${OUTPUT_DIR}/verification_report.tex"

    # Write environment metadata
    cat >"${OUTPUT_DIR}/environment.json" <<ENVJSON
{
  "timestamp": "$TIMESTAMP",
  "git_commit": "${GIT_HASH}${GIT_DIRTY}",
  "git_subject": "$GIT_SUBJECT",
  "rustc_version": "$(rustc --version)",
  "cargo_version": "$(cargo --version)",
  "os": "$OS_INFO",
  "release_mode": $RELEASE_MODE
}
ENVJSON
    log "  Wrote ${OUTPUT_DIR}/environment.json"

    # Write a README for reviewers (honest classification — #3502).
    # Template lives in scripts/README.reviewer.template.txt so this
    # script stays under the 500-line limit; edit the template
    # directly if the disclosure wording changes.
    README_TEMPLATE="${SCRIPT_DIR}/README.reviewer.template.txt"
    if [ -f "$README_TEMPLATE" ]; then
        cp "$README_TEMPLATE" "${OUTPUT_DIR}/README.txt"
    else
        log_err "WARNING: README template missing: $README_TEMPLATE"
        echo "Gamma-Crown Verification Artifact (template missing)" \
            >"${OUTPUT_DIR}/README.txt"
    fi
    log "  Wrote ${OUTPUT_DIR}/README.txt"

    log ""
    log "All artifacts written to: $OUTPUT_DIR"
else
    # Default: print human-readable report to stdout
    cargo run "${RUN_FLAGS[@]}" -- 2>/dev/null
fi

# --- Step 7: Final status ----------------------------------------------------

log ""
log "=================================================================="

# Extract summary numbers from JSON (via jq)
TOTAL="$(jq_live '.total_conjectures')"
VERIFIED="$(jq_live '.conjectures_verified')"
CONSTRUCTIVE="$(jq_live '.fully_constructive')"
TOTAL_AXIOMS="$(jq_live '.total_domain_axioms')"
TOTAL_TIME_RAW="$(jq_live '.total_verification_time_ms')"
# Format with one decimal place via awk (portable across BSD/GNU)
if [ "$TOTAL_TIME_RAW" = "?" ]; then
    TOTAL_TIME="?"
else
    TOTAL_TIME="$(awk -v t="$TOTAL_TIME_RAW" 'BEGIN{printf "%.1f", t}')"
fi

# Honest classification fields — per #3502 and design doc Proof Soundness
# Rules. Legacy `fully_constructive` counts conjectures with zero live
# domain axioms, including sorry-inhabited scaffolds; it is NOT the
# publishable-proof count. The summary surfaces BOTH numbers so a reviewer
# can see the correct value (`constructive_conjectures`).
HONEST_CONSTRUCTIVE="$(jq_live '.constructive_conjectures // "?"')"
HONEST_MIXED="$(jq_live '.mixed_conjectures // "?"')"
HONEST_SCAFFOLDED="$(jq_live '.scaffolded_conjectures // "?"')"
HONEST_AXIOM_DEP="$(jq_live '.axiom_dependent_conjectures // "?"')"

log "  Conjectures kernel type-checked: $VERIFIED / $TOTAL"
log "  Proved (constructive):           $HONEST_CONSTRUCTIVE  (real proof terms only)"
log "  Mixed (partial scaffolding):     $HONEST_MIXED  (some theorems sorry-inhabited)"
log "  Scaffolded (sorry-inhabited):    $HONEST_SCAFFOLDED  (all claim Opaques are @sorry)"
log "  Axiom-dependent:                 $HONEST_AXIOM_DEP  (Declaration::Axiom remains)"
log "  Zero-live-axiom (legacy):        $CONSTRUCTIVE  (includes scaffolded; not publishable)"
log "  Total domain axioms:             $TOTAL_AXIOMS  (target: 0)"
log "  Verification time:               ${TOTAL_TIME}ms"

# --- Step 7: Integrity gate (fail-closed) -----------------------------------
# Exit non-zero if any claimed-constructive conjecture has >0 live axioms.
# This is the paper-artifact integrity guarantee.

if [ "$INTEGRITY_OK" = false ]; then
    log_err ""
    log_err "FAIL: INTEGRITY VIOLATION -- audit claims constructive but live"
    log_err "shows >0 domain axioms for one or more conjectures. Reject this artifact."
    exit 3
fi
if [ "$CROSS_CHECK_OK" = false ]; then
    log_err ""
    log_err "WARNING: axiom_audit.json parity check FAILED (details above)."
    exit 3
fi

log "=================================================================="
log ""
if [ -z "$JQ_BIN" ]; then
    log "SUCCESS: All conjectures verified by the kernel."
    log "NOTE:    jq was not available; integrity cross-check skipped."
else
    log "SUCCESS: All conjectures passed kernel type checking."
    log "         Cross-checks against data/axiom_audit.json passed."
    log ""
    log "IMPORTANT honesty disclosure (#3502):"
    log "  - Proved (constructive): $HONEST_CONSTRUCTIVE of $TOTAL"
    log "  - The remaining $HONEST_MIXED mixed + $HONEST_SCAFFOLDED scaffolded conjectures"
    log "    pass type checking with zero domain axioms but contain one or more"
    log "    claim-level Opaque entries inhabited by @sorry. These are logically"
    log "    vacuous placeholders, NOT constructive proofs. See PAPER_ARTIFACT.md."
fi

exit 0
