#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Integration tests for run_conformance.sh
#
# Validates:
#   1. Script syntax (bash -n)
#   2. Default internal scope runs combined conformance filter
#   3. --sat narrows to SAT conformance tests
#   4. --smt --verbose narrows to SMT conformance tests without nocapture
#   5. --sat --smt fails cleanly as conflicting selectors
#   6. --help prints the full usage block
#   7. --external skips honestly when SAT oracles are unavailable
#   8. --sat --external wires ay-lrat-check explicitly
#   9. --sat --external wires cake_lpr explicitly
#   10. --smt --external skips the unsupported lane honestly
#   11. Default --external reports SAT-only support honestly
#   12. Unknown arguments fail fast

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
RUNNER_SCRIPT="${REPO_ROOT}/scripts/run_conformance.sh"

PASS=0
FAIL=0

pass() {
    PASS=$((PASS + 1))
    echo "  PASS: $1"
}

fail() {
    FAIL=$((FAIL + 1))
    echo "  FAIL: $1" >&2
}

make_mock_cli() {
    local path="$1"
    local body="$2"
    cat >"$path" <<EOF
#!/usr/bin/env bash
set -euo pipefail
$body
EOF
    chmod +x "$path"
}

assert_log_contains() {
    local log_path="$1"
    local expected="$2"
    local label="$3"
    if grep -Fqx -- "$expected" "$log_path"; then
        pass "$label"
    else
        fail "$label"
    fi
}

assert_output_contains() {
    local output="$1"
    local expected="$2"
    local label="$3"
    if printf '%s' "$output" | grep -Fq -- "$expected"; then
        pass "$label"
    else
        fail "$label"
    fi
}

assert_log_not_contains() {
    local log_path="$1"
    local unexpected="$2"
    local label="$3"
    if [ ! -e "$log_path" ] || ! grep -Fq -- "$unexpected" "$log_path"; then
        pass "$label"
    else
        fail "$label"
    fi
}

echo "=== Test: run_conformance.sh ==="
echo

TMP_DIR="$(mktemp -d -t run_conformance_test.XXXXXX)"
trap 'rm -rf "$TMP_DIR"' EXIT

MOCK_BIN="$TMP_DIR/bin"
mkdir -p "$MOCK_BIN"

# ---- Test 1: Script exists and is executable ----------------------------------
echo "--- Test 1: Script exists and is executable ---"
if [ -x "$RUNNER_SCRIPT" ]; then
    pass "script is executable"
else
    fail "script not found or not executable at $RUNNER_SCRIPT"
fi

# ---- Test 2: Bash syntax check ------------------------------------------------
echo "--- Test 2: Bash syntax check ---"
if bash -n "$RUNNER_SCRIPT" 2>/dev/null; then
    pass "bash -n syntax check"
else
    fail "bash -n syntax check"
fi

if grep -Fqx 'export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"' "$RUNNER_SCRIPT"; then
    pass "defaults to one cargo build job"
else
    fail "missing CARGO_BUILD_JOBS single-job default"
fi

if grep -Fq 'cargo test --locked --message-format=short -j "$CARGO_BUILD_JOBS"' "$RUNNER_SCRIPT" &&
    ! grep -Fq "via cargo test" "$RUNNER_SCRIPT"; then
    pass "usage guidance advertises bounded cargo test"
else
    fail "usage guidance should advertise bounded cargo test"
fi

# ---- Test 3: Default scope uses combined filter -------------------------------
echo "--- Test 3: Default scope runs combined filter ---"
CARGO_LOG="$TMP_DIR/default-cargo.log"
make_mock_cli "$MOCK_BIN/cargo" "
printf '%s\n' \"\$*\" >> \"$CARGO_LOG\"
exit 0
"

OUTPUT="$(
    PATH="$MOCK_BIN:/usr/bin:/bin" "$RUNNER_SCRIPT"
)"

assert_log_contains \
    "$CARGO_LOG" \
    "test --locked --message-format=short -j 1 -p clean-verify --lib -- conformance" \
    "default run uses combined conformance filter"

assert_output_contains \
    "$OUTPUT" \
    "Running internal conformance tests (SAT + SMT)" \
    "default output reports SAT + SMT scope"

# ---- Test 4: --sat narrows to SAT conformance tests ---------------------------
echo "--- Test 4: --sat narrows internal scope ---"
CARGO_LOG="$TMP_DIR/sat-cargo.log"
make_mock_cli "$MOCK_BIN/cargo" "
printf '%s\n' \"\$*\" >> \"$CARGO_LOG\"
exit 0
"

OUTPUT="$(
    PATH="$MOCK_BIN:/usr/bin:/bin" "$RUNNER_SCRIPT" --sat
)"

assert_log_contains \
    "$CARGO_LOG" \
    "test --locked --message-format=short -j 1 -p clean-verify --lib -- sat_verify::conformance_tests::" \
    "--sat uses SAT module filter"

assert_output_contains \
    "$OUTPUT" \
    "Running internal conformance tests (SAT only)" \
    "--sat output reports SAT scope"

# ---- Test 5: --smt --verbose narrows to SMT filter without nocapture ---------
echo "--- Test 5: --smt --verbose narrows internal scope ---"
CARGO_LOG="$TMP_DIR/smt-cargo.log"
make_mock_cli "$MOCK_BIN/cargo" "
printf '%s\n' \"\$*\" >> \"$CARGO_LOG\"
exit 0
"

OUTPUT="$(
    PATH="$MOCK_BIN:/usr/bin:/bin" "$RUNNER_SCRIPT" --smt --verbose
)"

assert_log_contains \
    "$CARGO_LOG" \
    "test --locked --message-format=short -j 1 -p clean-verify --lib -- smt_verify::conformance_tests::" \
    "--smt --verbose uses SMT filter"

assert_log_not_contains \
    "$CARGO_LOG" \
    "--nocapture" \
    "--verbose does not stream test bodies by default"

assert_output_contains \
    "$OUTPUT" \
    "Running internal conformance tests (SMT only)" \
    "--smt output reports SMT scope"

assert_output_contains \
    "$OUTPUT" \
    "cargo: cargo test --locked --message-format=short -j 1 -p clean-verify --lib -- smt_verify::conformance_tests::" \
    "--verbose prints the resolved bounded cargo command"

# ---- Test 5b: --nocapture is explicit for focused debugging ------------------
echo "--- Test 5b: --nocapture is explicit ---"
CARGO_LOG="$TMP_DIR/smt-nocapture-cargo.log"
make_mock_cli "$MOCK_BIN/cargo" "
printf '%s\n' \"\$*\" >> \"$CARGO_LOG\"
exit 0
"

OUTPUT="$(
    PATH="$MOCK_BIN:/usr/bin:/bin" "$RUNNER_SCRIPT" --smt --nocapture
)"

assert_log_contains \
    "$CARGO_LOG" \
    "test --locked --message-format=short -j 1 -p clean-verify --lib -- smt_verify::conformance_tests:: --nocapture" \
    "--nocapture explicitly streams SMT test bodies"

# ---- Test 6: conflicting selectors fail cleanly -------------------------------
echo "--- Test 6: --sat --smt conflicting selectors ---"
CONFLICT_LOG="$TMP_DIR/conflict-cargo.log"
make_mock_cli "$MOCK_BIN/cargo" "
printf '%s\n' \"\$*\" >> \"$CONFLICT_LOG\"
exit 0
"

set +e
OUTPUT="$(
    PATH="$MOCK_BIN:/usr/bin:/bin" "$RUNNER_SCRIPT" --sat --smt 2>&1
)"
STATUS=$?
set -e

if [ "$STATUS" -eq 1 ]; then
    pass "conflicting selectors exit with status 1"
else
    fail "conflicting selectors expected status 1, got $STATUS"
fi

assert_output_contains \
    "$OUTPUT" \
    "Conflicting selectors: --sat and --smt cannot be used together. Omit both flags to run SAT + SMT." \
    "conflicting selectors report the contract"

assert_output_contains \
    "$OUTPUT" \
    "Selectors:  --sat and --smt are mutually exclusive; omit both to run both" \
    "conflicting selectors print usage guidance"

if [ ! -e "$CONFLICT_LOG" ]; then
    pass "conflicting selectors do not invoke cargo"
else
    fail "conflicting selectors unexpectedly invoked cargo"
fi

# ---- Test 7: --help prints the full usage block -------------------------------
echo "--- Test 7: --help prints full usage block ---"
OUTPUT="$(
    PATH="$MOCK_BIN:/usr/bin:/bin" "$RUNNER_SCRIPT" --help
)"

assert_output_contains \
    "$OUTPUT" \
    "Usage:" \
    "--help output includes usage header"

assert_output_contains \
    "$OUTPUT" \
    "./scripts/run_conformance.sh [--sat | --smt] [--external] [--verbose] [--nocapture] [--help]" \
    "--help output includes full usage synopsis"

assert_output_contains \
    "$OUTPUT" \
    "  - ay-lrat-check: https://github.com/Z3Prover/z3" \
    "--help output includes wired SAT oracle details"

assert_output_contains \
    "$OUTPUT" \
    "and Carcara remains separate." \
    "--help output includes trailing scope note"

# ---- Test 8: --external skips honestly when SAT oracles are unavailable ------
echo "--- Test 8: --external handles missing SAT oracles ---"
OUTPUT="$(
    PATH="$MOCK_BIN:/usr/bin:/bin" "$RUNNER_SCRIPT" --external
)"

assert_output_contains \
    "$OUTPUT" \
    "WARNING: No supported SAT external oracles found (looked for ay-lrat-check and cake_lpr)." \
    "--external reports missing SAT oracles cleanly"

assert_output_contains \
    "$OUTPUT" \
    "External checker comparison: SKIPPED (missing SAT oracles)" \
    "--external skips instead of false-greening when SAT oracles are absent"

# ---- Test 9: --sat --external wires ay-lrat-check explicitly -----------------
echo "--- Test 9: --sat --external uses ay-lrat-check explicitly ---"
CARGO_LOG="$TMP_DIR/ay-external-cargo.log"
make_mock_cli "$MOCK_BIN/cargo" "
printf '%s\n' \"\$*\" >> \"$CARGO_LOG\"
if [ \"\$1\" = \"run\" ]; then
  printf '%s\n' '## fake lrat report'
  printf '%s\n' 'Oracle(s): ay-lrat-check'
fi
exit 0
"
make_mock_cli "$MOCK_BIN/ay-lrat-check" "exit 0"

OUTPUT="$(
    PATH="$MOCK_BIN:/usr/bin:/bin" "$RUNNER_SCRIPT" --sat --external
)"

assert_log_contains \
    "$CARGO_LOG" \
    "test --locked --message-format=short -j 1 -p clean-verify --lib -- sat_verify::conformance_tests::" \
    "--sat --external still runs SAT internal coverage"

assert_log_contains \
    "$CARGO_LOG" \
    "run --locked -q --message-format=short -j 1 -p clean --bin clean -- kernel lrat-conform --ay-lrat-check $MOCK_BIN/ay-lrat-check" \
    "--sat --external forwards the discovered ay-lrat-check path"

assert_output_contains \
    "$OUTPUT" \
    "SAT external checker comparison: PASSED" \
    "--sat --external reports SAT external success"

# ---- Test 10: --sat --external wires cake_lpr explicitly ---------------------
echo "--- Test 10: --sat --external uses cake_lpr explicitly ---"
CARGO_LOG="$TMP_DIR/cake-external-cargo.log"
rm -f "$MOCK_BIN/ay-lrat-check"
make_mock_cli "$MOCK_BIN/cargo" "
printf '%s\n' \"\$*\" >> \"$CARGO_LOG\"
if [ \"\$1\" = \"run\" ]; then
  printf '%s\n' '## fake lrat report'
  printf '%s\n' 'Oracle(s): cake_lpr'
fi
exit 0
"
make_mock_cli "$MOCK_BIN/cake_lpr" "exit 0"

OUTPUT="$(
    PATH="$MOCK_BIN:/usr/bin:/bin" "$RUNNER_SCRIPT" --sat --external
)"

assert_log_contains \
    "$CARGO_LOG" \
    "run --locked -q --message-format=short -j 1 -p clean --bin clean -- kernel lrat-conform --cake-lpr $MOCK_BIN/cake_lpr" \
    "--sat --external forwards the discovered cake_lpr path"

assert_output_contains \
    "$OUTPUT" \
    "using cake_lpr" \
    "--sat --external reports the cake_lpr oracle it resolved"

# ---- Test 11: --smt --external skips the unsupported lane honestly -----------
echo "--- Test 11: --smt --external skips unsupported external lane ---"
CARGO_LOG="$TMP_DIR/smt-external-cargo.log"
make_mock_cli "$MOCK_BIN/cargo" "
printf '%s\n' \"\$*\" >> \"$CARGO_LOG\"
exit 0
"

OUTPUT="$(
    PATH="$MOCK_BIN:/usr/bin:/bin" "$RUNNER_SCRIPT" --smt --external
)"

assert_log_contains \
    "$CARGO_LOG" \
    "test --locked --message-format=short -j 1 -p clean-verify --lib -- smt_verify::conformance_tests::" \
    "--smt --external still runs SMT internal coverage"

assert_log_not_contains \
    "$CARGO_LOG" \
    "kernel lrat-conform" \
    "--smt --external does not invoke the SAT-only external harness"

assert_output_contains \
    "$OUTPUT" \
    "External checker comparison: SKIPPED (SMT external comparison not implemented)" \
    "--smt --external reports the unsupported lane honestly"

# ---- Test 12: default --external reports SAT-only support honestly -----------
echo "--- Test 12: default --external reports SAT-only support honestly ---"
CARGO_LOG="$TMP_DIR/default-external-cargo.log"
make_mock_cli "$MOCK_BIN/cargo" "
printf '%s\n' \"\$*\" >> \"$CARGO_LOG\"
if [ \"\$1\" = \"run\" ]; then
  printf '%s\n' '## fake lrat report'
  printf '%s\n' 'Oracle(s): cake_lpr'
fi
exit 0
"

OUTPUT="$(
    PATH="$MOCK_BIN:/usr/bin:/bin" "$RUNNER_SCRIPT" --external
)"

assert_log_contains \
    "$CARGO_LOG" \
    "run --locked -q --message-format=short -j 1 -p clean --bin clean -- kernel lrat-conform --cake-lpr $MOCK_BIN/cake_lpr" \
    "default --external still forwards the discovered SAT oracle"

assert_output_contains \
    "$OUTPUT" \
    "SMT external checker comparison: SKIPPED (not implemented)" \
    "default --external makes the SAT-only scope explicit"

# ---- Test 13: Unknown arguments fail fast ------------------------------------
echo "--- Test 13: Unknown argument handling ---"
set +e
OUTPUT="$(
    PATH="$MOCK_BIN:/usr/bin:/bin" "$RUNNER_SCRIPT" --bogus 2>&1
)"
STATUS=$?
set -e

if [ "$STATUS" -eq 1 ]; then
    pass "unknown argument exits with status 1"
else
    fail "unknown argument expected status 1, got $STATUS"
fi

assert_output_contains \
    "$OUTPUT" \
    "Unknown argument: --bogus" \
    "unknown argument reports the offending flag"

# ---- Summary ------------------------------------------------------------------
echo
echo "=== Results: $PASS passed, $FAIL failed ==="
if [ "$FAIL" -gt 0 ]; then
    exit 1
fi
