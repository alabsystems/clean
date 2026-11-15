#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Run a filtered `cargo test` and require a passing libtest summary on exit 0.
#
# WHY
# ---
# Measured 2026-08-26 on a throwaway crate, so the output shape is not assumed:
#
#     $ cargo test -q --lib -- no_such_test
#     running 0 tests
#     test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 2 filtered out
#     $ echo $?
#     0
#
# `-q` does NOT suppress the `test result:` line, and libtest reports a filter
# that selects nothing as `ok`. So a gate whose filter is renamed, moved to
# another crate, or feature-gated out keeps passing while measuring nothing --
# which is `docs/GATE_REGISTRY.md`'s UNFALSIFIABLE class. The live instance was
# `cargo test --locked -p clean-kernel axiom_refutation_gate`: that gate is
# crates/clean-verify/tests/axiom_refutation_gate.rs, and the clean-kernel
# spelling exits 0 with "0 passed; ...; 10412 filtered out".
#
# scripts/check_cargo_test_selectors.py is the STATIC half and costs no cargo.
# This is the runtime half, for the cases static resolution cannot decide: a
# filter behind an inactive `#[cfg(feature = ...)]`, a test deleted between
# scan and run, a `--exact` name that no longer exists.
#
# WHAT IT REQUIRES
# ----------------
# A successful command must print a complete libtest-shaped summary with a
# non-zero `passed` count. Ignored tests do not count as executed tests. Every
# reported summary must be well formed and report no failure, even if the
# command incorrectly exits 0. Multiple test binaries are normal: empty or
# ignored-only binaries beside a passing binary are allowed. The scope remains
# "at least one binary passed tests", not "every binary passed tests".
#
# Missing summaries on exit 0 are refused. Non-zero command exits propagate
# unchanged, including compile failures and killed builds. This is a check of
# untrusted output, not authentication that libtest or the tests executed.
# The self-test below uses synthetic text only; it runs no Rust or libtest.
# Its scratch state is isolated from the wrapped command. Setup, raw-output
# replay and cleanup failures refuse success; a non-zero child exit takes
# precedence over those wrapper failures.
#
# Usage:
#     scripts/cargo_test_nonvacuous.sh <label> -- <command...>
#     scripts/cargo_test_nonvacuous.sh --selftest

set -uo pipefail

selftest() (
    # Globals are private to this subshell and survive Bash's fatal-expansion
    # unwinding of function locals, so EXIT cleanup can still find its scratch.
    nonvacuous_selftest_pass=0
    nonvacuous_selftest_fail=0
    nonvacuous_selftest_complete=0
    nonvacuous_selftest_dir=""
    if nonvacuous_selftest_dir="$(mktemp -d "${TMPDIR:-/tmp}/cargo-nonvacuous-selftest.XXXXXX")" && [[ -d "$nonvacuous_selftest_dir" ]]; then
        :
    else
        echo "NONVACUOUS_SELFTEST=fail reason=setup-error" >&2
        exit 2
    fi
    selftest_cleanup() {
        local status=$? cleanup_rc
        trap - EXIT
        # Some Bash errexit paths report 0 after a fatal expansion in a
        # conditional subshell. Success also requires explicit completion.
        if [[ "$nonvacuous_selftest_complete" -ne 1 ]]; then
            echo "NONVACUOUS_SELFTEST=fail reason=incomplete" >&2 || true
            if [[ "$status" -eq 0 ]]; then status=2; fi
        fi
        if rm -rf "$nonvacuous_selftest_dir"; then
            :
        else
            cleanup_rc=$?
            echo "NONVACUOUS_SELFTEST=fail reason=cleanup-error exit=$cleanup_rc" >&2 || true
            if [[ "$status" -eq 0 ]]; then status=2; fi
        fi
        exit "$status"
    }
    trap selftest_cleanup EXIT
    arm() { # arm <name> <expected-rc> <output-text>
        local name="$1" want="$2" text="$3" got
        # Decode only these synthetic fixture escapes; Bash variables cannot
        # contain NUL bytes. Command output is never decoded this way.
        if printf '%b' "$text" >|"$nonvacuous_selftest_dir/out"; then
            :
        else
            echo "NONVACUOUS_SELFTEST=fail reason=fixture-write-error" >&2
            exit 2
        fi
        if verdict_for "$nonvacuous_selftest_dir/out" 0 >|"$nonvacuous_selftest_dir/verdict" 2>&1; then
            got=0
        else
            got=$?
        fi
        if [[ "$got" == "$want" ]]; then
            nonvacuous_selftest_pass=$((nonvacuous_selftest_pass + 1))
            echo "  ok   $name"
        else
            nonvacuous_selftest_fail=$((nonvacuous_selftest_fail + 1))
            echo "  FAIL $name (want rc=$want got rc=$got): $(cat "$nonvacuous_selftest_dir/verdict")"
        fi
    }
    arm "a synthetic passing summary is accepted" 0 \
        'running 1 test
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1 filtered out
'
    # THE BUG, verbatim from `cargo test --locked -p clean-kernel axiom_refutation_gate`.
    arm "a zero-test run is REFUSED" 1 \
        'running 0 tests
test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 10412 filtered out
'
    arm "one empty binary beside a non-empty one passes" 0 \
        'test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 12 filtered out
test result: ok. 5 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
'
    arm "an ignored-only run is REFUSED" 1 \
        'test result: ok. 0 passed; 0 failed; 3 ignored; 0 measured; 0 filtered out
'
    arm "a successful command without a summary is REFUSED" 1 \
        'error: could not compile `clean-kernel`
'
    arm "a two-digit count is not read as a leading zero" 0 \
        'test result: ok. 10 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
'
    arm "empty successful output is REFUSED" 1 ''
    arm "ignored tests beside passing tests are allowed" 0 \
        'test result: ok. 0 passed; 0 failed; 3 ignored; 0 measured; 0 filtered out
test result: ok. 2 passed; 0 failed; 1 ignored; 0 measured; 0 filtered out
'
    arm "the optional libtest duration is accepted" 0 \
        'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s
'
    arm "a failed status on command exit 0 is REFUSED" 1 \
        'test result: FAILED. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
'
    arm "a nonzero failed count on command exit 0 is REFUSED" 1 \
        'test result: ok. 1 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out
'
    arm "a failing binary beside a passing binary is REFUSED" 1 \
        'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out
'
    arm "an incomplete summary is REFUSED" 1 \
        'test result: ok. 1 passed
'
    arm "a malformed summary beside a passing one is REFUSED" 1 \
        'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
test result: arbitrary 1 passed
'
    arm "a NUL suffix inside a summary is REFUSED" 1 \
        'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out\000garbage
'
    arm "a NUL-corrupted summary beside a passing one is REFUSED" 1 \
        'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out\000garbage
'
    arm "unrelated binary bytes before a passing summary are allowed" 0 \
        '\377\000unrelated-prefix
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
'
    echo "CARGO_TEST_NONVACUOUS_SELFTEST arms=$((nonvacuous_selftest_pass + nonvacuous_selftest_fail)) passed=$nonvacuous_selftest_pass failed=$nonvacuous_selftest_fail"
    if [[ "$nonvacuous_selftest_fail" -ne 0 ]]; then exit 1; fi
    nonvacuous_selftest_complete=1
    exit 0
)

# Print a byte-safe match count; fail on read/transform/grep errors. A grep
# no-match exit (1) still prints a legitimate zero count.
count_matches() {
    local out="$1" pattern="$2"
    local -a pipeline_status
    # BSD grep treats NUL as an end anchor even with -a. Map NUL to an invalid
    # grammar character only in parser streams; cat preserves raw output.
    # Text mode and the C locale keep unrelated binary bytes from hiding lines.
    LC_ALL=C tr '\000' '?' <"$out" | LC_ALL=C grep -acE "$pattern"
    pipeline_status=("${PIPESTATUS[@]}")
    [[ "${pipeline_status[0]}" -eq 0 && "${pipeline_status[1]}" -le 1 ]]
}

# verdict_for <output-file> <command-exit-code>
# Called for command exit 0. 0 = passing summary, 1 = refused output.
# Prints one machine-readable verdict line.
verdict_for() {
    local out="$1" rc="$2" results valid failed ran
    results="$(count_matches "$out" '^test result:')" || { echo "NONVACUOUS=fail reason=parser-error"; return 1; }
    if [[ "$results" -eq 0 ]]; then
        echo "NONVACUOUS=fail reason=no-test-result-line exit=$rc"
        return 1
    fi
    valid="$(count_matches "$out" '^test result: (ok|FAILED)[.] [0-9]+ passed; [0-9]+ failed; [0-9]+ ignored; [0-9]+ measured; [0-9]+ filtered out(; finished in [0-9]+([.][0-9]+)?s)?[[:space:]]*$')" || { echo "NONVACUOUS=fail reason=parser-error"; return 1; }
    if [[ "$valid" -ne "$results" ]]; then
        echo "NONVACUOUS=fail reason=malformed-test-result-line result_lines=$results valid=$valid"
        return 1
    fi
    failed="$(count_matches "$out" '^test result: FAILED[.]|^test result: ok[.] [0-9]+ passed; [0-9]*[1-9][0-9]* failed;')" || { echo "NONVACUOUS=fail reason=parser-error"; return 1; }
    if [[ "$failed" -ne 0 ]]; then
        echo "NONVACUOUS=fail reason=reported-test-failure result_lines=$results failed=$failed"
        return 1
    fi
    # Require executed, passing tests; ignored and measured counts do not count.
    ran="$(count_matches "$out" '^test result: ok[.] [0-9]*[1-9][0-9]* passed;')" || { echo "NONVACUOUS=fail reason=parser-error"; return 1; }
    if [[ "$ran" -eq 0 ]]; then
        echo "NONVACUOUS=fail reason=zero-tests-passed result_lines=$results"
        return 1
    fi
    echo "NONVACUOUS=ok result_lines=$results nonempty=$ran"
    return 0
}

main() {
    if [[ "${1:-}" == "--selftest" ]]; then
        if [[ $# -ne 1 ]]; then
            echo "$0: --selftest takes no command or trailing arguments" >&2
            exit 2
        fi
        if selftest; then return 0; else return $?; fi
    fi
    local label="${1:-}"
    shift || true
    if [[ "${1:-}" != "--" ]]; then
        echo "usage: $0 <label> -- <command...>" >&2
        echo "       $0 --selftest" >&2
        exit 2
    fi
    shift
    if [[ $# -eq 0 ]]; then
        echo "$0: no command given after --" >&2
        exit 2
    fi

    local out rc replay_rc cleanup_rc verdict="" vrc=1
    if out="$(mktemp "${TMPDIR:-/tmp}/cargo-nonvacuous.XXXXXX")" && [[ -f "$out" ]]; then
        :
    else
        echo "[$label] NONVACUOUS=fail reason=capture-setup-error" >&2
        return 2
    fi
    if "$@" >|"$out" 2>&1; then rc=0; else rc=$?; fi
    if cat "$out"; then replay_rc=0; else replay_rc=$?; fi

    if [[ "$rc" -eq 0 && "$replay_rc" -eq 0 ]]; then
        if verdict="$(verdict_for "$out" "$rc")"; then vrc=0; else vrc=$?; fi
    fi
    if rm -f "$out"; then cleanup_rc=0; else cleanup_rc=$?; fi
    if [[ "$replay_rc" -ne 0 ]]; then
        echo "[$label] NONVACUOUS=fail reason=output-replay-error exit=$replay_rc" >&2 || true
    fi
    if [[ "$cleanup_rc" -ne 0 ]]; then
        echo "[$label] NONVACUOUS=fail reason=capture-cleanup-error exit=$cleanup_rc" >&2 || true
    fi
    if [[ "$rc" -ne 0 ]]; then return "$rc"; fi
    if [[ "$replay_rc" -ne 0 || "$cleanup_rc" -ne 0 ]]; then return 1; fi
    echo "[$label] $verdict"
    if [[ $vrc -ne 0 ]]; then
        {
            echo "[$label] the command EXITED 0 without a valid passing libtest result."
            echo "  Require at least one passed test, no failed or malformed summaries."
            echo "  Ignored-only output and missing summaries measure no executed tests."
            echo "  Static filter check: \`scripts/check_cargo_test_selectors.py\`"
            echo "  Command: $*"
        } >&2
    fi
    return $vrc
}

# Run the self-test first on every invocation, the same contract the
# add-decl-ratchet and gate-registry legs use: a guard whose own falsifiability
# is only checked when somebody remembers is the artifact this exists to stop.
if [[ "${1:-}" != "--selftest" ]]; then
    if ! selftest >/dev/null 2>&1; then
        echo "$0: refusing to run -- its own self-test arms no longer fire" >&2
        exit 2
    fi
fi

main "$@"
