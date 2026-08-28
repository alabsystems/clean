#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Run a filtered `cargo test` and REFUSE a zero-test run that exits 0.
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
# WHAT IT REFUSES, AND WHAT IT DELIBERATELY DOES NOT
# --------------------------------------------------
# Refuses when libtest printed at least one `test result:` line and NONE of them
# reports a non-zero `passed` count. Multiple test binaries are normal (a `-p X`
# with several targets), and one of them running zero tests while another runs
# five is not vacuous -- so the requirement is "at least one binary ran
# something", not "every binary ran something".
#
# It does NOT fire when there is no `test result:` line at all: that is a run
# that never reached libtest (a compile error, a killed build), and the
# command's own non-zero exit is the right signal for it. To keep that from
# becoming a silent skip, the verdict line always says which case it saw.
#
# Usage:
#     scripts/cargo_test_nonvacuous.sh <label> -- <command...>
#     scripts/cargo_test_nonvacuous.sh --selftest

set -uo pipefail

selftest() {
    local pass=0 fail=0
    arm() { # arm <name> <expected-rc> <output-text>
        local name="$1" want="$2" text="$3" got
        printf '%s' "$text" >"$TMP/out"
        verdict_for "$TMP/out" 0 >"$TMP/verdict" 2>&1
        got=$?
        if [[ "$got" == "$want" ]]; then
            pass=$((pass + 1))
            echo "  ok   $name"
        else
            fail=$((fail + 1))
            echo "  FAIL $name (want rc=$want got rc=$got): $(cat "$TMP/verdict")"
        fi
    }
    TMP="$(mktemp -d "${TMPDIR:-/tmp}/cargo-nonvacuous-selftest.XXXXXX")"
    trap 'rm -rf "$TMP"' RETURN

    arm "a real run passes" 0 \
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
    arm "an ignored-only run counts as having selected tests" 0 \
        'test result: ok. 0 passed; 0 failed; 3 ignored; 0 measured; 0 filtered out
'
    arm "no test-result line at all does not fire" 0 \
        'error: could not compile `clean-kernel`
'
    arm "a two-digit count is not read as a leading zero" 0 \
        'test result: ok. 10 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out
'
    echo "CARGO_TEST_NONVACUOUS_SELFTEST arms=$((pass + fail)) passed=$pass failed=$fail"
    [[ $fail -eq 0 ]]
}

# verdict_for <output-file> <command-exit-code>
# 0 = fine, 1 = vacuous. Prints one machine-readable verdict line.
verdict_for() {
    local out="$1" rc="$2" results ran
    results="$(grep -cE '^test result:' "$out" || true)"
    if [[ "$results" -eq 0 ]]; then
        echo "NONVACUOUS=unchecked reason=no-test-result-line exit=$rc"
        return 0
    fi
    # "at least one binary ran something": a non-zero passed OR ignored count.
    ran="$(grep -cE '^test result:.*[^0-9]([1-9][0-9]*) (passed|ignored)' "$out" || true)"
    if [[ "$ran" -eq 0 ]]; then
        echo "NONVACUOUS=fail reason=zero-tests-selected result_lines=$results"
        return 1
    fi
    echo "NONVACUOUS=ok result_lines=$results nonempty=$ran"
    return 0
}

main() {
    if [[ "${1:-}" == "--selftest" ]]; then
        selftest
        exit $?
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

    local out
    out="$(mktemp "${TMPDIR:-/tmp}/cargo-nonvacuous.XXXXXX")"
    "$@" >"$out" 2>&1
    local rc=$?
    cat "$out"

    if [[ $rc -ne 0 ]]; then
        rm -f "$out"
        return $rc
    fi

    local verdict vrc
    verdict="$(verdict_for "$out" "$rc")"
    vrc=$?
    echo "[$label] $verdict"
    if [[ $vrc -ne 0 ]]; then
        {
            echo "[$label] the command EXITED 0 having selected zero tests."
            echo "  libtest reports a filter that matches nothing as \`ok\`, so this leg"
            echo "  could not have failed. Point the filter at the crate that owns the"
            echo "  test, or delete the leg. Static check: \`scripts/check_cargo_test_selectors.py\`"
            echo "  Command: $*"
        } >&2
    fi
    rm -f "$out"
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
