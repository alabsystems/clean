// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `AyProofBackend::check_sat_with_effort`: the caller's count bounds the
//! solve, the caller's clock only backs it up, and an undecided answer says
//! which of the two ended it.

use super::*;
use std::num::NonZeroU64;
use std::time::Duration;

/// A clock no solve below should reach. Firing would read as `timeout`, so a
/// test that expects the count to stop the solve fails by name instead of
/// hanging.
const HANG_BACKSTOP: Duration = Duration::from_secs(60);

fn effort(count: u64) -> NonZeroU64 {
    NonZeroU64::new(count).expect("a nonzero effort")
}

/// A spent effort reads as ay's resource-out, with ay's sentence beside it,
/// under proof production as the certification lanes solve.
#[test]
fn test_effort_stopped_solve_reads_as_resourceout() {
    let mut backend =
        support::pigeonhole_proof_backend(AyBackendConfig::with_proofs(AyLogic::QfUf), 5);

    match backend
        .check_sat_with_effort(effort(1), HANG_BACKSTOP)
        .expect("solve")
    {
        AyProofResult::Unknown { reason, detail } => {
            assert_eq!(reason, AyUnknownReason::ResourceLimit);
            assert_eq!(reason.to_string(), "resourceout");
            assert!(
                detail.is_some(),
                "ay records a sentence beside a spent count"
            );
        }
        other => panic!("Expected Unknown(resourceout), got {other:?}"),
    }
}

/// A backstop that fires first reads as ay's timeout: a clock, never a count.
/// The effort is far more than a millisecond of search can spend, so a
/// backstop that was not applied fails here as `resourceout`.
#[test]
fn test_tiny_backstop_reads_as_timeout() {
    let mut backend =
        support::pigeonhole_proof_backend(AyBackendConfig::with_proofs(AyLogic::QfUf), 11);

    match backend
        .check_sat_with_effort(effort(100_000), Duration::from_millis(1))
        .expect("solve")
    {
        AyProofResult::Unknown { reason, .. } => {
            assert_eq!(reason, AyUnknownReason::Timeout);
            assert_eq!(reason.to_string(), "timeout");
        }
        other => panic!("Expected Unknown(timeout), got {other:?}"),
    }
}

/// The count alone decides where the search stops: the same formula that a
/// small effort leaves undecided as `resourceout` is refuted under enough
/// effort, with the same backstop. (Proof production is off here: with it on,
/// ay at the pinned revision withholds this refutation by strict
/// certification, a different stop that this test is not about.)
#[test]
fn test_sufficient_effort_decides_the_same_formula() {
    let solve = |count| {
        support::pigeonhole_proof_backend(AyBackendConfig::new(AyLogic::QfUf), 5)
            .check_sat_with_effort(effort(count), HANG_BACKSTOP)
            .expect("solve")
    };

    match solve(1) {
        AyProofResult::Unknown { reason, .. } => {
            assert_eq!(reason, AyUnknownReason::ResourceLimit);
        }
        other => panic!("Expected Unknown(resourceout) under effort 1, got {other:?}"),
    }
    match solve(10_000_000) {
        AyProofResult::Unsat { .. } => {}
        other => panic!("Expected UNSAT under a sufficient effort, got {other:?}"),
    }
}

/// The effort entry sets exactly the caller's count and clock, first, and
/// nothing from the environment; the clock is rounded up and never `0`.
#[test]
fn test_effort_entry_sets_only_the_callers_bounds() {
    for (backstop, written_ms) in [
        (Duration::from_millis(1500), 1500),
        (Duration::from_micros(1500), 2),
        (Duration::ZERO, 1),
    ] {
        let mut backend = AyProofBackend::new_default(AyLogic::QfUf);
        let b = backend.fresh_bool("b");
        backend.assert_formula(&b);
        let _answer = backend
            .check_sat_with_effort(effort(7), backstop)
            .expect("solve");
        let script = &backend.last_problem;
        assert!(
            script.starts_with(&format!(
                "(set-logic QF_UF)\n(set-option :rlimit 7)\n(set-option :timeout {written_ms})\n"
            )),
            "backstop {backstop:?}: {script}"
        );
        assert_eq!(script.matches("set-option").count(), 2, "{script}");
    }
}

/// `check_sat` writes the script it wrote before the effort entry existed,
/// byte for byte: a `:timeout` from `AY_DIRECT_SOLVE_TIMEOUT_MS` (90 s when the
/// knob is unset or unreadable, none for `0`) and no `:rlimit`. That
/// `:timeout` is what keeps an in-process host's solve bounded (the trustc
/// 300 GB incident), so the whole script is compared, not a fragment of it.
///
/// The body runs in a process of its own (`--exact`, one test thread), the
/// only process whose environment it edits, so no other test reads the knob
/// mid-edit.
#[test]
fn test_check_sat_writes_the_old_script() {
    crate::test_env::in_isolated_test_process(|| {
        const KNOB: &str = "AY_DIRECT_SOLVE_TIMEOUT_MS";
        for (knob, timeout_line) in [
            (None, "(set-option :timeout 90000)\n"),
            (Some("1234"), "(set-option :timeout 1234)\n"),
            (Some("not a count"), "(set-option :timeout 90000)\n"),
            (Some("0"), ""),
        ] {
            let _knob = match knob {
                Some(value) => crate::test_env::ScopedEnvVar::set(KNOB, value),
                None => crate::test_env::ScopedEnvVar::unset(KNOB),
            };
            let mut backend = AyProofBackend::new_default(AyLogic::QfUf);
            backend.add_raw_declaration("(declare-const b Bool)");
            backend.assert_formula("b");
            let _answer = backend.check_sat().expect("solve");
            assert_eq!(
                backend.last_problem,
                format!(
                    "(set-logic QF_UF)\n{timeout_line}(declare-const b Bool)\n(assert b)\n(check-sat)\n"
                ),
                "{KNOB}={knob:?}"
            );
        }
    });
}
