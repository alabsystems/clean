// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::cmd_core::{check_file, collect_check_outcome, emit_check_summary};
use clean_kernel::cli::{PreludeMode, DEFAULT_DECL_BUDGET};
use std::{fs, time::Duration};

#[test]
fn emit_check_summary_success_uses_lean_parser_summary_line() {
    let mut buf = Vec::new();
    emit_check_summary(&mut buf, 2, Duration::from_millis(7), 2, 0, 0)
        .expect("write should succeed");
    let output = String::from_utf8(buf).expect("valid utf8");
    assert!(
        output
            .lines()
            .any(|line| line.contains("2 passed, 0 failed")),
        "successful checks should keep the lean parser summary: {output}"
    );
}

#[test]
fn emit_check_summary_failure_uses_lean_parser_summary_line() {
    let mut buf = Vec::new();
    emit_check_summary(&mut buf, 4, Duration::from_millis(11), 2, 2, 0)
        .expect("write should succeed");
    let output = String::from_utf8(buf).expect("valid utf8");
    // The failure path MUST emit the "N passed, M failed" summary line so
    // external parsers (bench-solver-status parse_lean) can classify the result
    // as type_check_failed instead of falling through to exit-code heuristics.
    // The prior format ("outcome: check_failed" / "accepted" / "reported")
    // was not recognized by parse_lean, causing wrong-answer misclassification.
    assert!(
        output
            .lines()
            .any(|line| line.contains("2 passed") && line.contains("2 failed")),
        "failing checks must emit the lean parser summary line: {output}"
    );
    assert!(
        !output.contains("0 failed"),
        "failing checks must not claim 0 failed: {output}"
    );
}

/// Regression test for wrong-answer bug (#3078): a file containing only
/// administrative declarations (set_option) and no actual theorems must NOT
/// report "N passed, 0 failed". Skipped declarations are not verified and
/// must not inflate the pass count.
#[test]
fn check_file_skipped_only_reports_zero_passed() {
    // set_option is parsed as a SurfaceDecl::SetOption and elaborated as Skipped.
    // Before the fix, this would increment success_count, producing "1 passed, 0 failed".
    let code = "set_option maxHeartbeats 0\n";

    let dir = tempfile::tempdir().expect("tempdir should be created");
    let path = dir.path().join("skipped_only.clean");
    fs::write(&path, code).expect("write should succeed");

    // The file should succeed (no errors), but with 0 passed since nothing
    // was actually type-checked.
    let result = check_file(&path, false, false, PreludeMode::Builtin);
    assert!(
        result.is_ok(),
        "file with only skipped declarations should not error"
    );
}

/// Regression test for wrong-answer bug (#3078): a file with sorry must
/// produce output containing both "passed" and "failed" with non-zero
/// failed count, so external parsers classify it as type_check_failed.
#[test]
fn check_file_sorry_output_has_nonzero_failed() {
    let code = "theorem bad : True := by sorry\n";

    let dir = tempfile::tempdir().expect("tempdir should be created");
    let path = dir.path().join("sorry_output.clean");
    fs::write(&path, code).expect("write should succeed");

    let result = check_file(&path, false, false, PreludeMode::Builtin);
    assert!(result.is_err(), "sorry file must fail");
}

#[test]
fn check_file_explicit_sorry_fails_closed() {
    let code = r"
theorem incomplete : True := by
  sorry
";

    let dir = tempfile::tempdir().expect("tempdir should be created");
    let path = dir.path().join("sorry.clean");
    fs::write(&path, code).expect("write should succeed");

    let result = check_file(&path, false, false, PreludeMode::Builtin);
    assert!(result.is_err(), "explicit sorry must fail closed");
}

#[test]
fn check_file_clears_trust_state_between_runs() {
    use clean_kernel::sorry::sorry_count;

    let failing_code = r"
theorem incomplete : True := by
  sorry
";
    let clean_code = r"
def idFun (A : Type) (x : A) : A := x
";

    let dir = tempfile::tempdir().expect("tempdir should be created");
    let failing_path = dir.path().join("sorry.clean");
    let clean_path = dir.path().join("clean.clean");
    fs::write(&failing_path, failing_code).expect("write should succeed");
    fs::write(&clean_path, clean_code).expect("write should succeed");

    let baseline = sorry_count();
    let failing_result = check_file(&failing_path, false, false, PreludeMode::Builtin);
    assert!(
        failing_result.is_err(),
        "explicit sorry must still fail closed"
    );
    assert_eq!(
        sorry_count(),
        baseline,
        "check_file should restore the trust counter state after failure"
    );

    check_file(&clean_path, false, false, PreludeMode::Builtin)
        .expect("clean file should type check");
    assert_eq!(
        sorry_count(),
        baseline,
        "check_file should leave the trust counter state unchanged after success"
    );
}

// ── Per-declaration budget (task #31) ────────────────────────────────────
//
// The gap these cover: `clean check` had no per-declaration bound, so ONE
// diverging declaration held a whole file's measurement hostage — a single
// `by grind` in `Mathlib/Logic/Basic.lean` burned 40+ minutes with no output
// and the run was abandoned with no verdict for any of the other 250+
// declarations.
//
// Every test here is written so that REMOVING the budget makes it fail: with
// no budget the tiny-budget runs would simply pass, so `diverged` would be 0
// and `success_count` 1.

/// Helper: run one snippet through the real check pipeline under an explicit
/// budget and hand back the outcome.
fn check_snippet_with_budget(
    name: &str,
    code: &str,
    decl_budget: u64,
) -> super::cmd_core::FileCheckOutcome {
    let dir = tempfile::tempdir().expect("tempdir should be created");
    let path = dir.path().join(name);
    fs::write(&path, code).expect("write should succeed");
    let (outcome, _elapsed) = collect_check_outcome(
        &path,
        false,
        false,
        PreludeMode::Builtin,
        false,
        false,
        clean_elab::ImportPolicy::default(),
        decl_budget,
    )
    .expect("the check pipeline itself must not error out");
    outcome
}

/// A declaration that PASSES comfortably under the default budget.
///
/// This is the control for every tiny-budget test below: without it, a
/// `diverged` verdict under a tiny budget would prove nothing (the snippet
/// might simply be broken).
#[test]
fn decl_budget_default_leaves_a_passing_declaration_passing() {
    let outcome = check_snippet_with_budget(
        "budget_ok.lean",
        "def idNat (n : Nat) : Nat := n\n",
        DEFAULT_DECL_BUDGET,
    );
    assert_eq!(outcome.success_count, 1, "control must pass: {outcome:?}");
    assert!(
        outcome.diverged.is_empty(),
        "control must not diverge: {outcome:?}"
    );
    assert!(
        outcome.errors.is_empty(),
        "control must not error: {outcome:?}"
    );
}

/// FAIL CLOSED, the central rule: a declaration that runs out of ambient fuel
/// is `diverged` — NEVER a pass.
///
/// The snippet is the same one the control above proves passes, so the only
/// thing that changed is the budget. If exhaustion were folded into the pass
/// count (or simply ignored), `success_count` would be 1 here.
#[test]
fn decl_budget_exhaustion_is_never_a_pass() {
    let outcome =
        check_snippet_with_budget("budget_tight.lean", "def idNat (n : Nat) : Nat := n\n", 1);
    assert_eq!(
        outcome.success_count, 0,
        "a declaration that did not finish must not be counted as passing: {outcome:?}"
    );
    assert_eq!(
        outcome.diverged.len(),
        1,
        "exhaustion must be recorded in its own bucket: {outcome:?}"
    );
    assert!(
        outcome.diverged[0].contains("idNat") && outcome.diverged[0].contains("did not finish"),
        "the diverged row must name the declaration and say what happened: {outcome:?}"
    );
}

/// …and NEVER a failure-to-prove either. Nothing was refuted, so the error /
/// trust / kernel-failure buckets must be empty: a consumer that counts those
/// as "Clean rejected this declaration" would be reading a claim the run never
/// made.
#[test]
fn decl_budget_exhaustion_is_never_a_failure_to_prove() {
    let outcome = check_snippet_with_budget(
        "budget_tight_fail.lean",
        "theorem tNat (n : Nat) : n = n := rfl\n",
        1,
    );
    assert_eq!(outcome.diverged.len(), 1, "must diverge: {outcome:?}");
    assert!(
        outcome.errors.is_empty(),
        "a budget exhaustion must not be reported as an elaboration error: {outcome:?}"
    );
    assert!(
        outcome.kernel_failures.is_empty(),
        "a budget exhaustion must not be reported as a kernel failure: {outcome:?}"
    );
    assert!(
        outcome.trust_failures.is_empty(),
        "a budget exhaustion must not be reported as a trust failure: {outcome:?}"
    );
    assert_eq!(
        outcome.success_count, 0,
        "and must not be reported as a pass: {outcome:?}"
    );
}

/// THE REFILL. The budget is PER DECLARATION, which means it is handed back at
/// each one — not spent down across the file.
///
/// The distinction is invisible under a 1-tick budget (everything diverges
/// either way, because the exhaustion latch carries forward), so this test
/// picks a budget that only a refilling implementation can survive: 1.5× what
/// the single heaviest declaration actually spends, measured here rather than
/// hard-coded. Refilling → all three pass. Not refilling → the first
/// declaration eats the pot and its two identical siblings diverge.
#[test]
fn decl_budget_is_refilled_at_every_declaration() {
    let code =
        "def pA (n : Nat) : Nat := n\ndef pB (n : Nat) : Nat := n\ndef pC (n : Nat) : Nat := n\n";

    // Measure, do not guess: the run under the default budget reports the
    // heaviest single declaration's tick count, so this test re-derives its own
    // threshold whenever the elaborator's cost profile moves.
    let measured = check_snippet_with_budget("budget_multi.lean", code, DEFAULT_DECL_BUDGET);
    assert_eq!(
        measured.success_count, 3,
        "control: all three must pass under the default budget: {measured:?}"
    );
    let peak = measured.peak_decl_ticks;
    assert!(
        peak > 0,
        "the run must have spent measurable fuel: {measured:?}"
    );

    // Enough for the heaviest declaration and half again — but nowhere near
    // enough for three of them out of one pot.
    let per_decl = peak + peak / 2;
    let refilled = check_snippet_with_budget("budget_multi_refill.lean", code, per_decl);
    assert!(
        refilled.diverged.is_empty(),
        "with the budget refilled per declaration, a per-declaration-sized \
         budget must carry the whole file: {refilled:?}"
    );
    assert_eq!(
        refilled.success_count, 3,
        "all three declarations must still pass: {refilled:?}"
    );
}

/// One diverging declaration must NOT take the rest of the file with it: every
/// declaration is measured and recorded on its own, and the denominator still
/// shows all of them.
#[test]
fn decl_budget_starvation_still_reports_every_declaration() {
    let code =
        "def qA (n : Nat) : Nat := n\ndef qB (n : Nat) : Nat := n\ndef qC (n : Nat) : Nat := n\n";
    let starved = check_snippet_with_budget("budget_multi_starved.lean", code, 1);
    assert_eq!(
        starved.diverged.len(),
        3,
        "each declaration must get its own row rather than the run being \
         abandoned at the first one: {starved:?}"
    );
    assert_eq!(
        starved.success_count, 0,
        "none of them finished: {starved:?}"
    );
    assert_eq!(
        starved.decl_count, 3,
        "and the denominator must still show all three were looked at: {starved:?}"
    );
}

/// `0` means unlimited, and unlimited must be indistinguishable from the
/// mechanism being absent.
#[test]
fn decl_budget_zero_is_unlimited() {
    let outcome =
        check_snippet_with_budget("budget_zero.lean", "def idZ (n : Nat) : Nat := n\n", 0);
    assert_eq!(
        outcome.success_count, 1,
        "0 must mean unlimited: {outcome:?}"
    );
    assert!(
        outcome.diverged.is_empty(),
        "0 must never diverge: {outcome:?}"
    );
}

/// The budget must not leak out of a `clean check` call. It is thread-local
/// and the CLI's worker thread is reused by the test harness; a leftover
/// 1-tick limit would silently starve everything that ran afterwards.
#[test]
fn decl_budget_does_not_leak_past_the_check_call() {
    let starved =
        check_snippet_with_budget("budget_leak_a.lean", "def leakA (n : Nat) : Nat := n\n", 1);
    assert_eq!(starved.diverged.len(), 1, "setup must diverge: {starved:?}");
    assert_eq!(
        clean_kernel::tc::declaration_budget_limit(),
        0,
        "the ambient budget must be disarmed when `clean check` returns"
    );
    let after = check_snippet_with_budget(
        "budget_leak_b.lean",
        "def leakB (n : Nat) : Nat := n\n",
        DEFAULT_DECL_BUDGET,
    );
    assert_eq!(
        after.success_count, 1,
        "a later run must not inherit the earlier run's starvation: {after:?}"
    );
}

/// The summary line grows a third clause only when something diverged, so
/// every existing consumer of "N passed, M failed" keeps parsing it.
#[test]
fn emit_check_summary_reports_diverged_separately() {
    let mut buf = Vec::new();
    emit_check_summary(&mut buf, 3, Duration::from_millis(5), 2, 0, 1)
        .expect("write should succeed");
    let output = String::from_utf8(buf).expect("valid utf8");
    assert!(
        output.contains("2 passed, 0 failed, 1 did not finish"),
        "diverged declarations must be reported in their own clause: {output}"
    );
}

/// `"check failed"` is a string other tooling matches on (`clean check`'s own
/// fail-closed import tests, `scripts/source_elab_gate.sh`). Adding a third
/// status must not have quietly reworded it.
#[test]
fn check_failure_message_keeps_the_load_bearing_failed_string() {
    assert_eq!(
        super::cmd_core::check_failure_message("fail"),
        "check failed"
    );
    assert_ne!(
        super::cmd_core::check_failure_message("diverged"),
        "check failed",
        "a run that did not finish must not claim to have failed"
    );
    assert!(
        super::cmd_core::check_failure_message("diverged").contains("did not finish"),
        "the diverged message must say what actually happened"
    );
}
