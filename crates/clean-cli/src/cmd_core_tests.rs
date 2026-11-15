// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::cmd_core::{check_file, collect_check_outcome, emit_check_summary};
use clean_kernel::cli::{PreludeMode, DEFAULT_DECL_BUDGET};
use std::{fs, time::Duration};

#[test]
fn emit_check_summary_success_uses_lean_parser_summary_line() {
    let mut buf = Vec::new();
    emit_check_summary(&mut buf, 2, Duration::from_millis(7), 2, 0, 0, 0)
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
    emit_check_summary(&mut buf, 4, Duration::from_millis(11), 2, 2, 0, 0)
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

    // Nothing was type-checked, so nothing is counted as passed. And a run
    // that checked nothing has no verdict: it is refused (`nothing_checked`),
    // not passed — this test used to require exit 0, which the round-22
    // verification of `317f48b45` measured as a vacuous pass.
    let result = check_file(&path, false, false, PreludeMode::Builtin);
    let err = result.expect_err("a file that checks nothing must not pass");
    assert!(
        err.to_string().contains("no declaration was checked"),
        "unexpected error: {err}"
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

/// `check_file` starts and ends every run with a cleared trust ledger
/// (`TrustCounterScope` resets the sorry counter on entry and on drop), so a
/// failing run's sorries never carry into the next run or into a later reader.
///
/// Read through this thread's view of the counter, not the process-wide one:
/// the global is shared by every test in the binary, and another test's
/// elaboration (for example `test_check_rows_match_module_driver_verdicts`,
/// which mints a `sorry` under the module lock and leaves it in the global)
/// can leave it non-zero before this test starts or bump it between
/// `check_file` returning and the read. The thread view counts exactly what
/// this test's own runs minted and is cleared by the same reset, so removing
/// the reset in `TrustCounterScope::drop` still fails this test (the failing
/// run's `sorry` stays counted).
#[test]
fn check_file_clears_trust_state_between_runs() {
    use clean_kernel::sorry::local_sorry_count;

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

    let failing_result = check_file(&failing_path, false, false, PreludeMode::Builtin);
    assert!(
        failing_result.is_err(),
        "explicit sorry must still fail closed"
    );
    assert_eq!(
        local_sorry_count(),
        0,
        "check_file should clear the trust counter state after failure"
    );

    check_file(&clean_path, false, false, PreludeMode::Builtin)
        .expect("clean file should type check");
    assert_eq!(
        local_sorry_count(),
        0,
        "check_file should leave the trust counter state cleared after success"
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
        clean_kernel::cli::DEFAULT_AUTOMATION_BUDGET,
        &[],
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
    emit_check_summary(&mut buf, 3, Duration::from_millis(5), 2, 0, 1, 0)
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

// ── Trust counters (task #66) ────────────────────────────────────────────
//
// `Clean-check-report-v1`'s `trust_summary.sorry_axioms` and
// `.kernel_check_failures` were STRUCTURALLY always 0 from `d935d692e` until
// this fix: `collect_check_outcome` holds a `TrustCounterScope` whose `Drop`
// zeroes both globals when it returns, and `finalize_check_run` — which runs
// afterwards — read those globals. Three sorry-tainted successes in the pinned
// Mathlib slice were reported as zero. Full diagnosis:
// `docs/issues/2026-08-30-check-report-trust-counters-read-after-reset.md`.
//
// Every test here is written so that RESTORING the global read makes it fail:
// each asserts a counter carried on `FileCheckOutcome`, and separately asserts
// that the global a re-reader would consult is zero by the time the value is
// available. Those two assertions together are the mutation proof — the second
// one is what makes the first one about the guard rather than about counting.

/// Helper: run one snippet through the real check pipeline under the default
/// budget, with `allow_sorry` selectable, and hand back the outcome.
pub(crate) fn check_snippet_allowing_sorry(
    name: &str,
    code: &str,
    allow_sorry: bool,
) -> super::cmd_core::FileCheckOutcome {
    let dir = tempfile::tempdir().expect("tempdir should be created");
    let path = dir.path().join(name);
    fs::write(&path, code).expect("write should succeed");
    let (outcome, _elapsed) = collect_check_outcome(
        &path,
        false,
        allow_sorry,
        PreludeMode::Builtin,
        false,
        false,
        clean_elab::ImportPolicy::default(),
        DEFAULT_DECL_BUDGET,
        clean_kernel::cli::DEFAULT_AUTOMATION_BUDGET,
        &[],
    )
    .expect("the check pipeline itself must not error out");
    outcome
}

/// THE REGRESSION TEST. Two sorries under `--allow-sorry` are two counted
/// successes AND two recorded sorry axioms — the taint must survive the run.
///
/// Under `allow_sorry`, `record_checked_decl` folds a sorry-tainted
/// declaration into `success_count` and leaves `trust_failures` empty, so
/// `sorry_axioms` is the ONLY evidence in the report that these two passes are
/// not sorry-free. A structural zero here is a signal that cannot say no.
#[test]
fn trust_counters_sorry_axioms_survive_the_guard() {
    let outcome = check_snippet_allowing_sorry(
        "two_sorry.lean",
        "theorem tTac (a : Nat) : a = a := by sorry\n\
         theorem tTerm (a : Nat) : a = a := sorry\n",
        true,
    );
    assert_eq!(
        outcome.success_count, 2,
        "control: --allow-sorry must count both declarations as passes: {outcome:?}"
    );
    assert!(
        outcome.trust_failures.is_empty(),
        "control: --allow-sorry must not record them as trust failures — which is \
         exactly why the counter is the only taint evidence left: {outcome:?}"
    );
    assert_eq!(
        outcome.sorry_axioms, 2,
        "two declarations use sorry and the report must say so: {outcome:?}"
    );
    assert_eq!(
        outcome.sorry_terms_minted, 2,
        "the run created two sorry terms and the report must say so: {outcome:?}"
    );
}

/// The other half of the mutation proof: by the time anyone outside
/// `collect_check_outcome` can look, the global is already zero.
///
/// This is what makes the test above a test of the READ SITE rather than of
/// the counter. Re-point `finalize_check_run` at `sorry_count()` and it gets
/// this 0, not the 2 asserted above.
#[test]
fn trust_counters_the_global_is_already_zero_when_collect_returns() {
    use clean_kernel::sorry::sorry_count;

    let outcome = check_snippet_allowing_sorry(
        "two_sorry_global.lean",
        "theorem gTac (a : Nat) : a = a := by sorry\n\
         theorem gTerm (a : Nat) : a = a := sorry\n",
        true,
    );
    assert_eq!(
        outcome.sorry_terms_minted, 2,
        "setup: the run must have observed two minted sorries: {outcome:?}"
    );
    assert_eq!(
        sorry_count(),
        0,
        "TrustCounterScope::drop zeroes the global on return, so any read from \
         outside collect_check_outcome is a structural zero — that is the whole \
         defect, and it must stay reproducible so this test keeps its meaning"
    );
}

/// A clean file must report zero. Without this control, a `sorry_axioms` field
/// hard-wired to a constant would pass the test above.
#[test]
fn trust_counters_a_clean_file_reports_zero_sorry_axioms() {
    let outcome = check_snippet_allowing_sorry(
        "no_sorry.lean",
        "theorem tClean (a : Nat) : a = a := rfl\n",
        true,
    );
    assert_eq!(outcome.success_count, 1, "control must pass: {outcome:?}");
    assert_eq!(
        outcome.sorry_axioms, 0,
        "a sorry-free file must report no sorry axioms: {outcome:?}"
    );
    assert_eq!(outcome.sorry_terms_minted, 0, "{outcome:?}");
}

/// The same defect, same fix, for `kernel_check_failures`.
///
/// `theorem tBad : Nat := Nat.zero` is rejected by the kernel with
/// `TheoremTypeNotProp`, which bumps `KERNEL_CHECK_FAILURE_COUNTER` and
/// surfaces as an ordinary `errors` row. So this counter is NOT derivable from
/// `outcome.kernel_failures` (empty here): without it a kernel rejection is
/// indistinguishable from any other elaboration error, which is precisely what
/// a trust summary is for.
///
/// The counter is a LOWER BOUND on kernel rejections — only
/// `add_decl_with_kernel_check` bumps it — so this fixture is chosen to be one
/// that does. See the field's doc comment on `FileCheckOutcome`.
#[test]
fn trust_counters_kernel_check_failures_survive_the_guard() {
    use clean_elab::kernel_check_failure_count;

    let outcome = check_snippet_allowing_sorry(
        "two_kernel_rejects.lean",
        "theorem kBadA : Nat := Nat.zero\ntheorem kBadB : Nat := Nat.zero\n",
        false,
    );
    assert_eq!(
        outcome.errors.len(),
        2,
        "control: both declarations must be rejected: {outcome:?}"
    );
    assert!(
        outcome
            .errors
            .iter()
            .all(|e| e.contains("Kernel check failed")),
        "control: the rejection must come from the kernel, not from an earlier \
         elaboration check: {outcome:?}"
    );
    assert!(
        outcome.kernel_failures.is_empty(),
        "control: a kernel rejection during elaboration lands in `errors`, so the \
         counter is not recoverable from this bucket: {outcome:?}"
    );
    assert_eq!(
        outcome.kernel_check_failures, 2,
        "the kernel rejected two declarations and the report must say so: {outcome:?}"
    );
    assert_eq!(
        kernel_check_failure_count(),
        0,
        "and the global a late reader would consult is already zero"
    );
}

/// Control for the above: a file the kernel accepts reports zero.
#[test]
fn trust_counters_an_accepted_file_reports_zero_kernel_check_failures() {
    let outcome = check_snippet_allowing_sorry(
        "kernel_ok.lean",
        "theorem kOk (a : Nat) : a = a := rfl\n",
        false,
    );
    assert_eq!(outcome.success_count, 1, "control must pass: {outcome:?}");
    assert_eq!(
        outcome.kernel_check_failures, 0,
        "an accepted file must report no kernel check failures: {outcome:?}"
    );
}

// ---------------------------------------------------------------------------
// The summary's three numbers must partition the denominator, or say they do not
// ---------------------------------------------------------------------------

/// `clean check` printed `Checked 207 declarations` / `69 passed, 146 failed`
/// on `Mathlib/Order/Basic.lean`. 69 + 146 is 215.
///
/// The excess was exactly the file's eight PARSER RECOVERY notes, which were
/// pushed onto `errors` and so counted as declaration failures. They are not
/// declarations: one declaration can emit several (the pending-recovery batch),
/// and a `RawDecl` emits one recovery note AND a real error row for the same
/// declaration — so no arithmetic on a count could have separated them after
/// the fact. Three checked-in artifacts under `reports/source-elab/` show the
/// same shape: Order/Basic +8 with 8 notes, Function/Basic +7 with 7,
/// Logic/Basic +1 with 1.
///
/// This is the fixture from `cmd_core`'s own tests: two good declarations and
/// one the parser must recover from.
#[test]
fn parser_recovery_notes_are_not_counted_as_declaration_failures() {
    let outcome = check_snippet_with_budget(
        "Recovery.lean",
        "def foo := 1\ndef ??? := !!!\ndef bar := 2\n",
        DEFAULT_DECL_BUDGET,
    );

    assert!(
        !outcome.parser_diagnostics.is_empty(),
        "the fixture must actually exercise parser recovery, or this test proves \
         nothing: {outcome:?}"
    );
    let failed =
        outcome.errors.len() + outcome.trust_failures.len() + outcome.kernel_failures.len();
    assert_eq!(
        outcome.success_count + failed + outcome.diverged.len(),
        outcome.decl_count,
        "passed + failed + diverged must equal the declaration count a reader is \
         shown; recovery notes belong in `parser_diagnostics`, not `errors`. \
         outcome = {outcome:?}"
    );
}

/// A reader adds the two numbers the summary prints. When they cannot add up —
/// a failure row from an intra-project import is reported here while that
/// module's declarations are not in the denominator — the summary must SAY so.
/// Silence is what let the parser-recovery defect live: nothing in the output
/// ever admitted the sum was wrong.
#[test]
fn a_summary_that_does_not_partition_says_that_it_does_not() {
    let mut buf = Vec::new();
    emit_check_summary(&mut buf, 207, Duration::from_millis(1), 69, 146, 0, 8)
        .expect("write should succeed");
    let output = String::from_utf8(buf).expect("valid utf8");
    assert!(
        output.contains("add to 215, not 207"),
        "a non-partitioning summary must name both totals: {output}"
    );
    assert!(
        output.contains("8 parser recovery note(s)"),
        "recovery notes get their own line, not a share of the partition: {output}"
    );

    // And when they DO partition, no note appears — it would be noise on every
    // clean run, and a line that always prints is a line nobody reads.
    let mut buf = Vec::new();
    emit_check_summary(&mut buf, 207, Duration::from_millis(1), 69, 138, 0, 8)
        .expect("write should succeed");
    let output = String::from_utf8(buf).expect("valid utf8");
    assert!(
        !output.contains("add to"),
        "no note when it adds up: {output}"
    );
}

/// `clean check --json`'s `timing` block: one per-declaration record per
/// declaration the user wrote -- `section`/`namespace` members included, the
/// blocks themselves never -- under its qualified name and its OWN line, and a
/// phase split that accounts for the elaboration. The fixture is accepted by
/// the pinned Lean v4.30.0-rc2 (exit 0, measured 2026-09-24).
#[test]
fn test_check_timing_per_declaration_names_lines_and_phases() {
    let code = "namespace Foo\ndef a : Nat := 1\ndef b : Nat := a + 1\nend Foo\n\
                section S\ntheorem t : Foo.b = 2 := rfl\nend S\n";
    let outcome = check_snippet_with_budget("timing.lean", code, DEFAULT_DECL_BUDGET);
    assert_eq!(
        outcome.success_count, 3,
        "control: all three pass: {outcome:?}"
    );
    let rows: Vec<(&str, u32)> = outcome
        .timing
        .per_declaration
        .iter()
        .map(|r| (r.name.as_str(), r.line))
        .collect();
    assert_eq!(
        rows,
        vec![("Foo.a", 2), ("Foo.b", 3), ("t", 6)],
        "{:?}",
        outcome.timing
    );
    // An import-free file spends nothing importing, and its elaboration phase
    // covers the declarations timed inside it.
    assert_eq!(
        outcome.timing.import,
        Duration::ZERO,
        "{:?}",
        outcome.timing
    );
    let per_decl_ms: f64 = outcome
        .timing
        .per_declaration
        .iter()
        .map(|r| r.elapsed_ms)
        .sum();
    assert!(
        outcome.timing.elab.as_secs_f64() * 1000.0 + 1.0 >= per_decl_ms,
        "elab phase {:?} must cover the per-declaration total {per_decl_ms} ms",
        outcome.timing.elab
    );
    let report = crate::check_timing::report(outcome.timing.clone(), Duration::from_secs(1));
    let json = serde_json::to_value(&report).expect("timing serializes");
    for key in [
        "total_s",
        "setup_s",
        "parse_s",
        "import_s",
        "elab_s",
        "per_declaration",
    ] {
        assert!(json.get(key).is_some(), "timing.{key} missing: {json}");
    }
}
