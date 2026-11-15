// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean check --automation-budget`: the per-declaration automation work
//! budget (Lean's `maxHeartbeats` shape; `clean-auto`'s `work_budget.rs`),
//! measured through the real check pipeline.
//!
//! Each test is written so that REMOVING the budget makes it fail: with no
//! budget the starved runs would pass, and with no per-declaration refill the
//! refill run would fail its second and third declarations.

use super::cmd_core::{collect_check_outcome, FileCheckOutcome};
use clean_kernel::cli::{PreludeMode, DEFAULT_AUTOMATION_BUDGET, DEFAULT_DECL_BUDGET};
use std::fs;

/// A `simp` proof the builtin prelude closes (`Nat.add_zero` is a builtin
/// simp lemma), so every run below spends simp work units.
const SIMP_PROOF: &str = "theorem simpAddZero (n : Nat) : n + 0 = n := by simp\n";

fn check_with_automation_budget(
    name: &str,
    code: &str,
    automation_budget: u64,
) -> FileCheckOutcome {
    check_with_budgets(name, code, DEFAULT_DECL_BUDGET, automation_budget)
}

fn check_with_budgets(
    name: &str,
    code: &str,
    decl_budget: u64,
    automation_budget: u64,
) -> FileCheckOutcome {
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
        automation_budget,
        &[],
    )
    .expect("the check pipeline itself must not error out");
    outcome
}

fn work_of(outcome: &FileCheckOutcome, decl: &str) -> u64 {
    outcome
        .timing
        .per_declaration
        .iter()
        .find(|d| d.name == decl)
        .map(|d| d.automation_work)
        .unwrap_or_else(|| panic!("no timing record for {decl}: {outcome:?}"))
}

/// The control: the default budget leaves a `simp` proof passing, and the
/// report records the work it spent (the calibration input).
#[test]
fn automation_budget_default_leaves_a_simp_proof_passing_and_measured() {
    let outcome =
        check_with_automation_budget("auto_ok.lean", SIMP_PROOF, DEFAULT_AUTOMATION_BUDGET);
    assert_eq!(outcome.success_count, 1, "control must pass: {outcome:?}");
    assert!(
        outcome.errors.is_empty(),
        "control must not error: {outcome:?}"
    );
    let spent = work_of(&outcome, "simpAddZero");
    assert!(
        spent > 0,
        "a simp proof must be charged work units: {outcome:?}"
    );
    assert!(
        spent < DEFAULT_AUTOMATION_BUDGET,
        "and far less than the default: {spent}"
    );
}

/// A declaration that exhausts the budget FAILS, and says so by name — Lean's
/// "(deterministic) timeout … maximum number of heartbeats" shape. It is a
/// failure, not `diverged`: the kernel's `--decl-budget` verdict is untouched.
#[test]
fn automation_budget_exhaustion_fails_the_declaration_with_the_named_error() {
    let outcome = check_with_automation_budget("auto_starved.lean", SIMP_PROOF, 1);
    assert_eq!(
        outcome.success_count, 0,
        "a simp proof with one unit of automation budget must not pass: {outcome:?}"
    );
    assert!(
        outcome.diverged.is_empty(),
        "automation exhaustion is a failure, not a kernel-budget divergence: {outcome:?}"
    );
    assert_eq!(
        outcome.errors.len(),
        1,
        "exactly one failure row: {outcome:?}"
    );
    let row = &outcome.errors[0];
    assert!(
        row.contains("simpAddZero")
            && row.contains("automation budget exhausted")
            && row.contains("`simp`")
            && row.contains("--automation-budget"),
        "the row must name the declaration, the budget, the site and the knob: {row}"
    );
}

/// One unit under what the proof measurably needs fails; exactly what it needs
/// passes. The line is deterministic, so the two runs cannot straddle it by
/// load or luck.
#[test]
fn automation_budget_exact_need_passes_one_under_fails() {
    let measured = check_with_automation_budget("auto_measure.lean", SIMP_PROOF, u64::MAX);
    assert_eq!(measured.success_count, 1, "control: {measured:?}");
    let need = work_of(&measured, "simpAddZero");

    let exact = check_with_automation_budget("auto_exact.lean", SIMP_PROOF, need);
    assert_eq!(
        exact.success_count, 1,
        "exactly the measured need must pass: {exact:?}"
    );
    assert_eq!(
        work_of(&exact, "simpAddZero"),
        need,
        "the charge is deterministic"
    );

    let under = check_with_automation_budget("auto_under.lean", SIMP_PROOF, need - 1);
    assert_eq!(
        under.success_count, 0,
        "one unit under the measured need must fail: {under:?}"
    );
}

/// THE REFILL, and at LEAF granularity: three `simp` theorems inside one
/// `namespace` (one top-level unit for `--decl-budget`) each get the whole
/// budget. A budget sized for one of them carries all three only if it is
/// refilled per member.
#[test]
fn automation_budget_is_refilled_for_every_namespace_member() {
    let code = "namespace AutoRefill\n\
                theorem a (n : Nat) : n + 0 = n := by simp\n\
                theorem b (n : Nat) : n + 0 = n := by simp\n\
                theorem c (n : Nat) : n + 0 = n := by simp\n\
                end AutoRefill\n";
    let measured = check_with_automation_budget("auto_refill_measure.lean", code, u64::MAX);
    assert_eq!(measured.success_count, 3, "control: {measured:?}");
    let need = ["AutoRefill.a", "AutoRefill.b", "AutoRefill.c"]
        .iter()
        .map(|d| work_of(&measured, d))
        .max()
        .unwrap_or(0);
    assert!(need > 0, "each member must spend work: {measured:?}");

    let per_member = need + need / 2;
    let refilled = check_with_automation_budget("auto_refill.lean", code, per_member);
    assert_eq!(
        refilled.success_count, 3,
        "a budget sized for one member must carry every member when it is \
         refilled per declaration: {refilled:?}"
    );
}

/// The simp lemma index is cached across `simp` calls, so a lemma that
/// becomes `@[simp]` MID-FILE — after a `simp` call has already built and
/// cached the index — must still be seen by the next call. A stale index would
/// be a correctness bug that the kernel re-check cannot catch (it only ever
/// sees the proofs simp DID find). Both the global and the `local` attribute.
#[test]
fn simp_index_sees_a_simp_attribute_added_mid_file() {
    let code = "axiom fAuto : Nat → Nat\n\
                axiom fAuto_eq (n : Nat) : fAuto n = n\n\
                axiom gAuto : Nat → Nat\n\
                axiom gAuto_eq (n : Nat) : gAuto n = n\n\
                theorem beforeF (n : Nat) : fAuto n = n := by simp\n\
                attribute [simp] fAuto_eq\n\
                theorem afterF (n : Nat) : fAuto n = n := by simp\n\
                section\n\
                attribute [local simp] gAuto_eq\n\
                theorem afterG (n : Nat) : gAuto n = n := by simp\n\
                end\n\
                theorem outsideG (n : Nat) : gAuto n = n := by simp\n";
    let outcome =
        check_with_automation_budget("simp_index_mid_file.lean", code, DEFAULT_AUTOMATION_BUDGET);
    let failed = |decl: &str| {
        outcome
            .errors
            .iter()
            .any(|row| row.starts_with(&format!("{decl}:")))
    };
    assert!(
        failed("beforeF"),
        "control: before the attribute simp has no lemma for `fAuto`: {outcome:?}"
    );
    assert!(
        !failed("afterF"),
        "a global simp attribute added mid-file must be seen: {outcome:?}"
    );
    assert!(
        !failed("afterG"),
        "a local simp attribute must be seen inside its section: {outcome:?}"
    );
    assert!(
        failed("outsideG"),
        "…and must be gone after the section ends: {outcome:?}"
    );
    assert_eq!(outcome.success_count, 6, "{outcome:?}");
}

/// `0` means unlimited, and unlimited counts nothing.
#[test]
fn automation_budget_zero_is_unlimited_and_uncounted() {
    let outcome = check_with_automation_budget("auto_zero.lean", SIMP_PROOF, 0);
    assert_eq!(
        outcome.success_count, 1,
        "0 must mean unlimited: {outcome:?}"
    );
    assert_eq!(work_of(&outcome, "simpAddZero"), 0);
}

/// `--decl-budget` counts the KERNEL operations a `simp` or `grind` search
/// makes, so it bounds that work too; only the superposition loop, which makes
/// none, escapes it. `--automation-budget`'s help once said `--decl-budget`
/// "does not bound this work" at all.
///
/// Each probe's search FAILS inside `try`, and the `exact` after it is the
/// control's, so the kernel checks the same proof term in all three files and
/// every tick a probe spends beyond the control's is its search's. A decl
/// budget one tick above the control's spend passes the control and cuts both
/// probes as `diverged`.
#[test]
fn decl_budget_counts_the_kernel_operations_of_a_failed_simp_or_grind_search() {
    let file = |search: &str| {
        format!(
            "axiom fProbe : Nat → Nat\n\
             axiom fProbe_eq (a b : Nat) : fProbe a = fProbe b\n\
             theorem probe (a b : Nat) : fProbe (a + 0) = fProbe (b + 0) := by\n\
             {search}  exact fProbe_eq (a + 0) (b + 0)\n"
        )
    };
    let control =
        check_with_automation_budget("decl_ctl.lean", &file(""), DEFAULT_AUTOMATION_BUDGET);
    assert_eq!(control.success_count, 3, "control: {control:?}");
    assert_eq!(
        work_of(&control, "probe"),
        0,
        "the control runs no automation"
    );
    let control_ticks = control.peak_decl_ticks;
    assert!(
        control_ticks > 0,
        "the control must be counted: {control:?}"
    );

    let bounded = check_with_budgets(
        "decl_ctl_bounded.lean",
        &file(""),
        control_ticks + 1,
        DEFAULT_AUTOMATION_BUDGET,
    );
    assert_eq!(
        bounded.success_count, 3,
        "one tick above its own spend, the control must still pass: {bounded:?}"
    );

    for (name, search) in [
        ("decl_simp.lean", "  (try simp only [Nat.zero_add])\n"),
        ("decl_grind.lean", "  (try grind)\n"),
    ] {
        let measured = check_with_automation_budget(name, &file(search), DEFAULT_AUTOMATION_BUDGET);
        assert_eq!(
            measured.success_count, 3,
            "{name}: the search fails inside `try` and the `exact` closes: {measured:?}"
        );
        assert!(
            work_of(&measured, "probe") > 0,
            "{name}: the search must be charged automation work: {measured:?}"
        );
        assert!(
            measured.peak_decl_ticks > control_ticks + 1,
            "{name}: the failed search must spend kernel ticks of its own \
             ({} vs the control's {control_ticks})",
            measured.peak_decl_ticks
        );
        let cut = check_with_budgets(
            name,
            &file(search),
            control_ticks + 1,
            DEFAULT_AUTOMATION_BUDGET,
        );
        assert!(
            cut.diverged.iter().any(|row| row.starts_with("probe")),
            "{name}: --decl-budget must cut the search the control fits under: {cut:?}"
        );
    }
}
