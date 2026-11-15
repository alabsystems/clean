// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Attribution** regressions: a failing tactic must name itself.
//!
//! Brick T0 of `docs/plans/TACTICS_TO_100_2026-07-29.md` closed the *silent*
//! class (a construct that produced no diagnostic at all). This file guards the
//! neighbouring one, measured at **88 of 373** census probes on `origin/main`
//! (`data/silent_tactic_census.json`, verdict `unnamed`): the declaration fails
//! LOUDLY, but nothing in the diagnostic says which tactic gave up. A tactic
//! that fails without naming itself is effectively hidden — a reader cannot
//! tell whether `omega` ran and gave up or was never reached.
//!
//! Every test here grades `format!("{err:?}")` — the Debug rendering the
//! census gate (`tests/silent_tactic_census.rs`) and the attribution
//! predicate (`ElabCtx::attribute_tactic_failure`) grade. Since 2026-08-27
//! `clean check` itself prints the Display form (`cmd_core.rs`, "THE SINGLE
//! RENDERING SITE"); Debug carries every payload field Display can show, so a
//! failure graded `unnamed` here is unnamed on the terminal too.
//!
//! Verified RED: with `ElabCtx::attribute_tactic_failure` neutered to return
//! its argument, **4 of these 6 fail** and the two marked DECOY stay green.
//! The decoys are what discriminate a real attribution mechanism from cheap
//! imitations — blanket-wrapping every error (which would score identically on
//! the census while breaking every consumer that matches on `UnknownTactic`),
//! and letting the wrapper leak into `first`'s backtracking decision. A third
//! test doubles as a discriminator: naming a failure that `try` already
//! recovered from is a *false* attribution, and "remember the last error seen"
//! would produce exactly that.

use super::*;
use crate::tactic::TacticError;
use crate::ElabError;

/// Elaborate `source` against the builtin prelude and return the first error.
///
/// Drives the same pipeline `clean check` drives; the graded string is the
/// Debug rendering the census gate grades (see the module doc).
fn first_error(source: &str) -> ElabError {
    let patterns = crate::tactic::builtins::builtin_tactic_patterns();
    let report = clean_parser::parse_file_with_tactics_diagnostics(source, &patterns)
        .expect("probe source parses");
    let mut env = Environment::with_prelude();
    let mut file_ctx = crate::FileContext::new();
    let mut first: Option<ElabError> = None;
    for decl in &report.decls {
        let processed = crate::preprocess_decl_with_context(decl, &mut file_ctx);
        if let Err(err) = crate::elaborate_decl_and_register_with_warning(&mut env, &processed) {
            first.get_or_insert(err);
        }
    }
    first.unwrap_or_else(|| panic!("expected an elaboration failure for:\n{source}"))
}

fn elaborates_cleanly(source: &str) -> bool {
    let patterns = crate::tactic::builtins::builtin_tactic_patterns();
    let Ok(report) = clean_parser::parse_file_with_tactics_diagnostics(source, &patterns) else {
        return false;
    };
    let mut env = Environment::with_prelude();
    let mut file_ctx = crate::FileContext::new();
    report.decls.iter().all(|decl| {
        let processed = crate::preprocess_decl_with_context(decl, &mut file_ctx);
        crate::elaborate_decl_and_register_with_warning(&mut env, &processed).is_ok()
    })
}

/// `unsolved goals` is raised by the BLOCK, after every tactic already
/// returned `Ok` — so before attribution nothing in it named a tactic at all.
///
/// The second half of this test is the load-bearing half: the underlying
/// diagnostic must be structurally identical to before. Attribution changes
/// the message, never the verdict.
#[test]
fn test_unsolved_goals_names_the_last_tactic_that_ran() {
    let err = first_error("theorem probe (p q : Prop) (hp : p) : p → p := by\n  intro hx\n");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("intro"),
        "`unsolved goals` must name the tactic that ran and left the goal open; got: {rendered}"
    );
    assert!(
        matches!(
            err.innermost(),
            ElabError::TacticFailed(TacticError::UnsolvedGoals { count: 1, .. })
        ),
        "the underlying diagnostic must be unchanged, got: {err:?}"
    );
}

/// A failure inside a `conv` body must name **both** the block and the
/// navigation step. Blaming only `conv` would leave `lhs`, `rhs`, `arg`,
/// `enter`, `congr` — 25 of the 88 measured rows — still hidden.
#[test]
fn test_nested_conv_body_names_the_inner_tactic_and_the_chain() {
    let err =
        first_error("theorem probe (a b : Nat) (h : a = b) : a = a := by\n  conv =>\n    lhs\n");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("lhs"),
        "the conv-mode navigation step must be named, got: {rendered}"
    );
    assert!(
        rendered.contains("conv"),
        "the enclosing conv block must be named, got: {rendered}"
    );
}

/// The attribution must carry a source span, not just a name: with the same
/// tactic used twice, the position is the only thing that says which one.
#[test]
fn test_attribution_carries_the_source_span() {
    let source = "theorem probe (p q : Prop) (hp : p) : p → p := by\n  intro hx\n";
    let err = first_error(source);
    let ElabError::InTactic {
        span_start,
        span_end,
        ..
    } = &err
    else {
        panic!("expected an attributed failure, got: {err:?}");
    };
    assert!(
        span_start < span_end && *span_end <= source.len(),
        "span {span_start}..{span_end} must be a real range in a {}-byte source",
        source.len()
    );
    assert!(
        source[*span_start..*span_end].contains("intro"),
        "span {span_start}..{span_end} should cover the tactic, covers {:?}",
        &source[*span_start..*span_end]
    );
}

/// DECOY — an error that ALREADY names its tactic must come back structurally
/// unchanged.
///
/// This is what separates attribution from blanket-wrapping. A fix that wraps
/// every tactic failure would push `UnknownTactic` one level down and break
/// every consumer that matches on it, while scoring exactly the same on the
/// census. Passes before and after.
#[test]
fn test_an_error_that_already_names_its_tactic_is_not_rewrapped() {
    let err = first_error("theorem probe (a : Nat) : a = a := by\n  no_such_tactic_xyz\n");
    assert!(
        matches!(
            err,
            ElabError::TacticFailed(TacticError::UnknownTactic(ref name))
                if name == "no_such_tactic_xyz"
        ),
        "an already-attributed error must not be wrapped, got: {err:?}"
    );
}

/// DECOY — a failure that `try` recovered from must not be blamed for a later,
/// unrelated `unsolved goals`.
///
/// A naive implementation ("remember the last error seen") passes the census
/// and fails here: it would name `rfl`, which succeeded from the user's point
/// of view, and would never name `skip`, which is the tactic the block
/// actually ended on.
#[test]
fn test_a_recovered_failure_is_not_blamed_for_a_later_diagnostic() {
    let err =
        first_error("theorem probe (a b : Nat) (h : a = b) : a = b := by\n  try rfl\n  skip\n");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("skip"),
        "the block ended on `skip`; that is what must be named, got: {rendered}"
    );
    assert!(
        !rendered.contains("rfl"),
        "`rfl` failed but `try` recovered it — blaming it is a false attribution: {rendered}"
    );
}

/// DECOY — `first` must still backtrack across the elaboration boundary.
///
/// `first`'s backtracking decision is made by
/// `TacticError::is_recoverable_first_failure` on the error *variant*. If the
/// attribution wrapper leaked into that path, a losing branch would stop being
/// recoverable and this proof would fail. Passes before and after; it is the
/// verdict-preservation guard.
#[test]
fn test_attribution_does_not_change_combinator_backtracking() {
    assert!(
        elaborates_cleanly(
            "theorem probe (a b : Nat) (h : a = b) : a = b := by\n  first\n    | rfl\n    | exact h\n"
        ),
        "`first | rfl | exact h` must still backtrack past the failing branch"
    );
}
