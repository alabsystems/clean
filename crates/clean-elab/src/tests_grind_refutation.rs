// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! grind opens the GOAL: `exfalso` when the context can reach a
//! contradiction, `Iff.intro` on a biconditional.
//!
//! Lean's grind is a refutation prover — `intro`
//! (`Lean/Meta/Tactic/Grind/Intro.lean`) applies `MVarId.byContra?` whenever
//! the target is not `False`, so every search runs against `⊢ False`. Clean's
//! grind had no step that changed the goal at all, and the decisive
//! measurement is a pair differing only in the goal: with `hpq : p → ¬q`,
//! `hp : p`, `hq : q` in context, grind CLOSED `⊢ False` and FAILED on `⊢ r`.
//!
//! `exfalso`, not `Classical.byContradiction`. A contradictory context ALREADY
//! closes an arbitrary goal when the contradiction is syntactic —
//! `contradiction` handles `¬q` beside `q` — so what is missing is a TARGET
//! for the backward searchers when REACHING the contradiction takes a modus
//! ponens. `False.elim` supplies exactly that and adds no classical axiom to
//! the closure of every grind proof, where `Classical.byContradiction` would
//! add `Classical.choice`.
//!
//! PARTIAL, and pinned as such: `∃`-introduction is not attempted, so
//! `Subtype.coe_eq_iff` and `exists_subtype_mk_eq_iff` stay open. The refusal
//! below fails loudly the day that changes.

use crate::elaborate_decl_and_register_with_warning;
use crate::tactic::builtins::builtin_tactic_patterns;
use clean_kernel::Environment;
use clean_parser::parse_file_with_tactics;

fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file_with_tactics(src, &builtin_tactic_patterns())
        .unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

/// The measured pair, both halves. `⊢ False` closed before this existed;
/// `⊢ r`, same context, did not. Reaching the contradiction needs one modus
/// ponens on `hpq`, which only a `False` target gives the backward searchers.
#[test]
fn test_grind_closes_an_arbitrary_goal_from_a_derivable_contradiction() {
    let mut env = Environment::with_prelude();
    let src = "theorem contraFalse (p q : Prop) (hpq : p → ¬q) (hp : p) (hq : q) : False := by\n\
               \x20 grind\n\
               theorem contraAny (p q r : Prop) (hpq : p → ¬q) (hp : p) (hq : q) : r := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("a derivable contradiction must close any goal: {e}");
    }
}

/// CONTROL. A SYNTACTIC contradiction already closed an arbitrary goal through
/// `contradiction`, which runs in the closer fan before any of this. The
/// `exfalso` step is placed after that fan so this route is unchanged.
#[test]
fn test_grind_still_closes_a_syntactic_contradiction_through_the_fan() {
    let mut env = Environment::with_prelude();
    let src = "theorem contraDirect (q r : Prop) (hnq : ¬q) (hq : q) : r := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("the closer fan must still reach a syntactic contradiction: {e}");
    }
}

/// An `Iff` whose halves are EQUATIONS. `tauto` is propositional and cannot
/// cross them, while each half closes on its own — the measured hand route is
/// `constructor <;> grind`.
#[test]
fn test_grind_splits_an_iff_goal_into_its_two_halves() {
    let mut env = Environment::with_prelude();
    let src = "theorem iffEq (a b : Nat) : a = b ↔ b = a := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("grind must split an Iff goal: {e}");
    }
}

/// CONTROL. A purely propositional `Iff` already closed through `tauto`, which
/// runs in the closer fan before the split.
#[test]
fn test_grind_still_closes_a_propositional_iff_through_tauto() {
    let mut env = Environment::with_prelude();
    let src = "theorem iffProp (p q : Prop) : (p ∧ q) ↔ (q ∧ p) := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("tauto must still reach a propositional Iff: {e}");
    }
}

/// REFUSAL PIN — the part of this root cause that is NOT implemented.
/// `∃`-introduction needs a witness, which is search rather than a goal
/// transformation, so grind still leaves an existential goal open.
/// `Subtype.coe_eq_iff` and `exists_subtype_mk_eq_iff` are blocked on exactly
/// this. If a later increment closes it, this test fails and the entry that
/// calls the row open must be corrected with it.
#[test]
fn test_grind_does_not_introduce_an_existential_witness() {
    let mut env = Environment::with_prelude();
    let src = "theorem exGoal (p : Nat → Prop) (a : Nat) (h : p a) : ∃ n, p n := by\n\
               \x20 grind\n";
    let err = elab(&mut env, src)
        .expect("∃-introduction is not implemented; this refusal is the honest state");
    assert!(
        err.contains("grind"),
        "the refusal must come from grind, not from elaborating the fixture: {err}"
    );
}

/// SOUNDNESS CONTROL for the `exfalso` step. Its gate is "some hypothesis
/// concludes in `False` or a negation", which `hnq : ¬q` satisfies — but `q`
/// is not derivable here, so the sub-search over `⊢ False` must fail and the
/// goal must stay open. Pinned Lean v4.30.0-rc2 fails on the same file.
#[test]
fn test_grind_leaves_the_goal_open_when_the_contradiction_is_not_derivable() {
    let mut env = Environment::with_prelude();
    let src = "theorem noExfalso (p q r : Prop) (hp : p) (hnq : ¬q) : r := by\n\
               \x20 grind\n";
    let err = elab(&mut env, src).expect("an underivable contradiction must not close the goal");
    assert!(
        err.contains("grind"),
        "the refusal must come from grind: {err}"
    );
}

/// SOUNDNESS CONTROL for the `Iff.intro` split. Splitting an `Iff` gives the
/// searcher two halves; one of them is FALSE here, so the declaration must be
/// refused. Pinned Lean v4.30.0-rc2 refuses it too.
#[test]
fn test_grind_never_accepts_a_false_iff() {
    let mut env = Environment::with_prelude();
    let src = "theorem falseIff (a b : Nat) : a = b ↔ b = b := by\n\
               \x20 grind\n";
    let err = elab(&mut env, src).expect("a FALSE Iff must never be accepted");
    assert!(!err.is_empty(), "the refusal must carry a diagnostic");
}
