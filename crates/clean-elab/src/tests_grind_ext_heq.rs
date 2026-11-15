// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `grind` has an extensionality step and an `Eq`/`HEq` bridge.
//!
//! Neither existed. `funext` was reached from exactly one place,
//! `try_funext_propext_bridge`, gated by `pi_arity_into_prop` on a `Prop`
//! codomain because its terminator is `propext` — so `⊢ f = f'` at
//! `∀ a, β a` (`Function.hfunext`, `Subtype.surjective_restrict`) was left
//! untouched and the closer fan reported "no progress" on the unmodified
//! goal. And `HEq` appeared nowhere in `grind.rs` or `cc.rs`, so
//! `h : HEq a b ⊢ a = b` failed with the proof one `eq_of_heq` away.
//!
//! PLACEMENT is the safety argument and is pinned by its own controls: both
//! steps run AFTER the closer fan, never in preprocessing. A function
//! equality `rfl` or `assumption` already closes must keep closing that way —
//! an unconditional preprocessing `funext` would replace those goals with
//! pointwise ones that `assumption` no longer matches.
//!
//! SCOPE, stated because two recorded rows sit outside it:
//! `Subtype.heq_iff_coe_heq` is `HEq` at two DIFFERENT types and is declined
//! rather than coerced, and `Function.LeftInverse.cast_eq` needs `cast`/`Eq.rec`
//! congruence, strictly more than `eq_of_heq`.

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

/// A function equality at a NON-`Prop` codomain — the shape the old `Prop`-only
/// gate skipped.
#[test]
fn test_grind_closes_a_function_equality_at_a_non_prop_codomain() {
    let mut env = Environment::with_prelude();
    let src = "theorem extFn (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("grind must apply funext at any codomain: {e}");
    }
}

/// The dependent codomain `Function.hfunext` has, with the `HEq` wall behind
/// it: extensionality gets to `f x = g x` and `eq_of_heq` crosses to the
/// `HEq` fact the context holds.
#[test]
fn test_grind_crosses_heq_under_extensionality() {
    let mut env = Environment::with_prelude();
    let src = "universe u v\n\
               theorem hfunextShape {α : Type u} {β : α → Type v} (f g : ∀ a, β a)\n\
               \x20   (h : ∀ a, HEq (f a) (g a)) : f = g := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("grind must reach the HEq fact through funext: {e}");
    }
}

/// `h : HEq a b ⊢ a = b` — the bridge on its own, no extensionality involved.
#[test]
fn test_grind_closes_an_equality_from_a_homogeneous_heq_hypothesis() {
    let mut env = Environment::with_prelude();
    let src = "universe u\n\
               theorem heqToEq {α : Type u} (a b : α) (h : HEq a b) : a = b := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("grind must cross HEq → Eq at one type: {e}");
    }
}

/// The other direction: `⊢ HEq a b` at one type from `a = b`.
#[test]
fn test_grind_closes_a_homogeneous_heq_goal_from_an_equality() {
    let mut env = Environment::with_prelude();
    let src = "universe u\n\
               theorem eqToHeq {α : Type u} (a b : α) (h : a = b) : HEq a b := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("grind must cross Eq → HEq at one type: {e}");
    }
}

/// CONTROL. A function equality the closer fan already handles must keep
/// closing through the fan — this is why both new steps sit after it. An
/// extensionality step run in preprocessing would replace these goals with
/// pointwise ones `assumption` no longer matches.
#[test]
fn test_grind_still_closes_function_equalities_through_the_closer_fan() {
    let mut env = Environment::with_prelude();
    let src = "theorem fnAssumption (f g : Nat → Nat) (h : f = g) : f = g := by\n\
               \x20 grind\n\
               theorem fnRfl (f : Nat → Nat) : f = f := by\n\
               \x20 grind\n\
               theorem fnPropAssumption (f g : Nat → Prop) (h : f = g) : f = g := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("the closer fan must still reach a function equality first: {e}");
    }
}

/// The SOUNDNESS half, pinned without a proof state: an `HEq` goal whose two
/// type arguments differ is DECLINED. `heq_of_eq` cannot build it, and
/// answering it would be the one way this bridge could be wrong.
/// `Subtype.heq_iff_coe_heq` is exactly that shape and stays open.
#[test]
fn test_heq_bridge_declines_a_heterogeneous_goal() {
    use clean_kernel::level::Level;
    use clean_kernel::{Expr, Name};

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let ty_b = Expr::const_(Name::from_string("B"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let heq = |l: Expr, x: Expr, r: Expr, y: Expr| {
        Expr::apps(
            Expr::const_(
                Name::from_string("HEq"),
                vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
            ),
            [l, x, r, y],
        )
    };

    assert_eq!(
        crate::tactic::grind_bridges::heq_bridge_for(
            &heq(ty_a.clone(), a.clone(), ty_a.clone(), b.clone()),
            false
        ),
        Some("heq_of_eq"),
        "one type: the bridge is available"
    );
    assert_eq!(
        crate::tactic::grind_bridges::heq_bridge_for(
            &heq(ty_a.clone(), a.clone(), ty_b, b.clone()),
            false
        ),
        None,
        "two different types: never coerced"
    );

    // The `Eq` direction is gated on the context actually holding an `HEq`,
    // so a failing equality goal in an HEq-free context pays nothing.
    let eq_goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [ty_a, a, b],
    );
    assert_eq!(
        crate::tactic::grind_bridges::heq_bridge_for(&eq_goal, false),
        None,
        "no HEq in context: not attempted"
    );
    assert_eq!(
        crate::tactic::grind_bridges::heq_bridge_for(&eq_goal, true),
        Some("eq_of_heq"),
        "an HEq in context: worth the bridge"
    );
}

/// REGRESSION. The `Eq`/`HEq` bridge must fire INSIDE a case-split branch.
///
/// Its success test was `state.is_complete()`, which is `goals.is_empty()` —
/// and every branch of a split runs `grind_core` with its sibling branch still
/// on the goal list, so the bridge rolled itself back everywhere except a
/// single-goal top level. That is exactly where the rows it exists for do NOT
/// sit. Measured face before the fix: `h : HEq #F2 #F3 #F4`, `h_grind.0 : #F0`,
/// `⊢ Eq #F2 #F3 #F4` — the bridge's own shape, reported as no progress.
///
/// Pinned Lean v4.30.0-rc2 closes this.
#[test]
fn test_grind_crosses_heq_inside_a_case_split_branch() {
    let mut env = Environment::with_prelude();
    let src = "theorem heqInBranch (P : Prop) [Decidable P] {α : Type} (x y : α) (h : HEq x y) :\n\
               \x20   (if P then x else y) = y := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("the HEq bridge must work inside a split branch: {e}");
    }
}

/// Extensionality runs once per LEADING binder, not once. `pi_arity` counts
/// the whole chain, so a two-argument function equality is taken to its
/// pointwise form in one step and cannot re-enter.
#[test]
fn test_grind_applies_extensionality_at_every_leading_binder() {
    let mut env = Environment::with_prelude();
    let src = "theorem ext2b (f g : Nat → Nat → Nat) (h : ∀ x y, f x y = g x y) : f = g := by\n\
               \x20 grind\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("grind must funext both binders: {e}");
    }
}
