// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `subst`/`cases` on `h : x = e` is Lean's `substCore`: the motive abstracts
//! the equation too when the goal mentions it (`cast h a`, `Eq.mp h`), and
//! every local whose type depends on the eliminated variable is reverted and
//! re-introduced with the substituted type. Measured 2026-09-11 on
//! `Mathlib/Logic/Basic.lean` (`cast_heq_iff_heq`, `heq_cast_iff_heq`),
//! `Mathlib/Logic/Function/Basic.lean` (`eq_mp_bijective`, `cast_bijective`,
//! `hfunext`) and `Mathlib/Logic/Unique.lean` (`Unique.subtypeEq'`): the old
//! non-dependent motive left `h : α = β` under `cast` at `α = α`.

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::Environment;
use clean_parser::parse_file;

fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

#[test]
fn test_subst_on_a_type_equation_mentioned_by_the_goal() {
    let mut env = Environment::with_prelude();
    let src = "theorem castHeq {α β γ : Sort _} (e : α = β) (a : α) (c : γ) :\n\
               \x20   HEq (cast e a) c ↔ HEq a c := by subst e; exact Iff.rfl\n\
               theorem heqCast {α β γ : Sort _} (e : β = γ) (a : α) (b : β) :\n\
               \x20   HEq a (cast e b) ↔ HEq a b := by subst e; exact Iff.rfl\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("subst must abstract the equation out of `cast e a`: {e}");
    }
}

#[test]
fn test_cases_on_a_type_equation_routes_through_the_dependent_motive() {
    let mut env = Environment::with_prelude();
    let src = "def Bij {α β : Sort _} (f : α → β) : Prop :=\n\
               \x20 (∀ a b, f a = f b → a = b) ∧ (∀ b, ∃ a, f a = b)\n\
               theorem eqMpBij {α β : Sort _} (h : α = β) : Bij (Eq.mp h) := by\n\
               \x20 cases h\n\
               \x20 exact ⟨fun _ _ => id, fun x => ⟨x, rfl⟩⟩\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`cases h` on `h : α = β` under `Eq.mp h` must kernel-check: {e}");
    }
}

#[test]
fn test_subst_reverts_and_reintroduces_dependent_hypotheses() {
    let mut env = Environment::with_prelude();
    // Both sides carry dependents (`p` on `x`, `q` on `y`): Lean eliminates
    // the right side, so `q` comes back as `q : x = 3` and closes the goal.
    let src = "theorem depBoth (x y : Nat) (h : x = y) (p : x = 3) (q : y = 3) : x = 3 := by\n\
               \x20 subst h\n\
               \x20 exact q\n\
               theorem depTypes {α β : Sort u} (h : α = β) (a : α) (b : β) (k : HEq a b) :\n\
               \x20   HEq b a := by\n\
               \x20 subst h\n\
               \x20 exact HEq.symm k\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("dependent hypotheses must be re-introduced with substituted types: {e}");
    }
}

#[test]
fn test_subst_reintroduces_tactic_introduced_dependents_at_the_right_depth() {
    let mut env = Environment::with_prelude();
    // Every local is a tactic binder here, so the re-introduced `q` must
    // land at the depth of the goal being closed (not at the narrowed
    // goal's `max + 1`), or the closed term captures the OUTER `q`.
    let src = "theorem depIntro : ∀ (x y : Nat) (h : x = y) (p : x = 3) (q : y = 3), x = 3 := by\n\
               \x20 intro x y h p q\n\
               \x20 subst h\n\
               \x20 exact q\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("tactic-introduced dependents must be re-bound at the goal's depth: {e}");
    }
}

#[test]
fn test_subst_with_the_variable_on_the_left_and_a_goal_mentioning_the_equation() {
    let mut env = Environment::with_prelude();
    // `Nat` is not a variable, so the LEFT side is eliminated (Lean's
    // `symm := false`) with the `Eq.symm hAux` motive trick.
    let src = "theorem leftVar {α : Type} (h : α = Nat) (a : α) : HEq (cast h a) a := by\n\
               \x20 subst h\n\
               \x20 exact HEq.rfl\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("left-side elimination under a dependent goal must kernel-check: {e}");
    }
}

#[test]
fn test_subst_reverts_a_have_bound_dependent_as_a_plain_hypothesis() {
    let mut env = Environment::with_prelude();
    // The first `this` (a tactic `have`, recorded with a value) mentions `y`
    // through `q`; `subst h` must revert it as an opaque hypothesis.
    let src = "theorem haveDep (x y : Nat) (h : x = y) (q : y = 3) : x = 3 := by\n\
               \x20 have this : y = 3 := q\n\
               \x20 subst h\n\
               \x20 exact this\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("a have-bound dependent must be reverted and re-introduced: {e}");
    }
}

#[test]
fn test_subst_refuses_a_variable_occurring_in_the_other_side() {
    let mut env = Environment::with_prelude();
    let src = "theorem occ (n : Nat) (h : n = n + 1) : False := by\n\
               \x20 subst h\n\
               \x20 trivial\n";
    let err = elab(&mut env, src).expect("`subst` on `n = n + 1` must be refused");
    assert!(
        err.contains("occurs"),
        "the refusal must name the occurrence, got: {err}"
    );
}
