// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A hypothesis that `simp … at h` simplifies to `False` closes the goal —
//! Lean's `applySimpResult` (`Lean/Meta/Tactic/Simp/Main.lean`) assigns
//! `False.elim (Eq.mp eqProof h)` and visits no later location. Clean replaced
//! the hypothesis and handed `h : False ⊢ 1 = 2` back as an unsolved goal
//! (measured 2026-09-20). It is what a global `¬p` lemma — turned into
//! `p = False` by Lean's `preprocess` — leads to at a hypothesis.
//!
//! Every fixture was ground-truthed on the pinned v4.30.0-rc2 `lean` binary
//! (2026-09-20): each accepted declaration elaborates there as written, and
//! `n1` fails there with "No goals to be solved".

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

const SETUP: &str = "axiom QQ : Nat → Prop\n\
                     axiom PP : Prop → Prop\n\
                     axiom lemN (n : Nat) : ¬ QQ n\n";

fn env_with_setup() -> Environment {
    let mut env = Environment::with_prelude();
    if let Some(e) = elab(&mut env, SETUP) {
        panic!("fixture setup must elaborate: {e}");
    }
    env
}

/// The goal is closed whatever its sort (`f2`'s target is `Nat`, so the
/// `False.elim` is taken at `Sort 1`), a later hypothesis location is not
/// visited (`f3`), and neither is a trailing `⊢` (`f4`).
#[test]
fn test_simp_at_hypothesis_simplified_to_false_closes_the_goal() {
    let mut env = env_with_setup();
    let src = "theorem f1 (n : Nat) (h : QQ n) : 1 = 2 := by simp only [lemN] at h\n\
               def f2 (n : Nat) (h : QQ n) : Nat := by simp only [lemN] at h\n\
               theorem f3 (n m : Nat) (h₁ : QQ n) (h₂ : QQ m) : False := by\n\
               \x20 simp only [lemN] at h₁ h₂\n\
               theorem f4 (n : Nat) (h : QQ n) : PP (QQ n) := by simp only [lemN] at h ⊢\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`simp at h` with `h` simplified to `False` must close the goal: {e}");
    }
}

/// Only the goal the hypothesis belongs to is closed: the sibling goal is
/// still there for the next bullet, untouched.
#[test]
fn test_simp_at_false_hypothesis_leaves_sibling_goals_untouched() {
    let mut env = env_with_setup();
    let src = "theorem f5 (n : Nat) (h : QQ n) (k : PP True) : False ∧ PP True := by\n\
               \x20 constructor\n\
               \x20 · simp only [lemN] at h\n\
               \x20 · exact k\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("closing one goal from `h : False` must leave its sibling open: {e}");
    }
}

/// A hypothesis that does not become `False` itself is replaced as before and
/// the goal stays open.
#[test]
fn test_simp_at_hypothesis_mentioning_false_keeps_the_goal_open() {
    let mut env = env_with_setup();
    let src = "theorem f7 (n : Nat) (h : PP (QQ n)) : PP False := by\n\
               \x20 simp only [lemN] at h; exact h\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`PP False` is not `False`: the goal must stay open for `exact h`: {e}");
    }
}

/// The closure is real, not a swallowed goal: a tactic after it has nothing
/// to run on, as in Lean ("No goals to be solved").
#[test]
fn test_simp_at_false_hypothesis_leaves_no_goal_for_a_later_tactic() {
    let mut env = env_with_setup();
    let err = elab(
        &mut env,
        "theorem n1 (n : Nat) (h : QQ n) : 1 = 2 := by\n\
         \x20 simp only [lemN] at h\n\
         \x20 rfl\n",
    )
    .expect("Lean reports no goals for the `rfl` after the closing `simp at h`");
    assert!(
        err.contains("NoGoals"),
        "the `rfl` must find no goal left, not a goal it cannot prove: {err}"
    );
}

/// The same through the `@[simp]` registry, for `simp at h`, `simp_all` and
/// `simp at *`, a list of locations ending in `⊢`, and a sibling goal.
#[test]
fn test_simp_registry_negation_closes_the_goal_at_every_location_form() {
    let mut env = Environment::with_prelude();
    let src = "axiom QQ : Nat → Prop\n\
               axiom PP : Prop → Prop\n\
               @[simp] axiom lemN (n : Nat) : ¬ QQ n\n\
               theorem g1 (n : Nat) (h : QQ n) : 1 = 2 := by simp_all\n\
               theorem g2 (n : Nat) (h : QQ n) (k : PP (QQ n)) : 1 = 2 := by simp at *\n\
               theorem g3 (n : Nat) (h : QQ n) : 1 = 2 := by simp at h\n\
               theorem g4 (n m : Nat) (h₁ : PP (QQ n)) (h₂ : QQ m) : PP (QQ m) := by\n\
               \x20 simp at h₁ h₂ ⊢\n\
               theorem g5 (n : Nat) (h : QQ n) (k : PP True) : (1 = 2) ∧ PP True := by\n\
               \x20 constructor\n\
               \x20 · simp at h\n\
               \x20 · exact k\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("a registry `¬p` lemma must close the goal from `h : p`: {e}");
    }
}
