// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The rest of Lean's grammar for `by_cases`, `suffices` and `replace`:
//! the anonymous `by_cases p` (`Init/ByCases.lean:20-23`), the anonymous
//! `suffices p by …` binding `this` (`Init/Tactics.lean:871-873`), and
//! `replace` (`Lean/Elab/Tactic/BuiltinTactic.lean:631-642`).
//!
//! Ground-truthed on the pinned v4.30.0-rc2 `lean` binary (2026-09-12): the
//! accepted fixtures elaborate there as written. `rp_gone` is refused there
//! ("Tactic `assumption` failed", context `h1 h : a = 1` — the old `h` is
//! gone) and `bc_hidden` is refused ("Unknown identifier `h`" — the
//! anonymous `by_cases` hypothesis is hygienic).

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

fn accepts(src: &str, what: &str) {
    let mut env = Environment::with_prelude();
    if let Some(e) = elab(&mut env, src) {
        panic!("{what}: {e}");
    }
}

fn refuses(src: &str, what: &str) {
    let mut env = Environment::with_prelude();
    assert!(elab(&mut env, src).is_some(), "{what}");
}

/// `by_cases P <;> simp [*, …]` (Mathlib `Logic/Basic.lean:824`).
#[test]
fn test_by_cases_anonymous_proposition() {
    accepts(
        "theorem bc_anon (P : Prop) [Decidable P] (q : Prop) (hq : q) : q := by\n\
         \x20 by_cases P <;> exact hq\n\
         theorem bc_anon_uses (P : Prop) [Decidable P] : P ∨ ¬P := by\n\
         \x20 by_cases P\n\
         \x20 · exact Or.inl ‹P›\n\
         \x20 · exact Or.inr ‹¬P›\n\
         theorem bc_named (P : Prop) [Decidable P] (q : Prop) (hq : q) : q := by\n\
         \x20 by_cases h : P <;> exact hq\n",
        "`by_cases P` splits on `P` with a hygienic hypothesis",
    );
}

#[test]
fn test_by_cases_anonymous_hypothesis_is_not_nameable() {
    refuses(
        "theorem bc_hidden (P : Prop) [Decidable P] : P ∨ ¬P := by\n\
         \x20 by_cases P\n\
         \x20 · exact Or.inl h\n\
         \x20 · exact Or.inr h\n",
        "the hypothesis of an anonymous `by_cases` must not be reachable as `h`",
    );
}

/// `suffices cast hU (g s).2 = … by …` (Mathlib `Logic/Function/Basic.lean:
/// 277`): the first identifier is part of the proposition, and the
/// hypothesis is `this`.
#[test]
fn test_suffices_anonymous_proposition_binds_this() {
    accepts(
        "theorem sf_anon (f : Nat → Nat) (a : Nat) (h : f a = 1) : f a = 1 := by\n\
         \x20 suffices f a = 1 by exact this\n\
         \x20 exact h\n\
         theorem sf_app (f : Nat → Nat → Nat) (a : Nat) (h : f a a = 1) : f a a = 1 := by\n\
         \x20 suffices f a a = 1 by exact this\n\
         \x20 exact h\n\
         theorem sf_named (f : Nat → Nat) (a : Nat) (h : f a = 1) : f a = 1 := by\n\
         \x20 suffices h' : f a = 1 by exact h'\n\
         \x20 exact h\n",
        "`suffices P by …` must parse `P` whole and bind `this`",
    );
}

/// `replace h := @h … ?_` (Mathlib `Logic/Function/Basic.lean:681`).
#[test]
fn test_replace_supersedes_the_hypothesis() {
    accepts(
        "theorem rp (a : Nat) (h : a = 1 → a = 1) (h1 : a = 1) : a = 1 := by\n\
         \x20 replace h := h h1\n\
         \x20 exact h\n\
         theorem rp_typed (a : Nat) (h : a = 1 → a = 1) (h1 : a = 1) : a = 1 := by\n\
         \x20 replace h : a = 1 := h h1\n\
         \x20 exact h\n",
        "`replace h := e` must rebind `h`",
    );
}

/// Lean's `tryClear`: the superseded hypothesis is gone afterwards.
#[test]
fn test_replace_clears_the_old_hypothesis() {
    refuses(
        "theorem rp_gone (a : Nat) (h : a = 1 → a = 1) (h1 : a = 1) : a = 1 → a = 1 := by\n\
         \x20 replace h := h h1\n\
         \x20 assumption\n",
        "the old `h : a = 1 → a = 1` must be cleared by `replace`",
    );
}

/// ... and kept when something depends on it (`tryClear` gives up quietly).
#[test]
fn test_replace_keeps_a_hypothesis_something_depends_on() {
    accepts(
        "theorem rp_keep (p : Prop) (h : p) (hh : h = h) : p := by\n\
         \x20 replace h : p := h\n\
         \x20 exact h\n",
        "`replace` must not fail when the old hypothesis has dependents",
    );
}
