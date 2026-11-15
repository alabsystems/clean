// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A GLOBAL theorem whose statement is neither `=` nor `↔` is still a simp
//! lemma: Lean's `preprocess` (`SimpTheorems.lean:288-363`) turns `p` into
//! `p = True`, `¬p` into `p = False`, `a ≠ b` into `(a = b) = False`, and
//! splits `p ∧ q`. Clean collected only `=` and `↔` conclusions, so
//! `simp [cast_heq]`, `simp only [Decidable.em, …]` and
//! `simp only [exists_apply_eq_apply]` rewrote nothing (measured 2026-09-12 on
//! `Mathlib/Logic/Basic.lean` and `Mathlib/Logic/Function/Basic.lean`).
//!
//! Every fixture was ground-truthed on the pinned v4.30.0-rc2 `lean` binary
//! (2026-09-12): each declaration elaborates there as written.

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

const SETUP: &str = "axiom PP {α : Type} : α → Prop\n\
                     axiom QQ : Nat → Prop\n\
                     axiom ff : Nat → Nat\n";

fn elab_with_setup(src: &str) -> Option<String> {
    let mut env = Environment::with_prelude();
    if let Some(e) = elab(&mut env, SETUP) {
        panic!("fixture setup must elaborate: {e}");
    }
    elab(&mut env, src)
}

/// `p` becomes `p = True`, for an axiom, for a THEOREM, and for a
/// universe-polymorphic heterogeneous equality (`cast_heq`'s shape).
#[test]
fn test_simp_uses_a_global_plain_proposition_as_equal_to_true() {
    let src = "axiom lemM {α : Type} (x : α) : PP x\n\
               theorem tM (n : Nat) : PP n := by simp only [lemM]\n\
               theorem ex_app1 {α β : Type} (f : α → β) (a' : α) : ∃ a, f a = f a' := ⟨a', rfl⟩\n\
               theorem t_a {α β : Type} (f : α → β) (a' : α) : (∃ a, f a = f a') ↔ True := by\n\
               \x20 simp only [ex_app1]\n\
               axiom my_cast_heq {α β : Sort u} (h : α = β) (a : α) : HEq (cast h a) a\n\
               theorem tH {α β : Sort w} (e : α = β) (b : α) : HEq (cast e b) b := by\n\
               \x20 simp only [my_cast_heq]\n";
    if let Some(e) = elab_with_setup(src) {
        panic!("a global plain proposition must rewrite to `True`: {e}");
    }
}

/// `¬p` becomes `p = False` and `a ≠ b` becomes `(a = b) = False`, at the
/// goal and at a hypothesis. (A hypothesis rewritten to exactly `False` would
/// also close the goal in Lean — `applySimpResultToLocalDecl` — which is a
/// separate `simp … at h` rule, so the hypothesis fixtures wrap the rewritten
/// proposition in an opaque `PP`.)
#[test]
fn test_simp_uses_a_global_negation_and_disequality_as_equal_to_false() {
    let src = "axiom lemN (n : Nat) : ¬ QQ n\n\
               theorem tN (n : Nat) (p : Prop) (h : p) : QQ n ∨ p := by\n\
               \x20 simp only [lemN]; exact Or.inr h\n\
               theorem tN2 (n : Nat) (h : PP (QQ n)) : PP False := by\n\
               \x20 simp only [lemN] at h; exact h\n\
               axiom lemNe (n : Nat) : ff n ≠ n\n\
               theorem tNe (n : Nat) (h : PP (ff n = n)) : PP False := by\n\
               \x20 simp only [lemNe] at h; exact h\n\
               theorem tNe2 (n : Nat) (p : Prop) (h : p) : ff n = n ∨ p := by\n\
               \x20 simp only [lemNe]; exact Or.inr h\n";
    if let Some(e) = elab_with_setup(src) {
        panic!("a global negation or disequality must rewrite to `False`: {e}");
    }
}

/// `p ∧ q` gives the rules of both halves.
#[test]
fn test_simp_splits_a_global_conjunction_into_both_halves() {
    let src = "axiom lemA (n : Nat) : QQ (ff n) ∧ PP n\n\
               theorem tA1 (n : Nat) : PP n := by simp only [lemA]\n\
               theorem tA2 (n : Nat) : QQ (ff n) := by simp only [lemA]\n";
    if let Some(e) = elab_with_setup(src) {
        panic!("both halves of a global conjunction must rewrite to `True`: {e}");
    }
}
