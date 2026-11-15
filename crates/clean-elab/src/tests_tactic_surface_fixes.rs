// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Three tactic-surface fixes from the verified diagnosis workflow
//! (2026-09-12), each fixture taken from its replica file and accepted as a
//! whole by the pinned v4.30.0-rc2 binary:
//! - `rcases` on a term that is not a local generalizes it (Lean's
//!   `generalizeExceptFVar`), as `obtain` already did;
//! - `simpa [l]` uses its lemma list without `only`, and its `using` term's
//!   leading implicits become metavariables solved by the closing `exact`;
//! - a name-shaped `rw` rule resolves through `export` aliases, and one that
//!   names no local or global (generalized field notation on a local) is
//!   elaborated as a term, whose `∀`-telescope is instantiated.

use crate::elaborate_decl_and_register_with_warning;
use crate::FileContext;
use crate::{elaborate_decl_and_register_with_context, preprocess_decl_with_context};
use clean_kernel::Environment;
use clean_parser::parse_file;

/// Elaborate with a file context, so `export`/`namespace` state persists
/// across declarations as it does under `clean check`.
fn elab_in_file(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    let mut file_ctx = FileContext::new();
    for d in &decls {
        let processed = preprocess_decl_with_context(d, &mut file_ctx);
        if let Err(e) = elaborate_decl_and_register_with_context(env, &processed, &mut file_ctx) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

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
fn test_rcases_generalizes_a_scrutinee_that_is_not_a_local() {
    let mut env = Environment::with_prelude();
    let src = "theorem v1 (p : Prop) : p ∨ ¬p := by
  rcases Classical.em p with hx | hx
  · exact Or.inl hx
  · exact Or.inr hx
theorem v2 (p : Prop) : p ∨ ¬p := by
  obtain hx | hx := Classical.em p
  · exact Or.inl hx
  · exact Or.inr hx
theorem v3 (p : Prop) : p ∨ ¬p := by
  rcases (Classical.em p) with (hx | hx)
  · exact Or.inl hx
  · exact Or.inr hx
theorem v4 (p : Prop) (h : p ∨ ¬p) : p ∨ ¬p := by
  rcases h with (hx | hx)
  · exact Or.inl hx
  · exact Or.inr hx
theorem v5 (p : Prop) : p ∨ ¬p := by
  cases Classical.em p with
  | inl hx => exact Or.inl hx
  | inr hx => exact Or.inr hx
";
    if let Some(e) = elab(&mut env, src) {
        panic!("rcases on `Classical.em p` must destructure the generalized term: {e}");
    }
}

#[test]
fn test_simpa_uses_its_lemmas_without_only_and_opens_the_using_term() {
    let mut env = Environment::with_prelude();
    let src = "variable {α β : Sort u}

theorem s_nonly {f : α → β} {p : β → Prop} (x : α) (y : β) (hpy : p y) (hx : f x = y) :
    p (f x) := by
  simpa [hx]

theorem s_nonly_using {f : α → β} {p : β → Prop} (x : α) (y : β) (hpy : p y) (hx : f x = y) :
    p (f x) := by
  simpa [hx] using hpy

theorem s_only_using {f : α → β} {p : β → Prop} (x : α) (y : β) (hpy : p y) (hx : f x = y) :
    p (f x) := by
  simpa only [hx] using hpy

axiom myle {γ : Type} [LT γ] [LE γ] {a b : γ} : a < b → a ≤ b

theorem s_using_implicit {γ : Type} [LT γ] [LE γ] (a b : γ) : a < b → a ≤ b := by
  simpa using myle

theorem s_exact_implicit {γ : Type} [LT γ] [LE γ] (a b : γ) : a < b → a ≤ b := by
  exact myle
";
    if let Some(e) = elab(&mut env, src) {
        panic!("simpa must honour [lemmas] and instantiate the using term's implicits: {e}");
    }
}

#[test]
fn test_rw_name_rules_resolve_aliases_and_fall_back_to_the_term_path() {
    let mut env = Environment::with_prelude();
    let src = "namespace Foo
theorem bar_iff {p : Prop} : (p ∧ p) ↔ p := ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
end Foo

export Foo (bar_iff)

theorem alias_term (q : Prop) (h : q) : q ∧ q := bar_iff.2 h

theorem alias_rw (q : Prop) (h : q) : q ∧ q := by
  rw [bar_iff]; exact h

def MyInv (g f : Nat → Nat) : Prop := ∀ x, g (f x) = x
theorem MyInv.comp_eq {g f : Nat → Nat} (h : MyInv g f) (x : Nat) : g (f x) = x := h x

theorem dot_term (g f : Nat → Nat) (h : MyInv g f) : g (f 3) = 3 := h.comp_eq 3

theorem dot_rw (g f : Nat → Nat) (h : MyInv g f) : g (f 3) = 3 := by
  rw [h.comp_eq]
theorem dot_rw_paren (g f : Nat → Nat) (h : MyInv g f) : g (f 3) = 3 := by
  rw [(h.comp_eq)]

theorem dot_rw_app (g f : Nat → Nat) (h : MyInv g f) : g (f 3) = 3 := by
  rw [h.comp_eq 3]

theorem term_forall_rule (g f : Nat → Nat) (h : MyInv g f) : g (f 3) = 3 := by
  rw [MyInv.comp_eq h]
";
    if let Some(e) = elab_in_file(&mut env, src) {
        panic!("rw rules must resolve aliases, dot notation on locals and ∀-typed terms: {e}");
    }
}
