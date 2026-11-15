// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `simp only [H]` with a NON-equational local `H : P` rewrites `P` to `True`
//! (`H : ¬P` rewrites `P` to `False`, `H : a ↔ b` rewrites `a` to `b`), as
//! Lean's `mkSimpTheorems` does with `eq_true`/`eq_false`/`propext`; and
//! `simpa only [...]` parses its `only` in every position, including after a
//! bullet or `<;>`. Measured 2026-09-11 (`Prop.exists_iff`, `Prop.forall_iff`
//! in `Mathlib/Logic/Basic.lean`): the hypothesis was silently skipped as
//! "not an equality", and `· simpa only [H] using hp` died on an
//! "unknown tactic `only`".

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
fn test_simp_only_uses_a_prop_hypothesis_as_an_equality_with_true() {
    let mut env = Environment::with_prelude();
    let src = "theorem viaSimpa (p : Prop → Prop) (h₁ : Prop) (H : h₁) (h₂ : p h₁) : p True := by\n\
               \x20 simpa only [H] using h₂\n\
               theorem viaSimpAt (p : Prop → Prop) (h₁ : Prop) (H : h₁) (h₂ : p h₁) : p True := by\n\
               \x20 simp only [H] at h₂\n\
               \x20 exact h₂\n\
               theorem viaNot (p : Prop → Prop) (h₁ : Prop) (H : ¬h₁) (h₂ : p h₁) : p False := by\n\
               \x20 simpa only [H] using h₂\n\
               theorem viaIff (p : Prop → Prop) (a b : Prop) (H : a ↔ b) (h₂ : p a) : p b := by\n\
               \x20 simpa only [H] using h₂\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("a Prop-valued hypothesis must rewrite as `P = True` / `P = False` / `a = b`: {e}");
    }
}

#[test]
fn test_simpa_only_parses_after_a_bullet_and_after_seq_focus() {
    let mut env = Environment::with_prelude();
    let src = "theorem bullets (p : Prop → Prop) (h : Prop) (hp : p h) : p h := by\n\
               \x20 by_cases H : h\n\
               \x20 · simpa only [H] using hp\n\
               \x20 · simpa only [H] using hp\n\
               theorem focused (p : Prop → Prop) (h : Prop) (hp : p h) : p h := by\n\
               \x20 by_cases H : h <;> simpa only [H] using hp\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`simpa only` must parse in every tactic position: {e}");
    }
}

#[test]
fn test_anonymous_constructor_field_is_rewritten_by_simpa_over_an_exists() {
    let mut env = Environment::with_prelude();
    // `h₂` is bound at the head-beta-reduced `p h₁` (see
    // `tests_pattern_field_head_beta`), which `simpa only [H]` can rewrite.
    let src = "theorem propExists {p : Prop → Prop} : (∃ h, p h) → p False ∨ p True :=\n\
               \x20 fun ⟨h₁, h₂⟩ => by\n\
               \x20   by_cases H : h₁\n\
               \x20   · exact .inr (by simpa only [H] using h₂)\n\
               \x20   · exact .inl (by simpa only [H] using h₂)\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`fun ⟨h₁, h₂⟩ => … simpa only [H] using h₂` must elaborate: {e}");
    }
}
