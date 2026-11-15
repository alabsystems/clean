// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `simp [h]` collapses a `dite` whose condition it rewrites to `True`/`False`
//! through `dif_pos`/`dif_neg` (the dependent twin of the `ite` collapse).
//! Measured 2026-09-11 on `Mathlib/Logic/Basic.lean` (`apply_dite₂`,
//! `dite_apply`, `dite_mem`, `mem_dite`): `by_cases h : P <;> simp [h]`
//! rewrote the condition of `dite P inst f g` and left `inst : Decidable P`
//! beside `dite True …` — `expected Decidable True, got Decidable P`.
//!
//! `dif_pos`/`dif_neg` live in `Init.Core`, not the built-in prelude, so the
//! fixture registers them as IMPORTED constants with Lean's exact signatures
//! (`crate::tests_support_imported_core`); the collapse only asks the
//! environment for constants of those names. A source file may not declare
//! them: both are Lean 4.8.0 core names (Lean: "already declared";
//! `crate::lean_core_names`), and the prelude does not supply them because
//! Clean's collapse also fires under `simp only [h]`, where Lean 4.8.0 leaves
//! the `dite` (see `clean_kernel`'s `lean_core_supply`).

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
fn test_simp_collapses_a_dite_whose_condition_rewrites_to_true_or_false() {
    let mut env = Environment::with_prelude();
    crate::tests_support_imported_core::import_core_constants(
        &mut env,
        crate::tests_support_imported_core::DIF_POS_NEG,
    );
    let src = String::from(
        "theorem diteTrue (P : Prop) [Decidable P] (a : P → Nat) (b : ¬P → Nat) (h : P) :\n\
         \x20   dite P a b = a h := by\n\
         \x20 simp [h]\n\
         theorem diteFalse (P : Prop) [Decidable P] (a : P → Nat) (b : ¬P → Nat) (h : ¬P) :\n\
         \x20   dite P a b = b h := by\n\
         \x20 simp [h]\n\
         theorem diteApply {α : Sort u} {σ : α → Sort v} {P : Prop} [Decidable P]\n\
         \x20   (f : P → ∀ a, σ a) (g : ¬P → ∀ a, σ a) (a : α) :\n\
         \x20   (dite P f g) a = dite P (fun h ↦ f h a) fun h ↦ g h a := by\n\
         \x20 by_cases h : P <;> simp [h]\n",
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("`simp [h]` must collapse the `dite` through `dif_pos`/`dif_neg`: {e}");
    }
}

#[test]
fn test_dite_is_left_alone_without_the_collapse_lemmas() {
    let mut env = Environment::with_prelude();
    // No `dif_pos` in scope: the term is untouched, so this proof cannot
    // close by simp alone — it must fail, never fabricate.
    let src =
        "theorem diteTrueNoLemma (P : Prop) [Decidable P] (a : P → Nat) (b : ¬P → Nat) (h : P) :\n\
               \x20   dite P a b = a h := by\n\
               \x20 simp only [h]\n";
    assert!(
        elab(&mut env, src).is_some(),
        "without `dif_pos` the dite must not collapse"
    );
}
