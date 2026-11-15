// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The simp-lemma construction rules COMPOSED, in the shapes of the Mathlib
//! rows the work package measured — each rule has its own pin
//! (`tests_simp_lemma_levels`, `tests_simp_prop_lemmas`,
//! `tests_simp_instance_args`, `tests_rintro_rfl`); a row needs several at
//! once:
//!
//! * `Decidable.and_forall_ne` uses `Decidable.em : (p : Prop) → [Decidable p]
//!   → p ∨ ¬p` — a plain proposition (`p = True`) whose instance binder the
//!   left-hand side does not determine (typeclass synthesis, here from a local
//!   `DecidableEq` and from `Nat`'s global instance);
//! * `heq_of_eq_cast` is `rintro rfl; simp` with `cast_heq` — a top-level
//!   `rfl` pattern, then a universe-polymorphic `HEq` statement as a rule;
//! * `Decidable.iff_congr_left` is the `@[simp]` lemma the package's verifier
//!   measured aborting a declaration ("Unbound variable index") once `↔`
//!   templates instantiate their levels: three `Decidable` binders no side
//!   mentions.
//!
//! Every fixture was ground-truthed on the pinned v4.30.0-rc2 `lean` binary
//! (2026-09-20): each accepted declaration elaborates there as written, and
//! each refused one fails there with "`simp` made no progress". The goals are
//! stated as `PPr … ↔ PPr …` so that the rewrite alone closes them in both
//! systems.

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

const SETUP: &str = "axiom PPr : Prop → Prop\n\
    axiom my_em (p : Prop) [Decidable p] : p ∨ ¬p\n\
    axiom my_cast_heq {α β : Sort u} (h : α = β) (a : α) : HEq (cast h a) a\n\
    axiom my_iff_congr_left {P Q R : Prop} [Decidable P] [Decidable Q] [Decidable R] :\n\
    \x20   ((P ↔ R) ↔ (Q ↔ R)) ↔ (P ↔ Q)\n";

fn env_with_setup() -> Environment {
    let mut env = Environment::with_prelude();
    if let Some(e) = elab(&mut env, SETUP) {
        panic!("fixture setup must elaborate: {e}");
    }
    env
}

fn expect_no_progress(theorem: &str) {
    let mut env = env_with_setup();
    let err = elab(&mut env, theorem)
        .unwrap_or_else(|| panic!("Lean refuses this rewrite (no progress); so must Clean"));
    assert!(
        !err.contains("Unbound variable"),
        "the rewrite must be refused by simp, not by the kernel on a loose binder: {err}"
    );
    assert!(
        err.contains("NoProgress") || err.contains("no progress"),
        "the refusal must be simp's own 'no progress': {err}"
    );
}

/// `Decidable.em`'s shape: the rule is `(p ∨ ¬p) = True`, and its
/// `[Decidable p]` binder is synthesized in the goal's scope.
#[test]
fn test_simp_plain_proposition_lemma_synthesizes_its_instance_binder() {
    let mut env = env_with_setup();
    let src = "theorem r7 {α : Sort u} [DecidableEq α] (a b : α) :\n\
               \x20   PPr (b = a ∨ ¬ b = a) ↔ PPr True := by\n\
               \x20 simp only [my_em]\n\
               theorem r7n (a b : Nat) : PPr (b = a ∨ ¬ b = a) ↔ PPr True := by\n\
               \x20 simp only [my_em]\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`p ∨ ¬p` must rewrite to `True` with `Decidable p` synthesized: {e}");
    }
}

/// With no `Decidable p` to be found the rule does not fire — and the
/// declaration is refused by simp, never by the kernel.
#[test]
fn test_simp_plain_proposition_lemma_without_an_instance_makes_no_progress() {
    expect_no_progress(
        "theorem r7x (p : Prop) : PPr (p ∨ ¬ p) ↔ PPr True := by\n\x20 simp only [my_em]\n",
    );
}

/// `heq_of_eq_cast` as Mathlib writes it, with the simp set spelled out.
#[test]
fn test_rintro_rfl_then_simp_with_a_heq_lemma_closes_heq_of_eq_cast() {
    let mut env = env_with_setup();
    let src = "theorem r5 {α β : Sort u} (a : α) (b : β) (e : β = α) :\n\
               \x20   a = cast e b → HEq a b := by\n\
               \x20 rintro rfl; simp only [my_cast_heq]\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`rintro rfl; simp only [cast_heq]` must close `heq_of_eq_cast`: {e}");
    }
}

/// `Decidable.iff_congr_left`'s shape: three instance binders no side of the
/// statement mentions. Local instances let it fire; without them it is
/// refused by simp ("no progress"), not by the kernel on a loose de Bruijn
/// index.
#[test]
fn test_simp_iff_lemma_with_three_unmentioned_instance_binders() {
    let mut env = env_with_setup();
    let src = "theorem p6d (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] :\n\
               \x20   PPr ((a ↔ c) ↔ (b ↔ c)) ↔ PPr (a ↔ b) := by\n\
               \x20 simp only [my_iff_congr_left]\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("local `Decidable` instances must fill the lemma's three binders: {e}");
    }
    expect_no_progress(
        "theorem p6 (a b c : Prop) : PPr ((a ↔ c) ↔ (b ↔ c)) ↔ PPr (a ↔ b) := by\n\
         \x20 simp only [my_iff_congr_left]\n",
    );
}

/// The rows behind which universe-polymorphic `↔` lemmas were the only wall,
/// in Mathlib's own shapes: `and_symm_right`/`and_symm_left` (`eq_comm`, a
/// permutation lemma, under a conjunction), `forall_apply_eq_imp_iff'` and
/// `forall_eq_apply_imp_iff'` (`forall_eq'`/`forall_eq` under a `∀` binder),
/// `not_forall`, and `Decidable.forall_or_left`, whose `[Decidable q]` no side
/// mentions (the "Unbound variable index: 0" row).
///
/// simp's rewrite under a `∀` binder is proved with Lean's `forall_congr`,
/// which exists only after `import Init` (measured: without it the step is
/// refused as a non-definitional target change, for the level-constant
/// control alike — a property of the prelude-only harness, not of the
/// lemma). It is a Lean 4.8.0 core name a file may not declare, so the
/// fixture registers it as an imported constant
/// (`crate::tests_support_imported_core`). Lean 4.8.0 accepts every row below
/// as written, with `universe u v w` (measured 2026-09-27).
#[test]
fn test_simp_universe_polymorphic_iff_lemmas_fire_in_the_measured_row_shapes() {
    let mut env = Environment::with_prelude();
    crate::tests_support_imported_core::import_core_constants(
        &mut env,
        crate::tests_support_imported_core::FORALL_CONGR,
    );
    let src = "axiom my_eq_comm {α : Sort u} {a b : α} : a = b ↔ b = a\n\
               theorem r0 {α : Sort v} (a b : α) (p : Prop) : p ∧ a = b ↔ p ∧ b = a := by\n\
               \x20 simp only [my_eq_comm]\n\
               theorem r1 {α : Sort v} (a b : α) (p : Prop) : a = b ∧ p ↔ b = a ∧ p := by\n\
               \x20 simp only [my_eq_comm]\n\
               axiom my_forall_eq {α : Sort u} {p : α → Prop} {a' : α} :\n\
               \x20   (∀ a, a = a' → p a) ↔ p a'\n\
               axiom my_forall_eq' {α : Sort u} {p : α → Prop} {a' : α} :\n\
               \x20   (∀ a, a' = a → p a) ↔ p a'\n\
               theorem r8 {α : Sort v} {β : Sort w} {f : α → β} {p : β → Prop} :\n\
               \x20   (∀ a b, f a = b → p b) ↔ ∀ a, p (f a) := by simp only [my_forall_eq']\n\
               theorem r9 {α : Sort v} {β : Sort w} {f : α → β} {p : β → Prop} :\n\
               \x20   (∀ a b, b = f a → p b) ↔ ∀ a, p (f a) := by simp only [my_forall_eq]\n\
               axiom my_not_forall {α : Sort u} {p : α → Prop} : (¬∀ x, p x) ↔ ∃ x, ¬p x\n\
               theorem r10 {α : Sort v} (q : α → Prop) : (¬ ∀ x, q x) ↔ ∃ x, ¬ q x := by\n\
               \x20 simp only [my_not_forall]\n\
               axiom my_forall_or_left {α : Sort u} {q : Prop} {p : α → Prop} [Decidable q] :\n\
               \x20   (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x\n\
               theorem r11 {α : Sort v} {q : Prop} {p : α → Prop} [Decidable q] :\n\
               \x20   (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x := by simp only [my_forall_or_left]\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("universe-polymorphic `↔` lemmas must fire in the measured row shapes: {e}");
    }
}

/// The same rules through the `@[simp]` REGISTRY (`collect_registry_lemmas`),
/// not only `simp only [name]` (`collect_extra_lemmas`).
#[test]
fn test_simp_registry_plain_proposition_and_negation_lemmas_rewrite() {
    let mut env = env_with_setup();
    let src = "axiom QQ : Nat → Prop\n\
               axiom ff : Nat → Nat\n\
               @[simp] axiom lemR (n : Nat) : QQ (ff n)\n\
               theorem p4 (n : Nat) : PPr (QQ (ff n)) ↔ PPr True := by simp\n\
               @[simp] axiom lemRn (n : Nat) : ¬ QQ n\n\
               theorem p4n (n : Nat) : PPr (QQ n) ↔ PPr False := by simp\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`@[simp]` plain-proposition and negation lemmas must rewrite: {e}");
    }
}
