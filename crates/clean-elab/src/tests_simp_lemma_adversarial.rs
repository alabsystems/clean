// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Adversarial review battery for simp's lemma construction: near-miss
//! shapes around the four rules the package landed (fresh universe levels per
//! use, `preprocess` for a global non-`=`/`↔` theorem, typeclass synthesis
//! for an undetermined instance binder, a hypothesis simplified to `False`).
//!
//! Every fixture is the EXACT text that was run on the pinned v4.30.0-rc2
//! `lean` binary (2026-09-20): each declaration named in a `refused` list
//! fails there (with "`simp` made no progress", or "Unknown identifier" for
//! the missing location) and every other one elaborates as written. The
//! `Init` constants the fixtures rely on are Lean 4.8.0 core names a file may
//! not declare: the prelude supplies `Bool.of_not_eq_true`/`_false`
//! (`clean_kernel`'s `lean_core_supply`), and `MEMO` gets `forall_congr` as
//! an imported constant (`crate::tests_support_imported_core`). Lean 4.8.0
//! accepts the `BOOLS` and `MEMO` fixtures as written (measured 2026-09-27).
//!
//! Four of these were RED on the package as ported and are the repairs that
//! landed with this file:
//!
//! * the `Bool` special case of `preprocess` (`b ≠ true` ↦ `b = false`) was
//!   unreachable — it matched the constructor's name, and a source `true` is
//!   the builtin prelude's alias;
//! * the instance memo was keyed on the class goal alone, so "no instance"
//!   at the top level silenced every rewrite under a binder that supplies
//!   one, and one binder's instance was handed to its sibling;
//! * `simp at h` with `h : False` reported no progress instead of closing the
//!   goal;
//! * `simp … at h hmissing` was accepted once `h` closed the goal, because
//!   the later name was never looked up.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file;

/// Elaborate `src` declaration by declaration and return, for every theorem
/// or definition that FAILED, its name and error. A failure never stops the
/// file — Lean's own behaviour, and what lets one fixture hold the accepted
/// shapes beside the refused ones.
pub(crate) fn failures(src: &str) -> Vec<(String, String)> {
    failures_in(Environment::with_prelude(), src)
}

/// [`failures`] over a given starting environment.
pub(crate) fn failures_in(mut env: Environment, src: &str) -> Vec<(String, String)> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    let mut file_ctx = FileContext::new();
    let mut failed = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx) {
            Ok(result) => {
                let mut leaves = Vec::new();
                result.leaf_decls(&mut leaves);
                for leaf in leaves {
                    if let ElabResult::Failed { name, error, .. } = leaf {
                        failed.push((name.clone(), format!("{error:?}")));
                    }
                }
            }
            Err(e) => {
                let name = crate::preprocess_ext::decl_name(decl)
                    .map_or_else(|| "<decl>".to_string(), ToString::to_string);
                failed.push((name, format!("{e:?}")));
            }
        }
    }
    failed
}

/// Assert that exactly the declarations in `refused` fail, each with an error
/// mentioning its expected fragment and none of them by the KERNEL aborting
/// on a term simp should never have emitted.
pub(crate) fn assert_refused_exactly(src: &str, refused: &[(&str, &str)]) {
    assert_refused_exactly_in(Environment::with_prelude(), src, refused);
}

/// [`assert_refused_exactly`] over a given starting environment.
pub(crate) fn assert_refused_exactly_in(env: Environment, src: &str, refused: &[(&str, &str)]) {
    let failed = failures_in(env, src);
    for (name, error) in &failed {
        let expected = refused.iter().find(|(n, _)| n == name);
        let Some((_, fragment)) = expected else {
            panic!("pinned Lean accepts `{name}`; Clean refused it: {error}");
        };
        assert!(
            error.contains(fragment),
            "`{name}` must be refused with `{fragment}`: {error}"
        );
        assert!(
            !error.contains("Unbound variable") && !error.contains("type check failed"),
            "`{name}` must be refused by the tactic, not by the kernel: {error}"
        );
    }
    for (name, _) in refused {
        assert!(
            failed.iter().any(|(n, _)| n == name),
            "pinned Lean refuses `{name}`; Clean accepted it"
        );
    }
}

const LEVELS: &str = r#"universe u v w
axiom RR {α : Sort u} : α → Prop
axiom my_exists_eq_I {α : Sort v} {a' : α} : (∃ a, a = a') ↔ True
theorem lv_succ {β : Type v} (b : β) : ∃ a, a = b := by simp only [my_exists_eq_I]
axiom lemRhs {α : Sort u} (x : α) : RR x ↔ ∃ (β : Sort v), β → True
theorem lv_rhs_only (n : Nat) : RR n := by
  simp only [lemRhs]
  exact ⟨True, fun _ => True.intro⟩
theorem lv_two (n : Nat) (T : Type) : (∃ a, a = n) ∧ (∃ a, a = T) := by
  simp only [my_exists_eq_I]
  exact ⟨True.intro, True.intro⟩
theorem lv_hyp {β : Sort w} (b : β) (h : (∃ a, a = b) → False) : False := by
  simp only [my_exists_eq_I] at h
  exact h True.intro
axiom PQ {γ : Type w} : γ → Prop
axiom prod_lem {α : Type u} {β : Type v} (p : α × β) : PQ p ↔ True
theorem lv_max0 (p : Nat × Nat) : PQ p := by simp only [prod_lem]
theorem lv_maxuv {α : Type u} {β : Type v} (p : α × β) : PQ p := by simp only [prod_lem]
theorem lv_maxvu {α : Type v} {β : Type u} (p : α × β) : PQ p := by simp only [prod_lem]
axiom SSort {α : Sort u} : α → Prop
axiom lemT {α : Type u} (x : α) : SSort x ↔ True
theorem lv_nearmiss (p : Prop) (hp : p) : SSort hp := by simp only [lemT]
axiom WW {α : Sort u} {β : Sort v} : α → β → Prop
axiom ww_lem {α : Sort u} {β : Sort v} (x : α) (y : β) : WW x y ↔ True
theorem lv_swap {α : Sort v} {β : Sort u} (x : α) (y : β) : WW x y := by simp only [ww_lem]
theorem lv_swap_type {α : Type v} {β : Type u} (x : α) (y : β) : WW x y := by simp only [ww_lem]
axiom shadow {α : Sort u} (x : α) : RR x ↔ True
theorem lv_shadow (n : Nat) (shadow : RR n = True) : RR n := by simp only [shadow]
"#;

/// Fresh levels per use, in the shapes a name-keyed level store gets wrong:
/// the lemma's `v` solved to the goal's `v + 1` (`lv_succ`), one lemma at two
/// universes inside ONE `simp` call (`lv_two`), at a hypothesis (`lv_hyp`),
/// `max` levels in either order (`lv_max*`), the lemma's `u`/`v` solved to
/// the goal's `v`/`u` — crossed (`lv_swap*`) — and a same-named LOCAL
/// shadowing the polymorphic constant (`lv_shadow`). Refused, as in Lean: a
/// level only the RIGHT-hand side mentions (`lv_rhs_only`; Lean: "has
/// unassigned metavariables"), and a `Type u` lemma against a `Prop` carrier
/// (`lv_nearmiss`).
#[test]
fn test_simp_fresh_lemma_levels_adversarial_shapes_match_lean() {
    assert_refused_exactly(
        LEVELS,
        &[("lv_rhs_only", "NoProgress"), ("lv_nearmiss", "NoProgress")],
    );
}

const PROPS: &str = r#"axiom PP : Nat → Prop
axiom QQ : Nat → Prop
axiom P3 : Nat → Prop
axiom P4 : Nat → Prop
axiom P5 : Nat → Prop
axiom pp3 : PP 3
axiom nQ (n : Nat) : ¬ QQ n
axiom both (n : Nat) : P3 n ∧ P4 n
axiom ne_lem (n : Nat) : n + 1 ≠ 0
axiom condL (n : Nat) (h : PP n) : P5 n
axiom nested (n : Nat) : P3 n ∧ (P4 n ∧ ¬ P5 n)
theorem pr_nearmiss : PP 4 := by simp only [pp3]
theorem pr_true : PP 3 := by simp only [pp3]
theorem pr_not : QQ 7 = False := by simp only [nQ]
theorem pr_and_l : P3 15 := by simp only [both]
theorem pr_and_r : P4 25 := by simp only [both]
theorem pr_ne (k : Nat) : (k + 1 = 0) = False := by simp only [ne_lem]
theorem pr_cond (k : Nat) (h : PP k) : P5 k := by simp only [condL, h]
theorem pr_cond_missing (k : Nat) : P5 k := by simp only [condL]
theorem pr_nested_a (k : Nat) : P4 k := by simp only [nested]
theorem pr_nested_b (k : Nat) : P5 k = False := by simp only [nested]
@[simp] axiom pp3s : PP 30
theorem pr_reg : PP 30 := by simp
theorem pr_reg_only_excludes : PP 30 := by simp only []
theorem pr_reg_nearmiss : PP 31 := by simp
"#;

/// Lean's `preprocess` rules for a global theorem, with their near misses: a
/// fact about `3` says nothing about `4` (`pr_nearmiss`, and `pr_reg_nearmiss`
/// through the `@[simp]` registry), a CONDITIONAL fact fires only when its
/// premise is discharged (`pr_cond` / `pr_cond_missing`), a nested
/// conjunction is split all the way down (`pr_nested_*`), and `simp only []`
/// does not see the registry (`pr_reg_only_excludes`).
#[test]
fn test_simp_global_proposition_lemmas_near_misses_match_lean() {
    assert_refused_exactly(
        PROPS,
        &[
            ("pr_nearmiss", "NoProgress"),
            ("pr_cond_missing", "NoProgress"),
            ("pr_reg_only_excludes", "NoProgress"),
            ("pr_reg_nearmiss", "NoProgress"),
        ],
    );
}

const BOOLS: &str = r#"axiom fb : Nat → Bool
axiom bne_t (n : Nat) : fb n ≠ true
axiom bnot_f (n : Nat) : ¬ (fb (n + 1) = false)
axiom bnot_t (n : Nat) : ¬ (fb (n + 2) = true)
theorem bo_ne_true (k : Nat) : fb k = false := by simp only [bne_t]
theorem bo_not_false (k : Nat) : fb (k + 1) = true := by simp only [bnot_f]
theorem bo_not_true (k : Nat) : fb (k + 2) = false := by simp only [bnot_t]
"#;

/// Lean's `Bool` special case: `b ≠ true` and `¬(b = true)` become the rule
/// `b = false` (and the `false` twins `b = true`), so the goal `fb k = false`
/// is CLOSED by the rewrite. The generic `(fb n = true) = False` rule cannot
/// do that — it does not even match the goal — which is how this was measured
/// dead before the literal's alias spelling was recognised.
#[test]
fn test_simp_bool_disequality_lemma_rewrites_to_the_other_literal() {
    assert_refused_exactly(BOOLS, &[]);
}

const MEMO: &str = r#"axiom PP {α : Type} : α → Prop
class Inh2 (α : Type) where
  pt : α
axiom lemK2 {α : Type} [Inh2 α] (x : α) : PP x ↔ True
theorem mm_siblings (n : Nat) :
    (∀ (i : Inh2 Nat), PP n ∧ PP (@Inh2.pt Nat i)) ∧ (∀ (j : Inh2 Nat), PP n ∧ PP (@Inh2.pt Nat j)) := by
  simp only [lemK2]
  exact ⟨fun _ => ⟨True.intro, True.intro⟩, fun _ => ⟨True.intro, True.intro⟩⟩
theorem mm_outer_then_inner (m : Nat) (hm : PP m) :
    PP m ∧ (∀ (i : Inh2 Nat), PP (@Inh2.pt Nat i)) := by
  simp only [lemK2]
  exact ⟨hm, fun _ => True.intro⟩
"#;

/// The same class goal has different answers in different local contexts: a
/// binder simp opened can BE the instance. `mm_outer_then_inner` asks
/// `Inh2 Nat` first where there is none and then under `∀ (i : Inh2 Nat)`;
/// `mm_siblings` asks it under two sibling binders, where the first answer
/// names a free variable that is out of scope in the second.
#[test]
fn test_simp_instance_answers_are_per_local_context() {
    let mut env = Environment::with_prelude();
    crate::tests_support_imported_core::import_core_constants(
        &mut env,
        crate::tests_support_imported_core::FORALL_CONGR,
    );
    assert_refused_exactly_in(env, MEMO, &[]);
}

const AT_FALSE: &str = r#"axiom QQ : Nat → Prop
axiom nQ (n : Nat) : ¬ QQ n
theorem af_already (h : False) : 1 = 2 := by simp at h
theorem af_already_only (h : False) : 1 = 2 := by simp only at h
theorem af_already_lemma (h : False) : 1 = 2 := by simp only [nQ] at h
theorem af_two (h : QQ 1) : 1 = 2 ∧ 2 = 3 := by
  constructor
  · simp only [nQ] at h
  · simp only [nQ] at h
theorem af_second_left (h : QQ 1) (k : 2 = 3) : 1 = 2 ∧ 2 = 3 := by
  constructor
  simp only [nQ] at h
  exact k
theorem af_later_missing (h : QQ 1) : 1 = 2 := by simp only [nQ] at h hmissing
theorem af_dependent (h : QQ 1) (k : h = h) : 1 = 2 := by simp only [nQ] at h
def af_poly.{u} {α : Sort u} (h : QQ 1) : α := by simp only [nQ] at h
"#;

/// Lean's `applySimpResult` tests the RESULT: a hypothesis that already is
/// `False` closes the goal (`af_already*`), each goal closes on its own
/// (`af_two`) and a sibling goal is left for the next tactic
/// (`af_second_left`), a hypothesis DEPENDING on the closed one is no
/// obstacle (`af_dependent`), and the target's universe is the goal's own
/// (`af_poly`). The location list is resolved up front, so a later name that
/// does not exist is an error even though `h` alone closes the goal.
#[test]
fn test_simp_at_false_hypothesis_adversarial_shapes_match_lean() {
    assert_refused_exactly(AT_FALSE, &[("af_later_missing", "HypothesisNotFound")]);
}

/// Mathlib's `simp_rw … at` resolves its locations the same way; the bare
/// pinned binary has no `simp_rw`, so this one is not ground-truthed there.
#[test]
fn test_simp_rw_at_unknown_later_location_is_an_error() {
    assert_refused_exactly(
        "axiom QQ : Nat → Prop\n\
         axiom nQ (n : Nat) : ¬ QQ n\n\
         theorem af_later_missing_rw (h : QQ 1) : 1 = 2 := by simp_rw [nQ] at h hmissing\n",
        &[("af_later_missing_rw", "HypothesisNotFound")],
    );
}
