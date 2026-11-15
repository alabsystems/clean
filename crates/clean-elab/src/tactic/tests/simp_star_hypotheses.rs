// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `simp [*]` / `simp only [*]` — the star element of a simp lemma list.
//!
//! `SimpConfig::use_hypotheses` (`simp/types.rs`) and its consumer
//! `collect_hypothesis_lemmas` (`simp/lemmas.rs`) implemented Lean's `simp [*]`
//! semantics, but no caller could reach them from source: `parse_simp_lemmas`
//! looped `self.expr()` over the bracket list with no arm for `*`, so every
//! `simp [*]` raised `Unexpected token: Star` and then lost the rest of the
//! declaration to parser recovery. Only `simp_all` and `cert_simp` ever set the
//! flag.
//!
//! These tests drive the whole production path — `parse_file` → preprocess →
//! elaborate → kernel — because the defect lived exactly in the seam between
//! the parser and an engine capability that already worked.

use clean_kernel::Environment;
use clean_parser::parse_file;

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};

/// Elaborate every declaration in `code` against one fresh prelude env.
fn elab_all(code: &str) -> Vec<Result<ElabResult, crate::ElabError>> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("parse_file should succeed");
    decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        })
        .collect()
}

#[track_caller]
fn assert_all_closed(code: &str, what: &str) {
    let results = elab_all(code);
    assert!(!results.is_empty(), "{what}: nothing parsed");
    for result in &results {
        assert!(
            matches!(result, Ok(ElabResult::Theorem { .. })),
            "{what}: expected a kernel-registered theorem, got {result:?}"
        );
    }
}

/// The goal every test below uses. It is chosen so that ONLY the hypothesis
/// rewrite can close it: `h : a = b` under a congruence, so simp's own
/// `assumption`-style closer cannot match `f a = f b`, and no @[simp] lemma
/// applies. Measured on the release binary: `simp` alone reports
/// `NoProgress { tactic: "simp" }` on exactly this goal.
///
/// (An earlier draft used `h : a = b ⊢ a = b`, which simp closes by assumption
/// with or without the star — it passed under a mutation that hard-coded
/// `use_hypotheses = false`, so it proved nothing.)
const CONGRUENCE_GOAL: &str = "(f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b";

fn thm(name: &str, tactic: &str) -> String {
    format!("theorem {name} {CONGRUENCE_GOAL} := by {tactic}\n")
}

/// Negative control: the same goal with a star-free `simp` must NOT close, so
/// every pass below is attributable to the star element and nothing else.
#[test]
fn test_plain_simp_cannot_close_the_congruence_goal() {
    let results = elab_all(&thm("plainSimp", "simp"));
    assert!(
        results.iter().any(|r| r.is_err()),
        "control is broken: plain `simp` closed the congruence goal, so the \
         star tests below no longer discriminate. Got {results:?}"
    );
}

/// The bare `simp [*]` closer — the form behind 424 of the 838 Mathlib
/// occurrences, and the standard finisher for `obtain … <;> simp [*]`.
#[test]
fn test_simp_star_uses_a_local_equality_hypothesis() {
    assert_all_closed(&thm("starSimp", "simp [*]"), "simp [*]");
}

/// `simp only [*]` must reach the same flag while still skipping the @[simp]
/// registry: `collect_simp_lemmas` adds hypothesis lemmas outside its
/// `if !config.only` guard, so the star element is the only rewrite source.
#[test]
fn test_simp_only_star_uses_a_local_equality_hypothesis() {
    assert_all_closed(&thm("starSimpOnly", "simp only [*]"), "simp only [*]");
}

/// `*` mixed with named lemmas, in both orders — the 405 remaining Mathlib
/// occurrences. The star must not be pushed into `extra_lemmas` (where it would
/// resolve to a nonexistent constant named `*`) and must not swallow its
/// neighbours.
#[test]
fn test_simp_star_mixes_with_named_lemmas_in_either_order() {
    assert_all_closed(
        &thm("starMixedTail", "simp [Nat.add_zero, *]"),
        "simp [lemma, *]",
    );
    assert_all_closed(
        &thm("starMixedHead", "simp [*, Nat.add_zero]"),
        "simp [*, lemma]",
    );
}

/// Control: a star-free lemma list must behave exactly as before.
#[test]
fn test_plain_simp_lemma_list_is_unchanged() {
    assert_all_closed(
        "theorem plainSimpList (a : Nat) : a + 0 = a := by simp [Nat.add_zero]\n",
        "plain simp [lemma] control",
    );
}

// ---------------------------------------------------------------------------
// `[*]` over NON-equational Prop hypotheses — Lean's `applyStarArg`
// ---------------------------------------------------------------------------
//
// Lean's `[*]` loops over `getPropHyps` — EVERY Prop hypothesis — and calls
// `simpTheorems.addTheorem (.fvar h)`, the same `preprocess` a named lemma
// takes: `hab : a ≤ b` becomes `(a ≤ b) = True` and `ha : a ≤ b → p a` becomes
// the conditional `∀ (_ : a ≤ b), p a = True`. Clean's `collect_hypothesis_lemmas`
// kept only `h : a = b`-shaped locals and `continue`d on the rest with no
// diagnostic, which is the residual CLAUDE.md class (27) states in its own
// text ("`simp [*]` still skips Prop locals"). It is what `Order/Basic.lean`'s
// four `Prod` rows and `min_rec` end on, and why `simp only [ha, hab]` — the
// named path, which has always had the fall-through — proved goals `simp [*]`
// could not.

/// Like [`assert_all_closed`], but only the LAST declaration must be a
/// theorem: the fixtures below open with `axiom` declarations.
#[track_caller]
fn assert_last_closed(code: &str, what: &str) {
    let results = elab_all(code);
    let last = results.last().expect("nothing parsed");
    assert!(
        matches!(last, Ok(ElabResult::Theorem { .. })),
        "{what}: expected a kernel-registered theorem, got {last:?}"
    );
}

/// The `min_rec` shape: a conditional Prop hypothesis plus its premise.
const COND_FIXTURE: &str = "\
axiom LEq : Nat → Nat → Prop
axiom p : Nat → Prop
";

/// Negative control: without the star nothing closes this goal, so the pass
/// below is attributable to the hypothesis rules and nothing else.
#[test]
fn test_plain_simp_cannot_close_the_conditional_prop_goal() {
    let results = elab_all(&format!(
        "{COND_FIXTURE}theorem ctl (a b : Nat) (ha : LEq a b → p a) (hab : LEq a b) : p a := by \
         simp\n"
    ));
    assert!(
        results.iter().any(|r| r.is_err()),
        "control is broken: plain `simp` closed the conditional goal, so the \
         star test below no longer discriminates. Got {results:?}"
    );
}

/// `simp [*]` with the facts present only as PROPOSITIONS.
#[test]
fn test_simp_star_uses_a_conditional_prop_hypothesis() {
    assert_last_closed(
        &format!(
            "{COND_FIXTURE}theorem starCond (a b : Nat) (ha : LEq a b → p a) (hab : LEq a b) : \
             p a := by simp [*]\n"
        ),
        "simp [*] over Prop hypotheses",
    );
}

/// The same facts reached by NAME already worked; this is the control that
/// isolates the `*` collection as the whole difference.
#[test]
fn test_named_prop_hypotheses_close_the_same_goal() {
    assert_last_closed(
        &format!(
            "{COND_FIXTURE}theorem namedCond (a b : Nat) (ha : LEq a b → p a) (hab : LEq a b) : \
             p a := by simp only [ha, hab]\n"
        ),
        "simp only [ha, hab]",
    );
}

/// The `Prod` rows' shape: a disjunctive goal whose two conjuncts sit in the
/// context as bare propositions.
#[test]
fn test_simp_star_uses_bare_prop_hypotheses_under_a_disjunction() {
    assert_all_closed(
        "theorem starDisj (P Q R : Prop) (h1 : P) (h2 : Q) : (P ∧ Q) ∨ R := by simp [*]\n",
        "simp [*] over bare Prop hypotheses",
    );
}

/// `simp [lemma, *]` — the rows' exact spelling, a named lemma AND the star in
/// one list.
#[test]
fn test_simp_star_beside_a_named_lemma_still_uses_prop_hypotheses() {
    assert_all_closed(
        "theorem starNamed (P Q R : Prop) (h1 : P) (h2 : Q) : (P ∧ Q) ∨ R := by \
         simp [Nat.add_zero, *]\n",
        "simp [lemma, *] over bare Prop hypotheses",
    );
}

/// A hypothesis must not be rewritten by its OWN rule: Lean's `simpGoal`
/// removes it from the set first. Here `h : P` and `e : P = Q` are both
/// priority-75 star rules and `h` is collected FIRST, so without the exclusion
/// `h`'s own `P = True` fires and `h : True` can no longer close `⊢ Q`.
#[test]
fn test_simp_star_at_a_hypothesis_excludes_that_hypothesis_own_rule() {
    assert_last_closed(
        "axiom P : Prop\naxiom Q : Prop\n\
         theorem starAt (h : P) (e : P = Q) : Q := by\n  simp [*] at h\n  exact h\n",
        "simp [*] at h excludes h's own rule",
    );
}
