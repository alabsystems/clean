// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! omega's propositional hypotheses (gap G26, ledger class 95).
//!
//! Every PROVE row here is proved by pinned Lean 4.8.0's `omega`, and every
//! REFUSE row is refused by it ("omega could not prove the goal") — measured
//! with `~/.elan/toolchains/leanprover--lean4---v4.8.0/bin/lean` on
//! 2026-10-08. A PROVE row must register the theorem through the kernel with
//! no axiom outside the foundational set (`axiom_deps` reports `sorryAx`,
//! `trustedArith` and every domain axiom); a REFUSE row must fail and must not
//! register. The negative rows are what keep the wider acceptance honest: each
//! differs from a PROVE row only in a constant that makes it false.

use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};

fn elab(code: &str) -> (Environment, Vec<Result<ElabResult, crate::ElabError>>) {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("parse_file should succeed");
    let results = decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        })
        .collect();
    (env, results)
}

/// `theorem <name> <sig> := by omega` must register with no non-foundational
/// axiom in its closure.
#[track_caller]
fn assert_proves(name: &str, sig: &str) {
    let code = format!("theorem {name} {sig} := by omega\n");
    let (env, results) = elab(&code);
    assert_eq!(results.len(), 1, "{name}: expected one declaration");
    if let Err(err) = &results[0] {
        panic!("{name}: pinned Lean 4.8 proves `{sig}` by omega; Clean refused: {err:?}");
    }
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name}: not registered"));
    assert!(
        deps.is_empty(),
        "{name}: proof must use only foundational axioms, reached {deps:?}"
    );
}

/// `theorem <name> <sig> := by omega` must fail and must not register; the
/// error is returned for further assertions.
#[track_caller]
fn assert_refuses(name: &str, sig: &str) -> String {
    let code = format!("theorem {name} {sig} := by omega\n");
    let (env, results) = elab(&code);
    let err = results
        .iter()
        .find_map(|r| r.as_ref().err())
        .unwrap_or_else(|| {
            panic!("{name}: `{sig}` is FALSE (pinned Lean refuses it); Clean proved it")
        });
    assert!(
        env.get_const(&Name::from_string(name)).is_none(),
        "{name}: a refused theorem must not be registered"
    );
    format!("{err:?}")
}

#[test]
fn test_omega_or_hypothesis_two_way_proves() {
    assert_proves("g26_or2", "(c : Nat) (hc : c = 1 ∨ c = 2) : c ≤ 2");
}

#[test]
fn test_omega_or_hypothesis_two_way_false_refused() {
    let err = assert_refuses("g26_or2n", "(c : Nat) (hc : c = 1 ∨ c = 3) : c ≤ 2");
    assert!(err.contains("omega"), "the refusal must name omega: {err}");
    assert!(
        err.contains("hypothesis case split"),
        "the refusal must say a branch of the split failed: {err}"
    );
}

#[test]
fn test_omega_or_hypothesis_three_way_proves_and_false_refused() {
    assert_proves("g26_or3", "(c : Nat) (hc : c = 1 ∨ c = 2 ∨ c = 0) : c ≤ 2");
    assert_refuses("g26_or3n", "(c : Nat) (hc : c = 1 ∨ c = 2 ∨ c = 5) : c ≤ 2");
}

#[test]
fn test_omega_or_hypothesis_six_way_proves_and_false_refused() {
    assert_proves(
        "g26_or6",
        "(c : Nat) (hc : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6) : c ≤ 6",
    );
    assert_refuses(
        "g26_or6n",
        "(c : Nat) (hc : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 7) : c ≤ 6",
    );
}

#[test]
fn test_omega_two_or_hypotheses_proves_and_false_refused() {
    assert_proves(
        "g26_two",
        "(a b : Nat) (h1 : a = 1 ∨ a = 2) (h2 : b = 3 ∨ b = 4) : a + b ≤ 6",
    );
    assert_refuses(
        "g26_twon",
        "(a b : Nat) (h1 : a = 1 ∨ a = 2) (h2 : b = 3 ∨ b = 4) : a + b ≤ 5",
    );
}

#[test]
fn test_omega_strict_or_equal_hypothesis_proves_and_false_refused() {
    assert_proves("g26_lt", "(x y : Nat) (h : x < y ∨ x = y) : x ≤ y");
    assert_refuses("g26_ltn", "(x y : Nat) (h : x < y ∨ x = y + 1) : x ≤ y");
}

#[test]
fn test_omega_and_hypothesis_proves_and_false_refused() {
    assert_proves("g26_and", "(a b : Nat) (h : a ≤ 2 ∧ b ≤ 3) : a + b ≤ 5");
    assert_refuses("g26_andn", "(a b : Nat) (h : a ≤ 2 ∧ b ≤ 3) : a + b ≤ 4");
}

#[test]
fn test_omega_or_of_and_hypothesis_proves_and_false_refused() {
    assert_proves(
        "g26_orand",
        "(a b : Nat) (h : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)) : a + b = 3",
    );
    assert_refuses(
        "g26_orandn",
        "(a b : Nat) (h : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 2)) : a + b = 3",
    );
}

#[test]
fn test_omega_disequality_hypothesis_proves_and_false_refused() {
    assert_proves("g26_ne", "(c : Nat) (h : c ≠ 1) (h1 : c ≥ 1) : c ≥ 2");
    assert_proves("g26_notEq", "(c : Nat) (h : ¬ c = 1) (h1 : c ≥ 1) : c ≥ 2");
    assert_proves(
        "g26_neFalse",
        "(c : Nat) (h : c ≠ 1) (h1 : c ≥ 1) (h2 : c ≤ 1) : False",
    );
    assert_refuses("g26_nen", "(c : Nat) (h : ¬ c = 1) (h1 : c ≥ 1) : c ≥ 3");
}

#[test]
fn test_omega_iff_hypothesis_proves_and_false_refused() {
    assert_proves(
        "g26_iff",
        "(a b : Nat) (h : a = 1 ↔ b = 1) (ha : a = 1) : b ≤ 1",
    );
    assert_refuses(
        "g26_iffn",
        "(a b : Nat) (h : a = 1 ↔ b = 2) (ha : a = 1) : b ≤ 1",
    );
}

#[test]
fn test_omega_not_or_hypothesis_proves_and_false_refused() {
    assert_proves("g26_notor", "(a : Nat) (h : ¬ (a = 0 ∨ a = 1)) : a ≥ 2");
    assert_refuses("g26_notorn", "(a : Nat) (h : ¬ (a = 0 ∨ a = 1)) : a ≥ 3");
}

#[test]
fn test_omega_not_and_and_implication_hypotheses_prove_and_false_refused() {
    assert_proves(
        "g26_notand",
        "(a : Nat) (h : ¬ (a ≤ 2 ∧ a ≥ 1)) (h1 : a ≥ 1) : a ≥ 3",
    );
    assert_refuses(
        "g26_notandn",
        "(a : Nat) (h : ¬ (a ≤ 2 ∧ a ≥ 1)) (h1 : a ≥ 1) : a ≥ 4",
    );
    assert_proves(
        "g26_imp",
        "(a b : Nat) (h : a ≤ 1 → b ≤ 1) (ha : a = 0) : b ≤ 1",
    );
    assert_refuses(
        "g26_impn",
        "(a b : Nat) (h : a ≤ 1 → b ≤ 1) (ha : a = 2) : b ≤ 1",
    );
}

/// Hypotheses that contradict each other close any goal (Lean's omega
/// refutes the facts with the goal's negation among them), including a goal
/// the refutation does not mention — here before any split is needed, since
/// the context carries a disjunction the layer could act on.
#[test]
fn test_omega_contradictory_hypotheses_close_unrelated_goal() {
    assert_proves(
        "g26_exf",
        "(a b : Nat) (h0 : b = 0 ∨ b = 5) (h1 : a < 1) (h2 : a > 0) : b ≤ 1",
    );
    assert_refuses(
        "g26_exfn",
        "(a b : Nat) (h0 : b = 0 ∨ b = 5) (h1 : a < 2) (h2 : a > 0) : b ≤ 1",
    );
}

/// A branch whose facts refute each other through an equality or a strict
/// comparison: Lean's omega reads `a < b` as `a + 1 ≤ b` and solves
/// equalities, so the leaf is restated that way before it is given up.
#[test]
fn test_omega_branch_refuted_through_equality_or_strict_fact() {
    assert_proves(
        "g26_eqleaf",
        "(c : Nat) (hc : c = 1 ∨ c = 5) (h : c < 3) : c ≤ 1",
    );
    assert_refuses(
        "g26_eqleafn",
        "(c : Nat) (hc : c = 1 ∨ c = 5) (h : c < 7) : c ≤ 1",
    );
    assert_proves(
        "g26_strictleaf",
        "(x y : Nat) (h : x = y ∨ x = y + 2) (h2 : x ≠ y) : x ≥ 2",
    );
    assert_refuses(
        "g26_strictleafn",
        "(x y : Nat) (h : x = y ∨ x = y + 2) : x ≥ 2",
    );
}

/// Lean's relevance rules, as negative controls. Pinned Lean 4.8.0 splits a
/// disjunction only when its LEFT disjunct adds a linear fact, and never reads
/// a hypothesis that adds none (`False`, an opaque `P`), so each of these is
/// REFUSED there although it is true. Clean must refuse them too: splitting on
/// the opaque side, or handing a branch its `False`, would accept what Lean
/// refuses.
#[test]
fn test_omega_factless_disjuncts_refused_like_lean() {
    assert_refuses("g26_falseL", "(c : Nat) (h : False ∨ c = 1) : c ≤ 1");
    assert_refuses("g26_falseR", "(c : Nat) (h : c = 1 ∨ False) : c ≤ 1");
    assert_refuses(
        "g26_propL",
        "(c : Nat) (P : Prop) (hp : ¬ P) (h : P ∨ c = 1) : c ≤ 1",
    );
    assert_refuses(
        "g26_propR",
        "(c : Nat) (P : Prop) (hp : ¬ P) (h : c = 1 ∨ P) : c ≤ 1",
    );
    assert_refuses(
        "g26_propImp",
        "(c : Nat) (P : Prop) (h : P → c = 1) (hp : P) : c ≤ 1",
    );
    // ... while a relevant disjunction beside an irrelevant one still splits.
    assert_proves(
        "g26_propSkip",
        "(c : Nat) (P : Prop) (h : P ∨ c = 1) (h2 : c = 1 ∨ c = 0) : c ≤ 1",
    );
}

/// Past the cap the search refuses LOUDLY. Eight two-way disjunctions need
/// 255 splits, beyond `MAX_HYP_CASE_SPLITS` (128). Pinned Lean 4.8 has no cap
/// and proves this goal; Clean refuses it by name — this pin fails the day the
/// cap or the search changes, so that day it is re-measured.
#[test]
fn test_omega_hypothesis_split_cap_refuses_loudly() {
    let err = assert_refuses(
        "g26_cap",
        "(a b c d e f g h : Nat) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) \
         (hc : c = 0 ∨ c = 1) (hd : d = 0 ∨ d = 1) (he : e = 0 ∨ e = 1) \
         (hf : f = 0 ∨ f = 1) (hg : g = 0 ∨ g = 1) (hh : h = 0 ∨ h = 1) : \
         a + b + c + d + e + f + g + h ≤ 8",
    );
    assert!(
        err.contains("case-split budget of 128 exhausted"),
        "the cap refusal must name the budget: {err}"
    );
}

/// Ordinary shapes past the old 32-split cap: two six-way disjunctions (35
/// splits) and one 34-way disjunction (33). Pinned Lean 4.8 proves both.
#[test]
fn test_omega_wide_disjunctions_within_cap_prove() {
    assert_proves(
        "g26_six_by_six",
        "(a b : Nat) (ha : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6) \
         (hb : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6) : a + b ≤ 12",
    );
    let wide: Vec<String> = (1..=34).map(|k| format!("c = {k}")).collect();
    assert_proves(
        "g26_wide34",
        &format!("(c : Nat) (hc : {}) : c ≤ 34", wide.join(" ∨ ")),
    );
}

/// Compound GOALS: Lean's omega negates the goal into a hypothesis first
/// (`falseOrByContra`), so `∨` / `∧` goals are read like hypotheses.
#[test]
fn test_omega_compound_goal_proves_and_false_refused() {
    assert_proves(
        "g26_goalor",
        "(a b : Nat) (h : a ≤ b ∨ b ≤ a) (h2 : a ≠ b) : a < b ∨ b < a",
    );
    assert_refuses(
        "g26_goalorn",
        "(a b : Nat) (h : a ≤ b ∨ b ≤ a) : a < b ∨ b < a",
    );
    assert_proves("g26_goaland", "(a : Nat) (h : a = 2) : a ≤ 2 ∧ a ≥ 2");
    assert_refuses("g26_goalandn", "(a : Nat) (h : a = 2) : a ≤ 2 ∧ a ≥ 3");
}

/// Hypotheses Lean's `omega` never collects — `False`, `P` beside `¬P`, a
/// `False` under `∧`, a written-out `p → False` — must not close a goal once
/// the layer acts (review of 2b1b305d9). Pinned Lean 4.8.0 refuses every row
/// ("omega could not prove the goal"). Before the fix each passed: the layer
/// ran the pipeline on `False` with every local in view.
#[test]
fn test_omega_unread_hypotheses_never_close_a_split_goal() {
    assert_refuses(
        "g26_hf_or",
        "(c : Nat) (hf : False) (h : c = 0 ∨ c = 5) : c ≤ 1",
    );
    assert_refuses("g26_hf_ne", "(x : Nat) (hf : False) (h : x ≠ 3) : x ≤ 1");
    assert_refuses(
        "g26_pnp_and",
        "(x : Nat) (P : Prop) (hp : P) (hnp : ¬ P) (h : x ≤ 2 ∧ x ≥ 0) : x ≤ 1",
    );
    assert_refuses(
        "g26_pnp_or",
        "(c : Nat) (P : Prop) (hp : P) (hnp : ¬P) (h : c = 0 ∨ c = 5) : c ≤ 1",
    );
    assert_refuses(
        "g26_and_false",
        "(c : Nat) (h : c = 1 ∨ c = 2 ∧ False) : c ≤ 1",
    );
    assert_refuses(
        "g26_false_and",
        "(c : Nat) (h : c = 1 ∨ (False ∧ c = 2)) : c ≤ 1",
    );
    assert_refuses(
        "g26_imp_false",
        "(c : Nat) (h : c = 0 ∨ c = 5) (h2 : c = 5 → False) : c ≤ 1",
    );
    // ... while the `Not` spelling of the same fact is read, as Lean reads it.
    assert_proves(
        "g26_not_eq",
        "(c : Nat) (h : c = 0 ∨ c = 5) (h2 : ¬ c = 5) : c ≤ 1",
    );
    assert_proves(
        "g26_ne_or",
        "(c : Nat) (h : c = 0 ∨ c = 5) (h2 : c ≠ 5) : c ≤ 1",
    );
}

/// Lean's `omega` reads `x * y`, `c * c`, `2 ^ c` as ATOMS, so a fact a
/// split hands it about `x` says nothing about `x * y`. Pinned Lean 4.8.0
/// refuses every REFUSE row with a counterexample over such an atom; Clean
/// proved them once a branch's equality reached a lane that multiplies out.
#[test]
fn test_omega_split_equalities_never_reach_inside_products() {
    assert_refuses("g26_mul_or", "(x y : Nat) (h : x = 0 ∨ y = 0) : x * y = 0");
    assert_refuses(
        "g26_mul_or3",
        "(x y : Nat) (h : x = 0 ∨ x = 1) (hy : y = 3) : x * y ≤ 3",
    );
    assert_refuses("g26_sq_or", "(c : Nat) (h : c = 0 ∨ c = 1) : c * c ≤ 1");
    assert_refuses("g26_pow_or", "(c : Nat) (h : c = 0 ∨ c = 1) : 2 ^ c ≤ 2");
    assert_refuses("g26_mul_and", "(x y : Nat) (h : x = 0 ∧ y = 3) : x * y ≤ 3");
    // A product beside the split is dropped, not trusted: Lean proves this
    // without it, and so does Clean.
    assert_proves(
        "g26_mul_beside",
        "(c : Nat) (h : c = 1 ∨ c = 2) (hx : c * c = 5) : c ≤ 2",
    );
}

/// Known divergence, safe side: Lean proves `x * y ≤ 1` from
/// `x * y = 0 ∨ x * y = 1` by reading `x * y` as one atom. Clean's split layer
/// refuses any goal with a product of atoms, since its pipeline does not keep
/// Lean's atom reading. Fails loudly the day the layer learns atoms.
#[test]
fn test_omega_split_product_atom_goal_still_refused() {
    let err = assert_refuses(
        "g26_atom_goal",
        "(x y : Nat) (h : x * y = 0 ∨ x * y = 1) : x * y ≤ 1",
    );
    assert!(err.contains("omega"), "the refusal must name omega: {err}");
}

/// Lean's `omega` opens with `falseOrByContra (useClassical := false)`: a
/// goal is negated only when it has a `Decidable` instance, and otherwise
/// dropped. Pinned Lean 4.8.0 refuses the undecidable rows and proves the row
/// with `[Decidable P]`.
#[test]
fn test_omega_undecidable_compound_goal_is_dropped_like_lean() {
    assert_refuses(
        "g26_goal_pl",
        "(P : Prop) (c : Nat) (h : c ≤ 1) : P ∨ c ≤ 1",
    );
    assert_refuses(
        "g26_goal_pr",
        "(P : Prop) (c : Nat) (h : c ≤ 1) : c ≤ 1 ∨ P",
    );
    assert_refuses(
        "g26_goal_pimp",
        "(P : Prop) (c : Nat) (h : c = 3) (h2 : c = 3 → P) : P ∨ c = 3",
    );
    assert_proves(
        "g26_goal_dec",
        "(P : Prop) [Decidable P] (c : Nat) (h : c ≤ 1) : P ∨ c ≤ 1",
    );
    assert_refuses(
        "g26_goal_decn",
        "(P : Prop) [Decidable P] (c : Nat) (h : c ≤ 2) : P ∨ c ≤ 1",
    );
}

/// `≠` over `Int` is split as over `Nat` (`Int.lt_trichotomy`, restated with
/// `LT.lt`). Pinned Lean 4.8.0 proves the PROVE rows and refuses the twin.
#[test]
fn test_omega_int_disequality_proves_and_false_refused() {
    assert_proves(
        "g26_int_ne_false",
        "(c : Int) (h : c ≠ 0) (h1 : c ≤ 0) (h2 : c ≥ 0) : False",
    );
    assert_proves("g26_int_ne", "(c : Int) (h : c ≠ 0) (h2 : c ≥ 0) : c > 0");
    assert_refuses("g26_int_nen", "(c : Int) (h : c ≠ 0) (h2 : c ≥ 0) : c > 1");
}

/// KNOWN DIVERGENCE, root level, older than G26: with no propositional
/// hypothesis for the layer to read, the linear pipeline itself proves these
/// by pushing an equality into a product, where pinned Lean 4.8.0 refuses both
/// (`x * y` is an atom to its `omega`). Both statements are true, so this is
/// an acceptance Lean lacks, not an unsound one. Filed in `docs/DECISIONS.md`
/// (R47; gap G60). Fails loudly the day the pipeline keeps Lean's
/// atoms: then each becomes a REFUSE row.
#[test]
fn test_omega_root_equality_into_product_known_divergence() {
    for (name, sig) in [
        (
            "g26_root_mul_eq",
            "(x y : Nat) (h : x = 0) (hy : y = 3) : x * y ≤ 3",
        ),
        (
            "g26_root_mul_ne",
            "(x y : Nat) (h : x ≠ 0) (hy : y = 0) : x * y = 0",
        ),
    ] {
        let code = format!("theorem {name} {sig} := by omega\n");
        let (env, results) = elab(&code);
        let errors: Vec<_> = results.iter().filter_map(|r| r.as_ref().err()).collect();
        assert!(
            errors.is_empty() && env.get_const(&Name::from_string(name)).is_some(),
            "{name}: the root divergence CLOSED (Clean now refuses `{sig}` like pinned Lean); \
             make it a REFUSE row and close the follow-up in docs/DECISIONS.md: {errors:?}"
        );
    }
}

/// KNOWN DIVERGENCE, safe side: pinned Lean 4.8.0 proves both, and Clean's
/// split layer reaches a leaf it cannot close because of the linear
/// pipeline's own replay defect — `¬(c ≤ 1)` beside an equality (`c = 0 ∧
/// ¬(c ≤ 1) ⊢ False` already fails at the root, with no layer involved): the
/// pipeline finds the contradiction and builds no kernel term. Fails loudly the
/// day that replay closes; then both become PROVE rows.
#[test]
fn test_omega_split_leaf_replay_defect_still_refused() {
    for (name, sig) in [
        (
            "g26_iff_chain5",
            "(a b c d e f : Nat) (h1 : a = 1 ↔ b = 1) (h2 : b = 1 ↔ c = 1) \
             (h3 : c = 1 ↔ d = 1) (h4 : d = 1 ↔ e = 1) (h5 : e = 1 ↔ f = 1) \
             (ha : a = 1) : f ≤ 1",
        ),
        (
            "g26_iff_ne_goal",
            "(c : Nat) (h : c = 0 ↔ c ≠ 5) (h2 : c ≤ 5) : c ≤ 1 ∨ c = 5",
        ),
    ] {
        let err = assert_refuses(name, sig);
        assert!(
            err.contains("has no kernel proof"),
            "{name}: expected the pipeline's replay refusal, got: {err}"
        );
    }
}
