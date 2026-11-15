// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Brick B5 of `designs/2026-10-08-mutual-nested-recursion.md` (ledger class
//! (92)) and its neighbours, through the production entry
//! `elaborate_decl_and_register`:
//!
//! - `cases` / `rcases` / `obtain` on a NESTED or MUTUAL inductive, whose
//!   kernel `casesOn` takes every member's and auxiliary container's motive
//!   and minors (`tactic/cases_on_spine.rs`);
//! - class (80): `cases x` reverts the hypotheses that mention `x` and
//!   re-introduces them per case (`tactic/major_dependents.rs`);
//! - gap G22: `induction x` generalizes them into the motive, with the
//!   `generalizing` variables, in context order;
//! - Lean's refusals of `induction` on a nested family and of a redundant
//!   `generalizing` argument.
//!
//! Fixtures and verdicts as in `mutual_lift.rs` (`tests/fixtures/mutual_nested/`,
//! `verdicts.json` re-derived from the pinned Lean binaries by
//! `scripts/mutual_nested_verdicts.py`). Every accepted shape carries a
//! Lean-refused twin.

use super::mutual_lift_tests::{
    accepts_all, fixture, fresh, lean_accepts, refuses_last, value_constants,
};
use super::*;
use clean_kernel::env::Environment;

/// The proof of `name` mentions every constant in `wanted`.
fn proof_mentions(env: &Environment, name: &str, wanted: &[&str]) {
    let consts = value_constants(env, name);
    for c in wanted {
        assert!(
            consts.contains(&Name::from_string(c)),
            "`{name}`'s proof applies `{c}`: {consts:?}"
        );
    }
}

/// Every form of case split on the nested `P` (and on `C`, whose `record`
/// field nests through the pair `String × C`): `cases … with`, bare `cases`
/// with bullets, `case` tags, `rcases`, `obtain`, `<;>`.
#[test]
fn test_cases_on_nested_inductive_every_form_elaborates_b5() {
    let f = fixture!("cases_nested.lean");
    assert!(lean_accepts(f.0));
    let mut env = fresh();
    accepts_all(&mut env, f);
    // The kernel's own nested `casesOn`, with its auxiliary `List P` slot
    // filled by the constant `PUnit` motive and `PUnit.unit` minors.
    proof_mentions(&env, "with_alts", &["P.casesOn", "PUnit", "PUnit.unit"]);
    proof_mentions(&env, "pair_intermediate", &["C.casesOn", "PUnit"]);
}

#[test]
fn test_cases_on_nested_inductive_false_claim_is_refused_b5() {
    let f = fixture!("cases_nested_twin.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    refuses_last(&mut env, f, "with_alts_twin");
}

#[test]
fn test_cases_on_mutual_inductive_member_elaborates_b5() {
    let f = fixture!("cases_mutual.lean");
    assert!(lean_accepts(f.0));
    let mut env = fresh();
    accepts_all(&mut env, f);
    proof_mentions(&env, "mutual_second", &["B.casesOn", "PUnit"]);
}

#[test]
fn test_cases_on_mutual_inductive_false_claim_is_refused_b5() {
    let f = fixture!("cases_mutual_twin.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    refuses_last(&mut env, f, "mutual_twin");
}

/// Class (80): the hypothesis `h` that mentions the eliminated variable is
/// about each constructor afterwards, under its own name, also when it and
/// the major were introduced by `intro`.
#[test]
fn test_cases_reintroduces_dependent_hypotheses_class_80() {
    let f = fixture!("cases_dependent.lean");
    assert!(lean_accepts(f.0));
    let mut env = fresh();
    accepts_all(&mut env, f);
}

#[test]
fn test_cases_dependent_hypothesis_does_not_prove_another_case_class_80() {
    let f = fixture!("cases_dependent_twin.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    refuses_last(&mut env, f, "bool_dep_twin");
}

/// G22: `induction` generalizes a hypothesis that mentions the target and
/// re-introduces it per case; with `generalizing n` the induction hypothesis
/// reads `∀ n, rest.length = n → …`, context order.
#[test]
fn test_induction_generalizes_dependent_hypotheses_g22() {
    let f = fixture!("induction_dependent.lean");
    assert!(lean_accepts(f.0));
    let mut env = fresh();
    accepts_all(&mut env, f);
}

#[test]
fn test_induction_hypothesis_premise_order_is_context_order_g22() {
    let f = fixture!("induction_dependent_twin.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    refuses_last(&mut env, f, "ih_order_twin");
}

/// Lean 4.8 refuses `induction` on a nested family (its recursor has several
/// motives); Clean refuses it with Lean's message.
#[test]
fn test_induction_on_nested_inductive_is_refused_as_lean_does() {
    let f = fixture!("induction_nested_refused.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    let err = refuses_last(&mut env, f, "induction_nested");
    assert!(
        err.contains("'induction' tactic does not support nested inductive types"),
        "Lean's refusal: {err}"
    );
}

/// Lean 4.8 refuses a `generalizing` argument the target's dependents already
/// include.
#[test]
fn test_induction_redundant_generalizing_argument_is_refused_as_lean_does() {
    let f = fixture!("induction_generalizing_unnecessary.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    let err = refuses_last(&mut env, f, "generalizing_unnecessary");
    assert!(
        err.contains("unnecessary 'generalizing' argument, variable 'h0'"),
        "Lean's refusal: {err}"
    );
}

/// G66: a name given inside a focused block (`rename_i` under `·`, a `case`
/// binder) reaches the terms that block elaborates; before, the block's
/// bridge held the local under its old name only.
#[test]
fn test_names_given_inside_a_focused_block_resolve_g66() {
    let f = fixture!("cases_rename_block.lean");
    assert!(lean_accepts(f.0));
    let mut env = fresh();
    accepts_all(&mut env, f);
}

/// G67: Lean refuses `rename_i` with more names than inaccessible locals.
#[test]
fn test_rename_i_with_too_many_names_is_refused_g67() {
    let f = fixture!("cases_rename_i_too_many.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    let err = refuses_last(&mut env, f, "rename_none");
    assert!(
        err.contains("too many variable names provided"),
        "Lean's refusal: {err}"
    );
}

/// B6: a `mutual` block's members are auxiliary declarations while their
/// bodies elaborate — a body that NAMES a sibling reaches it …
#[test]
fn test_mutual_member_named_by_a_sibling_resolves_b6() {
    let f = fixture!("aux_decl_named.lean");
    assert!(lean_accepts(f.0));
    let mut env = fresh();
    accepts_all(&mut env, f);
}

/// … but `assumption` does not see it (Lean: "tactic 'assumption' failed");
/// before B6 Clean closed `r1` with `r2` and registered both.
#[test]
fn test_assumption_skips_mutual_siblings_b6() {
    let f = fixture!("aux_decl_hidden.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    let err = refuses_last(&mut env, f, "r1");
    assert!(err.contains("assumption"), "refused by `assumption`: {err}");
}

/// … nor does `simp_all` (Lean: "simp_all made no progress").
#[test]
fn test_simp_all_skips_mutual_siblings_b6() {
    let f = fixture!("aux_decl_hidden_simp_all.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    refuses_last(&mut env, f, "q1");
}

/// Block 13 end to end (trust-ir `Pred.beq_eq` / `Pred.listBeq_eq`, its
/// leaf made nullary so the shape needs no `Nat` lemma the builtin prelude
/// spells differently): nested `cases a <;> cases b` (B5), `h` re-introduced
/// per case (class (80)), `simp only … at h` with ι on each case, sibling
/// calls lifted, `subst q`, and the siblings hidden from tactics (B6). With
/// its non-structural twin.
#[test]
fn test_tactic_form_theorem_block_over_nested_type_b6() {
    let f = fixture!("tac_form.lean");
    assert!(lean_accepts(f.0));
    let mut env = fresh();
    accepts_all(&mut env, f);
}

#[test]
fn test_tactic_form_theorem_block_non_structural_call_is_refused_b6() {
    let f = fixture!("tac_form_neg.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    refuses_last(&mut env, f, "P.beq_eq");
}

/// Class (81): `cases h` on an equation goes on where `subst` cannot —
/// distinct constructors close the goal, equal constructors leave their
/// fields' equations — on `List`, `Except` (heterogeneous `noConfusion`) and
/// the nested `P` (classic `noConfusion`).
#[test]
fn test_cases_on_constructor_equations_class_81() {
    let f = fixture!("cases_ctor_eq.lean");
    assert!(lean_accepts(f.0));
    let mut env = fresh();
    accepts_all(&mut env, f);
}

#[test]
fn test_cases_on_constructor_equation_does_not_identify_tails_class_81() {
    let f = fixture!("cases_ctor_eq_twin.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    refuses_last(&mut env, f, "ctor_inj_twin");
}

/// G70: `simp` rewrites an equation between applications of one constructor
/// to its fields' equations (Lean's `C.injEq`): `Option`/`Prod` (parameterized,
/// heterogeneous `noConfusion`) and a user inductive in the goal.
#[test]
fn test_simp_constructor_injectivity_g70() {
    let f = fixture!("simp_injeq.lean");
    assert!(lean_accepts(f.0));
    let mut env = fresh();
    accepts_all(&mut env, f);
}

#[test]
fn test_simp_constructor_injectivity_states_the_fields_g70() {
    let f = fixture!("simp_injeq_twin.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    refuses_last(&mut env, f, "inj_twin");
}

/// `injEq` lemmas are simp-set members: `simp only []` does not use them.
#[test]
fn test_simp_only_does_not_use_constructor_injectivity_g70() {
    let f = fixture!("simp_injeq_only_twin.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    refuses_last(&mut env, f, "inj_only");
}

/// G67: `this` (an unnamed `have`) is accessible, as in Lean.
#[test]
fn test_rename_i_does_not_rename_this_g67() {
    let f = fixture!("cases_rename_i_this.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    let err = refuses_last(&mut env, f, "rename_this");
    assert!(
        err.contains("too many variable names provided"),
        "Lean's refusal: {err}"
    );
}

/// `simp … at h` on every case of a `cases` (`<;>`, `all_goals`): the
/// simplified hypothesis takes its goal's binder base as its id, as `intro`
/// and `have` do. With the global counter the second goal's id named no
/// binder at its depth and the proof was refused as capturing an
/// out-of-scope local (block 13's `cases a <;> cases b <;> simp … at h`).
#[test]
fn test_simp_at_hypothesis_across_case_goals() {
    let f = fixture!("cases_simp_at_all_goals.lean");
    assert!(lean_accepts(f.0));
    let mut env = fresh();
    accepts_all(&mut env, f);
}

#[test]
fn test_simp_at_hypothesis_across_case_goals_twin() {
    let f = fixture!("cases_simp_at_all_goals_twin.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    refuses_last(&mut env, f, "z_twin");
}

/// Lean's `subst x` with `x` a variable (block 13's `subst q`): the oldest
/// equation for `x` eliminates `x`, on either side.
#[test]
fn test_subst_by_variable_finds_its_equation() {
    let f = fixture!("subst_var.lean");
    assert!(lean_accepts(f.0));
    let mut env = fresh();
    accepts_all(&mut env, f);
}

#[test]
fn test_subst_by_variable_without_equation_is_refused() {
    let f = fixture!("subst_var_twin.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    let err = refuses_last(&mut env, f, "sv_twin");
    assert!(
        err.contains("did not find equation for eliminating"),
        "Lean's refusal: {err}"
    );
}

/// `refine`'s holes see the goal's context only (trust-ir's
/// `Sem.bindFreshPair_ok`): a hypothesis `cases h` / `subst h` consumed and a
/// `mutual` block's hidden sibling are not revived in the new goals. Reviving
/// one minted a fresh local outside the goal's creation scope, and the
/// assignment was refused ("assignment violates its creation scope").
#[test]
fn test_refine_holes_do_not_capture_consumed_locals() {
    let f = fixture!("refine_after_consumed.lean");
    assert!(lean_accepts(f.0));
    let mut env = fresh();
    accepts_all(&mut env, f);
}

#[test]
fn test_refine_holes_after_cases_keep_the_substituted_values() {
    let f = fixture!("refine_after_consumed_twin.lean");
    assert!(!lean_accepts(f.0));
    let mut env = fresh();
    let err = refuses_last(&mut env, f, "run_ok_twin");
    // Refused for the claim, as Lean refuses it — not by the bridge.
    assert!(
        !err.contains("creation scope"),
        "refused by the hole bridge, not by the claim: {err}"
    );
}
