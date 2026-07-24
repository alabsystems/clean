// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::support::semantic::register_int_var;
use super::{
    attempt_reconstruction, Expr, ExprKind, Name, Proof, TermStore, TheoryLemmaKind,
    VariableMapping,
};

#[test]
fn test_theory_lemma_euf_transitivity_simple() {
    // EUF transitivity: {¬(a=b), ¬(b=c), a=c}
    // Should produce a proof using Classical.em + Eq.trans
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);

    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);
    let not_eq_ab = terms.mk_not(eq_ab);
    let not_eq_bc = terms.mk_not(eq_bc);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_eq_ab, not_eq_bc, eq_ac],
        TheoryLemmaKind::EufTransitive,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.total_steps, 1);
    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "EUF transitivity should be reconstructed, got {} with error: {:?}",
        result.stats.reconstructed_steps, result.stats.error,
    );
    let proof_term = result
        .proof_term
        .expect("EUF transitivity should produce a proof term");
    // The outermost constructor should be Or.rec (case split on Classical.em)
    let head = proof_term.get_app_fn();
    let actual_name = match head.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    };
    assert_eq!(
        actual_name.as_deref(),
        Some("Or.rec"),
        "EUF transitivity should use Or.rec on Classical.em; got {:?}",
        head
    );
}

#[test]
fn test_theory_lemma_euf_transitivity_two_step() {
    // EUF transitivity: {¬(a=b), a=b} (trivial: one negated + same positive)
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);

    let eq_ab = terms.mk_eq(a, b);
    let not_eq_ab = terms.mk_not(eq_ab);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_eq_ab, eq_ab],
        TheoryLemmaKind::EufTransitive,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "trivial EUF transitivity should be reconstructed, error: {:?}",
        result.stats.error,
    );
    let _ = result
        .proof_term
        .expect("trivial EUF transitivity should produce a proof term");
}

#[test]
fn test_theory_lemma_euf_transitivity_reversed() {
    // EUF transitivity with reversed order: {¬(b=c), ¬(a=b), a=c}
    // The chain ordering should handle out-of-order literals
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);

    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);
    let not_eq_ab = terms.mk_not(eq_ab);
    let not_eq_bc = terms.mk_not(eq_bc);

    let mut proof = Proof::new();
    // Note: literals in reverse order compared to chain
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_eq_bc, not_eq_ab, eq_ac],
        TheoryLemmaKind::EufTransitive,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "reversed EUF transitivity should be reconstructed, error: {:?}",
        result.stats.error,
    );
    let _ = result
        .proof_term
        .expect("reversed EUF transitivity should produce a proof term");
}

#[test]
fn test_theory_lemma_euf_transitivity_with_symm() {
    // EUF transitivity with symmetry needed: {¬(b=a), ¬(b=c), a=c}
    // Chain: a ← b → c needs Eq.symm on first edge
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);

    let eq_ba = terms.mk_eq(b, a); // b = a (needs symm for a → b)
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);
    let not_eq_ba = terms.mk_not(eq_ba);
    let not_eq_bc = terms.mk_not(eq_bc);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_eq_ba, not_eq_bc, eq_ac],
        TheoryLemmaKind::EufTransitive,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "EUF transitivity with symm should be reconstructed, error: {:?}",
        result.stats.error,
    );
    let _ = result
        .proof_term
        .expect("EUF transitivity with symm should produce a proof term");
}

#[test]
fn test_theory_lemma_resolution_chain() {
    // Theory lemma used as premise in resolution:
    // Step 0: TheoryLemma {¬(a=b), ¬(b=c), a=c}  (EUF transitivity)
    // Step 1: Assume {a=b}
    // Step 2: Resolution [{¬(b=c), a=c}] pivot=¬(a=b) on steps 0,1
    //
    // This verifies that theory lemma proofs unblock dependent resolution chains.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);

    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);
    let not_eq_ab = terms.mk_not(eq_ab);
    let not_eq_bc = terms.mk_not(eq_bc);

    let mut proof = Proof::new();
    let tl = proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_eq_ab, not_eq_bc, eq_ac],
        TheoryLemmaKind::EufTransitive,
    );

    // Assume a = b (as the equality itself, not negated)
    let eq_ab_clause = terms.mk_or(vec![eq_ab]);
    let h_assume = proof.add_assume(eq_ab_clause, None);

    // Resolve: {¬(a=b), ¬(b=c), a=c} + {a=b} → {¬(b=c), a=c}
    // Pivot: the literal a=b (not negated), found in h_assume; ¬(a=b) found in tl
    proof.add_resolution(vec![not_eq_bc, eq_ac], not_eq_ab, tl, h_assume);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.total_steps, 3);
    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(result.stats.resolution_steps, 1);
    assert!(
        result.stats.reconstructed_steps >= 3,
        "theory lemma + resolution should all be reconstructed, got {} with error: {:?}",
        result.stats.reconstructed_steps,
        result.stats.error,
    );
    let _ = result
        .proof_term
        .expect("theory lemma + resolution chain should produce a proof term");
}

#[test]
fn test_theory_lemma_euf_transitivity_positive_first() {
    // Regression: positive equality BEFORE negated equalities.
    // Clause: {a=c, ¬(a=b), ¬(b=c)} — positive equality at index 0.
    // Chain ordering must use clause_idx (not neg_eqs array index).
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let a = register_int_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_int_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_int_var(&mut terms, &mut map, "fvar_3", 3);

    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);
    let not_eq_ab = terms.mk_not(eq_ab);
    let not_eq_bc = terms.mk_not(eq_bc);

    let mut proof = Proof::new();
    // Positive equality first, then negated equalities
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![eq_ac, not_eq_ab, not_eq_bc],
        TheoryLemmaKind::EufTransitive,
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "positive-first EUF transitivity should be reconstructed, error: {:?}",
        result.stats.error,
    );
    let _ = result
        .proof_term
        .expect("positive-first EUF transitivity should produce a proof term");
}
