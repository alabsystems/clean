// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core goal and hypothesis clausification tests.

use super::super::*;
use super::support::mk_eq;
use clean_kernel::Level;

#[test]
fn test_clausify_equality_goal() {
    let mut clausifier = GoalClausifier::new();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let goal = mk_eq(nat, a, b);

    let (clauses, _map) = clausifier.clausify_goal(&goal);
    assert_eq!(clauses.len(), 1, "equality goal should produce 1 clause");
    assert_eq!(
        clauses[0].len(),
        1,
        "the clause should have 1 literal (a != b)"
    );
    assert!(
        !clauses[0][0].positive,
        "negated equality should be negative"
    );
}

#[test]
fn test_clausify_disequality_goal() {
    let mut clausifier = GoalClausifier::new();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Ne"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            a,
        ),
        b,
    );

    let (clauses, _map) = clausifier.clausify_goal(&goal);
    assert_eq!(clauses.len(), 1);
    assert_eq!(clauses[0].len(), 1);
    assert!(
        clauses[0][0].positive,
        "negated disequality should be positive (a = b)"
    );
}

#[test]
fn test_clausify_conjunction_goal() {
    let mut clausifier = GoalClausifier::new();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let eq_a_a = mk_eq(nat.clone(), a.clone(), a);
    let eq_b_b = mk_eq(nat, b.clone(), b);

    let goal = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), eq_a_a),
        eq_b_b,
    );

    let (clauses, _map) = clausifier.clausify_goal(&goal);
    assert_eq!(clauses.len(), 1, "negated conjunction should be one clause");
    assert_eq!(clauses[0].len(), 2, "should have 2 literals");
    assert!(
        clauses[0].iter().all(|literal| !literal.positive),
        "both literals should be negative"
    );
}

#[test]
fn test_clausify_disjunction_goal() {
    let mut clausifier = GoalClausifier::new();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let eq_a_a = mk_eq(nat.clone(), a.clone(), a);
    let eq_b_b = mk_eq(nat, b.clone(), b);

    let goal = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), eq_a_a),
        eq_b_b,
    );

    let (clauses, _map) = clausifier.clausify_goal(&goal);
    assert_eq!(
        clauses.len(),
        2,
        "negated disjunction should produce 2 clauses"
    );
    for clause in &clauses {
        assert_eq!(clause.len(), 1, "each clause should have 1 literal");
        assert!(!clause[0].positive, "literal should be negative");
    }
}

#[test]
fn test_clausify_implication_goal() {
    let mut clausifier = GoalClausifier::new();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let eq_a_a = mk_eq(nat.clone(), a.clone(), a);
    let eq_b_b = mk_eq(nat, b.clone(), b);

    let goal = Expr::pi(BinderInfo::Default, eq_a_a, eq_b_b);

    let (clauses, _map) = clausifier.clausify_goal(&goal);
    assert_eq!(
        clauses.len(),
        2,
        "negated implication should produce 2 clauses"
    );
    let positives = clauses
        .iter()
        .flat_map(|clause| clause.iter())
        .filter(|literal| literal.positive)
        .count();
    let negatives = clauses
        .iter()
        .flat_map(|clause| clause.iter())
        .filter(|literal| !literal.positive)
        .count();
    assert_eq!(positives, 1, "should have one positive literal (P)");
    assert_eq!(negatives, 1, "should have one negative literal (!Q)");
}

#[test]
fn test_clausify_populates_symbol_map() {
    let mut clausifier = GoalClausifier::new();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let goal = mk_eq(nat, a, b);

    let (clauses, _) = clausifier.clausify_goal(&goal);
    assert!(!clauses.is_empty());

    let symbol_map = clausifier.into_symbol_map();
    let lit = &clauses[0][0];
    let lhs = symbol_map
        .term_to_expr(&lit.lhs)
        .expect("lhs should be mapped in symbol_map");
    let rhs = symbol_map
        .term_to_expr(&lit.rhs)
        .expect("rhs should be mapped in symbol_map");
    assert_ne!(
        lhs, rhs,
        "symbol_map should recover distinct lhs/rhs for a != b literal"
    );
}

#[test]
fn test_clausify_double_negation() {
    let mut clausifier = GoalClausifier::new();
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let eq_a_a = mk_eq(nat, a.clone(), a);

    let goal = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        Expr::app(Expr::const_(Name::from_string("Not"), vec![]), eq_a_a),
    );

    let (clauses, _map) = clausifier.clausify_goal(&goal);
    assert_eq!(clauses.len(), 1);
    assert_eq!(clauses[0].len(), 1);
    assert!(!clauses[0][0].positive, "should be negative");
}

#[test]
fn test_clausify_true_goal() {
    let mut clausifier = GoalClausifier::new();
    let goal = Expr::const_(Name::from_string("True"), vec![]);

    let (clauses, _map) = clausifier.clausify_goal(&goal);
    assert!(
        clauses.iter().any(|clause| clause.is_empty()),
        "negated True should produce at least one empty clause (for UNSAT), got {} non-empty clauses",
        clauses.len()
    );
}

#[test]
fn test_clausify_false_goal() {
    let mut clausifier = GoalClausifier::new();
    let goal = Expr::const_(Name::from_string("False"), vec![]);

    let (clauses, _map) = clausifier.clausify_goal(&goal);
    let has_empty_clause = clauses.iter().any(|clause| clause.is_empty());
    assert!(
        !has_empty_clause,
        "negated False should not produce empty clauses (would incorrectly prove False)"
    );
}

#[test]
fn test_clausify_true_hypothesis() {
    let mut clausifier = GoalClausifier::new();
    let hyp = Expr::const_(Name::from_string("True"), vec![]);
    let fvar = FVarId::new(999);

    let clauses = clausifier.clausify_hypothesis(&hyp, 1, fvar);
    let has_empty_clause = clauses.iter().any(|clause| clause.is_empty());
    assert!(
        !has_empty_clause,
        "True hypothesis should not produce empty clauses"
    );
}

#[test]
fn test_clausify_false_hypothesis() {
    let mut clausifier = GoalClausifier::new();
    let hyp = Expr::const_(Name::from_string("False"), vec![]);
    let fvar = FVarId::new(998);

    let clauses = clausifier.clausify_hypothesis(&hyp, 2, fvar);
    assert!(
        clauses.iter().any(|clause| clause.is_empty()),
        "False hypothesis should produce at least one empty clause, got {} non-empty clauses",
        clauses.len()
    );
}

#[test]
fn test_clausify_atomic_proposition_goal() {
    let mut clausifier = GoalClausifier::new();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let p_a = Expr::app(p, a);

    let (clauses, _map) = clausifier.clausify_goal(&p_a);

    assert_eq!(
        clauses.len(),
        1,
        "negated atomic proposition should produce 1 clause"
    );
    assert_eq!(clauses[0].len(), 1);
    assert!(
        !clauses[0][0].positive,
        "negated atomic should be negative (P(a) != True)"
    );

    match &clauses[0][0].rhs {
        Term::Const(_) => {}
        other => panic!("expected True constant as rhs, got {:?}", other),
    }
}

#[test]
fn test_clausify_hypothesis_equality() {
    let mut clausifier = GoalClausifier::new();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let hyp = mk_eq(nat, a, b);

    let fvar_id = FVarId::new(42);
    let clauses = clausifier.clausify_hypothesis(&hyp, 0, fvar_id);

    assert_eq!(
        clauses.len(),
        1,
        "equality hypothesis should produce 1 clause"
    );
    assert_eq!(clauses[0].len(), 1);
    assert!(
        clauses[0][0].positive,
        "hypothesis equality should be positive"
    );
}

#[test]
fn test_clausify_hypothesis_conjunction() {
    let mut clausifier = GoalClausifier::new();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);

    let eq_a_b = mk_eq(nat.clone(), a, b.clone());
    let eq_b_c = mk_eq(nat, b, c);

    let hyp = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), eq_a_b),
        eq_b_c,
    );

    let fvar_id = FVarId::new(43);
    let clauses = clausifier.clausify_hypothesis(&hyp, 1, fvar_id);

    assert_eq!(
        clauses.len(),
        2,
        "conjunction hypothesis should produce 2 clauses"
    );
    for clause in &clauses {
        assert_eq!(clause.len(), 1, "each clause should be a unit clause");
        assert!(clause[0].positive, "hypothesis literals should be positive");
    }
}

/// Verify that CNF clause budget prevents exponential blowup.
///
/// The formula `(A₁ ∧ B₁) ∨ (A₂ ∧ B₂) ∨ ... ∨ (Aₙ ∧ Bₙ)` produces 2ⁿ
/// clauses under naive distributive CNF. With n=20, that's ~1M clauses.
/// The budget (MAX_CNF_CLAUSES = 10,000) must cap this.
#[test]
fn test_cnf_clause_budget_prevents_exponential_blowup() {
    let n = 20; // 2^20 = 1,048,576 without budget
    let mut clausifier = GoalClausifier::new();

    // Build: (A₁ ∧ B₁) ∨ (A₂ ∧ B₂) ∨ ... ∨ (Aₙ ∧ Bₙ)
    // As a goal, the clausifier negates this to produce CNF.
    // ¬((A₁∧B₁) ∨ ...) = (¬A₁ ∨ ¬B₁) ∧ ... ∧ (¬Aₙ ∨ ¬Bₙ) — only n clauses.
    // So we use it as a hypothesis instead (not negated), where the Or-of-And
    // pattern hits the exponential distribution path directly.
    let mut or_expr = {
        let a = Expr::const_(Name::from_string("A_0"), vec![]);
        let b = Expr::const_(Name::from_string("B_0"), vec![]);
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("And"), vec![]), a),
            b,
        )
    };
    for i in 1..n {
        let a = Expr::const_(Name::from_string(&format!("A_{i}")), vec![]);
        let b = Expr::const_(Name::from_string(&format!("B_{i}")), vec![]);
        let and_i = Expr::app(
            Expr::app(Expr::const_(Name::from_string("And"), vec![]), a),
            b,
        );
        or_expr = Expr::app(
            Expr::app(Expr::const_(Name::from_string("Or"), vec![]), or_expr),
            and_i,
        );
    }

    let fvar = FVarId::new(100);
    let clauses = clausifier.clausify_hypothesis(&or_expr, 0, fvar);

    // Without budget: 2^20 = 1,048,576 clauses
    // With budget: capped at MAX_CNF_CLAUSES (10,000)
    assert!(
        clauses.len() <= 10_000,
        "CNF clause budget should cap exponential blowup, got {} clauses",
        clauses.len()
    );
    assert!(
        clauses.len() >= 100,
        "should still produce meaningful clause set, got {} clauses",
        clauses.len()
    );
}
