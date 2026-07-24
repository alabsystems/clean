// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct helper-contract tests for classify_prop, add_hypothesis_with_fvar,
//! and propositional clause-shape verification (#2116).
//!
//! These tests pin the branch-local contracts of bridge helpers rather than
//! re-running full reconstruction or prove() scenarios.

use super::test_helpers::setup_env;
use super::*;
use clean_kernel::FVarId;

// ========================================================================
// Expression builders for propositional forms
// ========================================================================

fn mk_and(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), a.clone()),
        b.clone(),
    )
}

fn mk_or(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), a.clone()),
        b.clone(),
    )
}

fn mk_not(a: &Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), a.clone())
}

fn mk_implies(p: &Expr, q: &Expr) -> Expr {
    // Implies is a non-dependent Pi: (p : Prop) → q
    Expr::pi(BinderInfo::Default, p.clone(), q.clone())
}

fn mk_true() -> Expr {
    Expr::const_(Name::from_string("True"), vec![])
}

fn mk_false() -> Expr {
    Expr::const_(Name::from_string("False"), vec![])
}

/// Opaque proposition atom (not recognized as any connective).
fn mk_atom(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

// ========================================================================
// classify_prop passthrough tests
// ========================================================================

#[test]
fn test_classify_prop_and_passthrough() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);
    let p = mk_atom("P");
    let q = mk_atom("Q");
    let expr = mk_and(&p, &q);
    match bridge.classify_prop(&expr) {
        LogicalForm::And(a, b) => {
            assert_eq!(a, p, "And lhs must be P");
            assert_eq!(b, q, "And rhs must be Q");
        }
        other => panic!("Expected And, got {other:?}"),
    }
}

#[test]
fn test_classify_prop_or_passthrough() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);
    let p = mk_atom("P");
    let q = mk_atom("Q");
    let expr = mk_or(&p, &q);
    match bridge.classify_prop(&expr) {
        LogicalForm::Or(a, b) => {
            assert_eq!(a, p, "Or lhs must be P");
            assert_eq!(b, q, "Or rhs must be Q");
        }
        other => panic!("Expected Or, got {other:?}"),
    }
}

#[test]
fn test_classify_prop_not_passthrough() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);
    let p = mk_atom("P");
    let expr = mk_not(&p);
    match bridge.classify_prop(&expr) {
        LogicalForm::Not(inner) => {
            assert_eq!(inner, p, "Not inner must be P");
        }
        other => panic!("Expected Not, got {other:?}"),
    }
}

#[test]
fn test_classify_prop_implies_passthrough() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);
    let p = mk_atom("P");
    let q = mk_atom("Q");
    let expr = mk_implies(&p, &q);
    match bridge.classify_prop(&expr) {
        LogicalForm::Implies(a, b) => {
            assert_eq!(a, p, "Implies antecedent must be P");
            assert_eq!(b, q, "Implies consequent must be Q");
        }
        other => panic!("Expected Implies, got {other:?}"),
    }
}

#[test]
fn test_classify_prop_true_passthrough() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);
    let expr = mk_true();
    assert!(
        matches!(bridge.classify_prop(&expr), LogicalForm::True),
        "True must classify as LogicalForm::True"
    );
}

#[test]
fn test_classify_prop_false_passthrough() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);
    let expr = mk_false();
    assert!(
        matches!(bridge.classify_prop(&expr), LogicalForm::False),
        "False must classify as LogicalForm::False"
    );
}

#[test]
fn test_classify_prop_opaque_atom_passthrough() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);
    let expr = mk_atom("SomeOpaqueProposition");
    match bridge.classify_prop(&expr) {
        LogicalForm::Atom(inner) => {
            assert_eq!(inner, expr, "Opaque atom must pass through unchanged");
        }
        other => panic!("Expected Atom, got {other:?}"),
    }
}

// ========================================================================
// add_hypothesis_with_fvar clause-shape tests
// ========================================================================

#[test]
fn test_add_hypothesis_and_recursively_adds_both_children() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let p = mk_atom("P");
    let q = mk_atom("Q");
    let and_pq = mk_and(&p, &q);
    let fvar = FVarId::new(100);

    let pre_clauses = bridge.smt.num_clauses();
    bridge
        .add_hypothesis_with_fvar(&and_pq, Some(fvar))
        .expect("add_hypothesis And should succeed");
    let post_clauses = bridge.smt.num_clauses();

    // And recursively adds both P and Q as separate unit clauses (atoms)
    assert!(
        post_clauses >= pre_clauses + 2,
        "And hypothesis must add at least 2 clauses (one per child), got {} new",
        post_clauses - pre_clauses
    );
    // FVarId should be recorded in prop_hypotheses
    assert!(
        bridge.prop_hypotheses.iter().any(|(id, _)| *id == fvar),
        "FVarId must be recorded in prop_hypotheses"
    );
}

#[test]
fn test_add_hypothesis_implies_adds_two_literal_clause() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let p = mk_atom("P");
    let q = mk_atom("Q");
    let implies_pq = mk_implies(&p, &q);

    let pre_clauses = bridge.smt.num_clauses();
    bridge
        .add_hypothesis(&implies_pq)
        .expect("add_hypothesis Implies should succeed");
    let post_clauses = bridge.smt.num_clauses();

    // Implies adds exactly one clause: [NOT(P), Q]
    assert_eq!(
        post_clauses - pre_clauses,
        1,
        "Implies must add exactly 1 clause (not-P or Q)"
    );
}

#[test]
fn test_add_hypothesis_not_adds_unit_negative_clause() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let p = mk_atom("P");
    let not_p = mk_not(&p);

    let pre_clauses = bridge.smt.num_clauses();
    bridge
        .add_hypothesis(&not_p)
        .expect("add_hypothesis Not should succeed");
    let post_clauses = bridge.smt.num_clauses();

    // Not adds exactly one unit clause: [NOT(P)]
    assert_eq!(
        post_clauses - pre_clauses,
        1,
        "Not must add exactly 1 unit negative clause"
    );
}

#[test]
fn test_add_hypothesis_false_sets_unsat() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let false_expr = mk_false();

    bridge
        .add_hypothesis(&false_expr)
        .expect("add_hypothesis False should succeed");

    // False adds an empty clause. The CDCL solver handles empty clauses by
    // setting is_unsat = true without storing them in the clause list (the
    // empty clause is absorbed, not counted). Verify via prove() returning
    // an UNSAT-backed result against a fully declared goal so the lossy-atoms
    // guard from #2829 does not downgrade the outcome to Unknown.
    let goal = make_eq(
        Expr::const_(Name::from_string("A"), vec![]),
        Expr::const_(Name::from_string("a"), vec![]),
        Expr::const_(Name::from_string("b"), vec![]),
    );
    let result = bridge.prove(&goal);
    match result {
        Ok(SmtVerificationResult::Verified(_)) | Ok(SmtVerificationResult::Unverified { .. }) => {
            // Expected: empty clause -> UNSAT -> Verified or Unverified
        }
        other => panic!("False hypothesis should make problem UNSAT, got: {other:?}"),
    }
}

#[test]
fn test_add_hypothesis_or_adds_two_literal_clause() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let p = mk_atom("P");
    let q = mk_atom("Q");
    let or_pq = mk_or(&p, &q);

    let pre_clauses = bridge.smt.num_clauses();
    bridge
        .add_hypothesis(&or_pq)
        .expect("add_hypothesis Or should succeed");
    let post_clauses = bridge.smt.num_clauses();

    // Or adds exactly one clause: [P, Q]
    assert_eq!(
        post_clauses - pre_clauses,
        1,
        "Or must add exactly 1 clause (P or Q)"
    );
}

#[test]
fn test_add_hypothesis_true_is_noop() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let true_expr = mk_true();

    let pre_clauses = bridge.smt.num_clauses();
    bridge
        .add_hypothesis(&true_expr)
        .expect("add_hypothesis True should succeed");
    let post_clauses = bridge.smt.num_clauses();

    // True is a no-op — carries no information
    assert_eq!(post_clauses, pre_clauses, "True must not add any clauses");
}

#[test]
fn test_add_hypothesis_atom_adds_unit_positive_clause() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let p = mk_atom("P");

    let pre_clauses = bridge.smt.num_clauses();
    bridge
        .add_hypothesis(&p)
        .expect("add_hypothesis Atom should succeed");
    let post_clauses = bridge.smt.num_clauses();

    // Atom fallback adds exactly one unit positive clause
    assert_eq!(
        post_clauses - pre_clauses,
        1,
        "Atom must add exactly 1 unit positive clause"
    );
}

#[test]
fn test_add_hypothesis_with_fvar_records_in_prop_hypotheses() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let p = mk_atom("P");
    let fvar = FVarId::new(42);

    bridge
        .add_hypothesis_with_fvar(&p, Some(fvar))
        .expect("add_hypothesis with fvar should succeed");

    assert_eq!(
        bridge.prop_hypotheses.len(),
        1,
        "Exactly one hypothesis should be recorded"
    );
    assert_eq!(bridge.prop_hypotheses[0].0, fvar, "FVarId must match");
    assert_eq!(bridge.prop_hypotheses[0].1, p, "Expression must match");
}

#[test]
fn test_add_hypothesis_without_fvar_does_not_record() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let p = mk_atom("P");

    bridge
        .add_hypothesis(&p)
        .expect("add_hypothesis without fvar should succeed");

    assert!(
        bridge.prop_hypotheses.is_empty(),
        "No fvar = no prop_hypotheses entry"
    );
}
