// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct constructor and decomposition coverage for propositional proofs.

use super::*;

#[test]
#[timeout(30000)]
fn test_or_inl_from_left_hypothesis() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let or_pq = mk_or(&p, &q);

    bridge.prop_hypotheses.push((FVarId::new(1), p.clone()));

    let goal_class = bridge.classify_prop(&or_pq);
    let result = bridge.build_propositional_proof(&goal_class, &or_pq);
    assert!(result.is_ok(), "Or.inl should succeed: {:?}", result.err());
    let (step, _) = result.expect("Or.inl reconstruction should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.inl"));
}

#[test]
#[timeout(30000)]
fn test_or_inr_from_right_hypothesis() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let or_pq = mk_or(&p, &q);

    bridge.prop_hypotheses.push((FVarId::new(2), q.clone()));

    let goal_class = bridge.classify_prop(&or_pq);
    let result = bridge.build_propositional_proof(&goal_class, &or_pq);
    assert!(result.is_ok(), "Or.inr should succeed: {:?}", result.err());
    let (step, _) = result.expect("Or.inr reconstruction should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.inr"));
}

#[test]
#[timeout(30000)]
fn test_implies_lambda_from_hypothesis() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let implies_pq = Expr::pi(BinderInfo::Default, p.clone(), q.clone());

    bridge.prop_hypotheses.push((FVarId::new(3), q.clone()));

    let goal_class = bridge.classify_prop(&implies_pq);
    let result = bridge.build_propositional_proof(&goal_class, &implies_pq);
    assert!(
        result.is_ok(),
        "Implies.lam should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.expect("Implies.lam reconstruction should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Implies.lam"));
}

#[test]
#[timeout(30000)]
fn test_and_left_decomposition() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let and_pq = mk_and(&p, &q);

    bridge.prop_hypotheses.push((FVarId::new(4), and_pq));

    let goal_class = bridge.classify_prop(&p);
    let result = bridge.build_propositional_proof(&goal_class, &p);
    assert!(
        result.is_ok(),
        "And.left should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.expect("And.left reconstruction should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "And.left"));
}

#[test]
#[timeout(30000)]
fn test_and_right_decomposition() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let and_pq = mk_and(&p, &q);

    bridge.prop_hypotheses.push((FVarId::new(5), and_pq));

    let goal_class = bridge.classify_prop(&q);
    let result = bridge.build_propositional_proof(&goal_class, &q);
    assert!(
        result.is_ok(),
        "And.right should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.expect("And.right reconstruction should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "And.right"));
}

#[test]
#[timeout(30000)]
fn test_not_from_false_hypothesis() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let not_p = mk_not(&p);
    let false_expr = Expr::const_(Name::from_string("False"), vec![]);

    bridge.prop_hypotheses.push((FVarId::new(6), false_expr));

    let goal_class = bridge.classify_prop(&not_p);
    let result = bridge.build_propositional_proof(&goal_class, &not_p);
    assert!(
        result.is_ok(),
        "Not.lam_false should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.expect("Not.lam_false reconstruction should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Not.lam_false"));
}

#[test]
#[timeout(30000)]
fn test_absurd_from_contradictory_hypotheses() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let not_p = mk_not(&p);

    bridge.prop_hypotheses.push((FVarId::new(10), p.clone()));
    bridge.prop_hypotheses.push((FVarId::new(11), not_p));

    // Goal: False (absurd should derive it from contradictory P + !P)
    let false_expr = Expr::const_(Name::from_string("False"), vec![]);
    let goal_class = bridge.classify_prop(&false_expr);
    let result = bridge.build_propositional_proof(&goal_class, &q);
    assert!(result.is_ok(), "absurd should succeed: {:?}", result.err());
    let (step, _) = result.expect("absurd reconstruction should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "absurd"));
}

#[test]
#[timeout(30000)]
fn test_implies_identity_same_prop() {
    // Test Implies.id strategy: Goal P -> P (identity function).
    // Builds: fun (hp : P) => hp
    let env = setup_prop_env();
    let bridge = SmtBridge::new(&env);
    let p = prop("P");
    let implies_pp = Expr::pi(BinderInfo::Default, p.clone(), p.clone());

    let goal_class = bridge.classify_prop(&implies_pp);
    let result = bridge.build_propositional_proof(&goal_class, &implies_pp);
    assert!(
        result.is_ok(),
        "Implies.id should succeed for P -> P: {:?}",
        result.err()
    );
    let (step, _) = result.expect("Implies.id reconstruction should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Implies.id"));
}
