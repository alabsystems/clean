// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Classical, normalization, and Iff-oriented propositional coverage.

use super::*;

#[test]
#[timeout(30000)]
fn test_classical_em_excluded_middle() {
    // Classical.em strategy: Goal P ∨ !P with no hypotheses.
    // Neither P nor !P is provable independently, but Classical.em P
    // directly proves the excluded middle. Part of #302.
    let env = setup_prop_env();
    let bridge = SmtBridge::new(&env);
    let p = prop("P");
    let or_p_notp = mk_or(&p, &mk_not(&p));

    let goal_class = bridge.classify_prop(&or_p_notp);
    let result = bridge.build_propositional_proof(&goal_class, &or_p_notp);
    assert!(
        result.is_ok(),
        "Classical.em should prove P ∨ !P: {:?}",
        result.err()
    );
    let (step, _) = result.expect("Classical.em should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Classical.em"));
}

#[test]
#[timeout(30000)]
fn test_classical_em_excluded_middle_swapped() {
    // Regression: the excluded-middle reconstruction should also handle !P ∨ P.
    let env = setup_prop_env();
    let bridge = SmtBridge::new(&env);
    let p = prop("P");
    let or_notp_p = mk_or(&mk_not(&p), &p);

    let goal_class = bridge.classify_prop(&or_notp_p);
    let result = bridge.build_propositional_proof(&goal_class, &or_notp_p);
    assert!(
        result.is_ok(),
        "Classical.em should prove !P ∨ P: {:?}",
        result.err()
    );
    let (step, proof) = result.expect("swapped Classical.em should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Classical.em"));

    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Or.rec")),
        "swapped excluded middle should case-split on Or.rec, got {:?}",
        head.kind()
    );
}

#[test]
#[timeout(30000)]
fn test_iff_intro_direct_branch() {
    // Directly exercise the LogicalForm::Iff branch.
    // classify_prop currently folds Iff to And(->, <-), so the public entry point
    // reaches the same proof shape via And.intro instead of the explicit
    // Iff.intro helper branch.
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let dummy_goal = prop("R");

    bridge.prop_hypotheses.push((FVarId::new(99), p.clone()));
    bridge.prop_hypotheses.push((FVarId::new(100), q.clone()));

    let goal_class = LogicalForm::Iff(p.clone(), q.clone());
    let result = bridge.build_prop_proof_inner(&goal_class, &dummy_goal, 0);
    assert!(
        result.is_ok(),
        "direct Iff.intro helper path should succeed: {:?}",
        result.err()
    );
    let (step, proof) = result.expect("Iff helper path should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Iff.intro"));

    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Iff.intro")),
        "Iff helper path should build an Iff.intro proof term"
    );
    assert_eq!(
        proof.get_app_args().len(),
        4,
        "Iff.intro proof should apply 4 arguments (P, Q, mp, mpr)"
    );
}

#[test]
#[timeout(30000)]
fn test_iff_intro_from_both_directions() {
    // Iff(P, Q) where both P -> Q and Q -> P are provable:
    // h1 : P -> Q, h2 : Q -> P, goal: Iff(P, Q)
    // Builds: Iff.intro P Q (fun hp : P => h1 hp) (fun hq : Q => h2 hq)
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let implies_pq = Expr::pi(BinderInfo::Default, p.clone(), q.clone());
    let implies_qp = Expr::pi(BinderInfo::Default, q.clone(), p.clone());
    let iff_pq = mk_iff(&p, &q);

    bridge.prop_hypotheses.push((FVarId::new(100), implies_pq));
    bridge.prop_hypotheses.push((FVarId::new(101), implies_qp));

    let goal_class = bridge.classify_prop(&iff_pq);
    let result = bridge.build_propositional_proof(&goal_class, &iff_pq);
    assert!(
        result.is_ok(),
        "Iff.intro should succeed with both directions provable: {:?}",
        result.err()
    );
    let (step, _) = result.expect("Iff.intro reconstruction should return a proof");
    // Iff(P, Q) is classified as And(P -> Q, Q -> P) by classify_prop,
    // so it goes through the And.intro path with Implies sub-proofs.
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "And.intro"));
}

#[test]
#[timeout(30000)]
fn test_classify_prop_neq_folds_to_not_eq() {
    // classify_prop should fold Neq(ty, lhs, rhs) to Not(eq_expr) (#2442 Phase 2).
    // This enables all existing Not/absurd proof strategies to handle ≠ transparently.
    let env = setup_prop_env();
    let bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    // Build @Ne Prop P Q - classify_expr detects "Ne" with 3 args -> Neq
    let ne_expr = Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Ne"), vec![]), Expr::prop()),
            p,
        ),
        q,
    );
    let class = bridge.classify_prop(&ne_expr);
    assert!(
        matches!(class, LogicalForm::Not(_)),
        "classify_prop should fold Neq to Not(Eq), got {class:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_neq_hypothesis_enables_absurd_via_fold() {
    // Neq fold makes != hypotheses appear as Not(Eq), enabling absurd matching.
    // h1 : P, h2 : !P (simulates the output of Neq fold), goal: False
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let not_p = mk_not(&p);

    bridge.prop_hypotheses.push((FVarId::new(200), p.clone()));
    bridge.prop_hypotheses.push((FVarId::new(201), not_p));

    let false_expr = Expr::const_(Name::from_string("False"), vec![]);
    let goal_class = bridge.classify_prop(&false_expr);
    let result = bridge.build_propositional_proof(&goal_class, &false_expr);
    assert!(
        result.is_ok(),
        "absurd should derive False from P + !P (simulating Neq fold): {:?}",
        result.err()
    );
    let (step, _) = result.expect("Neq fold absurd path should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "absurd"));
}
