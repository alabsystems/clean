// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Composite proof-search coverage for propositional reconstruction.

use super::*;

fn count_const_occurrences(expr: &Expr, target: &str) -> usize {
    match expr.kind() {
        ExprKind::Const(name, _) => usize::from(name.to_string() == target),
        ExprKind::App(fun, arg) => {
            count_const_occurrences(fun, target) + count_const_occurrences(arg, target)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            count_const_occurrences(ty, target) + count_const_occurrences(body, target)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            count_const_occurrences(ty, target)
                + count_const_occurrences(val, target)
                + count_const_occurrences(body, target)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
            count_const_occurrences(inner, target)
        }
        _ => 0,
    }
}

#[test]
#[timeout(30000)]
fn test_or_with_nested_and_decomposition() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let r = prop("R");
    let and_pq = mk_and(&p, &q);
    let or_pr = mk_or(&p, &r);

    // h : P ∧ Q -> And.left gives P -> Or.inl gives P ∨ R
    bridge.prop_hypotheses.push((FVarId::new(20), and_pq));

    let goal_class = bridge.classify_prop(&or_pr);
    let result = bridge.build_propositional_proof(&goal_class, &or_pr);
    assert!(
        result.is_ok(),
        "Or.inl via And.left should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.expect("nested And decomposition should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.inl"));
}

#[test]
#[timeout(30000)]
fn test_implies_with_and_decomposition() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let r = prop("R");
    let and_pq = mk_and(&p, &q);
    let implies_rq = Expr::pi(BinderInfo::Default, r.clone(), q.clone());

    // h : P ∧ Q -> And.right gives Q -> lambda ignores R
    bridge.prop_hypotheses.push((FVarId::new(30), and_pq));

    let goal_class = bridge.classify_prop(&implies_rq);
    let result = bridge.build_propositional_proof(&goal_class, &implies_rq);
    assert!(
        result.is_ok(),
        "Implies with And decomposition should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.expect("And decomposition implication should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Implies.lam"));
}

#[test]
#[timeout(30000)]
fn test_or_elim_with_assumption_modus_ponens() {
    // Regression test for try_assumption_modus_ponens bug:
    // Before fix, assumption_key was set from goal_expr instead of assumption_type,
    // causing the function to search for h : G -> G (identity) instead of
    // h : assumption_type -> G.
    //
    // Setup: h1 : Or(P, Q), h2 : P -> Q, goal: Q
    // Left branch:  assumption P + h2 : P -> Q -> h2(bvar 0)   [needs fixed mp]
    // Right branch: assumption Q == goal Q -> bvar 0            [direct match]
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let or_pq = mk_or(&p, &q);
    let implies_pq = Expr::pi(BinderInfo::Default, p.clone(), q.clone());

    bridge.prop_hypotheses.push((FVarId::new(40), or_pq));
    bridge.prop_hypotheses.push((FVarId::new(41), implies_pq));

    let goal_class = bridge.classify_prop(&q);
    let result = bridge.build_propositional_proof(&goal_class, &q);
    assert!(
        result.is_ok(),
        "Or.elim via assumption modus ponens should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.expect("assumption modus ponens should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"));
}

#[test]
#[timeout(30000)]
fn test_implies_absurd_elim_from_neg_hypothesis() {
    // Test Implies.absurd_elim strategy: Goal P -> Q, Hypothesis !P.
    // Builds: fun (hp : P) => False.elim Q (absurd hp h_neg)
    // This strategy fires when Q is not directly provable and no h : P -> Q exists,
    // but !P allows deriving False from the lambda parameter via absurd.
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let not_p = mk_not(&p);
    let implies_pq = Expr::pi(BinderInfo::Default, p.clone(), q.clone());

    bridge.prop_hypotheses.push((FVarId::new(50), not_p));

    let goal_class = bridge.classify_prop(&implies_pq);
    let result = bridge.build_propositional_proof(&goal_class, &implies_pq);
    assert!(
        result.is_ok(),
        "Implies.absurd_elim should succeed with !P hypothesis: {:?}",
        result.err()
    );
    let (step, _) = result.expect("absurd-elim implication should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Implies.absurd_elim"));
}

#[test]
#[timeout(30000)]
fn test_or_elim_with_assumption_absurd() {
    // Coverage: try_prove_under_assumption -> try_assumption_absurd
    // Setup: h1 : Or(P, Q), h2 : !P, goal: Q
    // Left branch:  assumption P + h2 : !P -> absurd (bvar 0) h2 -> False.elim Q
    // Right branch: assumption Q == goal Q -> bvar 0
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let or_pq = mk_or(&p, &q);
    let not_p = mk_not(&p);

    bridge.prop_hypotheses.push((FVarId::new(60), or_pq));
    bridge.prop_hypotheses.push((FVarId::new(61), not_p));

    let goal_class = bridge.classify_prop(&q);
    let result = bridge.build_propositional_proof(&goal_class, &q);
    assert!(
        result.is_ok(),
        "Or.elim via assumption absurd should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.expect("assumption absurd path should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"));
}

#[test]
#[timeout(30000)]
fn test_or_elim_with_neg_assumption_absurd() {
    // Coverage: try_prove_under_assumption -> try_neg_assumption_absurd
    // Setup: h1 : Or(!P, Q), h2 : P, goal: Q
    // Left branch:  assumption !P + h2 : P -> absurd h2 (bvar 0) -> False.elim Q
    // Right branch: assumption Q == goal Q -> bvar 0
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let not_p = mk_not(&p);
    let or_notp_q = mk_or(&not_p, &q);

    bridge.prop_hypotheses.push((FVarId::new(70), or_notp_q));
    bridge.prop_hypotheses.push((FVarId::new(71), p.clone()));

    let goal_class = bridge.classify_prop(&q);
    let result = bridge.build_propositional_proof(&goal_class, &q);
    assert!(
        result.is_ok(),
        "Or.elim via neg assumption absurd should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.expect("neg assumption absurd path should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"));
}

#[test]
#[timeout(30000)]
fn test_or_elim_with_impossible_nat_lt_assumption() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let q = prop("Q");
    let impossible_lt = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.lt"), vec![]),
            Expr::nat_lit(5),
        ),
        Expr::nat_lit(3),
    );
    let or_lt_q = mk_or(&impossible_lt, &q);

    bridge.prop_hypotheses.push((FVarId::new(72), or_lt_q));

    let goal_class = bridge.classify_prop(&q);
    let result = bridge.build_propositional_proof(&goal_class, &q);
    assert!(
        result.is_ok(),
        "Or.elim via impossible Nat.lt assumption should succeed: {:?}",
        result.err()
    );
    let (step, proof) = result.expect("impossible Nat.lt branch should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"));
    assert!(
        count_const_occurrences(&proof, "False.elim") >= 1,
        "the impossible Nat.lt branch should discharge the goal through False.elim"
    );
    assert!(
        count_const_occurrences(&proof, "Nat.lt_irrefl") >= 1,
        "the impossible Nat.lt branch should build a Nat.lt_irrefl contradiction proof"
    );
}

#[test]
#[timeout(30000)]
fn test_top_level_modus_ponens() {
    // Coverage: try_modus_ponens (top-level in build_prop_proof_inner)
    // Setup: h1 : P -> Q, h2 : P, goal: Q
    // try_hypothesis_match fails (no direct Q), try_modus_ponens finds h1 : P -> Q
    // and proves P via hypothesis match h2 : P. Returns h1(h2).
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let implies_pq = Expr::pi(BinderInfo::Default, p.clone(), q.clone());

    bridge.prop_hypotheses.push((FVarId::new(80), implies_pq));
    bridge.prop_hypotheses.push((FVarId::new(81), p.clone()));

    let goal_class = bridge.classify_prop(&q);
    let result = bridge.build_propositional_proof(&goal_class, &q);
    assert!(
        result.is_ok(),
        "Top-level modus ponens should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.expect("top-level modus ponens should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "modus_ponens"));
}

#[test]
#[timeout(30000)]
fn test_and_intro_from_both_hypotheses() {
    // Coverage: And.intro path in build_prop_proof_inner
    // Setup: h1 : P, h2 : Q, goal: And(P, Q)
    // Both conjuncts provable via hypothesis match -> And.intro(h1, h2)
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let and_pq = mk_and(&p, &q);

    bridge.prop_hypotheses.push((FVarId::new(90), p.clone()));
    bridge.prop_hypotheses.push((FVarId::new(91), q.clone()));

    let goal_class = bridge.classify_prop(&and_pq);
    let result = bridge.build_propositional_proof(&goal_class, &and_pq);
    assert!(
        result.is_ok(),
        "And.intro should succeed: {:?}",
        result.err()
    );
    let (step, _) = result.expect("And.intro path should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "And.intro"));
}

#[test]
#[timeout(30000)]
fn test_implies_mp_bvar_direct_branch() {
    // Directly exercise build_implies_proof Strategy 3.
    // Top-level build_propositional_proof would short-circuit on hypothesis_match
    // for goal P -> Q when h : P -> Q is already present.
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let dummy_goal = prop("R");
    let implies_pq = Expr::pi(BinderInfo::Default, p.clone(), q.clone());
    let mp_hyp = FVarId::new(55);

    bridge.prop_hypotheses.push((mp_hyp, implies_pq));

    let goal_class = LogicalForm::Implies(p.clone(), q);
    let result = bridge.build_prop_proof_inner(&goal_class, &dummy_goal, 0);
    assert!(
        result.is_ok(),
        "Implies.mp_bvar should succeed on direct helper path: {:?}",
        result.err()
    );
    let (step, proof) = result.expect("Implies.mp_bvar should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Implies.mp_bvar"));

    assert!(
        matches!(proof.kind(), ExprKind::Lam(_, _, _)),
        "expected lambda proof for Implies.mp_bvar, got {:?}",
        proof.kind()
    );
    if let ExprKind::Lam(_, _, body) = proof.kind() {
        assert!(
            matches!(body.kind(), ExprKind::App(_, _)),
            "expected lambda body application, got {:?}",
            body.kind()
        );
        if let ExprKind::App(func, arg) = body.kind() {
            assert!(
                matches!(func.kind(), ExprKind::FVar(id) if *id == mp_hyp),
                "lambda body should apply the implication hypothesis"
            );
            assert!(
                matches!(arg.kind(), ExprKind::BVar(0)),
                "lambda body should pass the introduced binder to the implication"
            );
        }
    }
}

#[test]
#[timeout(30000)]
fn test_not_lam_absurd_direct_branch() {
    // Directly exercise build_not_proof Strategy 2.
    // Top-level build_propositional_proof would short-circuit on hypothesis_match
    // for goal !P when h : !P already exists.
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let not_p = mk_not(&p);
    let neg_hyp = FVarId::new(56);

    bridge.prop_hypotheses.push((neg_hyp, not_p));

    let goal_class = LogicalForm::Not(p.clone());
    let result = bridge.build_prop_proof_inner(&goal_class, &q, 0);
    assert!(
        result.is_ok(),
        "Not.lam_absurd should succeed on direct helper path: {:?}",
        result.err()
    );
    let (step, proof) = result.expect("Not.lam_absurd should return a proof");
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Not.lam_absurd"));

    assert!(
        matches!(proof.kind(), ExprKind::Lam(_, _, _)),
        "expected lambda proof for Not.lam_absurd, got {:?}",
        proof.kind()
    );
    if let ExprKind::Lam(_, _, body) = proof.kind() {
        let head = body.get_app_fn();
        assert!(
            matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("absurd")),
            "lambda body should be headed by absurd, got {:?}",
            head.kind()
        );
        let args = body.get_app_args();
        assert!(
            matches!(args.first().map(|arg| arg.kind()), Some(ExprKind::Const(name, _)) if *name == Name::from_string("P")),
            "absurd should take the proved proposition first"
        );
        assert!(
            matches!(args.last().map(|arg| arg.kind()), Some(ExprKind::FVar(id)) if *id == neg_hyp),
            "absurd should consume the matching negated hypothesis"
        );
    }
}
