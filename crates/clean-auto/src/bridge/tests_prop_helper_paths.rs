// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct helper-path coverage for propositional proof reconstruction (#2442).
//!
//! These tests intentionally call `build_prop_proof_inner` so they cover
//! branches that the public entrypoint short-circuits via hypothesis match or
//! Iff folding.

use super::super::*;
use crate::proof::ProofStep;
use clean_kernel::env::Declaration;
use ntest::timeout;

fn add_prop_axioms(env: &mut Environment) {
    for (name, type_) in [
        (
            "And",
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            ),
        ),
        (
            "Or",
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            ),
        ),
        (
            "Not",
            Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        ),
        ("True", Expr::prop()),
        ("False", Expr::prop()),
        (
            "Iff",
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            ),
        ),
    ] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
        })
        .unwrap();
    }
}

fn add_prop_constructors(env: &mut Environment) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("True.intro"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("True"), vec![]),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("False.elim"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Default,
                Expr::const_(Name::from_string("False"), vec![]),
                Expr::bvar(1),
            ),
        ),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Iff.intro"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::prop(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(1)),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(3)),
                        Expr::app(
                            Expr::app(
                                Expr::const_(Name::from_string("Iff"), vec![]),
                                Expr::bvar(3),
                            ),
                            Expr::bvar(2),
                        ),
                    ),
                ),
            ),
        ),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("absurd"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::prop(),
                Expr::pi(
                    BinderInfo::Default,
                    Expr::bvar(1),
                    Expr::pi(
                        BinderInfo::Default,
                        Expr::app(
                            Expr::const_(Name::from_string("Not"), vec![]),
                            Expr::bvar(2),
                        ),
                        Expr::bvar(2),
                    ),
                ),
            ),
        ),
    })
    .unwrap();
}

fn add_prop_constants(env: &mut Environment) {
    for name in ["P", "Q", "R"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .unwrap();
    }
}

fn setup_prop_env() -> Environment {
    let mut env = Environment::new();
    add_prop_axioms(&mut env);
    add_prop_constructors(&mut env);
    add_prop_constants(&mut env);
    env
}

fn prop(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn mk_not(a: &Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Not"), vec![]), a.clone())
}

fn mk_or(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), a.clone()),
        b.clone(),
    )
}

#[test]
#[timeout(30000)]
fn test_implies_mp_bvar_direct_branch_isolated_module() {
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
    let (step, proof) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Implies.mp_bvar"));

    match proof.kind() {
        ExprKind::Lam(_, _, body) => match body.kind() {
            ExprKind::App(func, arg) => {
                assert!(
                    matches!(func.kind(), ExprKind::FVar(id) if *id == mp_hyp),
                    "lambda body should apply the implication hypothesis"
                );
                assert!(
                    matches!(arg.kind(), ExprKind::BVar(0)),
                    "lambda body should pass the introduced binder to the implication"
                );
            }
            other => panic!("expected lambda body application, got {other:?}"),
        },
        other => panic!("expected lambda proof for Implies.mp_bvar, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn test_not_lam_absurd_direct_branch_isolated_module() {
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
    let (step, proof) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Not.lam_absurd"));

    match proof.kind() {
        ExprKind::Lam(_, _, body) => {
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
        other => panic!("expected lambda proof for Not.lam_absurd, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn test_depth_limit_guard_returns_exact_error_isolated_module() {
    let env = setup_prop_env();
    let bridge = SmtBridge::new(&env);
    let result = bridge.build_prop_proof_inner(&LogicalForm::True, &prop("P"), 101);
    assert!(
        matches!(result, Err(BridgeError::ProofTraceFailed(ref msg)) if msg == "propositional proof reconstruction depth exceeded"),
        "depth guard should return the dedicated overflow error, got {:?}",
        result
    );
}

#[test]
#[timeout(30000)]
fn test_or_without_provable_disjuncts_returns_exact_error_isolated_module() {
    let env = setup_prop_env();
    let bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let goal = mk_or(&p, &q);
    let goal_class = bridge.classify_prop(&goal);

    let result = bridge.build_propositional_proof(&goal_class, &goal);
    assert!(
        matches!(result, Err(BridgeError::ProofTraceFailed(ref msg)) if msg == "Or: neither disjunct provable and not excluded middle"),
        "Or failure should preserve the dedicated error, got {:?}",
        result
    );
}

#[test]
#[timeout(30000)]
fn test_implies_without_support_returns_exact_error_isolated_module() {
    let env = setup_prop_env();
    let bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let goal = Expr::pi(BinderInfo::Default, p.clone(), q.clone());

    let result =
        bridge.build_prop_proof_inner(&LogicalForm::Implies(p.clone(), q.clone()), &goal, 0);
    assert!(
        matches!(result, Err(BridgeError::UnsupportedExpr { ref context })
            if context == "propositional: Implies(P, Q) — Q not provable from hypotheses or lambda param"),
        "Implies failure should preserve the dedicated error, got {:?}",
        result
    );
}

#[test]
#[timeout(30000)]
fn test_not_without_support_returns_exact_error_isolated_module() {
    let env = setup_prop_env();
    let bridge = SmtBridge::new(&env);
    let p = prop("P");
    let goal = mk_not(&p);

    let result = bridge.build_prop_proof_inner(&LogicalForm::Not(p), &goal, 0);
    assert!(
        matches!(result, Err(BridgeError::UnsupportedExpr { ref context })
            if context == "propositional: Not(P) requires False or ¬P hypothesis"),
        "Not failure should preserve the dedicated error, got {:?}",
        result
    );
}

#[test]
#[timeout(30000)]
fn test_false_without_support_returns_exact_error_isolated_module() {
    let env = setup_prop_env();
    let bridge = SmtBridge::new(&env);
    let goal = Expr::const_(Name::from_string("False"), vec![]);
    let goal_class = bridge.classify_prop(&goal);

    let result = bridge.build_propositional_proof(&goal_class, &goal);
    assert!(
        matches!(result, Err(BridgeError::UnsupportedExpr { ref context })
            if context == "propositional: cannot derive False without False hypothesis"),
        "False failure should preserve the dedicated error, got {:?}",
        result
    );
}

#[test]
#[timeout(30000)]
fn test_atom_without_strategy_returns_exact_error_isolated_module() {
    let env = setup_prop_env();
    let bridge = SmtBridge::new(&env);
    let goal = prop("P");
    let goal_class = bridge.classify_prop(&goal);

    let result = bridge.build_propositional_proof(&goal_class, &goal);
    assert!(
        matches!(result, Err(BridgeError::UnsupportedExpr { ref context })
            if context == "propositional proof reconstruction: no matching strategy"),
        "Atomic fallback should preserve the dedicated error, got {:?}",
        result
    );
}

#[test]
#[timeout(30000)]
fn test_iff_intro_direct_branch_isolated_module() {
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
    let (step, proof) = result.unwrap();
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
fn test_or_elim_implies_branch_shifts_outer_assumption_isolated_module() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let r = prop("R");
    let or_pq = mk_or(&p, &q);
    let implies_rp = Expr::pi(BinderInfo::Default, r.clone(), p.clone());
    let q_implies_rp = Expr::pi(BinderInfo::Default, q.clone(), implies_rp.clone());
    let right_branch_hyp = FVarId::new(57);

    bridge.prop_hypotheses.push((FVarId::new(56), or_pq));
    bridge
        .prop_hypotheses
        .push((right_branch_hyp, q_implies_rp));

    let goal_class = bridge.classify_prop(&implies_rp);
    let result = bridge.build_propositional_proof(&goal_class, &implies_rp);
    assert!(
        result.is_ok(),
        "Or.elim with implication branch should succeed: {:?}",
        result.err()
    );
    let (step, proof) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"));

    let args = proof.get_app_args();
    assert_eq!(args.len(), 6, "Or.elim proof should apply 6 arguments");

    match args[3].kind() {
        ExprKind::Lam(_, _, left_body) => match left_body.kind() {
            ExprKind::Lam(_, _, inner_body) => {
                assert!(
                    matches!(inner_body.kind(), ExprKind::BVar(1)),
                    "left branch should shift the outer Or.elim assumption under the inner lambda"
                );
            }
            other => panic!("expected nested lambda in left branch, got {other:?}"),
        },
        other => panic!("expected left Or.elim branch lambda, got {other:?}"),
    }

    match args[4].kind() {
        ExprKind::Lam(_, _, right_body) => match right_body.kind() {
            ExprKind::App(func, arg) => {
                assert!(
                    matches!(func.kind(), ExprKind::FVar(id) if *id == right_branch_hyp),
                    "right branch should use the implication hypothesis directly"
                );
                assert!(
                    matches!(arg.kind(), ExprKind::BVar(0)),
                    "right branch should consume the Or.elim branch assumption"
                );
            }
            other => panic!("expected implication application in right branch, got {other:?}"),
        },
        other => panic!("expected right Or.elim branch lambda, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn test_or_elim_not_branch_shifts_outer_assumption_isolated_module() {
    let env = setup_prop_env();
    let mut bridge = SmtBridge::new(&env);
    let p = prop("P");
    let q = prop("Q");
    let r = prop("R");
    let or_pq = mk_or(&p, &q);
    let false_expr = Expr::const_(Name::from_string("False"), vec![]);
    let p_implies_false = Expr::pi(BinderInfo::Default, p.clone(), false_expr.clone());
    let implies_r_not_p = Expr::pi(BinderInfo::Default, r.clone(), mk_not(&p));
    let q_implies_goal = Expr::pi(BinderInfo::Default, q.clone(), implies_r_not_p.clone());
    let left_branch_hyp = FVarId::new(59);

    bridge.prop_hypotheses.push((FVarId::new(58), or_pq));
    bridge
        .prop_hypotheses
        .push((left_branch_hyp, p_implies_false));
    bridge
        .prop_hypotheses
        .push((FVarId::new(60), q_implies_goal));

    let goal_class = bridge.classify_prop(&implies_r_not_p);
    let result = bridge.build_propositional_proof(&goal_class, &implies_r_not_p);
    assert!(
        result.is_ok(),
        "Or.elim with negation branch should succeed: {:?}",
        result.err()
    );
    let (step, proof) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Or.elim"));

    let args = proof.get_app_args();
    assert_eq!(args.len(), 6, "Or.elim proof should apply 6 arguments");

    match args[3].kind() {
        ExprKind::Lam(_, _, left_body) => match left_body.kind() {
            ExprKind::Lam(_, _, negation_body) => match negation_body.kind() {
                ExprKind::Lam(_, _, inner_body) => match inner_body.kind() {
                    ExprKind::App(func, arg) => {
                        assert!(
                            matches!(func.kind(), ExprKind::FVar(id) if *id == left_branch_hyp),
                            "left branch should derive False via the P -> False hypothesis"
                        );
                        assert!(
                            matches!(arg.kind(), ExprKind::BVar(0)),
                            "left branch negation proof should use the innermost lambda parameter (¬P binder), got {:?}",
                            arg.kind()
                        );
                    }
                    other => {
                        panic!("expected hypothesis application in negation body, got {other:?}")
                    }
                },
                other => panic!("expected nested negation lambda in left branch, got {other:?}"),
            },
            other => panic!("expected implication lambda in negation branch, got {other:?}"),
        },
        other => panic!("expected left Or.elim negation branch lambda, got {other:?}"),
    }
}
