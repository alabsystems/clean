// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-validation regression for unkeyable existential witnesses.

use super::test_helpers::make_eq;
use super::tests_kernel_validate::{kernel_validate_proof, make_exists, setup_env_with_eq_exists};
use super::*;
use clean_kernel::env::Declaration;

#[test]
fn test_proof_kernel_validates_exists_with_goal_scoped_let_witness() {
    let env = setup_env_with_eq_exists();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let let_witness = Expr::let_named(
        Name::anon(),
        a_ty.clone(),
        Expr::const_(Name::from_string("a"), vec![]),
        Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0)),
        false,
    );
    bridge
        .term_to_expr
        .insert(TermId(9000), let_witness.clone());

    let goal = make_exists(
        a_ty.clone(),
        make_eq(a_ty, Expr::bvar(0), let_witness.clone()),
    );

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("Should prove the existential by reusing the goal-scoped let witness");

    assert!(
        matches!(&step, ProofStep::Propositional(rule) if rule == "Exists.intro"),
        "Proof step should use Exists.intro, got {step:?}"
    );

    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string() == "Exists.intro"),
        "Proof should use Exists.intro, got {head:?}"
    );
    kernel_validate_proof(&env, &proof, &goal, &[]);
}

#[test]
fn test_proof_kernel_validates_exists_with_local_assumption_and_goal_scoped_let_witness() {
    let mut env = setup_env_with_eq_exists();
    env.init_and().expect("init_and should succeed");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Q"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("Q should be declared");
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let let_witness = Expr::let_named(
        Name::anon(),
        a_ty.clone(),
        Expr::const_(Name::from_string("a"), vec![]),
        Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(0)),
        false,
    );
    bridge
        .term_to_expr
        .insert(TermId(9001), let_witness.clone());

    let exists_body = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), q.clone()),
        make_eq(a_ty.clone(), Expr::bvar(0), let_witness.clone()),
    );
    let exists_goal = make_exists(a_ty.clone(), exists_body);
    let goal = Expr::arrow(q.clone(), exists_goal.clone());

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge.build_propositional_proof(&goal_class, &goal).expect(
        "Should prove the existential by reusing the let witness under the implication assumption",
    );

    assert!(
        matches!(&step, ProofStep::Propositional(rule) if rule == "Implies.assumption_search"),
        "Proof step should use local-assumption search, got {step:?}"
    );

    kernel_validate_proof(&env, &proof, &goal, &[]);
}
