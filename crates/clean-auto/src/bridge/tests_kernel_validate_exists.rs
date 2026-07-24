// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Existential kernel-validation regressions for propositional proof reconstruction.

use super::tests_kernel_validate::{kernel_validate_proof, make_exists, setup_env_with_eq_exists};
use super::*;
use clean_kernel::env::Declaration;

fn setup_env_with_eq_exists_prop() -> Environment {
    let mut env = setup_env_with_eq_exists();
    env.init_and().expect("And should be declared");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Q"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("Q should be declared");
    env
}

fn setup_env_with_dependent_exists_prop() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat should succeed");
    env.init_and().expect("init_and should succeed");
    env.init_exists().expect("init_exists should succeed");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Vec"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, nat.clone(), Expr::type_()),
    })
    .expect("Vec should be declared");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Pred"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            nat,
            Expr::pi(
                BinderInfo::Default,
                Expr::app(
                    Expr::const_(Name::from_string("Vec"), vec![]),
                    Expr::bvar(0),
                ),
                Expr::prop(),
            ),
        ),
    })
    .expect("Pred should be declared");

    env
}

fn mk_and(left: &Expr, right: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), left.clone()),
        right.clone(),
    )
}

fn mk_pred(index: Expr, witness: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Pred"), vec![]), index),
        witness,
    )
}

#[test]
fn test_proof_kernel_validates_exists_elim_from_quantified_hypothesis() {
    let env = setup_env_with_eq_exists_prop();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let hyp_fvar = FVarId::new(0);
    let hyp_type = make_exists(a_ty.clone(), Expr::const_(Name::from_string("Q"), vec![]));
    bridge
        .add_hypothesis_with_fvar(&hyp_type, Some(hyp_fvar))
        .expect("existential hypothesis should register");

    let goal = Expr::const_(Name::from_string("Q"), vec![]);

    let verification = bridge.prove(&goal).unwrap();
    let result = match verification {
        SmtVerificationResult::Verified(result) => *result,
        other => panic!("Should rebuild the goal from an existential hypothesis: {other:?}"),
    };
    let proof = result.proof_term();

    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string() == "Exists.elim"),
        "Proof should use Exists.elim, got {head:?}"
    );
    kernel_validate_proof(&env, proof, &goal, &[(hyp_fvar, hyp_type)]);
}

#[test]
fn test_proof_kernel_validates_exists_elim_reuses_witness_inside_implication() {
    let env = setup_env_with_eq_exists_prop();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let hyp_fvar = FVarId::new(0);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let hyp_type = make_exists(
        a_ty.clone(),
        make_eq(a_ty.clone(), Expr::app(f.clone(), Expr::bvar(0)), a.clone()),
    );
    bridge
        .add_hypothesis_with_fvar(&hyp_type, Some(hyp_fvar))
        .expect("existential hypothesis should register");

    let goal = Expr::arrow(
        make_eq(a_ty.clone(), a.clone(), a.clone()),
        make_exists(a_ty.clone(), make_eq(a_ty, Expr::app(f, Expr::bvar(0)), a)),
    );

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("nested implication should reuse the extracted existential witness");

    assert!(matches!(&step, ProofStep::Propositional(rule) if rule == "Exists.elim"));
    kernel_validate_proof(&env, &proof, &goal, &[(hyp_fvar, hyp_type)]);
}

#[test]
fn test_proof_kernel_validates_exists_elim_reuses_witness_and_nested_binder() {
    let env = setup_env_with_eq_exists_prop();
    let mut bridge = SmtBridge::new(&env);

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let hyp_fvar = FVarId::new(0);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let hyp_type = make_exists(
        a_ty.clone(),
        make_eq(a_ty.clone(), Expr::app(f.clone(), Expr::bvar(0)), a.clone()),
    );
    bridge
        .add_hypothesis_with_fvar(&hyp_type, Some(hyp_fvar))
        .expect("existential hypothesis should register");

    let goal = Expr::arrow(
        q.clone(),
        make_exists(
            a_ty.clone(),
            mk_and(&make_eq(a_ty, Expr::app(f, Expr::bvar(0)), a), &q),
        ),
    );

    let goal_class = bridge.classify_prop(&goal);
    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("nested implication should use both the opened witness and the implication binder");

    assert!(matches!(&step, ProofStep::Propositional(rule) if rule == "Exists.elim"));
    kernel_validate_proof(&env, &proof, &goal, &[(hyp_fvar, hyp_type)]);
}

#[test]
fn test_proof_kernel_validates_exists_with_alias_typed_env_witness() {
    let mut env = setup_env_with_eq_exists_prop();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("A_alias"),
        level_params: vec![],
        type_: Expr::type_(),
        value: Expr::const_(Name::from_string("A"), vec![]),
        is_reducible: true,
    })
    .expect("A_alias should be declared as a reducible alias for A");

    let mut bridge = SmtBridge::new(&env);

    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let hyp_fvar = FVarId::new(0);
    bridge
        .add_hypothesis_with_fvar(&q, Some(hyp_fvar))
        .expect("Q hypothesis should register");

    let goal = make_exists(
        Expr::const_(Name::from_string("A_alias"), vec![]),
        q.clone(),
    );

    let verification = bridge.prove(&goal).unwrap();
    let result = match verification {
        SmtVerificationResult::Verified(result) => *result,
        other => panic!(
            "Exists witness reconstruction should accept environment constants whose \
             types are definitionally equal through a reducible alias: {other:?}"
        ),
    };
    let proof = result.proof_term();

    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string() == "Exists.intro"),
        "Proof should use Exists.intro, got {head:?}"
    );
    kernel_validate_proof(&env, proof, &goal, &[(hyp_fvar, q)]);
}

/// Regression test for #3077: when Exists.elim stores a witness via
/// with_bound_exists_witness, the binder_type must be lifted by 2 to match
/// the continuation lambda depth. Without lifting, a dependent binder type
/// containing loose bvars has its ExprKey in the wrong context, and
/// goal_scoped_witness_candidates rejects the witness.
#[test]
fn test_bound_witness_type_lifted_matches_dependent_binder_under_continuation() {
    let env = setup_env_with_eq_exists_prop();
    let bridge = SmtBridge::new(&env);

    let f = Expr::const_(Name::from_string("f"), vec![]);

    // dep_type = App(f, bvar(0)): a binder type that depends on an outer variable.
    let dep_type = Expr::app(f, Expr::bvar(0));

    // Simulate the context of try_exists_elim_continuation:
    // 1. Lift existing witnesses by 2 (for the 2 continuation lambdas)
    // 2. Store a new witness with binder_type lifted by 2
    // 3. Verify goal_scoped_witness_candidates finds the witness when the
    //    expected type is in the same (2-deep) context.
    let dep_type_in_continuation = dep_type.lift(2); // = App(f, bvar(2))
    bridge.with_lifted_bound_exists_witnesses(2, || {
        bridge.with_bound_exists_witness(&dep_type_in_continuation, &Expr::bvar(1), || {
            // The expected type in the continuation context is also App(f, bvar(2)).
            // goal_scoped_witness_candidates should find the stored witness.
            let candidates = bridge.goal_scoped_witness_candidates(&dep_type_in_continuation);
            assert!(
                candidates.iter().any(|c| *c == Expr::bvar(1)),
                "Witness bvar(1) should be found when binder_type is correctly lifted; \
                 candidates: {candidates:?}"
            );
        });
    });

    // Negative case: if the type were stored WITHOUT lifting (the bug),
    // the ExprKeys would differ and the witness would not be found.
    bridge.with_lifted_bound_exists_witnesses(2, || {
        // Store with UNLIFTED type (the pre-fix behavior)
        bridge.with_bound_exists_witness(&dep_type, &Expr::bvar(1), || {
            let candidates = bridge.goal_scoped_witness_candidates(&dep_type_in_continuation);
            assert!(
                !candidates.iter().any(|c| *c == Expr::bvar(1)),
                "Witness stored with unlifted type should NOT match the lifted expected type"
            );
        });
    });
}

#[test]
fn test_exists_elim_dependent_binder_type_reuses_witness() {
    let env = setup_env_with_dependent_exists_prop();
    let bridge = SmtBridge::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let hyp_vec_x = Expr::app(
        Expr::const_(Name::from_string("Vec"), vec![]),
        Expr::bvar(0),
    );
    let goal_vec_x = Expr::app(
        Expr::const_(Name::from_string("Vec"), vec![]),
        Expr::bvar(1),
    );
    let hyp_exists = make_exists(hyp_vec_x, mk_pred(Expr::bvar(1), Expr::bvar(0)));
    let goal_witness_body = mk_pred(Expr::bvar(2), Expr::bvar(0));
    let goal_exists = make_exists(goal_vec_x, mk_and(&goal_witness_body, &goal_witness_body));
    let goal = Expr::pi(
        BinderInfo::Default,
        nat,
        Expr::arrow(hyp_exists, goal_exists),
    );

    let goal_class = bridge.classify_prop(&goal);
    assert!(
        matches!(&goal_class, LogicalForm::Forall { .. }),
        "dependent outer binder should classify as Forall, got {goal_class:?}"
    );

    let (step, proof) = bridge
        .build_propositional_proof(&goal_class, &goal)
        .expect("dependent Exists.elim continuation should reuse the opened witness");

    assert!(matches!(&step, ProofStep::Propositional(rule) if rule == "Forall.lam"));

    let outer_body = match proof.kind() {
        ExprKind::Lam(_, _, body) => body,
        other => panic!("proof should start with a forall lambda, got {other:?}"),
    };
    let implication_body = match outer_body.kind() {
        ExprKind::Lam(_, _, body) => body,
        other => panic!("proof should then introduce the implication hypothesis, got {other:?}"),
    };
    let head = implication_body.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(ref name, _) if name.to_string() == "Exists.elim"),
        "dependent witness-reuse proof should use Exists.elim, got {head:?}"
    );

    kernel_validate_proof(&env, &proof, &goal, &[]);
}
