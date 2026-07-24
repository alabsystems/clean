// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 3 propositional proof reconstruction tests (#2442).
//!
//! Covers Eq.refl sub-goals, comparison sub-goal delegation, and Forall
//! lambda introduction. Extracted from `tests_prop_reconstruction.rs`.

use super::super::*;
use crate::proof::ProofStep;
use clean_kernel::env::Declaration;
use clean_kernel::Level;
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
}

/// Extended environment with propositional axioms + Eq, Eq.refl, type A.
fn setup_prop_env_with_eq() -> Environment {
    let mut env = Environment::new();
    add_prop_axioms(&mut env);
    add_prop_constructors(&mut env);

    // Eq : {α : Sort u} → α → α → Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(Name::from_string("u"))),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
            ),
        ),
    })
    .unwrap();

    // Eq.refl : ∀ {α : Sort u} (a : α), Eq α a a
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq.refl"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(Name::from_string("u"))),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::bvar(0),
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Eq"),
                                vec![Level::param(Name::from_string("u"))],
                            ),
                            Expr::bvar(1),
                        ),
                        Expr::bvar(0),
                    ),
                    Expr::bvar(0),
                ),
            ),
        ),
    })
    .unwrap();

    // A : Type (Sort 1)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Constants a, b : A
    for name in ["a", "b"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("A"), vec![]),
        })
        .unwrap();
    }

    env
}

fn prop(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn mk_and(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), a.clone()),
        b.clone(),
    )
}

fn mk_eq_type(ty: &Expr, lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty.clone(),
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

#[test]
#[timeout(30000)]
fn test_eq_refl_subgoal_in_conjunction() {
    // Phase 3: Eq(A, a, a) as sub-goal of And(Eq(A, a, a), True).
    // Left conjunct: Eq.refl a
    // Right conjunct: True.intro
    let env = setup_prop_env_with_eq();
    let bridge = SmtBridge::new(&env);
    let ty_a = prop("A");
    let a = prop("a");
    let eq_a_a = mk_eq_type(&ty_a, &a, &a);
    let true_expr = Expr::const_(Name::from_string("True"), vec![]);
    let and_goal = mk_and(&eq_a_a, &true_expr);

    let goal_class = bridge.classify_prop(&and_goal);
    let result = bridge.build_propositional_proof(&goal_class, &and_goal);
    assert!(
        result.is_ok(),
        "And(Eq(A, a, a), True) should succeed via Eq.refl + True.intro: {:?}",
        result.err()
    );
    let (step, _) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "And.intro"));
}

#[test]
#[timeout(30000)]
fn test_eq_refl_standalone_subgoal() {
    // Phase 3: Eq(A, a, a) directly as a propositional sub-goal.
    let env = setup_prop_env_with_eq();
    let bridge = SmtBridge::new(&env);
    let ty_a = prop("A");
    let a = prop("a");
    let eq_a_a = mk_eq_type(&ty_a, &a, &a);

    let goal_class = bridge.classify_prop(&eq_a_a);
    let result = bridge.build_propositional_proof(&goal_class, &eq_a_a);
    assert!(
        result.is_ok(),
        "Eq(A, a, a) should succeed via Eq.refl: {:?}",
        result.err()
    );
    let (step, proof) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Eq.refl"));

    // Verify proof structure is @Eq.refl A a
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Eq.refl")),
        "proof head should be Eq.refl, got {:?}",
        head.kind()
    );
}

#[test]
#[timeout(30000)]
fn test_eq_refl_fails_for_distinct_terms() {
    // Eq(A, a, b) where a ≠ b should NOT produce Eq.refl.
    let env = setup_prop_env_with_eq();
    let bridge = SmtBridge::new(&env);
    let ty_a = prop("A");
    let a = prop("a");
    let b = prop("b");
    let eq_a_b = mk_eq_type(&ty_a, &a, &b);

    let goal_class = bridge.classify_prop(&eq_a_b);
    let result = bridge.build_propositional_proof(&goal_class, &eq_a_b);
    // Should fail — no hypothesis, no refl (distinct terms)
    assert!(
        result.is_err(),
        "Eq(A, a, b) should fail without hypothesis"
    );
}

#[test]
#[timeout(30000)]
fn test_forall_with_eq_refl_body() {
    // Phase 3: ∀ (x : A), x = x
    // Body has bvar(0) = x. Eq.refl handler recognizes bvar(0) == bvar(0).
    // Proof: fun (x : A) => Eq.refl A x
    let env = setup_prop_env_with_eq();
    let bridge = SmtBridge::new(&env);
    let ty_a = prop("A");
    let eq_body = mk_eq_type(&ty_a, &Expr::bvar(0), &Expr::bvar(0));
    let forall_goal = Expr::pi(BinderInfo::Default, ty_a.clone(), eq_body.clone());

    let goal_class = bridge.classify_prop(&forall_goal);
    // Should classify as Forall since body has loose bvars
    assert!(
        matches!(&goal_class, LogicalForm::Forall { .. }),
        "∀ x : A, x = x should classify as Forall, got {:?}",
        goal_class
    );

    let result = bridge.build_propositional_proof(&goal_class, &forall_goal);
    assert!(
        result.is_ok(),
        "∀ x : A, x = x should succeed via Forall.lam + Eq.refl: {:?}",
        result.err()
    );
    let (step, proof) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Forall.lam"));

    // Proof should be a lambda
    assert!(
        matches!(proof.kind(), ExprKind::Lam(_, _, _)),
        "Forall proof should be a lambda, got {:?}",
        proof.kind()
    );
}

#[test]
#[timeout(30000)]
fn test_forall_with_true_body_classifies_as_implies() {
    // ∀ (x : A), True — body has no loose bvars, so classify_expr returns Implies.
    // This verifies the Forall path is only reached for genuine dependent binders.
    let env = setup_prop_env_with_eq();
    let bridge = SmtBridge::new(&env);
    let ty_a = prop("A");
    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    let forall_goal = Expr::pi(BinderInfo::Default, ty_a, true_const);

    let goal_class = bridge.classify_prop(&forall_goal);
    assert!(
        matches!(&goal_class, LogicalForm::Implies(_, _)),
        "∀ x : A, True should classify as Implies (non-dependent), got {:?}",
        goal_class
    );
}
