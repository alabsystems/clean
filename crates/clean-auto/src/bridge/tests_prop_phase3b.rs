// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Phase 3B propositional proof reconstruction tests (#2442).
//!
//! Covers Eq.symm and Eq.trans for non-reflexive equality sub-goals.

use super::super::*;
use crate::proof::ProofStep;
use clean_kernel::env::Declaration;
use clean_kernel::Level;
use ntest::timeout;

fn add_prop_basics(env: &mut Environment) {
    for (name, type_) in [
        (
            "And",
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            ),
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
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("True.intro"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("True"), vec![]),
    })
    .unwrap();
}

/// Build `@Eq.{u} bvar(n) bvar(m) bvar(k)` expression for declaration types.
fn mk_eq_app(u: &Name, alpha_idx: u32, lhs_idx: u32, rhs_idx: u32) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::param(u.clone())]),
                Expr::bvar(alpha_idx),
            ),
            Expr::bvar(lhs_idx),
        ),
        Expr::bvar(rhs_idx),
    )
}

fn add_eq_and_refl(env: &mut Environment, u: &Name) {
    // Eq : {α : Sort u} → α → α → Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq"),
        level_params: vec![u.clone()],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(u.clone())),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
            ),
        ),
    })
    .unwrap();

    // Eq.refl : {α : Sort u} → {a : α} → Eq α a a
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq.refl"),
        level_params: vec![u.clone()],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(u.clone())),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::bvar(0),
                mk_eq_app(u, 1, 0, 0), // Eq α a a
            ),
        ),
    })
    .unwrap();
}

fn add_eq_symm_and_trans(env: &mut Environment, u: &Name) {
    // Eq.symm : {α : Sort u} → {a b : α} → Eq α a b → Eq α b a
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq.symm"),
        level_params: vec![u.clone()],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(u.clone())),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::bvar(0), // a
                Expr::pi(
                    BinderInfo::Implicit,
                    Expr::bvar(1), // b
                    Expr::pi(
                        BinderInfo::Default,
                        mk_eq_app(u, 2, 1, 0), // Eq α a b
                        mk_eq_app(u, 3, 1, 2), // → Eq α b a
                    ),
                ),
            ),
        ),
    })
    .unwrap();

    // Eq.trans : {α} → {a b c} → Eq α a b → Eq α b c → Eq α a c
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Eq.trans"),
        level_params: vec![u.clone()],
        type_: Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::param(u.clone())),
            Expr::pi(
                BinderInfo::Implicit,
                Expr::bvar(0), // a
                Expr::pi(
                    BinderInfo::Implicit,
                    Expr::bvar(1), // b
                    Expr::pi(
                        BinderInfo::Implicit,
                        Expr::bvar(2), // c
                        Expr::pi(
                            BinderInfo::Default,
                            mk_eq_app(u, 3, 2, 1), // Eq α a b
                            Expr::pi(
                                BinderInfo::Default,
                                mk_eq_app(u, 4, 2, 1), // Eq α b c
                                mk_eq_app(u, 5, 4, 2), // → Eq α a c
                            ),
                        ),
                    ),
                ),
            ),
        ),
    })
    .unwrap();
}

/// Environment with Eq, Eq.refl, Eq.symm, Eq.trans, type A, constants a/b/c.
fn setup_eq_env() -> Environment {
    let mut env = Environment::new();
    add_prop_basics(&mut env);
    let u = Name::from_string("u");
    add_eq_and_refl(&mut env, &u);
    add_eq_symm_and_trans(&mut env, &u);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    for name in ["a", "b", "c"] {
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

fn mk_and(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), a.clone()),
        b.clone(),
    )
}

// --- Eq.symm tests ---

#[test]
#[timeout(30000)]
fn test_eq_symm_from_reversed_hypothesis() {
    let env = setup_eq_env();
    let mut bridge = SmtBridge::new(&env);
    let ty_a = prop("A");
    let a = prop("a");
    let b = prop("b");

    let eq_b_a = mk_eq_type(&ty_a, &b, &a);
    bridge.prop_hypotheses.push((FVarId::new(10), eq_b_a));

    let eq_a_b = mk_eq_type(&ty_a, &a, &b);
    let goal_class = bridge.classify_prop(&eq_a_b);
    let result = bridge.build_propositional_proof(&goal_class, &eq_a_b);
    assert!(
        result.is_ok(),
        "Eq(A,a,b) with h:b=a should succeed via Eq.symm: {:?}",
        result.err()
    );
    let (step, proof) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Eq.symm"));
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Eq.symm")),
    );
}

#[test]
#[timeout(30000)]
fn test_eq_symm_in_conjunction() {
    let env = setup_eq_env();
    let mut bridge = SmtBridge::new(&env);
    let (ty_a, a, b) = (prop("A"), prop("a"), prop("b"));

    bridge
        .prop_hypotheses
        .push((FVarId::new(10), mk_eq_type(&ty_a, &b, &a)));

    let and_goal = mk_and(
        &mk_eq_type(&ty_a, &a, &b),
        &Expr::const_(Name::from_string("True"), vec![]),
    );
    let goal_class = bridge.classify_prop(&and_goal);
    let result = bridge.build_propositional_proof(&goal_class, &and_goal);
    assert!(
        result.is_ok(),
        "And(Eq(A,a,b), True) with h:b=a: {:?}",
        result.err()
    );
    assert!(matches!(&result.unwrap().0, ProofStep::Propositional(s) if s == "And.intro"));
}

#[test]
#[timeout(30000)]
fn test_eq_symm_not_triggered_for_direct_match() {
    let env = setup_eq_env();
    let mut bridge = SmtBridge::new(&env);
    let eq_a_b = mk_eq_type(&prop("A"), &prop("a"), &prop("b"));
    bridge
        .prop_hypotheses
        .push((FVarId::new(10), eq_a_b.clone()));

    let goal_class = bridge.classify_prop(&eq_a_b);
    let result = bridge.build_propositional_proof(&goal_class, &eq_a_b);
    assert!(result.is_ok());
    assert!(
        matches!(&result.unwrap().0, ProofStep::Propositional(s) if s == "hypothesis_match"),
        "direct match should use hypothesis_match"
    );
}

// --- Eq.trans tests ---

#[test]
#[timeout(30000)]
fn test_eq_trans_direct_chain() {
    let env = setup_eq_env();
    let mut bridge = SmtBridge::new(&env);
    let (ty_a, a, b, c) = (prop("A"), prop("a"), prop("b"), prop("c"));

    bridge
        .prop_hypotheses
        .push((FVarId::new(10), mk_eq_type(&ty_a, &a, &b)));
    bridge
        .prop_hypotheses
        .push((FVarId::new(11), mk_eq_type(&ty_a, &b, &c)));

    let eq_a_c = mk_eq_type(&ty_a, &a, &c);
    let goal_class = bridge.classify_prop(&eq_a_c);
    let result = bridge.build_propositional_proof(&goal_class, &eq_a_c);
    assert!(
        result.is_ok(),
        "a=c from h1:a=b, h2:b=c: {:?}",
        result.err()
    );
    let (step, proof) = result.unwrap();
    assert!(matches!(&step, ProofStep::Propositional(s) if s == "Eq.trans"));
    let head = proof.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(name, _) if *name == Name::from_string("Eq.trans")),
    );
}

#[test]
#[timeout(30000)]
fn test_eq_trans_with_first_reversed() {
    let env = setup_eq_env();
    let mut bridge = SmtBridge::new(&env);
    let (ty_a, a, b, c) = (prop("A"), prop("a"), prop("b"), prop("c"));

    bridge
        .prop_hypotheses
        .push((FVarId::new(10), mk_eq_type(&ty_a, &b, &a)));
    bridge
        .prop_hypotheses
        .push((FVarId::new(11), mk_eq_type(&ty_a, &b, &c)));

    let eq_a_c = mk_eq_type(&ty_a, &a, &c);
    let goal_class = bridge.classify_prop(&eq_a_c);
    let result = bridge.build_propositional_proof(&goal_class, &eq_a_c);
    assert!(
        result.is_ok(),
        "a=c from h1:b=a, h2:b=c via symm h1: {:?}",
        result.err()
    );
    assert!(matches!(&result.unwrap().0, ProofStep::Propositional(s) if s == "Eq.trans"));
}

#[test]
#[timeout(30000)]
fn test_eq_trans_with_second_reversed() {
    let env = setup_eq_env();
    let mut bridge = SmtBridge::new(&env);
    let (ty_a, a, b, c) = (prop("A"), prop("a"), prop("b"), prop("c"));

    bridge
        .prop_hypotheses
        .push((FVarId::new(10), mk_eq_type(&ty_a, &a, &b)));
    bridge
        .prop_hypotheses
        .push((FVarId::new(11), mk_eq_type(&ty_a, &c, &b)));

    let eq_a_c = mk_eq_type(&ty_a, &a, &c);
    let goal_class = bridge.classify_prop(&eq_a_c);
    let result = bridge.build_propositional_proof(&goal_class, &eq_a_c);
    assert!(
        result.is_ok(),
        "a=c from h1:a=b, h2:c=b via symm h2: {:?}",
        result.err()
    );
    assert!(matches!(&result.unwrap().0, ProofStep::Propositional(s) if s == "Eq.trans"));
}

#[test]
#[timeout(30000)]
fn test_eq_trans_in_conjunction() {
    let env = setup_eq_env();
    let mut bridge = SmtBridge::new(&env);
    let (ty_a, a, b, c) = (prop("A"), prop("a"), prop("b"), prop("c"));

    bridge
        .prop_hypotheses
        .push((FVarId::new(10), mk_eq_type(&ty_a, &a, &b)));
    bridge
        .prop_hypotheses
        .push((FVarId::new(11), mk_eq_type(&ty_a, &b, &c)));

    let and_goal = mk_and(
        &mk_eq_type(&ty_a, &a, &c),
        &Expr::const_(Name::from_string("True"), vec![]),
    );
    let goal_class = bridge.classify_prop(&and_goal);
    let result = bridge.build_propositional_proof(&goal_class, &and_goal);
    assert!(
        result.is_ok(),
        "And(a=c, True) from h1:a=b, h2:b=c: {:?}",
        result.err()
    );
    assert!(matches!(&result.unwrap().0, ProofStep::Propositional(s) if s == "And.intro"));
}

#[test]
#[timeout(30000)]
fn test_eq_trans_with_both_reversed() {
    let env = setup_eq_env();
    let mut bridge = SmtBridge::new(&env);
    let (ty_a, a, b, c) = (prop("A"), prop("a"), prop("b"), prop("c"));

    bridge
        .prop_hypotheses
        .push((FVarId::new(10), mk_eq_type(&ty_a, &b, &a)));
    bridge
        .prop_hypotheses
        .push((FVarId::new(11), mk_eq_type(&ty_a, &c, &b)));

    let eq_a_c = mk_eq_type(&ty_a, &a, &c);
    let goal_class = bridge.classify_prop(&eq_a_c);
    let result = bridge.build_propositional_proof(&goal_class, &eq_a_c);
    assert!(
        result.is_ok(),
        "a=c from h1:b=a, h2:c=b via symm/symm: {:?}",
        result.err()
    );
    assert!(matches!(&result.unwrap().0, ProofStep::Propositional(s) if s == "Eq.trans"));
}

#[test]
#[timeout(30000)]
fn test_eq_no_hypothesis_still_fails() {
    let env = setup_eq_env();
    let bridge = SmtBridge::new(&env);
    let eq_a_b = mk_eq_type(&prop("A"), &prop("a"), &prop("b"));
    let goal_class = bridge.classify_prop(&eq_a_b);
    let result = bridge.build_propositional_proof(&goal_class, &eq_a_b);
    assert!(
        matches!(result, Err(BridgeError::UnsupportedExpr { .. })),
        "Eq(A,a,b) with no hypotheses should fail with UnsupportedExpr, got {:?}",
        result
    );
}
