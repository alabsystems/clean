// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::tactic::builtins::register_builtin_tactics;
use crate::tactic::registry::TacticRegistry;
use serial_test::serial;

#[test]
#[serial]
fn test_ay_decide_reflexivity_uses_no_trusted_axioms() {
    reset_all_counters();
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let target = make_eq(a_ty, a.clone(), a);

    let mut state = ProofState::new(env, target);
    let ax = axiom_snapshot();

    ay_decide(&mut state, AyConfig::default())
        .expect("ay_decide should prove reflexive equalities");

    assert!(
        state.is_complete(),
        "ay_decide should close the reflexive goal"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "ay_decide reflexivity should not spend trusted axioms"
    );
    assert_no_trusted_axiom_usage("ay_decide", "reflexive equality", ax);
}

#[test]
#[serial]
fn test_ay_smt_reflexivity_uses_no_trusted_axioms() {
    reset_all_counters();
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let target = make_eq(a_ty, a.clone(), a);

    let mut state = ProofState::new(env, target);
    let ax = axiom_snapshot();

    ay_smt(&mut state, AyConfig::default()).expect("ay_smt should prove reflexive equalities");

    assert!(
        state.is_complete(),
        "ay_smt should close the reflexive goal"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "ay_smt reflexivity should not spend trusted axioms"
    );
    assert_no_trusted_axiom_usage("ay_smt", "reflexive equality", ax);
}

#[test]
#[serial]
fn test_ay_omega_hypothesis_forwarding_uses_no_trusted_axioms() {
    reset_all_counters();
    let env = setup_env_with_eq();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let h_ty = make_eq(a_ty.clone(), a.clone(), b.clone());
    let h_decl = LocalDecl {
        fvar: FVarId::new(0),
        name: "h".to_string(),
        ty: h_ty,
        value: None,
    };
    let target = make_eq(a_ty, a, b);

    let mut state = ProofState::with_context(env, target, vec![h_decl]);
    let ax = axiom_snapshot();

    ay_omega(&mut state, AyConfig::default())
        .expect("ay_omega should use hypotheses to close matching goals");

    assert!(
        state.is_complete(),
        "ay_omega should close the hypothesis goal"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "ay_omega hypothesis forwarding should not spend trusted axioms"
    );
    assert_no_trusted_axiom_usage("ay_omega", "hypothesis forwarding", ax);
}

#[test]
#[serial]
fn test_ay_registry_dispatch_reflexivity_uses_no_trusted_axioms() {
    reset_all_counters();

    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_trusted_ay().unwrap();
    env.add_decl(clean_kernel::env::Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    env.add_decl(clean_kernel::env::Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
    })
    .unwrap();

    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);
    let entry = registry
        .get("ay_decide")
        .expect("ay_decide must be registered");

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let target = make_eq(a_ty, a.clone(), a);

    let mut state = ProofState::new(env, target);
    let ax = axiom_snapshot();

    (entry.handler)(&mut state, &[]).expect("ay_decide registry handler should close reflexivity");

    assert!(
        state.is_complete(),
        "registry dispatch should close the reflexive goal"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "registry-dispatched ay_decide reflexivity should not spend trusted axioms"
    );
    assert_no_trusted_axiom_usage("ay_decide registry", "reflexive equality", ax);
}
