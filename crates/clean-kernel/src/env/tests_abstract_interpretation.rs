// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for abstract interpretation framework formalization.
//!
//! Part of #3189.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_abstract_interpretation()
        .expect("init_abstract_interpretation");
    env
}

// ---------------------------------------------------------------
// Infrastructure type registration tests
// ---------------------------------------------------------------

#[test]
fn test_abstract_interpretation_abstract_state_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.AbstractState"))
        .is_some());
}

#[test]
fn test_abstract_interpretation_inst_le_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.instLEAbstractState"))
        .is_some());
}

// ---------------------------------------------------------------
// Definition registration tests
// ---------------------------------------------------------------

#[test]
fn test_abstract_interpretation_concrete_semantics_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.ConcreteSemantics"))
        .is_some());
}

#[test]
fn test_abstract_interpretation_abstract_semantics_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.AbstractSemantics"))
        .is_some());
}

#[test]
fn test_abstract_interpretation_widening_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Widening"))
        .is_some());
}

#[test]
fn test_abstract_interpretation_narrowing_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Narrowing"))
        .is_some());
}

#[test]
fn test_abstract_interpretation_fixpoint_iteration_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.fixpoint_iteration"))
        .is_some());
}

// ---------------------------------------------------------------
// Theorem registration tests
// ---------------------------------------------------------------

#[test]
fn test_abstract_interpretation_soundness_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string("AbstractInterp.soundness"))
            .is_some(),
        "soundness theorem should be registered"
    );
    assert!(
        env.get_const(&Name::from_string("AbstractInterp.soundness_axiom"))
            .is_some(),
        "soundness_axiom should be registered"
    );
}

#[test]
fn test_abstract_interpretation_widening_termination_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.widening_termination"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.widening_termination_axiom"
        ))
        .is_some());
}

#[test]
fn test_abstract_interpretation_narrowing_refines_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.narrowing_refines"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.narrowing_refines_axiom"))
        .is_some());
}

#[test]
fn test_abstract_interpretation_fixpoint_sound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.fixpoint_sound"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.fixpoint_sound_axiom"))
        .is_some());
}

#[test]
fn test_abstract_interpretation_domain_product_sound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.domain_product_sound"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.domain_product_sound_axiom"
        ))
        .is_some());
}

// ---------------------------------------------------------------
// Type checking tests
// ---------------------------------------------------------------

#[test]
fn test_abstract_interpretation_concrete_semantics_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("AbstractInterp.ConcreteSemantics"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer ConcreteSemantics type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_abstract_interpretation_abstract_semantics_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("AbstractInterp.AbstractSemantics"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer AbstractSemantics type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_abstract_interpretation_widening_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("AbstractInterp.Widening"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer Widening type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_abstract_interpretation_fixpoint_iteration_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("AbstractInterp.fixpoint_iteration"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer fixpoint_iteration type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_abstract_interpretation_soundness_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("AbstractInterp.soundness"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer soundness type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_abstract_interpretation_narrowing_refines_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("AbstractInterp.narrowing_refines"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer narrowing_refines type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// ---------------------------------------------------------------
// Definition vs axiom classification tests
// ---------------------------------------------------------------

#[test]
fn test_abstract_interpretation_definitions_are_axioms() {
    let env = make_env();
    for name in &[
        "AbstractInterp.AbstractState",
        "AbstractInterp.instLEAbstractState",
        "AbstractInterp.ConcreteSemantics",
        "AbstractInterp.AbstractSemantics",
        "AbstractInterp.Widening",
        "AbstractInterp.Narrowing",
        "AbstractInterp.fixpoint_iteration",
    ] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Axiom,
            "{name} should be an Axiom (definition-as-axiom pattern)"
        );
    }
}

#[test]
fn test_abstract_interpretation_theorem_axiom_pairs() {
    let env = make_env();
    let theorems = [
        "AbstractInterp.soundness",
        "AbstractInterp.widening_termination",
        "AbstractInterp.narrowing_refines",
        "AbstractInterp.fixpoint_sound",
        "AbstractInterp.domain_product_sound",
    ];
    for thm_name in &theorems {
        let info = env
            .get_const(&Name::from_string(thm_name))
            .unwrap_or_else(|| panic!("{thm_name} should be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{thm_name} should be a Theorem"
        );
        assert!(info.value.is_some(), "{thm_name} should have a proof term");

        let axiom_name = format!("{thm_name}_axiom");
        let axiom_info = env
            .get_const(&Name::from_string(&axiom_name))
            .unwrap_or_else(|| panic!("{axiom_name} should be registered"));
        assert_eq!(
            axiom_info.kind,
            ConstantKind::Axiom,
            "{axiom_name} should be an Axiom"
        );
    }
}

// ---------------------------------------------------------------
// AbstractInterp prefix naming convention test
// ---------------------------------------------------------------

#[test]
fn test_abstract_interpretation_naming_convention() {
    let env = make_env();
    let names = [
        "AbstractInterp.AbstractState",
        "AbstractInterp.instLEAbstractState",
        "AbstractInterp.ConcreteSemantics",
        "AbstractInterp.AbstractSemantics",
        "AbstractInterp.Widening",
        "AbstractInterp.Narrowing",
        "AbstractInterp.fixpoint_iteration",
        "AbstractInterp.soundness",
        "AbstractInterp.soundness_axiom",
        "AbstractInterp.widening_termination",
        "AbstractInterp.widening_termination_axiom",
        "AbstractInterp.narrowing_refines",
        "AbstractInterp.narrowing_refines_axiom",
        "AbstractInterp.fixpoint_sound",
        "AbstractInterp.fixpoint_sound_axiom",
        "AbstractInterp.domain_product_sound",
        "AbstractInterp.domain_product_sound_axiom",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
        assert!(
            name.starts_with("AbstractInterp."),
            "{name} must use AbstractInterp. prefix",
        );
    }
}

// ---------------------------------------------------------------
// Idempotency test
// ---------------------------------------------------------------

#[test]
fn test_abstract_interpretation_idempotent() {
    let mut env = Environment::new();
    env.init_abstract_interpretation().expect("first init");
    env.init_abstract_interpretation().expect("second init");
}
