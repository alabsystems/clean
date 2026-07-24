// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for interpolation kernel proofs (I01-I04).
//!
//! Verifies that all inductive types and theorem declarations are registered
//! and type-check through the kernel type checker.
//!
//! Part of #3365: Phase 4 kernel proofs.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_interpolation_proofs()
        .expect("init_interpolation_proofs");
    env
}

#[test]
fn test_interp_node_registered() {
    let env = make_env();
    for name in [
        "InterpolationSAT.InterpNode",
        "InterpolationSAT.InterpNode.a_input",
        "InterpolationSAT.InterpNode.b_input",
        "InterpolationSAT.InterpNode.resolve_a_pivot",
        "InterpolationSAT.InterpNode.resolve_b_pivot",
        "InterpolationSAT.InterpNode.resolve_shared",
        "InterpolationSAT.InterpNode.rec",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_witness_types_registered() {
    let env = make_env();
    for prefix in [
        "InterpolationSAT.CraigWitness",
        "InterpolationSAT.McMillanExtracted",
        "InterpolationSAT.SharedVarsWitness",
        "InterpolationSAT.PudlakWitness",
    ] {
        for suffix in [
            "",
            ".a_input",
            ".b_input",
            ".resolve_a_pivot",
            ".resolve_b_pivot",
            ".resolve_shared",
        ] {
            let name = format!("{prefix}{suffix}");
            assert!(
                env.get_const(&Name::from_string(&name)).is_some(),
                "{name} should be registered"
            );
        }
    }
}

#[test]
fn test_i01_theorem_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("InterpolationSAT.i01_craig_existence"))
        .is_some());
}

#[test]
fn test_i02_theorem_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "InterpolationSAT.i02_mcmillan_extraction"
        ))
        .is_some());
}

#[test]
fn test_i03_theorem_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("InterpolationSAT.i03_shared_variables"))
        .is_some());
}

#[test]
fn test_i04_theorem_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("InterpolationSAT.i04_pudlak_rule"))
        .is_some());
}

#[test]
fn test_i01_is_theorem_not_axiom() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("InterpolationSAT.i01_craig_existence"))
        .expect("i01 should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "I01 should be a Theorem, not an Axiom"
    );
}

#[test]
fn test_i02_is_theorem_not_axiom() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(
            "InterpolationSAT.i02_mcmillan_extraction",
        ))
        .expect("i02 should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "I02 should be a Theorem, not an Axiom"
    );
}

#[test]
fn test_i03_is_theorem_not_axiom() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("InterpolationSAT.i03_shared_variables"))
        .expect("i03 should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "I03 should be a Theorem, not an Axiom"
    );
}

#[test]
fn test_i04_is_theorem_not_axiom() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("InterpolationSAT.i04_pudlak_rule"))
        .expect("i04 should exist");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "I04 should be a Theorem, not an Axiom"
    );
}

#[test]
fn test_i01_type_checks() {
    let env = make_env();
    let expr = crate::expr::Expr::const_(
        Name::from_string("InterpolationSAT.i01_craig_existence"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&expr).expect("I01 should type-check");
    // forall (nv : Nat) (node : InterpNode nv), CraigWitness nv node
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_i02_type_checks() {
    let env = make_env();
    let expr = crate::expr::Expr::const_(
        Name::from_string("InterpolationSAT.i02_mcmillan_extraction"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&expr).expect("I02 should type-check");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_i03_type_checks() {
    let env = make_env();
    let expr = crate::expr::Expr::const_(
        Name::from_string("InterpolationSAT.i03_shared_variables"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&expr).expect("I03 should type-check");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_i04_type_checks() {
    let env = make_env();
    let expr = crate::expr::Expr::const_(
        Name::from_string("InterpolationSAT.i04_pudlak_rule"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&expr).expect("I04 should type-check");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_interp_node_type_checks() {
    let env = make_env();
    let expr = crate::expr::Expr::const_(Name::from_string("InterpolationSAT.InterpNode"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&expr).expect("InterpNode should type-check");
    // InterpNode : Nat -> Type
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_interp_node_rec_type_checks() {
    let env = make_env();
    let expr =
        crate::expr::Expr::const_(Name::from_string("InterpolationSAT.InterpNode.rec"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&expr)
        .expect("InterpNode.rec should type-check");
    // rec : (nv : Nat) -> (motive : ...) -> ... -> InterpNode nv -> motive t
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_interpolation_proofs().expect("first init");
    env.init_interpolation_proofs().expect("second init");
}

#[test]
fn test_craig_interpolation_dependency() {
    // init_interpolation_proofs should also initialize Craig interpolation defs
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ProofTheory.PropFormula"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("ProofTheory.interpolant"))
        .is_some());
}
