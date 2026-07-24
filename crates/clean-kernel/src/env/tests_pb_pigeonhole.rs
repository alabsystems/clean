// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for PB pigeonhole exponential separation formalization.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_pb_pigeonhole().expect("init_pb_pigeonhole");
    env
}

// ====================================================================
// Registration tests
// ====================================================================

#[test]
fn test_pb_constraint_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ProofTheory.PBConstraint"))
        .is_some());
}

#[test]
fn test_pb_proof_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.PBProof",
        "ProofTheory.PBProof.Axiom",
        "ProofTheory.PBProof.Addition",
        "ProofTheory.PBProof.Multiplication",
        "ProofTheory.PBProof.Division",
        "ProofTheory.PBProof.Saturation",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_all_definitions_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.PBConstraint",
        "ProofTheory.PBProof",
        "ProofTheory.PBProof.Axiom",
        "ProofTheory.PBProof.Addition",
        "ProofTheory.PBProof.Multiplication",
        "ProofTheory.PBProof.Division",
        "ProofTheory.PBProof.Saturation",
        "ProofTheory.pb_proof_size",
        "ProofTheory.pigeonhole_formula",
        "ProofTheory.pb_degree",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_all_theorems_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.pb_sound",
        "ProofTheory.pb_php_polynomial",
        "ProofTheory.resolution_php_exponential",
        "ProofTheory.pb_resolution_separation",
        "ProofTheory.pb_simulates_cp",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_helper_axioms_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.pb_sound_helper",
        "ProofTheory.pb_php_polynomial_helper",
        "ProofTheory.resolution_php_exponential_helper",
        "ProofTheory.pb_resolution_separation_helper",
        "ProofTheory.pb_simulates_cp_helper",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} helper should be registered"
        );
    }
}

// ====================================================================
// Type checking tests
// ====================================================================

#[test]
fn test_pb_proof_size_type_checks() {
    let env = make_env();
    let expr = crate::expr::Expr::const_(Name::from_string("ProofTheory.pb_proof_size"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&expr)
        .expect("infer ProofTheory.pb_proof_size type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_pb_degree_type_checks() {
    let env = make_env();
    let expr = crate::expr::Expr::const_(Name::from_string("ProofTheory.pb_degree"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&expr)
        .expect("infer ProofTheory.pb_degree type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_pigeonhole_formula_type_checks() {
    let env = make_env();
    let expr =
        crate::expr::Expr::const_(Name::from_string("ProofTheory.pigeonhole_formula"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&expr)
        .expect("infer ProofTheory.pigeonhole_formula type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_pb_sound_type_checks() {
    let env = make_env();
    let expr = crate::expr::Expr::const_(Name::from_string("ProofTheory.pb_sound"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&expr)
        .expect("infer ProofTheory.pb_sound type");
    // pb_sound : forall (p : PBProof), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_pb_php_polynomial_type_checks() {
    let env = make_env();
    let expr =
        crate::expr::Expr::const_(Name::from_string("ProofTheory.pb_php_polynomial"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&expr)
        .expect("infer ProofTheory.pb_php_polynomial type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_resolution_php_exponential_type_checks() {
    let env = make_env();
    let expr = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.resolution_php_exponential"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&expr)
        .expect("infer ProofTheory.resolution_php_exponential type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_pb_simulates_cp_type_checks() {
    let env = make_env();
    let expr = crate::expr::Expr::const_(Name::from_string("ProofTheory.pb_simulates_cp"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&expr)
        .expect("infer ProofTheory.pb_simulates_cp type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// ====================================================================
// Structural tests
// ====================================================================

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_pb_pigeonhole().expect("first init");
    env.init_pb_pigeonhole().expect("second init");
}

#[test]
fn test_naming_convention() {
    let env = make_env();
    // All declarations should use ProofTheory. prefix
    for name in [
        "ProofTheory.PBConstraint",
        "ProofTheory.PBProof",
        "ProofTheory.pb_proof_size",
        "ProofTheory.pigeonhole_formula",
        "ProofTheory.pb_degree",
        "ProofTheory.pb_sound",
        "ProofTheory.pb_php_polynomial",
        "ProofTheory.resolution_php_exponential",
        "ProofTheory.pb_resolution_separation",
        "ProofTheory.pb_simulates_cp",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered with ProofTheory. prefix"
        );
    }
    // Bare names should not exist
    for name in [
        "PBConstraint",
        "PBProof",
        "pb_proof_size",
        "pigeonhole_formula",
        "pb_degree",
        "pb_sound",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} should NOT be registered without ProofTheory. prefix"
        );
    }
}

#[test]
fn test_definition_vs_axiom_classification() {
    let env = make_env();
    // All PB pigeonhole declarations are axioms (opaque types/theorems)
    for name in [
        "ProofTheory.PBConstraint",
        "ProofTheory.PBProof",
        "ProofTheory.pb_proof_size",
        "ProofTheory.pigeonhole_formula",
        "ProofTheory.pb_degree",
        "ProofTheory.pb_sound",
        "ProofTheory.pb_php_polynomial",
        "ProofTheory.resolution_php_exponential",
        "ProofTheory.pb_resolution_separation",
        "ProofTheory.pb_simulates_cp",
    ] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(info.kind, ConstantKind::Axiom, "{name} should be an axiom");
    }
}

#[test]
fn test_cutting_planes_dependency() {
    // init_pb_pigeonhole should also initialize cutting planes
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ProofTheory.CuttingPlanesProof"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("ProofTheory.LinearInequality"))
        .is_some());
}

#[test]
fn test_resolution_complexity_dependency() {
    // init_pb_pigeonhole -> init_cutting_planes -> init_resolution_complexity
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ResComplexity.CNF"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("ResComplexity.TreeResProof"))
        .is_some());
}

#[test]
fn test_saturation_constructor_distinguishes_pb_from_cp() {
    // The saturation rule is the key distinguishing feature of PB over CP
    let env = make_env();
    let sat = env.get_const(&Name::from_string("ProofTheory.PBProof.Saturation"));
    assert!(
        sat.is_some(),
        "PBProof.Saturation should exist (PB-specific rule)"
    );
    // CP should not have saturation
    assert!(
        env.get_const(&Name::from_string(
            "ProofTheory.CuttingPlanesProof.Saturation"
        ))
        .is_none(),
        "CuttingPlanesProof should NOT have Saturation"
    );
}
