// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for cutting planes proof system formalization.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_cutting_planes().expect("init_cutting_planes");
    env
}

#[test]
fn test_linear_inequality_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ProofTheory.LinearInequality"))
        .is_some());
}

#[test]
fn test_cp_proof_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.CuttingPlanesProof",
        "ProofTheory.CuttingPlanesProof.Axiom",
        "ProofTheory.CuttingPlanesProof.Add",
        "ProofTheory.CuttingPlanesProof.Multiply",
        "ProofTheory.CuttingPlanesProof.Divide",
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
        "ProofTheory.LinearInequality",
        "ProofTheory.CuttingPlanesProof",
        "ProofTheory.CuttingPlanesProof.Axiom",
        "ProofTheory.CuttingPlanesProof.Add",
        "ProofTheory.CuttingPlanesProof.Multiply",
        "ProofTheory.CuttingPlanesProof.Divide",
        "ProofTheory.cp_proof_size",
        "ProofTheory.cp_degree",
        "ProofTheory.resolution_to_cp",
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
        "ProofTheory.cp_sound",
        "ProofTheory.cp_simulates_resolution",
        "ProofTheory.cp_simulation_size_bound",
        "ProofTheory.cp_php_exponential",
        "ProofTheory.cp_separation_from_resolution",
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
        "ProofTheory.cp_sound_helper",
        "ProofTheory.cp_simulates_resolution_helper",
        "ProofTheory.cp_simulation_size_bound_helper",
        "ProofTheory.cp_php_exponential_helper",
        "ProofTheory.cp_separation_helper",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} helper should be registered"
        );
    }
}

#[test]
fn test_cp_proof_size_type_checks() {
    let env = make_env();
    let cp_size = crate::expr::Expr::const_(Name::from_string("ProofTheory.cp_proof_size"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&cp_size)
        .expect("infer ProofTheory.cp_proof_size type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_cp_sound_type_checks() {
    let env = make_env();
    let cp_sound = crate::expr::Expr::const_(Name::from_string("ProofTheory.cp_sound"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&cp_sound)
        .expect("infer ProofTheory.cp_sound type");
    // cp_sound : forall (p : CuttingPlanesProof), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_cp_simulates_resolution_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.cp_simulates_resolution"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer ProofTheory.cp_simulates_resolution type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_cp_php_exponential_type_checks() {
    let env = make_env();
    let thm =
        crate::expr::Expr::const_(Name::from_string("ProofTheory.cp_php_exponential"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer ProofTheory.cp_php_exponential type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_cutting_planes().expect("first init");
    env.init_cutting_planes().expect("second init");
}

#[test]
fn test_naming_convention() {
    let env = make_env();
    // All declarations should use ProofTheory. prefix
    for name in [
        "ProofTheory.LinearInequality",
        "ProofTheory.CuttingPlanesProof",
        "ProofTheory.cp_proof_size",
        "ProofTheory.cp_degree",
        "ProofTheory.resolution_to_cp",
        "ProofTheory.cp_sound",
        "ProofTheory.cp_simulates_resolution",
        "ProofTheory.cp_simulation_size_bound",
        "ProofTheory.cp_php_exponential",
        "ProofTheory.cp_separation_from_resolution",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered with ProofTheory. prefix",
        );
    }
    // Bare names should not exist
    for name in [
        "LinearInequality",
        "CuttingPlanesProof",
        "cp_proof_size",
        "cp_degree",
        "resolution_to_cp",
        "cp_sound",
        "cp_simulates_resolution",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} should NOT be registered without ProofTheory. prefix",
        );
    }
}

#[test]
fn test_definition_vs_axiom_classification() {
    let env = make_env();
    // All cutting planes declarations are axioms (opaque types/theorems)
    for name in [
        "ProofTheory.LinearInequality",
        "ProofTheory.CuttingPlanesProof",
        "ProofTheory.cp_proof_size",
        "ProofTheory.cp_degree",
        "ProofTheory.resolution_to_cp",
        "ProofTheory.cp_sound",
        "ProofTheory.cp_simulates_resolution",
        "ProofTheory.cp_simulation_size_bound",
        "ProofTheory.cp_php_exponential",
        "ProofTheory.cp_separation_from_resolution",
    ] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(info.kind, ConstantKind::Axiom, "{name} should be an axiom");
    }
}

#[test]
fn test_resolution_complexity_dependency() {
    // init_cutting_planes should also initialize resolution complexity
    let env = make_env();
    // Check that ResComplexity types are available (dependency)
    assert!(env
        .get_const(&Name::from_string("ResComplexity.CNF"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("ResComplexity.TreeResProof"))
        .is_some());
}
