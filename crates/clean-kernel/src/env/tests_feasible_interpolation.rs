// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for feasible interpolation formalization.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_feasible_interpolation()
        .expect("init_feasible_interpolation");
    env
}

// ====================================================================
// Registration tests
// ====================================================================

#[test]
fn test_all_definitions_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.FeasibleInterpolant",
        "ProofTheory.communication_complexity",
        "ProofTheory.monotone_circuit",
        "ProofTheory.monotone_circuit.Input",
        "ProofTheory.monotone_circuit.And",
        "ProofTheory.monotone_circuit.Or",
        "ProofTheory.monotone_circuit_size",
        "ProofTheory.dag_like_proof",
        "ProofTheory.dag_like_proof.Axiom",
        "ProofTheory.dag_like_proof.Resolve",
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
        "ProofTheory.pudlak_feasible_interpolation",
        "ProofTheory.interpolant_to_monotone_circuit",
        "ProofTheory.monotone_circuit_lower_bound",
        "ProofTheory.feasible_interpolation_lower_bound",
        "ProofTheory.dag_vs_tree_separation",
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
        "ProofTheory.pudlak_feasible_interpolation_helper",
        "ProofTheory.interpolant_to_monotone_circuit_helper",
        "ProofTheory.monotone_circuit_lower_bound_helper",
        "ProofTheory.feasible_interpolation_lower_bound_helper",
        "ProofTheory.dag_vs_tree_separation_helper",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} helper should be registered"
        );
    }
}

// ====================================================================
// Type-checking tests
// ====================================================================

#[test]
fn test_feasible_interpolant_type_checks() {
    let env = make_env();
    let fi =
        crate::expr::Expr::const_(Name::from_string("ProofTheory.FeasibleInterpolant"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&fi)
        .expect("infer ProofTheory.FeasibleInterpolant type");
    // FeasibleInterpolant : PropFormula -> PropFormula -> Resolution.Proof -> Type
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_communication_complexity_type_checks() {
    let env = make_env();
    let cc = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.communication_complexity"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&cc)
        .expect("infer ProofTheory.communication_complexity type");
    // communication_complexity : PropFormula -> PropFormula -> Nat
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_monotone_circuit_type_checks() {
    let env = make_env();
    let mc = crate::expr::Expr::const_(Name::from_string("ProofTheory.monotone_circuit"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&mc)
        .expect("infer ProofTheory.monotone_circuit type");
    // monotone_circuit : Type 0, so its type is Sort(1)
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_monotone_circuit_size_type_checks() {
    let env = make_env();
    let mcs = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.monotone_circuit_size"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&mcs)
        .expect("infer ProofTheory.monotone_circuit_size type");
    // monotone_circuit_size : monotone_circuit -> Nat
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_dag_like_proof_type_checks() {
    let env = make_env();
    let dag = crate::expr::Expr::const_(Name::from_string("ProofTheory.dag_like_proof"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&dag)
        .expect("infer ProofTheory.dag_like_proof type");
    // dag_like_proof : Type 0, so its type is Sort(1)
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_pudlak_theorem_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.pudlak_feasible_interpolation"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer pudlak_feasible_interpolation type");
    // forall (a b : PropFormula) (p : Resolution.Proof), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_monotone_circuit_lower_bound_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.monotone_circuit_lower_bound"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer monotone_circuit_lower_bound type");
    // forall (n : Nat), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_dag_vs_tree_separation_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.dag_vs_tree_separation"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer dag_vs_tree_separation type");
    // forall (n : Nat), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// ====================================================================
// Idempotency test
// ====================================================================

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_feasible_interpolation().expect("first init");
    env.init_feasible_interpolation().expect("second init");
}

// ====================================================================
// Classification tests
// ====================================================================

#[test]
fn test_definition_vs_axiom_classification() {
    let env = make_env();
    // All type declarations and operations should be axioms (opaque)
    let axiom_names = [
        "ProofTheory.FeasibleInterpolant",
        "ProofTheory.communication_complexity",
        "ProofTheory.monotone_circuit",
        "ProofTheory.monotone_circuit.Input",
        "ProofTheory.monotone_circuit.And",
        "ProofTheory.monotone_circuit.Or",
        "ProofTheory.monotone_circuit_size",
        "ProofTheory.dag_like_proof",
        "ProofTheory.dag_like_proof.Axiom",
        "ProofTheory.dag_like_proof.Resolve",
        "ProofTheory.pudlak_feasible_interpolation",
        "ProofTheory.interpolant_to_monotone_circuit",
        "ProofTheory.monotone_circuit_lower_bound",
        "ProofTheory.feasible_interpolation_lower_bound",
        "ProofTheory.dag_vs_tree_separation",
    ];
    for name in axiom_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(info.kind, ConstantKind::Axiom, "{name} should be an axiom");
    }
}

// ====================================================================
// Naming convention tests
// ====================================================================

#[test]
fn test_naming_convention() {
    let env = make_env();
    // All declarations should use ProofTheory. prefix
    for name in [
        "ProofTheory.FeasibleInterpolant",
        "ProofTheory.communication_complexity",
        "ProofTheory.monotone_circuit",
        "ProofTheory.monotone_circuit_size",
        "ProofTheory.dag_like_proof",
        "ProofTheory.pudlak_feasible_interpolation",
        "ProofTheory.interpolant_to_monotone_circuit",
        "ProofTheory.monotone_circuit_lower_bound",
        "ProofTheory.feasible_interpolation_lower_bound",
        "ProofTheory.dag_vs_tree_separation",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered with ProofTheory. prefix",
        );
    }
    // Bare names should not exist
    for name in [
        "FeasibleInterpolant",
        "communication_complexity",
        "monotone_circuit",
        "monotone_circuit_size",
        "dag_like_proof",
        "pudlak_feasible_interpolation",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} should NOT be registered without ProofTheory. prefix",
        );
    }
}

// ====================================================================
// Dependency tests
// ====================================================================

#[test]
fn test_craig_interpolation_deps_available() {
    // Feasible interpolation depends on Craig interpolation types
    let env = make_env();
    // These should be available from the Craig interpolation dependency
    for name in ["ProofTheory.PropFormula", "ProofTheory.Resolution.Proof"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be available from Craig interpolation dependency"
        );
    }
}

#[test]
fn test_monotone_circuit_constructors_type_check() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    // Input : Nat -> monotone_circuit
    let input = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.monotone_circuit.Input"),
        vec![],
    );
    let ty = tc
        .infer_type(&input)
        .expect("infer monotone_circuit.Input type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));

    // And : monotone_circuit -> monotone_circuit -> monotone_circuit
    let and = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.monotone_circuit.And"),
        vec![],
    );
    let ty = tc
        .infer_type(&and)
        .expect("infer monotone_circuit.And type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));

    // Or : monotone_circuit -> monotone_circuit -> monotone_circuit
    let or =
        crate::expr::Expr::const_(Name::from_string("ProofTheory.monotone_circuit.Or"), vec![]);
    let ty = tc.infer_type(&or).expect("infer monotone_circuit.Or type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_dag_like_proof_constructors_type_check() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());

    // Axiom : PropFormula -> dag_like_proof
    let axiom = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.dag_like_proof.Axiom"),
        vec![],
    );
    let ty = tc
        .infer_type(&axiom)
        .expect("infer dag_like_proof.Axiom type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));

    // Resolve : Nat -> Nat -> Nat -> dag_like_proof
    let resolve = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.dag_like_proof.Resolve"),
        vec![],
    );
    let ty = tc
        .infer_type(&resolve)
        .expect("infer dag_like_proof.Resolve type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}
