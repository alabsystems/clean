// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for proof complexity hierarchy formalization.

use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_proof_hierarchy().expect("init_proof_hierarchy");
    env
}

// ====================================================================
// Registration tests
// ====================================================================

#[test]
fn test_proof_system_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ProofTheory.ProofSystem"))
        .is_some());
}

#[test]
fn test_formula_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ProofTheory.Formula"))
        .is_some());
}

#[test]
fn test_p_simulation_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ProofTheory.PSimulation"))
        .is_some());
}

#[test]
fn test_frege_proof_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ProofTheory.FregeProof"))
        .is_some());
}

#[test]
fn test_extended_frege_proof_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ProofTheory.ExtendedFregeProof"))
        .is_some());
}

#[test]
fn test_all_definitions_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.Formula",
        "ProofTheory.ProofSystem",
        "ProofTheory.PSimulation",
        "ProofTheory.FregeProof",
        "ProofTheory.ExtendedFregeProof",
        "ProofTheory.frege_proof_size",
        "ProofTheory.simulation_gap",
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
        "ProofTheory.resolution_below_cp",
        "ProofTheory.cp_below_frege",
        "ProofTheory.frege_below_extended_frege",
        "ProofTheory.resolution_exponential_gap",
        "ProofTheory.cook_reckhow_completeness",
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
        "ProofTheory.resolution_below_cp_helper",
        "ProofTheory.cp_below_frege_helper",
        "ProofTheory.frege_below_ef_helper",
        "ProofTheory.resolution_exp_gap_helper",
        "ProofTheory.cook_reckhow_helper",
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
fn test_proof_system_type_checks() {
    let env = make_env();
    let ps = crate::expr::Expr::const_(Name::from_string("ProofTheory.ProofSystem"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&ps)
        .expect("infer ProofTheory.ProofSystem type");
    // ProofSystem : Type 0
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_p_simulation_type_checks() {
    let env = make_env();
    let psim = crate::expr::Expr::const_(Name::from_string("ProofTheory.PSimulation"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&psim)
        .expect("infer ProofTheory.PSimulation type");
    // PSimulation : ProofSystem -> ProofSystem -> Prop
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_resolution_below_cp_type_checks() {
    let env = make_env();
    let thm =
        crate::expr::Expr::const_(Name::from_string("ProofTheory.resolution_below_cp"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer ProofTheory.resolution_below_cp type");
    // forall (res cp : ProofSystem), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_cook_reckhow_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.cook_reckhow_completeness"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer ProofTheory.cook_reckhow_completeness type");
    // cook_reckhow_completeness : cook_reckhow_helper  (a Prop)
    // The type of a Prop-valued constant is a Sort(0) after checking,
    // but the declared type is the helper (which is Prop).
    // We just verify it type-checks without error.
    let _ = ty;
}

#[test]
fn test_frege_proof_size_type_checks() {
    let env = make_env();
    let fps = crate::expr::Expr::const_(Name::from_string("ProofTheory.frege_proof_size"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&fps)
        .expect("infer ProofTheory.frege_proof_size type");
    // frege_proof_size : FregeProof -> Nat
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_simulation_gap_type_checks() {
    let env = make_env();
    let sg = crate::expr::Expr::const_(Name::from_string("ProofTheory.simulation_gap"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&sg)
        .expect("infer ProofTheory.simulation_gap type");
    // simulation_gap : ProofSystem -> ProofSystem -> Formula -> Nat
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// ====================================================================
// Naming convention tests
// ====================================================================

#[test]
fn test_naming_convention() {
    let env = make_env();
    // All declarations should use ProofTheory. prefix
    for name in [
        "ProofTheory.ProofSystem",
        "ProofTheory.PSimulation",
        "ProofTheory.FregeProof",
        "ProofTheory.ExtendedFregeProof",
        "ProofTheory.resolution_below_cp",
        "ProofTheory.cook_reckhow_completeness",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered with ProofTheory. prefix",
        );
    }
    // Bare names should not exist
    for name in [
        "ProofSystem",
        "PSimulation",
        "FregeProof",
        "resolution_below_cp",
        "cook_reckhow_completeness",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} should NOT be registered without ProofTheory. prefix",
        );
    }
}

// ====================================================================
// Idempotency test
// ====================================================================

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_proof_hierarchy().expect("first init");
    env.init_proof_hierarchy().expect("second init");
}

// ====================================================================
// Classification test
// ====================================================================

#[test]
fn test_definition_vs_theorem_classification() {
    let env = make_env();

    // Definitions should be Type-valued (Type 0)
    let tc = TypeChecker::with_mode(&env, env.mode());
    for name in [
        "ProofTheory.ProofSystem",
        "ProofTheory.Formula",
        "ProofTheory.FregeProof",
        "ProofTheory.ExtendedFregeProof",
    ] {
        let expr = crate::expr::Expr::const_(Name::from_string(name), vec![]);
        let ty = tc
            .infer_type(&expr)
            .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
        assert!(
            matches!(ty.kind(), ExprKind::Sort(..)),
            "{name} should be Type-valued (Sort), got {ty:?}"
        );
    }

    // Operations should be Pi-typed (function types)
    for name in [
        "ProofTheory.PSimulation",
        "ProofTheory.frege_proof_size",
        "ProofTheory.simulation_gap",
    ] {
        let expr = crate::expr::Expr::const_(Name::from_string(name), vec![]);
        let ty = tc
            .infer_type(&expr)
            .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
        assert!(
            matches!(ty.kind(), ExprKind::Pi(..)),
            "{name} should be Pi-typed (function), got {ty:?}"
        );
    }
}
