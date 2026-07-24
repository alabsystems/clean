// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Craig interpolation formalization.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_craig_interpolation()
        .expect("init_craig_interpolation");
    env
}

#[test]
fn test_prop_formula_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ProofTheory.PropFormula"))
        .is_some());
}

#[test]
fn test_prop_formula_constructors_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.PropFormula.Var",
        "ProofTheory.PropFormula.Neg",
        "ProofTheory.PropFormula.And",
        "ProofTheory.PropFormula.Or",
        "ProofTheory.PropFormula.Implies",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_resolution_proof_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.Resolution.Proof",
        "ProofTheory.Resolution.Proof.Axiom",
        "ProofTheory.Resolution.Proof.Resolve",
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
        "ProofTheory.PropFormula",
        "ProofTheory.PropFormula.Var",
        "ProofTheory.PropFormula.Neg",
        "ProofTheory.PropFormula.And",
        "ProofTheory.PropFormula.Or",
        "ProofTheory.PropFormula.Implies",
        "ProofTheory.VarSet",
        "ProofTheory.variables_of",
        "ProofTheory.uses_only",
        "ProofTheory.Resolution.Proof",
        "ProofTheory.Resolution.Proof.Axiom",
        "ProofTheory.Resolution.Proof.Resolve",
        "ProofTheory.shared_variables",
        "ProofTheory.interpolant",
        "ProofTheory.proof_complexity",
        "ProofTheory.formula_size",
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
        "ProofTheory.craig_interpolation",
        "ProofTheory.interpolant_uses_shared_vars",
        "ProofTheory.interpolant_size_bound",
        "ProofTheory.interpolant_from_resolution",
        "ProofTheory.reverse_interpolation",
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
        "ProofTheory.craig_interpolation_helper",
        "ProofTheory.interpolant_uses_shared_vars_helper",
        "ProofTheory.interpolant_size_bound_helper",
        "ProofTheory.interpolant_from_resolution_helper",
        "ProofTheory.reverse_interpolation_helper",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} helper should be registered"
        );
    }
}

#[test]
fn test_prop_formula_type_checks() {
    let env = make_env();
    let pf = crate::expr::Expr::const_(Name::from_string("ProofTheory.PropFormula"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&pf)
        .expect("infer ProofTheory.PropFormula type");
    // PropFormula : Type 0, so its type should be Sort(1) = Type
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_interpolant_type_checks() {
    let env = make_env();
    let interp = crate::expr::Expr::const_(Name::from_string("ProofTheory.interpolant"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&interp)
        .expect("infer ProofTheory.interpolant type");
    // interpolant : PropFormula -> PropFormula -> Resolution.Proof -> PropFormula
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_shared_variables_type_checks() {
    let env = make_env();
    let sv = crate::expr::Expr::const_(Name::from_string("ProofTheory.shared_variables"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&sv)
        .expect("infer ProofTheory.shared_variables type");
    // shared_variables : PropFormula -> PropFormula -> VarSet
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_proof_complexity_type_checks() {
    let env = make_env();
    let pc = crate::expr::Expr::const_(Name::from_string("ProofTheory.proof_complexity"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&pc)
        .expect("infer ProofTheory.proof_complexity type");
    // proof_complexity : Resolution.Proof -> Nat
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_craig_interpolation_type_checks() {
    let env = make_env();
    let ci =
        crate::expr::Expr::const_(Name::from_string("ProofTheory.craig_interpolation"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&ci)
        .expect("infer ProofTheory.craig_interpolation type");
    // forall (a b : PropFormula), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_craig_interpolation().expect("first init");
    env.init_craig_interpolation().expect("second init");
}

#[test]
fn test_naming_convention() {
    let env = make_env();
    // All declarations should use ProofTheory. prefix
    for name in [
        "ProofTheory.PropFormula",
        "ProofTheory.Resolution.Proof",
        "ProofTheory.shared_variables",
        "ProofTheory.interpolant",
        "ProofTheory.proof_complexity",
        "ProofTheory.craig_interpolation",
        "ProofTheory.interpolant_uses_shared_vars",
        "ProofTheory.interpolant_size_bound",
        "ProofTheory.interpolant_from_resolution",
        "ProofTheory.reverse_interpolation",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered with ProofTheory. prefix",
        );
    }
    // Bare names should not exist
    for name in [
        "PropFormula",
        "Resolution.Proof",
        "shared_variables",
        "interpolant",
        "proof_complexity",
        "craig_interpolation",
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
    // All type declarations and operations should be axioms (opaque)
    let axiom_names = [
        "ProofTheory.PropFormula",
        "ProofTheory.Resolution.Proof",
        "ProofTheory.VarSet",
        "ProofTheory.shared_variables",
        "ProofTheory.interpolant",
        "ProofTheory.proof_complexity",
        "ProofTheory.formula_size",
        "ProofTheory.craig_interpolation",
        "ProofTheory.interpolant_uses_shared_vars",
        "ProofTheory.interpolant_size_bound",
        "ProofTheory.interpolant_from_resolution",
        "ProofTheory.reverse_interpolation",
    ];
    for name in axiom_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(info.kind, ConstantKind::Axiom, "{name} should be an axiom");
    }
}
