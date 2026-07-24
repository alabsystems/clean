// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for labelled interpolation minimality formalization.
//!
//! Part of #3156.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_labelled_interpolation_minimality()
        .expect("init_labelled_interpolation_minimality");
    env
}

// ====================================================================
// Registration tests
// ====================================================================

#[test]
fn test_labelling_function_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "ProofTheory.LabelledInterpolation.LabellingFunction"
        ))
        .is_some());
}

#[test]
fn test_interpolation_system_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.LabelledInterpolation.InterpolationSystem",
        "ProofTheory.LabelledInterpolation.InterpolationSystem.labelling",
        "ProofTheory.LabelledInterpolation.InterpolationSystem.valid",
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
        "ProofTheory.LabelledInterpolation.LabellingFunction",
        "ProofTheory.LabelledInterpolation.InterpolationSystem",
        "ProofTheory.LabelledInterpolation.InterpolationSystem.labelling",
        "ProofTheory.LabelledInterpolation.InterpolationSystem.valid",
        "ProofTheory.LabelledInterpolation.labelled_interpolant",
        "ProofTheory.LabelledInterpolation.mcmillan_labelling",
        "ProofTheory.LabelledInterpolation.reverse_mcmillan_labelling",
        "ProofTheory.LabelledInterpolation.variable_support",
        "ProofTheory.LabelledInterpolation.var_subset",
        "ProofTheory.LabelledInterpolation.interpolant_implies",
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
        "ProofTheory.LabelledInterpolation.labelled_interpolant_valid",
        "ProofTheory.LabelledInterpolation.mcmillan_support_minimal",
        "ProofTheory.LabelledInterpolation.interpolant_lattice_complete",
        "ProofTheory.LabelledInterpolation.mcmillan_is_lattice_bottom",
        "ProofTheory.LabelledInterpolation.reverse_mcmillan_is_lattice_top",
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
        "ProofTheory.LabelledInterpolation.labelled_interpolant_valid_helper",
        "ProofTheory.LabelledInterpolation.mcmillan_support_minimal_helper",
        "ProofTheory.LabelledInterpolation.interpolant_lattice_complete_helper",
        "ProofTheory.LabelledInterpolation.mcmillan_is_lattice_bottom_helper",
        "ProofTheory.LabelledInterpolation.reverse_mcmillan_is_lattice_top_helper",
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
fn test_labelling_function_type_checks() {
    let env = make_env();
    let lf = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.LabelledInterpolation.LabellingFunction"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&lf).expect("infer LabellingFunction type");
    // LabellingFunction : Type 0, so its type is Sort(1) = Type
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_interpolation_system_type_checks() {
    let env = make_env();
    let is = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.LabelledInterpolation.InterpolationSystem"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&is).expect("infer InterpolationSystem type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_labelled_interpolant_type_checks() {
    let env = make_env();
    let li = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.LabelledInterpolation.labelled_interpolant"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&li).expect("infer labelled_interpolant type");
    // PropFormula -> PropFormula -> Proof -> LabellingFunction -> PropFormula
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_mcmillan_labelling_type_checks() {
    let env = make_env();
    let ml = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.LabelledInterpolation.mcmillan_labelling"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&ml).expect("infer mcmillan_labelling type");
    // PropFormula -> PropFormula -> LabellingFunction
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_reverse_mcmillan_labelling_type_checks() {
    let env = make_env();
    let rml = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.LabelledInterpolation.reverse_mcmillan_labelling"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&rml)
        .expect("infer reverse_mcmillan_labelling type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_variable_support_type_checks() {
    let env = make_env();
    let vs = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.LabelledInterpolation.variable_support"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&vs).expect("infer variable_support type");
    // PropFormula -> VarSet
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_var_subset_type_checks() {
    let env = make_env();
    let sub = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.LabelledInterpolation.var_subset"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&sub).expect("infer var_subset type");
    // VarSet -> VarSet -> Prop
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_interpolant_implies_type_checks() {
    let env = make_env();
    let imp = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.LabelledInterpolation.interpolant_implies"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&imp).expect("infer interpolant_implies type");
    // PropFormula -> PropFormula -> Prop
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_mcmillan_support_minimal_type_checks() {
    let env = make_env();
    let msm = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.LabelledInterpolation.mcmillan_support_minimal"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&msm)
        .expect("infer mcmillan_support_minimal type");
    // forall (a b : PropFormula) (pi : Proof) (L : LabellingFunction), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_interpolant_lattice_complete_type_checks() {
    let env = make_env();
    let ilc = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.LabelledInterpolation.interpolant_lattice_complete"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&ilc)
        .expect("infer interpolant_lattice_complete type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_mcmillan_is_lattice_bottom_type_checks() {
    let env = make_env();
    let mlb = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.LabelledInterpolation.mcmillan_is_lattice_bottom"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&mlb)
        .expect("infer mcmillan_is_lattice_bottom type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_reverse_mcmillan_is_lattice_top_type_checks() {
    let env = make_env();
    let rmt = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.LabelledInterpolation.reverse_mcmillan_is_lattice_top"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&rmt)
        .expect("infer reverse_mcmillan_is_lattice_top type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// ====================================================================
// Structural tests
// ====================================================================

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_labelled_interpolation_minimality()
        .expect("first init");
    env.init_labelled_interpolation_minimality()
        .expect("second init");
}

#[test]
fn test_naming_convention() {
    let env = make_env();
    let prefix = "ProofTheory.LabelledInterpolation.";
    let all_names = [
        "LabellingFunction",
        "InterpolationSystem",
        "InterpolationSystem.labelling",
        "InterpolationSystem.valid",
        "labelled_interpolant",
        "mcmillan_labelling",
        "reverse_mcmillan_labelling",
        "variable_support",
        "var_subset",
        "interpolant_implies",
        "labelled_interpolant_valid",
        "labelled_interpolant_valid_helper",
        "mcmillan_support_minimal",
        "mcmillan_support_minimal_helper",
        "interpolant_lattice_complete",
        "interpolant_lattice_complete_helper",
        "mcmillan_is_lattice_bottom",
        "mcmillan_is_lattice_bottom_helper",
        "reverse_mcmillan_is_lattice_top",
        "reverse_mcmillan_is_lattice_top_helper",
    ];
    for suffix in &all_names {
        let full = format!("{prefix}{suffix}");
        assert!(
            env.get_const(&Name::from_string(&full)).is_some(),
            "{full} should be registered"
        );
    }
    // Bare names should not exist
    for suffix in &[
        "LabellingFunction",
        "InterpolationSystem",
        "labelled_interpolant",
    ] {
        assert!(
            env.get_const(&Name::from_string(suffix)).is_none(),
            "{suffix} should NOT be registered without prefix"
        );
    }
}

#[test]
fn test_definition_vs_axiom_classification() {
    let env = make_env();
    let axiom_names = [
        "ProofTheory.LabelledInterpolation.LabellingFunction",
        "ProofTheory.LabelledInterpolation.InterpolationSystem",
        "ProofTheory.LabelledInterpolation.InterpolationSystem.labelling",
        "ProofTheory.LabelledInterpolation.InterpolationSystem.valid",
        "ProofTheory.LabelledInterpolation.labelled_interpolant",
        "ProofTheory.LabelledInterpolation.mcmillan_labelling",
        "ProofTheory.LabelledInterpolation.reverse_mcmillan_labelling",
        "ProofTheory.LabelledInterpolation.variable_support",
        "ProofTheory.LabelledInterpolation.var_subset",
        "ProofTheory.LabelledInterpolation.interpolant_implies",
        "ProofTheory.LabelledInterpolation.labelled_interpolant_valid",
        "ProofTheory.LabelledInterpolation.mcmillan_support_minimal",
        "ProofTheory.LabelledInterpolation.interpolant_lattice_complete",
        "ProofTheory.LabelledInterpolation.mcmillan_is_lattice_bottom",
        "ProofTheory.LabelledInterpolation.reverse_mcmillan_is_lattice_top",
    ];
    for name in axiom_names {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(info.kind, ConstantKind::Axiom, "{name} should be an axiom");
    }
}

#[test]
fn test_craig_interpolation_also_initialized() {
    let env = make_env();
    // Dependency: craig_interpolation declarations should be available
    assert!(env
        .get_const(&Name::from_string("ProofTheory.PropFormula"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("ProofTheory.Resolution.Proof"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("ProofTheory.VarSet"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("ProofTheory.interpolant"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("ProofTheory.variables_of"))
        .is_some());
}

#[test]
fn test_total_declaration_count() {
    let env = make_env();
    let expected_names = [
        // Definitions (10)
        "ProofTheory.LabelledInterpolation.LabellingFunction",
        "ProofTheory.LabelledInterpolation.InterpolationSystem",
        "ProofTheory.LabelledInterpolation.InterpolationSystem.labelling",
        "ProofTheory.LabelledInterpolation.InterpolationSystem.valid",
        "ProofTheory.LabelledInterpolation.labelled_interpolant",
        "ProofTheory.LabelledInterpolation.mcmillan_labelling",
        "ProofTheory.LabelledInterpolation.reverse_mcmillan_labelling",
        "ProofTheory.LabelledInterpolation.variable_support",
        "ProofTheory.LabelledInterpolation.var_subset",
        "ProofTheory.LabelledInterpolation.interpolant_implies",
        // Theorems (5)
        "ProofTheory.LabelledInterpolation.labelled_interpolant_valid",
        "ProofTheory.LabelledInterpolation.mcmillan_support_minimal",
        "ProofTheory.LabelledInterpolation.interpolant_lattice_complete",
        "ProofTheory.LabelledInterpolation.mcmillan_is_lattice_bottom",
        "ProofTheory.LabelledInterpolation.reverse_mcmillan_is_lattice_top",
        // Helpers (5)
        "ProofTheory.LabelledInterpolation.labelled_interpolant_valid_helper",
        "ProofTheory.LabelledInterpolation.mcmillan_support_minimal_helper",
        "ProofTheory.LabelledInterpolation.interpolant_lattice_complete_helper",
        "ProofTheory.LabelledInterpolation.mcmillan_is_lattice_bottom_helper",
        "ProofTheory.LabelledInterpolation.reverse_mcmillan_is_lattice_top_helper",
    ];
    for name in expected_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should exist in environment"
        );
    }
}

#[test]
fn test_labelled_interpolant_valid_type_checks() {
    let env = make_env();
    let e = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.LabelledInterpolation.labelled_interpolant_valid"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer labelled_interpolant_valid type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}
