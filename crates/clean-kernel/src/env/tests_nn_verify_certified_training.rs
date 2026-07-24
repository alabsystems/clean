// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for certified training (differentiable IBP) formalization.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_certified_training()
        .expect("init_nn_verify_certified_training should succeed");
    env
}

// ---------------------------------------------------------------
// All declarations registered
// ---------------------------------------------------------------

/// All expected NNVerify.CertTrain.* names must be registered.
#[test]
fn test_all_declarations_registered() {
    let env = make_env();
    let expected = [
        // Auxiliary definitions
        "NNVerify.CertTrain.standard_loss",
        "NNVerify.CertTrain.worst_case_loss",
        "NNVerify.CertTrain.is_differentiable",
        "NNVerify.CertTrain.ibp_bounds",
        // Main definitions
        "NNVerify.CertTrain.ibp_loss",
        "NNVerify.CertTrain.certified_radius",
        "NNVerify.CertTrain.training_objective",
        "NNVerify.CertTrain.bound_tightness",
        // Theorem axioms
        "NNVerify.CertTrain.ibp_loss_upper_bound_axiom",
        "NNVerify.CertTrain.certified_radius_sound_axiom",
        "NNVerify.CertTrain.training_convergence_bound_axiom",
        "NNVerify.CertTrain.ibp_loss_differentiable_axiom",
        "NNVerify.CertTrain.certified_training_sound_axiom",
        // Theorems (wrapper)
        "NNVerify.CertTrain.ibp_loss_upper_bound",
        "NNVerify.CertTrain.certified_radius_sound",
        "NNVerify.CertTrain.training_convergence_bound",
        "NNVerify.CertTrain.ibp_loss_differentiable",
        "NNVerify.CertTrain.certified_training_sound",
        // Training step types (from _thms module)
        "NNVerify.CertTrain.TrainingConfig",
        "NNVerify.CertTrain.CertLoss",
        "NNVerify.CertTrain.TrainStep",
        // Training step definitions (from _thms module)
        "NNVerify.CertTrain.cert_evolution",
        // Training step theorem axioms (from _thms module)
        "NNVerify.CertTrain.train_step_preserves_cert_axiom",
        "NNVerify.CertTrain.monotone_cert_loss_axiom",
        // Training step theorems (from _thms module)
        "NNVerify.CertTrain.train_step_preserves_cert",
        "NNVerify.CertTrain.monotone_cert_loss",
    ];
    for name in &expected {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

// ---------------------------------------------------------------
// NNVerify. prefix convention
// ---------------------------------------------------------------

#[test]
fn test_naming_convention() {
    let env = make_env();
    let all_names = [
        "NNVerify.CertTrain.ibp_loss",
        "NNVerify.CertTrain.certified_radius",
        "NNVerify.CertTrain.training_objective",
        "NNVerify.CertTrain.bound_tightness",
        "NNVerify.CertTrain.ibp_loss_upper_bound",
        "NNVerify.CertTrain.certified_radius_sound",
        "NNVerify.CertTrain.training_convergence_bound",
        "NNVerify.CertTrain.ibp_loss_differentiable",
        "NNVerify.CertTrain.certified_training_sound",
        "NNVerify.CertTrain.TrainingConfig",
        "NNVerify.CertTrain.CertLoss",
        "NNVerify.CertTrain.TrainStep",
        "NNVerify.CertTrain.cert_evolution",
        "NNVerify.CertTrain.train_step_preserves_cert",
        "NNVerify.CertTrain.monotone_cert_loss",
    ];
    for name in &all_names {
        assert!(
            name.starts_with("NNVerify."),
            "{name} must start with NNVerify."
        );
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered with NNVerify. prefix"
        );
    }
    // Verify short names are NOT registered
    let short_names = [
        "ibp_loss",
        "certified_radius",
        "training_objective",
        "certified_training_sound",
        "TrainingConfig",
        "CertLoss",
        "TrainStep",
        "cert_evolution",
        "train_step_preserves_cert",
        "monotone_cert_loss",
    ];
    for name in &short_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} should NOT be registered (use NNVerify.CertTrain. prefix)"
        );
    }
}

// ---------------------------------------------------------------
// Definition vs axiom classification
// ---------------------------------------------------------------

#[test]
fn test_definitions_are_axioms() {
    let env = make_env();
    let defs = [
        "NNVerify.CertTrain.standard_loss",
        "NNVerify.CertTrain.worst_case_loss",
        "NNVerify.CertTrain.is_differentiable",
        "NNVerify.CertTrain.ibp_bounds",
        "NNVerify.CertTrain.ibp_loss",
        "NNVerify.CertTrain.certified_radius",
        "NNVerify.CertTrain.training_objective",
        "NNVerify.CertTrain.bound_tightness",
        "NNVerify.CertTrain.TrainingConfig",
        "NNVerify.CertTrain.CertLoss",
        "NNVerify.CertTrain.TrainStep",
        "NNVerify.CertTrain.cert_evolution",
    ];
    for name in &defs {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(
            info.kind,
            ConstantKind::Axiom,
            "{name} should be an Axiom, got {:?}",
            info.kind
        );
    }
}

#[test]
fn test_theorems_are_theorems() {
    let env = make_env();
    let thms = [
        "NNVerify.CertTrain.ibp_loss_upper_bound",
        "NNVerify.CertTrain.certified_radius_sound",
        "NNVerify.CertTrain.training_convergence_bound",
        "NNVerify.CertTrain.ibp_loss_differentiable",
        "NNVerify.CertTrain.certified_training_sound",
        "NNVerify.CertTrain.train_step_preserves_cert",
        "NNVerify.CertTrain.monotone_cert_loss",
    ];
    for name in &thms {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} should be a Theorem, got {:?}",
            info.kind
        );
        assert!(info.value.is_some(), "{name} should have a proof term");
    }
}

#[test]
fn test_backing_axioms_are_axioms() {
    let env = make_env();
    let axioms = [
        "NNVerify.CertTrain.ibp_loss_upper_bound_axiom",
        "NNVerify.CertTrain.certified_radius_sound_axiom",
        "NNVerify.CertTrain.training_convergence_bound_axiom",
        "NNVerify.CertTrain.ibp_loss_differentiable_axiom",
        "NNVerify.CertTrain.certified_training_sound_axiom",
        "NNVerify.CertTrain.train_step_preserves_cert_axiom",
        "NNVerify.CertTrain.monotone_cert_loss_axiom",
    ];
    for name in &axioms {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(
            info.kind,
            ConstantKind::Axiom,
            "{name} should be an Axiom, got {:?}",
            info.kind
        );
    }
}

// ---------------------------------------------------------------
// Type checking
// ---------------------------------------------------------------

#[test]
fn test_all_declarations_type_check() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let names = [
        "NNVerify.CertTrain.standard_loss",
        "NNVerify.CertTrain.worst_case_loss",
        "NNVerify.CertTrain.is_differentiable",
        "NNVerify.CertTrain.ibp_bounds",
        "NNVerify.CertTrain.ibp_loss",
        "NNVerify.CertTrain.certified_radius",
        "NNVerify.CertTrain.training_objective",
        "NNVerify.CertTrain.bound_tightness",
        "NNVerify.CertTrain.ibp_loss_upper_bound",
        "NNVerify.CertTrain.certified_radius_sound",
        "NNVerify.CertTrain.training_convergence_bound",
        "NNVerify.CertTrain.ibp_loss_differentiable",
        "NNVerify.CertTrain.certified_training_sound",
        "NNVerify.CertTrain.TrainingConfig",
        "NNVerify.CertTrain.CertLoss",
        "NNVerify.CertTrain.TrainStep",
        "NNVerify.CertTrain.cert_evolution",
        "NNVerify.CertTrain.train_step_preserves_cert",
        "NNVerify.CertTrain.monotone_cert_loss",
    ];
    for name in &names {
        let e = Expr::const_(Name::from_string(name), vec![]);
        let ty = tc
            .infer_type(&e)
            .unwrap_or_else(|err| panic!("{name} should type-check: {err:?}"));
        assert!(
            matches!(ty.kind(), ExprKind::Pi(..) | ExprKind::Sort(..)),
            "{name} type should be Pi or Sort, got {:?}",
            ty.kind()
        );
    }
}

#[test]
fn test_theorem_proof_terms_type_check() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    let thms = [
        "NNVerify.CertTrain.ibp_loss_upper_bound",
        "NNVerify.CertTrain.certified_radius_sound",
        "NNVerify.CertTrain.training_convergence_bound",
        "NNVerify.CertTrain.ibp_loss_differentiable",
        "NNVerify.CertTrain.certified_training_sound",
        "NNVerify.CertTrain.train_step_preserves_cert",
        "NNVerify.CertTrain.monotone_cert_loss",
    ];
    for name in &thms {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        let proof = info.value.as_ref().expect("should have proof term");
        let inferred = tc
            .infer_type(proof)
            .unwrap_or_else(|err| panic!("{name} proof should type-check: {err:?}"));
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "{name}: inferred type should match declared type"
        );
    }
}

// ---------------------------------------------------------------
// No sorry
// ---------------------------------------------------------------

#[test]
fn test_no_sorry() {
    let env = make_env();
    let thms = [
        "NNVerify.CertTrain.ibp_loss_upper_bound",
        "NNVerify.CertTrain.certified_radius_sound",
        "NNVerify.CertTrain.training_convergence_bound",
        "NNVerify.CertTrain.ibp_loss_differentiable",
        "NNVerify.CertTrain.certified_training_sound",
        "NNVerify.CertTrain.train_step_preserves_cert",
        "NNVerify.CertTrain.monotone_cert_loss",
    ];
    for name in &thms {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        let sorry = info.sorry_summary();
        assert!(!sorry.has_sorry, "{name} proof should not use sorry");
    }
}

// ---------------------------------------------------------------
// Idempotency
// ---------------------------------------------------------------

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_certified_training().expect("first init");
    env.init_nn_verify_certified_training()
        .expect("second init (idempotent)");
}

// ---------------------------------------------------------------
// Dependencies available
// ---------------------------------------------------------------

#[test]
fn test_dependencies_available() {
    let env = make_env();
    let deps = [
        "NNVerify.NNVec",
        "NNVerify.NNMat",
        "NNVerify.IntervalBounds",
    ];
    for name in &deps {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be available after certified training init"
        );
    }
}

// ---------------------------------------------------------------
// Declaration count
// ---------------------------------------------------------------

#[test]
fn test_declaration_count() {
    let env = make_env();
    let mut count = 0;
    let prefixes = [
        // Original definitions (8)
        "NNVerify.CertTrain.standard_loss",
        "NNVerify.CertTrain.worst_case_loss",
        "NNVerify.CertTrain.is_differentiable",
        "NNVerify.CertTrain.ibp_bounds",
        "NNVerify.CertTrain.ibp_loss",
        "NNVerify.CertTrain.certified_radius",
        "NNVerify.CertTrain.training_objective",
        "NNVerify.CertTrain.bound_tightness",
        // Original axioms (5) + theorems (5) = 10
        "NNVerify.CertTrain.ibp_loss_upper_bound_axiom",
        "NNVerify.CertTrain.ibp_loss_upper_bound",
        "NNVerify.CertTrain.certified_radius_sound_axiom",
        "NNVerify.CertTrain.certified_radius_sound",
        "NNVerify.CertTrain.training_convergence_bound_axiom",
        "NNVerify.CertTrain.training_convergence_bound",
        "NNVerify.CertTrain.ibp_loss_differentiable_axiom",
        "NNVerify.CertTrain.ibp_loss_differentiable",
        "NNVerify.CertTrain.certified_training_sound_axiom",
        "NNVerify.CertTrain.certified_training_sound",
        // Training step types (3) + definition (1) = 4
        "NNVerify.CertTrain.TrainingConfig",
        "NNVerify.CertTrain.CertLoss",
        "NNVerify.CertTrain.TrainStep",
        "NNVerify.CertTrain.cert_evolution",
        // Training step axioms (2) + theorems (2) = 4
        "NNVerify.CertTrain.train_step_preserves_cert_axiom",
        "NNVerify.CertTrain.train_step_preserves_cert",
        "NNVerify.CertTrain.monotone_cert_loss_axiom",
        "NNVerify.CertTrain.monotone_cert_loss",
    ];
    for name in &prefixes {
        if env.get_const(&Name::from_string(name)).is_some() {
            count += 1;
        }
    }
    // 8+4 definitions + 5+2 backing axioms + 5+2 theorems = 26
    assert_eq!(
        count, 26,
        "should have exactly 26 CertTrain declarations, got {count}"
    );
}
