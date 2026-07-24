// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for proof-guided neural architecture search (NAS) formalization.
//!
//! Part of #3259.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_proof_guided_nas()
        .expect("init_nn_verify_proof_guided_nas");
    env
}

// =============================================================================
// Phase 1: Registration tests
// =============================================================================

#[test]
fn test_proof_guided_nas_architecture_space_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.architecture_space"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_verifiability_score_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.verifiability_score"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_pareto_front_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.pareto_front"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_architecture_transform_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.architecture_transform"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_verified_accuracy_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.verified_accuracy"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_helper_defs_registered() {
    let env = make_env();
    for name in &[
        "NNVerify.arch_depth",
        "NNVerify.arch_width",
        "NNVerify.standard_accuracy",
        "NNVerify.has_skip_connections",
        "NNVerify.without_skip",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
    }
}

#[test]
fn test_proof_guided_nas_wider_more_verifiable_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.wider_more_verifiable"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("NNVerify.wider_more_verifiable_axiom"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_depth_verifiability_tradeoff_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.depth_verifiability_tradeoff"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.depth_verifiability_tradeoff_axiom"
        ))
        .is_some());
}

#[test]
fn test_proof_guided_nas_pareto_dominance_sound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.pareto_dominance_sound"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("NNVerify.pareto_dominance_sound_axiom"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_search_monotone_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.nas_search_monotone"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("NNVerify.nas_search_monotone_axiom"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_skip_connections_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.skip_connections_improve_verifiability"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.skip_connections_improve_verifiability_axiom"
        ))
        .is_some());
}

#[test]
fn test_proof_guided_nas_certified_accuracy_bound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.certified_accuracy_bound"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.certified_accuracy_bound_axiom"
        ))
        .is_some());
}

// =============================================================================
// Phase 2: Registration tests
// =============================================================================

#[test]
fn test_proof_guided_nas_architecture_type_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.Architecture"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_layer_spec_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.LayerSpec"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_activation_kind_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.ActivationKind"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_architecture_metric_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.ArchitectureMetric"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_cert_objective_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.cert_objective"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_cert_tightness_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.cert_tightness"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_pareto_optimal_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.pareto_optimal"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_has_residual_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.has_residual"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_residual_sub_cert_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.residual_sub_cert"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_deeper_larger_cert_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.deeper_larger_cert"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("NNVerify.deeper_larger_cert_axiom"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_wider_tighter_bounds_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.wider_tighter_bounds"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("NNVerify.wider_tighter_bounds_axiom"))
        .is_some());
}

#[test]
fn test_proof_guided_nas_residual_cert_composition_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.residual_cert_composition"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.residual_cert_composition_axiom"
        ))
        .is_some());
}

// =============================================================================
// Phase 1: Type checking tests
// =============================================================================

#[test]
fn test_proof_guided_nas_architecture_space_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.architecture_space"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer architecture_space type");
    // architecture_space : Type (a sort)
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_proof_guided_nas_verifiability_score_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.verifiability_score"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer verifiability_score type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_proof_guided_nas_pareto_front_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.pareto_front"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer pareto_front type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_proof_guided_nas_wider_more_verifiable_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.wider_more_verifiable"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer wider_more_verifiable type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_proof_guided_nas_depth_tradeoff_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.depth_verifiability_tradeoff"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer depth_verifiability_tradeoff type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_proof_guided_nas_certified_accuracy_bound_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.certified_accuracy_bound"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer certified_accuracy_bound type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_proof_guided_nas_skip_connections_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.skip_connections_improve_verifiability"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer skip_connections_improve_verifiability type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// =============================================================================
// Phase 2: Type checking tests
// =============================================================================

#[test]
fn test_proof_guided_nas_architecture_type_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.Architecture"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer Architecture type");
    // Architecture : Type (a sort)
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_proof_guided_nas_layer_spec_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.LayerSpec"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer LayerSpec type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_proof_guided_nas_activation_kind_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.ActivationKind"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer ActivationKind type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_proof_guided_nas_architecture_metric_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.ArchitectureMetric"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer ArchitectureMetric type");
    // Architecture -> Nat -> Type => Pi
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_proof_guided_nas_cert_objective_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.cert_objective"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer cert_objective type");
    // Architecture -> Nat => Pi
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_proof_guided_nas_cert_tightness_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.cert_tightness"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer cert_tightness type");
    // Architecture -> Rat => Pi
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_proof_guided_nas_pareto_optimal_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.pareto_optimal"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer pareto_optimal type");
    // Architecture -> Prop => Pi
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_proof_guided_nas_has_residual_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.has_residual"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer has_residual type");
    // Architecture -> Prop => Pi
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_proof_guided_nas_residual_sub_cert_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.residual_sub_cert"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer residual_sub_cert type");
    // Architecture -> Nat => Pi
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_proof_guided_nas_deeper_larger_cert_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.deeper_larger_cert"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer deeper_larger_cert type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_proof_guided_nas_wider_tighter_bounds_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.wider_tighter_bounds"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer wider_tighter_bounds type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_proof_guided_nas_residual_cert_composition_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.residual_cert_composition"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer residual_cert_composition type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// =============================================================================
// Idempotency and naming convention tests
// =============================================================================

#[test]
fn test_proof_guided_nas_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_proof_guided_nas().expect("first init");
    env.init_nn_verify_proof_guided_nas().expect("second init");
}

/// Verify all declarations use the `NNVerify.` prefix.
#[test]
fn test_proof_guided_nas_naming_convention() {
    let env = make_env();
    let names = [
        // Phase 1 definitions
        "NNVerify.architecture_space",
        "NNVerify.verifiability_score",
        "NNVerify.pareto_front",
        "NNVerify.architecture_transform",
        "NNVerify.apply_transform",
        "NNVerify.verified_accuracy",
        "NNVerify.arch_depth",
        "NNVerify.arch_width",
        "NNVerify.standard_accuracy",
        "NNVerify.has_skip_connections",
        "NNVerify.without_skip",
        // Phase 1 theorems
        "NNVerify.wider_more_verifiable",
        "NNVerify.wider_more_verifiable_axiom",
        "NNVerify.depth_verifiability_tradeoff",
        "NNVerify.depth_verifiability_tradeoff_axiom",
        "NNVerify.pareto_dominance_sound",
        "NNVerify.pareto_dominance_sound_axiom",
        "NNVerify.nas_search_monotone",
        "NNVerify.nas_search_monotone_axiom",
        "NNVerify.skip_connections_improve_verifiability",
        "NNVerify.skip_connections_improve_verifiability_axiom",
        "NNVerify.certified_accuracy_bound",
        "NNVerify.certified_accuracy_bound_axiom",
        // Phase 2 definitions
        "NNVerify.Architecture",
        "NNVerify.LayerSpec",
        "NNVerify.ActivationKind",
        "NNVerify.ArchitectureMetric",
        "NNVerify.cert_objective",
        "NNVerify.cert_tightness",
        "NNVerify.pareto_optimal",
        "NNVerify.has_residual",
        "NNVerify.residual_sub_cert",
        // Phase 2 theorems
        "NNVerify.deeper_larger_cert",
        "NNVerify.deeper_larger_cert_axiom",
        "NNVerify.wider_tighter_bounds",
        "NNVerify.wider_tighter_bounds_axiom",
        "NNVerify.residual_cert_composition",
        "NNVerify.residual_cert_composition_axiom",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
        assert!(
            name.starts_with("NNVerify."),
            "{} must use NNVerify. prefix",
            name,
        );
    }
}

/// Count: 20 definitions + 18 theorem/axiom pairs = 38 declarations total.
#[test]
fn test_proof_guided_nas_declaration_count() {
    let env = make_env();
    let prefix = "NNVerify.";
    let nas_names = [
        // Phase 1 definitions (11)
        "architecture_space",
        "verifiability_score",
        "pareto_front",
        "architecture_transform",
        "apply_transform",
        "verified_accuracy",
        "arch_depth",
        "arch_width",
        "standard_accuracy",
        "has_skip_connections",
        "without_skip",
        // Phase 1 theorem/axiom pairs (12)
        "wider_more_verifiable",
        "wider_more_verifiable_axiom",
        "depth_verifiability_tradeoff",
        "depth_verifiability_tradeoff_axiom",
        "pareto_dominance_sound",
        "pareto_dominance_sound_axiom",
        "nas_search_monotone",
        "nas_search_monotone_axiom",
        "skip_connections_improve_verifiability",
        "skip_connections_improve_verifiability_axiom",
        "certified_accuracy_bound",
        "certified_accuracy_bound_axiom",
        // Phase 2 definitions (9)
        "Architecture",
        "LayerSpec",
        "ActivationKind",
        "ArchitectureMetric",
        "cert_objective",
        "cert_tightness",
        "pareto_optimal",
        "has_residual",
        "residual_sub_cert",
        // Phase 2 theorem/axiom pairs (6)
        "deeper_larger_cert",
        "deeper_larger_cert_axiom",
        "wider_tighter_bounds",
        "wider_tighter_bounds_axiom",
        "residual_cert_composition",
        "residual_cert_composition_axiom",
    ];
    for short in &nas_names {
        let full = format!("{}{}", prefix, short);
        assert!(
            env.get_const(&Name::from_string(&full)).is_some(),
            "{} missing",
            full,
        );
    }
    assert_eq!(nas_names.len(), 38);
}
