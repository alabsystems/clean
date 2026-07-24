// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for abstract domain theory formalization.
//!
//! Part of #3261.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_abstract_domain()
        .expect("init_nn_verify_abstract_domain");
    env
}

/// Environment with IBP instance proofs (depends on T80/T81/T82).
fn make_env_with_ibp() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_abstract_domain_ibp()
        .expect("init_nn_verify_abstract_domain_ibp");
    env
}

// ---------------------------------------------------------------
// Definition registration tests
// ---------------------------------------------------------------

#[test]
fn test_abstract_domain_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.abstract_domain"
        ))
        .is_some());
}

#[test]
fn test_galois_connection_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.galois_connection"
        ))
        .is_some());
}

#[test]
fn test_abstract_transformer_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.abstract_transformer"
        ))
        .is_some());
}

#[test]
fn test_domain_precision_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.domain_precision"
        ))
        .is_some());
}

#[test]
fn test_domain_composition_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.domain_composition"
        ))
        .is_some());
}

// ---------------------------------------------------------------
// Theorem registration tests
// ---------------------------------------------------------------

#[test]
fn test_galois_soundness_registered() {
    let env = make_env();
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.AbstractDomain.galois_soundness"
        ))
        .is_some(),
        "galois_soundness theorem should be registered"
    );
    assert!(
        env.get_const(&Name::from_string(
            "NNVerify.AbstractDomain.galois_soundness_axiom"
        ))
        .is_some(),
        "galois_soundness_axiom should be registered"
    );
}

#[test]
fn test_transformer_soundness_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.transformer_soundness"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.transformer_soundness_axiom"
        ))
        .is_some());
}

#[test]
fn test_composition_soundness_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.composition_soundness"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.composition_soundness_axiom"
        ))
        .is_some());
}

#[test]
fn test_precision_monotone_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.precision_monotone"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.precision_monotone_axiom"
        ))
        .is_some());
}

#[test]
fn test_ibp_is_interval_domain_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.ibp_is_interval_domain"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.ibp_is_interval_domain_axiom"
        ))
        .is_some());
}

#[test]
fn test_zonotope_refines_interval_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.zonotope_refines_interval"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.zonotope_refines_interval_axiom"
        ))
        .is_some());
}

// ---------------------------------------------------------------
// Type checking tests
// ---------------------------------------------------------------

#[test]
fn test_abstract_domain_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.AbstractDomain.abstract_domain"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer abstract_domain type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_galois_connection_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.AbstractDomain.galois_connection"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer galois_connection type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_abstract_transformer_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.AbstractDomain.abstract_transformer"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer abstract_transformer type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_transformer_soundness_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.AbstractDomain.transformer_soundness"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer transformer_soundness type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_zonotope_refines_interval_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.AbstractDomain.zonotope_refines_interval"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer zonotope_refines_interval type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// ---------------------------------------------------------------
// Definition vs axiom classification tests
// ---------------------------------------------------------------

#[test]
fn test_definitions_are_axioms() {
    let env = make_env();
    for name in &[
        "NNVerify.AbstractDomain.abstract_domain",
        "NNVerify.AbstractDomain.galois_connection",
        "NNVerify.AbstractDomain.abstract_transformer",
        "NNVerify.AbstractDomain.domain_precision",
        "NNVerify.AbstractDomain.domain_composition",
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
fn test_theorem_axiom_pairs_are_correct_kinds() {
    let env = make_env();
    let theorems = [
        "NNVerify.AbstractDomain.galois_soundness",
        "NNVerify.AbstractDomain.transformer_soundness",
        "NNVerify.AbstractDomain.composition_soundness",
        "NNVerify.AbstractDomain.precision_monotone",
        "NNVerify.AbstractDomain.ibp_is_interval_domain",
        "NNVerify.AbstractDomain.zonotope_refines_interval",
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
// NNVerify prefix naming convention test
// ---------------------------------------------------------------

#[test]
fn test_nn_verify_abstract_domain_naming_convention() {
    let env = make_env();
    let names = [
        "NNVerify.AbstractDomain.abstract_domain",
        "NNVerify.AbstractDomain.galois_connection",
        "NNVerify.AbstractDomain.abstract_transformer",
        "NNVerify.AbstractDomain.domain_precision",
        "NNVerify.AbstractDomain.domain_composition",
        "NNVerify.AbstractDomain.galois_soundness",
        "NNVerify.AbstractDomain.galois_soundness_axiom",
        "NNVerify.AbstractDomain.transformer_soundness",
        "NNVerify.AbstractDomain.transformer_soundness_axiom",
        "NNVerify.AbstractDomain.composition_soundness",
        "NNVerify.AbstractDomain.composition_soundness_axiom",
        "NNVerify.AbstractDomain.precision_monotone",
        "NNVerify.AbstractDomain.precision_monotone_axiom",
        "NNVerify.AbstractDomain.ibp_is_interval_domain",
        "NNVerify.AbstractDomain.ibp_is_interval_domain_axiom",
        "NNVerify.AbstractDomain.zonotope_refines_interval",
        "NNVerify.AbstractDomain.zonotope_refines_interval_axiom",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
        assert!(
            name.starts_with("NNVerify.AbstractDomain."),
            "{name} must use NNVerify.AbstractDomain. prefix",
        );
    }
}

// ---------------------------------------------------------------
// Generalized domain operations registration tests
// ---------------------------------------------------------------

#[test]
fn test_ad_contains_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.AbstractDomain.ad_contains"))
        .is_some());
}

#[test]
fn test_sound_linear_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.AbstractDomain.sound_linear"))
        .is_some());
}

#[test]
fn test_sound_relu_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.AbstractDomain.sound_relu"))
        .is_some());
}

#[test]
fn test_sound_compose_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.AbstractDomain.sound_compose"))
        .is_some());
}

#[test]
fn test_tighter_than_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.AbstractDomain.tighter_than"))
        .is_some());
}

// ---------------------------------------------------------------
// IBP instance registration tests
// ---------------------------------------------------------------

#[test]
fn test_ibp_instance_registered() {
    let env = make_env_with_ibp();
    assert!(env
        .get_const(&Name::from_string("NNVerify.AbstractDomain.ibp_instance"))
        .is_some());
}

#[test]
fn test_ibp_sound_linear_registered() {
    let env = make_env_with_ibp();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.ibp_sound_linear"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.ibp_sound_linear_axiom"
        ))
        .is_some());
}

#[test]
fn test_ibp_sound_relu_registered() {
    let env = make_env_with_ibp();
    assert!(env
        .get_const(&Name::from_string("NNVerify.AbstractDomain.ibp_sound_relu"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.ibp_sound_relu_axiom"
        ))
        .is_some());
}

#[test]
fn test_ibp_sound_compose_registered() {
    let env = make_env_with_ibp();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.ibp_sound_compose"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.AbstractDomain.ibp_sound_compose_axiom"
        ))
        .is_some());
}

// ---------------------------------------------------------------
// Generalized domain operations type checking tests
// ---------------------------------------------------------------

#[test]
fn test_ad_contains_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.AbstractDomain.ad_contains"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer ad_contains type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_sound_linear_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.AbstractDomain.sound_linear"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer sound_linear type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_sound_relu_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.AbstractDomain.sound_relu"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer sound_relu type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_sound_compose_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.AbstractDomain.sound_compose"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer sound_compose type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_tighter_than_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.AbstractDomain.tighter_than"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer tighter_than type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_ibp_instance_type_checks() {
    let env = make_env_with_ibp();
    let e = Expr::const_(
        Name::from_string("NNVerify.AbstractDomain.ibp_instance"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer ibp_instance type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_ibp_sound_linear_type_checks() {
    let env = make_env_with_ibp();
    let e = Expr::const_(
        Name::from_string("NNVerify.AbstractDomain.ibp_sound_linear"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer ibp_sound_linear type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_ibp_sound_relu_type_checks() {
    let env = make_env_with_ibp();
    let e = Expr::const_(
        Name::from_string("NNVerify.AbstractDomain.ibp_sound_relu"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer ibp_sound_relu type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_ibp_sound_compose_type_checks() {
    let env = make_env_with_ibp();
    let e = Expr::const_(
        Name::from_string("NNVerify.AbstractDomain.ibp_sound_compose"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer ibp_sound_compose type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// ---------------------------------------------------------------
// IBP instance theorem kinds
// ---------------------------------------------------------------

#[test]
fn test_ibp_instance_theorem_axiom_pairs() {
    let env = make_env_with_ibp();
    let theorems = [
        "NNVerify.AbstractDomain.ibp_sound_linear",
        "NNVerify.AbstractDomain.ibp_sound_relu",
        "NNVerify.AbstractDomain.ibp_sound_compose",
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
// Generalized domain ops are axioms (definition-as-axiom pattern)
// ---------------------------------------------------------------

#[test]
fn test_generalized_domain_ops_are_axioms() {
    let env = make_env();
    for name in &[
        "NNVerify.AbstractDomain.ad_contains",
        "NNVerify.AbstractDomain.sound_linear",
        "NNVerify.AbstractDomain.sound_relu",
        "NNVerify.AbstractDomain.sound_compose",
        "NNVerify.AbstractDomain.tighter_than",
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
fn test_ibp_instance_is_axiom() {
    let env = make_env_with_ibp();
    let info = env
        .get_const(&Name::from_string("NNVerify.AbstractDomain.ibp_instance"))
        .expect("ibp_instance should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Axiom,
        "ibp_instance should be an Axiom (definition-as-axiom pattern)"
    );
}

// ---------------------------------------------------------------
// Idempotency test
// ---------------------------------------------------------------

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_abstract_domain().expect("first init");
    env.init_nn_verify_abstract_domain().expect("second init");
}

#[test]
fn test_ibp_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_abstract_domain_ibp()
        .expect("first ibp init");
    env.init_nn_verify_abstract_domain_ibp()
        .expect("second ibp init");
}

// ---------------------------------------------------------------
// Complete naming convention test (updated for new declarations)
// ---------------------------------------------------------------

#[test]
fn test_all_abstract_domain_names_use_prefix() {
    // Uses IBP env since it's a superset of the base env
    let env = make_env_with_ibp();
    let names = [
        // Original definitions
        "NNVerify.AbstractDomain.abstract_domain",
        "NNVerify.AbstractDomain.galois_connection",
        "NNVerify.AbstractDomain.abstract_transformer",
        "NNVerify.AbstractDomain.domain_precision",
        "NNVerify.AbstractDomain.domain_composition",
        // Generalized operations
        "NNVerify.AbstractDomain.ad_contains",
        "NNVerify.AbstractDomain.sound_linear",
        "NNVerify.AbstractDomain.sound_relu",
        "NNVerify.AbstractDomain.sound_compose",
        "NNVerify.AbstractDomain.tighter_than",
        // IBP instance
        "NNVerify.AbstractDomain.ibp_instance",
        "NNVerify.AbstractDomain.ibp_sound_linear",
        "NNVerify.AbstractDomain.ibp_sound_linear_axiom",
        "NNVerify.AbstractDomain.ibp_sound_relu",
        "NNVerify.AbstractDomain.ibp_sound_relu_axiom",
        "NNVerify.AbstractDomain.ibp_sound_compose",
        "NNVerify.AbstractDomain.ibp_sound_compose_axiom",
        // Original theorems
        "NNVerify.AbstractDomain.galois_soundness",
        "NNVerify.AbstractDomain.galois_soundness_axiom",
        "NNVerify.AbstractDomain.transformer_soundness",
        "NNVerify.AbstractDomain.transformer_soundness_axiom",
        "NNVerify.AbstractDomain.composition_soundness",
        "NNVerify.AbstractDomain.composition_soundness_axiom",
        "NNVerify.AbstractDomain.precision_monotone",
        "NNVerify.AbstractDomain.precision_monotone_axiom",
        "NNVerify.AbstractDomain.ibp_is_interval_domain",
        "NNVerify.AbstractDomain.ibp_is_interval_domain_axiom",
        "NNVerify.AbstractDomain.zonotope_refines_interval",
        "NNVerify.AbstractDomain.zonotope_refines_interval_axiom",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
        assert!(
            name.starts_with("NNVerify.AbstractDomain."),
            "{name} must use NNVerify.AbstractDomain. prefix",
        );
    }
}
