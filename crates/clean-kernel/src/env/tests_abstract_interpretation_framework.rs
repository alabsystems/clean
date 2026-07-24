// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for abstract interpretation framework (lattice ops, Galois connections,
//! domain instances, transfer functions).
//!
//! Part of #3189.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_abstract_interpretation_framework()
        .expect("init_abstract_interpretation_framework");
    env
}

// ---------------------------------------------------------------
// Lattice operation registration tests
// ---------------------------------------------------------------

#[test]
fn test_framework_join_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Framework.join"))
        .is_some());
}

#[test]
fn test_framework_meet_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Framework.meet"))
        .is_some());
}

#[test]
fn test_framework_bot_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Framework.bot"))
        .is_some());
}

#[test]
fn test_framework_top_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Framework.top"))
        .is_some());
}

// ---------------------------------------------------------------
// Galois connection registration tests
// ---------------------------------------------------------------

#[test]
fn test_framework_galois_connection_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.GaloisConnection"
        ))
        .is_some());
}

#[test]
fn test_framework_galois_adjunction_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.galois_adjunction"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.galois_adjunction_axiom"
        ))
        .is_some());
}

// ---------------------------------------------------------------
// Interval domain instance registration tests
// ---------------------------------------------------------------

#[test]
fn test_framework_interval_join_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Framework.interval_join"))
        .is_some());
}

#[test]
fn test_framework_interval_meet_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Framework.interval_meet"))
        .is_some());
}

#[test]
fn test_framework_interval_bot_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Framework.interval_bot"))
        .is_some());
}

#[test]
fn test_framework_interval_top_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Framework.interval_top"))
        .is_some());
}

#[test]
fn test_framework_interval_widening_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.interval_widening"
        ))
        .is_some());
}

// ---------------------------------------------------------------
// Zonotope domain instance registration tests
// ---------------------------------------------------------------

#[test]
fn test_framework_zonotope_join_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Framework.zonotope_join"))
        .is_some());
}

#[test]
fn test_framework_zonotope_meet_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Framework.zonotope_meet"))
        .is_some());
}

#[test]
fn test_framework_zonotope_bot_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Framework.zonotope_bot"))
        .is_some());
}

#[test]
fn test_framework_zonotope_top_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Framework.zonotope_top"))
        .is_some());
}

#[test]
fn test_framework_zonotope_widening_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.zonotope_widening"
        ))
        .is_some());
}

// ---------------------------------------------------------------
// Transfer function registration tests
// ---------------------------------------------------------------

#[test]
fn test_framework_linear_transfer_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.linear_transfer"
        ))
        .is_some());
}

#[test]
fn test_framework_relu_transfer_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Framework.relu_transfer"))
        .is_some());
}

#[test]
fn test_framework_layer_compose_transfer_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.layer_compose_transfer"
        ))
        .is_some());
}

// ---------------------------------------------------------------
// Soundness theorem registration tests
// ---------------------------------------------------------------

#[test]
fn test_framework_join_upper_bound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.join_upper_bound"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.join_upper_bound_axiom"
        ))
        .is_some());
}

#[test]
fn test_framework_meet_lower_bound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.meet_lower_bound"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.meet_lower_bound_axiom"
        ))
        .is_some());
}

#[test]
fn test_framework_bot_least_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Framework.bot_least"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.bot_least_axiom"
        ))
        .is_some());
}

#[test]
fn test_framework_top_greatest_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Framework.top_greatest"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.top_greatest_axiom"
        ))
        .is_some());
}

#[test]
fn test_framework_galois_connection_sound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.galois_connection_sound"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.galois_connection_sound_axiom"
        ))
        .is_some());
}

#[test]
fn test_framework_interval_is_abstract_domain_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.interval_is_abstract_domain"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.interval_is_abstract_domain_axiom"
        ))
        .is_some());
}

#[test]
fn test_framework_zonotope_is_abstract_domain_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.zonotope_is_abstract_domain"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.zonotope_is_abstract_domain_axiom"
        ))
        .is_some());
}

#[test]
fn test_framework_interval_zonotope_galois_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.interval_zonotope_galois"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.interval_zonotope_galois_axiom"
        ))
        .is_some());
}

#[test]
fn test_framework_zonotope_refines_interval_galois_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.zonotope_refines_interval_galois"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.zonotope_refines_interval_galois_axiom"
        ))
        .is_some());
}

#[test]
fn test_framework_linear_transfer_sound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.linear_transfer_sound"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.linear_transfer_sound_axiom"
        ))
        .is_some());
}

#[test]
fn test_framework_relu_transfer_sound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.relu_transfer_sound"
        ))
        .is_some());
    assert!(env
        .get_const(&Name::from_string(
            "AbstractInterp.Framework.relu_transfer_sound_axiom"
        ))
        .is_some());
}

// ---------------------------------------------------------------
// Type checking tests
// ---------------------------------------------------------------

#[test]
fn test_framework_join_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("AbstractInterp.Framework.join"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer join type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_framework_meet_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("AbstractInterp.Framework.meet"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer meet type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_framework_bot_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("AbstractInterp.Framework.bot"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer bot type");
    // bot : AbstractState (an element of the abstract state type)
    assert!(
        matches!(ty.kind(), ExprKind::Const(..)),
        "bot type should be AbstractState (Const), got {:?}",
        ty.kind()
    );
}

#[test]
fn test_framework_top_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("AbstractInterp.Framework.top"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer top type");
    // top : AbstractState (an element of the abstract state type)
    assert!(
        matches!(ty.kind(), ExprKind::Const(..)),
        "top type should be AbstractState (Const), got {:?}",
        ty.kind()
    );
}

#[test]
fn test_framework_galois_connection_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("AbstractInterp.Framework.GaloisConnection"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer GaloisConnection type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_framework_linear_transfer_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("AbstractInterp.Framework.linear_transfer"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer linear_transfer type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_framework_relu_transfer_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("AbstractInterp.Framework.relu_transfer"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer relu_transfer type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_framework_join_upper_bound_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("AbstractInterp.Framework.join_upper_bound"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&e).expect("infer join_upper_bound type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_framework_interval_is_abstract_domain_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("AbstractInterp.Framework.interval_is_abstract_domain"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer interval_is_abstract_domain type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_framework_zonotope_refines_interval_galois_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("AbstractInterp.Framework.zonotope_refines_interval_galois"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer zonotope_refines_interval_galois type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// ---------------------------------------------------------------
// Definition vs axiom classification tests
// ---------------------------------------------------------------

#[test]
fn test_framework_definitions_are_axioms() {
    let env = make_env();
    let axiom_names = [
        "AbstractInterp.Framework.join",
        "AbstractInterp.Framework.meet",
        "AbstractInterp.Framework.bot",
        "AbstractInterp.Framework.top",
        "AbstractInterp.Framework.GaloisConnection",
        "AbstractInterp.Framework.interval_join",
        "AbstractInterp.Framework.interval_meet",
        "AbstractInterp.Framework.interval_bot",
        "AbstractInterp.Framework.interval_top",
        "AbstractInterp.Framework.interval_widening",
        "AbstractInterp.Framework.zonotope_join",
        "AbstractInterp.Framework.zonotope_meet",
        "AbstractInterp.Framework.zonotope_bot",
        "AbstractInterp.Framework.zonotope_top",
        "AbstractInterp.Framework.zonotope_widening",
        "AbstractInterp.Framework.linear_transfer",
        "AbstractInterp.Framework.relu_transfer",
        "AbstractInterp.Framework.layer_compose_transfer",
    ];
    for name in &axiom_names {
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
fn test_framework_theorem_axiom_pairs() {
    let env = make_env();
    let theorems = [
        "AbstractInterp.Framework.join_upper_bound",
        "AbstractInterp.Framework.meet_lower_bound",
        "AbstractInterp.Framework.bot_least",
        "AbstractInterp.Framework.top_greatest",
        "AbstractInterp.Framework.galois_adjunction",
        "AbstractInterp.Framework.galois_connection_sound",
        "AbstractInterp.Framework.interval_is_abstract_domain",
        "AbstractInterp.Framework.zonotope_is_abstract_domain",
        "AbstractInterp.Framework.interval_zonotope_galois",
        "AbstractInterp.Framework.zonotope_refines_interval_galois",
        "AbstractInterp.Framework.linear_transfer_sound",
        "AbstractInterp.Framework.relu_transfer_sound",
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
// Naming convention test
// ---------------------------------------------------------------

#[test]
fn test_framework_naming_convention() {
    let env = make_env();
    let names = [
        // Lattice operations
        "AbstractInterp.Framework.join",
        "AbstractInterp.Framework.meet",
        "AbstractInterp.Framework.bot",
        "AbstractInterp.Framework.top",
        // Galois connection
        "AbstractInterp.Framework.GaloisConnection",
        "AbstractInterp.Framework.galois_adjunction",
        "AbstractInterp.Framework.galois_adjunction_axiom",
        // Interval domain
        "AbstractInterp.Framework.interval_join",
        "AbstractInterp.Framework.interval_meet",
        "AbstractInterp.Framework.interval_bot",
        "AbstractInterp.Framework.interval_top",
        "AbstractInterp.Framework.interval_widening",
        // Zonotope domain
        "AbstractInterp.Framework.zonotope_join",
        "AbstractInterp.Framework.zonotope_meet",
        "AbstractInterp.Framework.zonotope_bot",
        "AbstractInterp.Framework.zonotope_top",
        "AbstractInterp.Framework.zonotope_widening",
        // Transfer functions
        "AbstractInterp.Framework.linear_transfer",
        "AbstractInterp.Framework.relu_transfer",
        "AbstractInterp.Framework.layer_compose_transfer",
        // Soundness theorems
        "AbstractInterp.Framework.join_upper_bound",
        "AbstractInterp.Framework.join_upper_bound_axiom",
        "AbstractInterp.Framework.meet_lower_bound",
        "AbstractInterp.Framework.meet_lower_bound_axiom",
        "AbstractInterp.Framework.bot_least",
        "AbstractInterp.Framework.bot_least_axiom",
        "AbstractInterp.Framework.top_greatest",
        "AbstractInterp.Framework.top_greatest_axiom",
        "AbstractInterp.Framework.galois_connection_sound",
        "AbstractInterp.Framework.galois_connection_sound_axiom",
        "AbstractInterp.Framework.interval_is_abstract_domain",
        "AbstractInterp.Framework.interval_is_abstract_domain_axiom",
        "AbstractInterp.Framework.zonotope_is_abstract_domain",
        "AbstractInterp.Framework.zonotope_is_abstract_domain_axiom",
        "AbstractInterp.Framework.interval_zonotope_galois",
        "AbstractInterp.Framework.interval_zonotope_galois_axiom",
        "AbstractInterp.Framework.zonotope_refines_interval_galois",
        "AbstractInterp.Framework.zonotope_refines_interval_galois_axiom",
        "AbstractInterp.Framework.linear_transfer_sound",
        "AbstractInterp.Framework.linear_transfer_sound_axiom",
        "AbstractInterp.Framework.relu_transfer_sound",
        "AbstractInterp.Framework.relu_transfer_sound_axiom",
    ];
    for name in &names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
        assert!(
            name.starts_with("AbstractInterp.Framework."),
            "{name} must use AbstractInterp.Framework. prefix",
        );
    }
}

// ---------------------------------------------------------------
// Idempotency test
// ---------------------------------------------------------------

#[test]
fn test_framework_idempotent() {
    let mut env = Environment::new();
    env.init_abstract_interpretation_framework()
        .expect("first init");
    env.init_abstract_interpretation_framework()
        .expect("second init");
}

// ---------------------------------------------------------------
// Dependency test: base init is included
// ---------------------------------------------------------------

#[test]
fn test_framework_includes_base_abstract_interpretation() {
    let env = make_env();
    // The base abstract interpretation should also be initialized
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.AbstractState"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.Widening"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("AbstractInterp.soundness"))
        .is_some());
}
