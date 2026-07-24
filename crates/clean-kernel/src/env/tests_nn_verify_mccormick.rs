// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for McCormick bilinear relaxation envelope module.
//!
//! Part of #3204.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_mccormick()
        .expect("init_nn_verify_mccormick");
    env
}

#[test]
fn test_envelope_lower_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.McCormick.envelope_lower"))
        .is_some());
}

#[test]
fn test_envelope_upper_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.McCormick.envelope_upper"))
        .is_some());
}

#[test]
fn test_gap_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.McCormick.gap"))
        .is_some());
}

#[test]
fn test_mccormick_sound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.McCormick.mccormick_sound"))
        .is_some());
}

#[test]
fn test_mccormick_gap_bound_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("NNVerify.McCormick.mccormick_gap_bound"))
        .is_some());
}

#[test]
fn test_mccormick_tight_at_corners_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string(
            "NNVerify.McCormick.mccormick_tight_at_corners"
        ))
        .is_some());
}

#[test]
fn test_envelope_lower_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.McCormick.envelope_lower"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer NNVerify.McCormick.envelope_lower type");
    // Should be Rat -> Rat -> Rat -> Rat -> Rat -> Rat -> Prop
    assert!(
        matches!(ty.kind(), ExprKind::Pi(..)),
        "envelope_lower should have Pi type, got {:?}",
        ty.kind()
    );
}

#[test]
fn test_envelope_upper_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.McCormick.envelope_upper"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer NNVerify.McCormick.envelope_upper type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_gap_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string("NNVerify.McCormick.gap"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer NNVerify.McCormick.gap type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_mccormick_sound_type_checks() {
    let env = make_env();
    let e = Expr::const_(
        Name::from_string("NNVerify.McCormick.mccormick_sound"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&e)
        .expect("infer NNVerify.McCormick.mccormick_sound type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_mccormick_sound_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("NNVerify.McCormick.mccormick_sound"))
        .expect("mccormick_sound must be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "mccormick_sound should be a local-evidence theorem, got {:?}",
        info.kind
    );
    assert!(
        info.value.is_some(),
        "mccormick_sound theorem must carry the local-evidence proof value"
    );
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_mccormick().expect("first init");
    env.init_nn_verify_mccormick().expect("second init");
}

/// Verify all McCormick names use the `NNVerify.McCormick.` prefix.
#[test]
fn test_nn_verify_mccormick_naming_convention() {
    let env = make_env();
    let expected_names = [
        "NNVerify.McCormick.envelope_lower",
        "NNVerify.McCormick.envelope_upper",
        "NNVerify.McCormick.gap",
        "NNVerify.McCormick.mccormick_sound",
        "NNVerify.McCormick.mccormick_gap_bound",
        "NNVerify.McCormick.mccormick_tight_at_corners",
    ];
    for name in &expected_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{} should be registered",
            name,
        );
    }
}

/// C005 local-evidence retirement: `mccormick_gap_bound` is a theorem whose
/// final premise is the old conclusion. The proof returns that premise,
/// avoiding the old `Rat.le_refl`-over-reducible-`gap` masquerade.
#[test]
fn test_mccormick_gap_bound_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let name = Name::from_string("NNVerify.McCormick.mccormick_gap_bound");
    let info = env
        .get_const(&name)
        .expect("mccormick_gap_bound must be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "mccormick_gap_bound should be a local-evidence theorem, got {:?}",
        info.kind,
    );
    assert!(
        info.value.is_some(),
        "mccormick_gap_bound theorem must carry the local-evidence proof value",
    );
}

#[test]
fn test_mccormick_tight_at_corners_is_hypothesis_wrapped_theorem() {
    let env = make_env();
    let name = Name::from_string("NNVerify.McCormick.mccormick_tight_at_corners");
    let info = env
        .get_const(&name)
        .expect("mccormick_tight_at_corners must be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "mccormick_tight_at_corners should be a local-evidence theorem, got {:?}",
        info.kind,
    );
    assert!(
        info.value.is_some(),
        "mccormick_tight_at_corners theorem must carry the local-evidence proof value",
    );
}
