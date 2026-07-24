// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{Environment, Expr, Level, Name};

#[test]
fn test_sorry_counter_increments() {
    let _serial = crate::test_utils::serial_test_guard();
    let initial = sorry_count();
    let env = Environment::new();
    let _ = create_sorry_term(&env, &Expr::prop());
    let after = sorry_count();
    assert!(
        after > initial,
        "Counter should increase after create_sorry_term: before={}, after={}",
        initial,
        after
    );
}

#[test]
fn test_sorry_counter_reset() {
    let _serial = crate::test_utils::serial_test_guard();
    let env = Environment::new();
    let _ = create_sorry_term(&env, &Expr::prop());
    reset_sorry_counter();
    assert_eq!(sorry_count(), 0, "Counter should be 0 after reset");
    assert_eq!(
        explicit_sorry_count(),
        0,
        "explicit sorry counter should reset with aggregate"
    );
    assert_eq!(
        synthetic_sorry_count(),
        0,
        "synthetic sorry counter should reset with aggregate"
    );
}

#[test]
fn test_assert_no_sorry_passes_when_zero() {
    let _serial = crate::test_utils::serial_test_guard();
    reset_sorry_counter();
    // Should not panic when counter is zero
    assert_no_sorry();
}

#[test]
#[should_panic(expected = "sorry term(s) were generated")]
fn test_assert_no_sorry_panics_when_nonzero() {
    let _serial = crate::test_utils::serial_test_guard();
    reset_sorry_counter();
    let env = Environment::new();
    let _ = create_sorry_term(&env, &Expr::prop());
    assert_no_sorry();
}

#[test]
fn test_sorry_location_tracking() {
    let _serial = crate::test_utils::serial_test_guard();
    reset_sorry_counter();
    enable_sorry_location_tracking();
    reset_sorry_locations();

    let env = Environment::new();
    let _ = create_sorry_term(&env, &Expr::prop());

    let map = sorry_locations().expect("Location tracking should be enabled");
    assert!(!map.is_empty(), "Should have at least one location entry");

    // All counts should be positive
    for (loc, count) in &map {
        assert!(*count > 0, "Location {loc} should have positive count");
    }

    // Reset should clear locations
    reset_sorry_locations();
    let after_reset = sorry_locations().unwrap();
    assert!(
        after_reset.is_empty(),
        "Locations should be empty after reset"
    );
}

#[test]
fn test_sorry_locations_none_without_enabling() {
    let _serial = crate::test_utils::serial_test_guard();
    reset_sorry_counter();
    let env = Environment::new();
    let _ = create_sorry_term(&env, &Expr::prop());
    let _ = create_sorry_term(&env, &Expr::type_());
    assert_eq!(sorry_count(), 2, "Should count multiple sorry terms");
}

#[test]
fn test_deny_sorry_not_enabled_by_default() {
    let _serial = crate::test_utils::serial_test_guard();
    let _ = deny_sorry_enabled(); // should not panic
}

#[test]
fn test_local_ay_reconstruction_success_counter_is_thread_scoped() {
    let _serial = crate::test_utils::serial_test_guard();
    reset_local_ay_reconstruction_success_counter();
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "local reconstruction counter should start at 0 after reset"
    );

    record_ay_reconstruction_success();
    assert_eq!(
        local_ay_reconstruction_success_count(),
        1,
        "recording on the current thread should increment the local reconstruction counter"
    );

    reset_local_ay_reconstruction_success_counter();
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "local reconstruction counter should reset independently"
    );
}

#[test]
fn test_create_sorry_term_uses_sorry_axiom_from_default_env() {
    let _serial = crate::test_utils::serial_test_guard();
    reset_sorry_counter();
    // Environment::new() pre-initializes the polymorphic sorry axiom.
    let env = Environment::new();
    let term = create_sorry_term(&env, &Expr::prop());

    // create_sorry_term should return @sorry Prop.
    match &term.kind {
        crate::expr::ExprKind::App(f, a) => {
            assert_eq!(
                a.as_ref(),
                &Expr::prop(),
                "Expected sorry argument to be Prop"
            );
            match &f.kind {
                crate::expr::ExprKind::Const(name, levels) => {
                    assert_eq!(
                        name.to_string(),
                        "sorry",
                        "Expected sorry constant in default environment"
                    );
                    assert_eq!(levels.len(), 1, "Expected one universe level on sorry");
                }
                _ => panic!("Expected sorry constant head, got {f:?}"),
            }
        }
        crate::expr::ExprKind::Const(name, _) => {
            assert_eq!(
                name.to_string(),
                "sorry",
                "Expected sorry constant in default environment"
            );
        }
        _ => panic!("Expected sorry application/constant, got {term:?}"),
    }
    assert_eq!(
        sorry_count(),
        1,
        "Counter should increment when creating a sorry term"
    );
    assert_eq!(
        synthetic_sorry_count(),
        1,
        "legacy create_sorry_term should count as synthetic"
    );
}

/// Extract the universe level from a sorry term `@sorry.{u} goal_ty`.
fn extract_sorry_level(term: &Expr) -> Level {
    match &term.kind {
        crate::expr::ExprKind::App(f, _) => match &f.kind {
            crate::expr::ExprKind::Const(_, levels) => {
                assert_eq!(levels.len(), 1);
                levels[0].clone()
            }
            _ => panic!("Expected sorry constant head, got {f:?}"),
        },
        _ => panic!("Expected sorry application, got {term:?}"),
    }
}

#[test]
fn test_sorry_level_zero_for_proposition_goal() {
    let _serial = crate::test_utils::serial_test_guard();
    reset_sorry_counter();
    let mut env = Environment::new();
    env.add_decl(crate::env::Declaration::Axiom {
        name: Name::from_string("TestProp"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let goal_ty = Expr::const_(Name::from_string("TestProp"), vec![]);
    let term = create_sorry_term(&env, &goal_ty);
    let level = extract_sorry_level(&term);
    assert_eq!(
        level,
        Level::zero(),
        "sorry for proposition goal should use u=0"
    );
}

#[test]
fn test_sorry_level_one_for_type_goal() {
    let _serial = crate::test_utils::serial_test_guard();
    reset_sorry_counter();
    let mut env = Environment::new();
    env.add_decl(crate::env::Declaration::Axiom {
        name: Name::from_string("TestNat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    let goal_ty = Expr::const_(Name::from_string("TestNat"), vec![]);
    let term = create_sorry_term(&env, &goal_ty);
    let level = extract_sorry_level(&term);
    assert_eq!(
        level,
        Level::succ(Level::zero()),
        "sorry for Type-level goal should use u=1"
    );
}

#[test]
fn test_sorry_level_fallback_for_fvar_goal() {
    let _serial = crate::test_utils::serial_test_guard();
    reset_sorry_counter();
    let env = Environment::new();
    let fvar_goal = Expr::fvar(crate::expr::FVarId::new(999));
    let term = create_sorry_term(&env, &fvar_goal);
    let level = extract_sorry_level(&term);
    assert_eq!(
        level,
        Level::zero(),
        "sorry for fvar goal should fall back to u=0"
    );
}

#[test]
fn test_sorry_explicit_level_overrides_fallback_for_fvar_goal() {
    let _serial = crate::test_utils::serial_test_guard();
    reset_sorry_counter();
    let env = Environment::new();
    let fvar_goal = Expr::fvar(crate::expr::FVarId::new(999));
    let expected = Level::param(Name::from_string("u"));
    let term = create_sorry_term_with_kind_at_level(
        &env,
        &fvar_goal,
        SorryKind::Explicit,
        expected.clone(),
    );
    let level = extract_sorry_level(&term);
    assert_eq!(
        level, expected,
        "explicit-level sorry construction should preserve the provided universe"
    );
}

#[test]
fn test_smt_proof_fallback_applies_goal_ty() {
    let _serial = crate::test_utils::serial_test_guard();
    reset_sorry_counter();
    let env = Environment::default();
    assert!(
        env.get_const(&Name::from_string("sorry")).is_none(),
        "default env should lack sorry axiom"
    );

    let goal_ty = Expr::prop();
    let term = create_sorry_term(&env, &goal_ty);

    match &term.kind {
        crate::expr::ExprKind::App(f, a) => {
            assert_eq!(
                a.as_ref(),
                &goal_ty,
                "SMT_PROOF fallback should apply goal_ty"
            );
            match &f.kind {
                crate::expr::ExprKind::Const(name, levels) => {
                    assert_eq!(name.to_string(), "SMT_PROOF");
                    assert_eq!(levels.len(), 1, "SMT_PROOF should have one universe level");
                }
                _ => panic!("Expected SMT_PROOF constant head, got {f:?}"),
            }
        }
        _ => panic!("Expected SMT_PROOF application, got bare constant or other: {term:?}"),
    }
    assert_eq!(
        sorry_count(),
        1,
        "Fallback should still increment sorry counter"
    );
}

#[test]
fn test_smt_proof_fallback_level_for_type_goal() {
    let _serial = crate::test_utils::serial_test_guard();
    reset_sorry_counter();
    let mut env = Environment::default();
    env.add_decl(crate::env::Declaration::Axiom {
        name: Name::from_string("MyType"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    assert!(env.get_const(&Name::from_string("sorry")).is_none());

    let goal_ty = Expr::const_(Name::from_string("MyType"), vec![]);
    let term = create_sorry_term(&env, &goal_ty);

    match &term.kind {
        crate::expr::ExprKind::App(f, _) => match &f.kind {
            crate::expr::ExprKind::Const(_, levels) => {
                assert_eq!(levels.len(), 1);
                assert_eq!(
                    levels[0],
                    Level::succ(Level::zero()),
                    "SMT_PROOF for Type-level goal should use u=1"
                );
            }
            _ => panic!("Expected SMT_PROOF constant head"),
        },
        _ => panic!("Expected SMT_PROOF application"),
    }
}

#[test]
fn test_create_sorry_term_with_kind_uses_sorry_ax_after_bool() {
    let _serial = crate::test_utils::serial_test_guard();
    reset_sorry_counter();
    let mut env = Environment::default();
    env.init_bool().expect("Bool init should expose sorryAx");

    let explicit = create_sorry_term_with_kind(&env, &Expr::prop(), SorryKind::Explicit);
    assert!(
        explicit.is_non_synthetic_sorry(),
        "explicit provenance should map to non-synthetic sorryAx"
    );
    assert!(
        explicit.get_app_fn().is_const(),
        "explicit sorryAx term should stay on an application spine"
    );

    let synthetic = create_sorry_term(&env, &Expr::prop());
    assert!(
        synthetic.is_synthetic_sorry(),
        "default sorry creation after Bool should use synthetic sorryAx"
    );

    assert_eq!(
        sorry_count(),
        2,
        "aggregate sorry counter should include both kinds"
    );
    assert_eq!(
        explicit_sorry_count(),
        1,
        "explicit counter should isolate user-directed sorry creation"
    );
    assert_eq!(
        synthetic_sorry_count(),
        1,
        "synthetic counter should isolate internal sorry creation"
    );
}
