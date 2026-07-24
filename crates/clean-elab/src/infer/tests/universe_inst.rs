// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for universe instance elaboration (.{u, v} syntax).
//!
//! Verifies that explicit universe level arguments on constants are wired
//! through elaboration instead of being replaced by fresh metavariables.

use super::*;
use clean_kernel::env::Declaration;

/// Create an environment with a polymorphic constant `MyList` that has
/// one universe parameter `u`, similar to `List.{u}`.
fn poly_env() -> Environment {
    let mut env = Environment::new();

    // MyList : Type u → Type u (one universe parameter)
    let u = Level::param(Name::from_string("u"));
    let type_u = Expr::sort(Level::succ(u.clone()));
    let mylist_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("MyList"),
        level_params: vec![Name::from_string("u")],
        type_: mylist_type,
    })
    .unwrap();

    // MyPair : Type u → Type v → Type (max u v) (two universe parameters)
    let v = Level::param(Name::from_string("v"));
    let type_v = Expr::sort(Level::succ(v.clone()));
    let type_max_uv = Expr::sort(Level::succ(Level::max(u.clone(), v.clone())));
    let mypair_type = Expr::pi(
        BinderInfo::Default,
        Expr::sort(Level::succ(u)),
        Expr::pi(BinderInfo::Default, type_v, type_max_uv),
    );

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("MyPair"),
        level_params: vec![Name::from_string("u"), Name::from_string("v")],
        type_: mypair_type,
    })
    .unwrap();

    // MonoConst : Prop (zero universe parameters)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("MonoConst"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    env
}

#[test]
fn test_universe_inst_single_level_literal() {
    // MyList.{1} should elaborate to Const("MyList", [Level::succ(Level::zero())])
    let env = poly_env();
    let expr = elab_with_env(&env, "@MyList.{1}").unwrap();
    match expr.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name, &Name::from_string("MyList"));
            assert_eq!(levels.len(), 1);
            // Level 1 = succ(zero)
            assert_eq!(levels[0], Level::succ(Level::zero()));
        }
        other => panic!("expected Const, got {other:?}"),
    }
}

#[test]
fn test_universe_inst_single_level_zero() {
    // MyList.{0} should elaborate with Level::zero()
    let env = poly_env();
    let expr = elab_with_env(&env, "@MyList.{0}").unwrap();
    match expr.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name, &Name::from_string("MyList"));
            assert_eq!(levels.len(), 1);
            assert_eq!(levels[0], Level::zero());
        }
        other => panic!("expected Const, got {other:?}"),
    }
}

#[test]
fn test_universe_inst_two_levels() {
    // MyPair.{1 2} should elaborate with two explicit levels
    let env = poly_env();
    let expr = elab_with_env(&env, "@MyPair.{1 2}").unwrap();
    match expr.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name, &Name::from_string("MyPair"));
            assert_eq!(levels.len(), 2);
            assert_eq!(levels[0], Level::succ(Level::zero()));
            assert_eq!(levels[1], Level::succ(Level::succ(Level::zero())));
        }
        other => panic!("expected Const, got {other:?}"),
    }
}

#[test]
fn test_universe_inst_named_param() {
    // MyList.{u} should elaborate with a named universe parameter
    let env = poly_env();
    let expr = elab_with_env(&env, "@MyList.{u}").unwrap();
    match expr.kind() {
        ExprKind::Const(name, levels) => {
            assert_eq!(name, &Name::from_string("MyList"));
            assert_eq!(levels.len(), 1);
            assert_eq!(levels[0], Level::param(Name::from_string("u")));
        }
        other => panic!("expected Const, got {other:?}"),
    }
}

#[test]
fn test_universe_inst_level_mismatch_too_many() {
    // MyList.{1 2} should fail: MyList has 1 universe param, got 2
    let env = poly_env();
    let err = elab_with_env(&env, "@MyList.{1 2}").unwrap_err();
    match err {
        ElabError::UniverseLevelMismatch {
            expected, actual, ..
        } => {
            assert_eq!(expected, 1);
            assert_eq!(actual, 2);
        }
        other => panic!("expected UniverseLevelMismatch, got {other}"),
    }
}

#[test]
fn test_universe_inst_level_mismatch_too_few() {
    // MyPair.{1} should fail: MyPair has 2 universe params, got 1
    let env = poly_env();
    let err = elab_with_env(&env, "@MyPair.{1}").unwrap_err();
    match err {
        ElabError::UniverseLevelMismatch {
            expected, actual, ..
        } => {
            assert_eq!(expected, 2);
            assert_eq!(actual, 1);
        }
        other => panic!("expected UniverseLevelMismatch, got {other}"),
    }
}

#[test]
fn test_universe_inst_mono_const_empty() {
    // MonoConst.{} — zero levels on a zero-param const should succeed.
    // Note: parser may not support empty .{}, so we test the error case instead.
    // MonoConst.{1} should fail: MonoConst has 0 universe params
    let env = poly_env();
    let err = elab_with_env(&env, "@MonoConst.{1}").unwrap_err();
    match err {
        ElabError::UniverseLevelMismatch {
            expected, actual, ..
        } => {
            assert_eq!(expected, 0);
            assert_eq!(actual, 1);
        }
        other => panic!("expected UniverseLevelMismatch, got {other}"),
    }
}

#[test]
fn test_universe_inst_without_explicit_marker() {
    // MyList.{1} without @ should also work (may insert implicits after)
    let env = poly_env();
    let expr = elab_with_env(&env, "MyList.{1}").unwrap();
    // The result may be wrapped in implicit argument applications,
    // but the innermost const should have the explicit level.
    fn find_const(e: &Expr) -> Option<(&Name, &[Level])> {
        match e.kind() {
            ExprKind::Const(name, levels) => Some((name, levels)),
            ExprKind::App(f, _) => find_const(f),
            _ => None,
        }
    }
    let (name, levels) = find_const(&expr).expect("should contain a Const");
    assert_eq!(name, &Name::from_string("MyList"));
    assert_eq!(levels.len(), 1);
    assert_eq!(levels[0], Level::succ(Level::zero()));
}
