// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! sorry elaboration regression tests

use super::*;
use clean_kernel::sorry::with_sorry_location_key;
use serial_test::serial;

// =========================================================================
// Issue #157: sorry elaboration with expected type
// =========================================================================

#[test]
fn test_sorry_theorem_elaboration() {
    // Regression test for issue #157: sorry term elaboration doesn't apply to expected type
    //
    // `sorry : {α : Sort u} → α` is polymorphic and needs to be applied to the expected type.
    // Previously, `theorem test : Prop := sorry` would fail with:
    //   TypeMismatch { expected: Prop, inferred: {α : Sort u_1} → α }
    //
    // The fix in apply_implicit_to_expected_type automatically applies sorry to the expected type.
    let result = elab_decl("theorem test_sorry : Prop := sorry");
    assert!(
        result.is_ok(),
        "theorem with sorry should elaborate: {:?}",
        result.err()
    );

    match result.unwrap() {
        ElabResult::Theorem {
            name, ty, proof, ..
        } => {
            assert_eq!(name, Name::from_string("test_sorry"));
            // Type should be Prop
            assert!(matches!(ty.kind(), ExprKind::Sort(Level::Zero)));
            // Proof should be sorry applied to Prop: App(sorry.{?u}, Prop)
            assert!(
                matches!(proof.kind(), ExprKind::App(func, arg) if matches!(func.kind(), ExprKind::Const(n, _) if n.to_string() == "sorry") && matches!(arg.kind(), ExprKind::Sort(Level::Zero))),
                "proof should be sorry applied to Prop, got: {:?}",
                proof
            );
        }
        other => panic!("expected Theorem, got: {:?}", other),
    }
}

#[test]
fn test_sorry_definition_elaboration() {
    // Test that definitions with sorry also work correctly
    let result = elab_decl("def test_sorry_def : Type := sorry");
    assert!(
        result.is_ok(),
        "def with sorry should elaborate: {:?}",
        result.err()
    );

    match result.unwrap() {
        ElabResult::Definition { name, ty, val, .. } => {
            assert_eq!(name, Name::from_string("test_sorry_def"));
            // Type should be Type (Sort 1)
            assert!(matches!(ty.kind(), ExprKind::Sort(Level::Succ(_))));
            // Value should be sorry applied to Type
            assert!(
                matches!(val.kind(), ExprKind::App(func, _) if matches!(func.kind(), ExprKind::Const(n, _) if n.to_string() == "sorry")),
                "value should be sorry applied to Type, got: {:?}",
                val
            );
        }
        other => panic!("expected Definition, got: {:?}", other),
    }
}

#[test]
fn test_sorry_with_custom_type() {
    // Test that sorry works with custom types, not just Prop/Type
    // This is the pattern used in FATE-X theorems where sorry must be applied
    // to a complex type like `IsPrincipalIdealRing R`

    // Environment::new() already initializes sorry: {α : Sort u} → α
    let mut env = Environment::new();

    // Add a simple typeclass-like type: MyClass : Type → Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("MyClass"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Implicit, Expr::type_(), Expr::prop()),
    })
    .unwrap();

    // Add Nat
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Now elaborate a theorem with sorry body where expected type is MyClass Nat
    let mut ctx = ElabCtx::new(&env);

    // Parse: theorem test : MyClass Nat := sorry
    let surface = parse_decl_for_elab("theorem test : MyClass Nat := sorry").unwrap();
    let result = ctx.elab_decl(&surface);

    assert!(
        result.is_ok(),
        "theorem with sorry and custom type should elaborate: {:?}",
        result.err()
    );

    match result.unwrap() {
        ElabResult::Theorem {
            name, ty, proof, ..
        } => {
            assert_eq!(name, Name::from_string("test"));
            // Type should be MyClass Nat (an App)
            assert!(
                matches!(ty.kind(), ExprKind::App(_, _)),
                "type should be MyClass Nat, got: {:?}",
                ty
            );
            // Proof should be sorry applied to (MyClass Nat)
            assert!(
                matches!(proof.kind(), ExprKind::App(func, _) if matches!(func.kind(), ExprKind::Const(n, _) if n.to_string() == "sorry")),
                "proof should be sorry applied to expected type, got: {:?}",
                proof
            );
        }
        other => panic!("expected Theorem, got: {:?}", other),
    }
}

/// Issue #169: Test that apply_implicit_to_expected_type unifies universe levels
///
/// When `sorry : {α : Sort u} → α` is applied to an expected type like `Nat → Nat → Nat`,
/// we need to unify `u` with `Succ(Zero)` (the level of `Nat → Nat → Nat : Type 0`).
#[test]
fn test_issue169_apply_implicit_level_unification() {
    // Environment::new() already initializes Nat and sorry
    let env = Environment::new();

    // Elaborate: def f : Nat → Nat → Nat := sorry
    // This previously failed with: TypeMismatch { expected: Sort(Param(u_0)), inferred: Sort(Succ(Zero)) }
    let mut ctx = ElabCtx::new(&env);

    let surface = parse_decl_for_elab("def f : Nat → Nat → Nat := sorry").unwrap();
    let result = ctx.elab_decl(&surface);

    assert!(
        result.is_ok(),
        "def with sorry and function type should elaborate without level mismatch: {:?}",
        result.err()
    );

    match result.unwrap() {
        ElabResult::Definition { name, ty, val, .. } => {
            assert_eq!(name, Name::from_string("f"));
            // Type should be Nat → Nat → Nat (a Pi type)
            assert!(
                matches!(ty.kind(), ExprKind::Pi(_, _, _)),
                "type should be Nat → Nat → Nat, got: {:?}",
                ty
            );
            // Value should contain sorry somewhere - the exact structure depends on
            // whether universe params are inserted as lambdas
            // The key is that elaboration succeeded without TypeMismatch
            fn contains_sorry(e: &Expr) -> bool {
                match e.kind() {
                    ExprKind::Const(n, _) => n.to_string() == "sorry",
                    ExprKind::App(f, a) => contains_sorry(f) || contains_sorry(a),
                    ExprKind::Lam(_, _, b) => contains_sorry(b),
                    _ => false,
                }
            }
            assert!(
                contains_sorry(&val),
                "value should contain sorry, got: {:?}",
                val
            );
        }
        other => panic!("expected Definition, got: {:?}", other),
    }
}

/// Issue #169: Test that complex nested function types work with sorry
#[test]
fn test_issue169_nested_function_type() {
    let env = Environment::new();

    // Elaborate: def g : (Nat → Nat) → Nat → Nat := sorry
    let mut ctx = ElabCtx::new(&env);

    let surface = parse_decl_for_elab("def g : (Nat → Nat) → Nat → Nat := sorry").unwrap();
    let result = ctx.elab_decl(&surface);

    assert!(
        result.is_ok(),
        "def with sorry and nested function type should elaborate: {:?}",
        result.err()
    );
}

/// Issue #1702: apply_implicit_to_expected_type must propagate infer_type failures
/// instead of silently returning the original term.
#[test]
fn test_issue1702_apply_implicit_propagates_infer_error() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let unknown = Expr::const_(Name::from_string("Issue1702.unknown"), vec![]);
    let result = ctx.apply_implicit_to_expected_type(&unknown, &Expr::prop());

    assert!(
        matches!(result, Err(ElabError::TypeMismatch { .. })),
        "expected infer_type failure to propagate, got: {:?}",
        result
    );
}

#[test]
#[serial]
fn test_explicit_sorry_uses_non_synthetic_provenance_after_bool() {
    with_sorry_location_key("fixture:sorry:infer:explicit_provenance", || {
        let mut env = Environment::new();
        env.init_true_false()
            .expect("True/False init should succeed before explicit sorry elaboration");
        env.init_bool()
            .expect("Bool init should expose sorryAx before explicit sorry elaboration");

        let mut ctx = ElabCtx::new(&env);
        let surface = parse_decl_for_elab("theorem explicit_sorry : True := sorry").unwrap();
        let result = ctx.elab_decl(&surface).unwrap();

        match result {
            ElabResult::Theorem { proof, .. } => {
                assert!(
                    proof.is_non_synthetic_sorry(),
                    "explicit term sorry should elaborate to non-synthetic sorryAx, got {proof:?}"
                );
                assert!(
                    !proof.has_synthetic_sorry(),
                    "explicit term sorry should not contain synthetic provenance, got {proof:?}"
                );
            }
            other => panic!("expected Theorem, got: {other:?}"),
        }
    });
}

#[test]
#[serial]
fn test_parser_recovery_sorry_stays_synthetic_after_bool() {
    with_sorry_location_key("fixture:sorry:infer:synthetic_parser_recovery", || {
        let mut env = Environment::new();
        env.init_true_false()
            .expect("True/False init should succeed before recovery elaboration");
        env.init_bool()
            .expect("Bool init should expose sorryAx before recovery elaboration");

        let mut ctx = ElabCtx::new(&env);
        let surface = parse_decl_for_elab(
            "theorem recovered : True := suffices h : True by have : True :=; True.intro",
        )
        .unwrap();
        let result = ctx.elab_decl(&surface).unwrap();

        match result {
            ElabResult::Theorem { proof, .. } => {
                assert!(
                    proof.has_synthetic_sorry(),
                    "parser recovery should elaborate to synthetic sorry, got {proof:?}"
                );
                assert!(
                    !proof.has_non_synthetic_sorry(),
                    "parser recovery should not be misclassified as explicit sorry, got {proof:?}"
                );
            }
            other => panic!("expected Theorem, got: {other:?}"),
        }
    });
}

// =========================================================================
// elab_by_tactic sorry fallback (#1144, W1-1268)
// =========================================================================

/// Test that elab_by_tactic rejects unsolved goals (#2203).
///
/// When a `by` block doesn't close all goals, elab_by_tactic returns Err
/// instead of silently filling with sorry. Explicit sorry tactic (user intent)
/// still works — it closes the goal at eval time via close_goal.
#[test]
fn test_elab_by_tactic_rejects_unsolved_goals() {
    // Call elab_by_tactic directly with an empty tactic list.
    // No tactics → goal stays open → error returned (no sorry auto-fill).
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);
    ctx.set_expected_type(Some(Expr::prop()));

    let result = ctx.elab_by_tactic(&[]);

    assert!(
        result.is_err(),
        "elab_by_tactic with unsolved goals must return Err, got: {:?}",
        result.ok()
    );

    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("unsolved goal"),
        "error should mention unsolved goals, got: {}",
        err_msg
    );
}

/// Test that unsolved goals error includes the goal target type (#1801).
///
/// The error message should show the remaining goal types so users can see
/// what remains to be proved, matching Lean 4's "unsolved goals" display.
#[test]
fn test_elab_by_tactic_unsolved_goals_includes_target_type() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);
    ctx.set_expected_type(Some(Expr::prop()));

    let result = ctx.elab_by_tactic(&[]);
    assert!(result.is_err());

    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("unsolved goals"),
        "error should start with 'unsolved goals', got: {}",
        err_msg
    );
    // The target type (Prop = Sort(Zero)) should appear after ⊢
    assert!(
        err_msg.contains("⊢"),
        "error should include ⊢ marker for goal target, got: {}",
        err_msg
    );
}

/// Documents that `by skip` through elab_decl does NOT reach elab_by_tactic
/// due to macro round-trip bug: expand_macros converts ByTactic to an empty
/// `byTactic` syntax node, then syntax_to_surface converts that to
/// Ident("byTactic") — losing the tactic block entirely.
///
/// With the macro round-trip fix (#2211), ByTactic nodes are intercepted
/// before expand_macros, so elab_by_tactic is now reachable through elab_decl.
/// `by skip` leaves the goal unsolved and should fail.
#[test]
#[serial]
fn test_elab_by_tactic_via_elab_decl_rejects_unsolved_by_skip() {
    let result = elab_decl("theorem test_tactic_sorry : Prop := by skip");
    assert!(
        result.is_err(),
        "elab_decl with `by skip` should fail — elab_by_tactic rejects unsolved goals"
    );
}

// =========================================================================
// Sorry tracking tests (#1144)
// =========================================================================

use crate::tactic::{
    create_sorry_term, enable_sorry_location_tracking, reset_sorry_counter, reset_sorry_locations,
    sorry_count, sorry_locations,
};

#[test]
#[serial]
fn test_sorry_counter_tracking() {
    // Reset counter to isolate this test
    reset_sorry_counter();
    let before_first = sorry_count();

    let env = Environment::new();
    let goal_ty = Expr::prop();

    // Create sorry term - count should increase and term should be an App
    let sorry1 = create_sorry_term(&env, &goal_ty);
    assert!(
        matches!(sorry1.kind(), ExprKind::App(..)),
        "sorry term should be an App (sorry applied to goal type), got {:?}",
        sorry1.kind()
    );
    let count_after_1 = sorry_count();
    assert!(
        count_after_1 > before_first,
        "sorry counter should increment after create_sorry_term: before={}, after={}",
        before_first,
        count_after_1
    );

    // Create another sorry term
    let before_second = sorry_count();
    let sorry2 = create_sorry_term(&env, &goal_ty);
    assert!(
        matches!(sorry2.kind(), ExprKind::App(..)),
        "second sorry term should also be an App, got {:?}",
        sorry2.kind()
    );
    let count_after_2 = sorry_count();
    assert!(
        count_after_2 > before_second,
        "sorry counter should increment again: before={}, after={}",
        before_second,
        count_after_2
    );
}

#[test]
#[serial]
fn test_sorry_location_tracking() {
    // Enable location tracking and reset
    enable_sorry_location_tracking();
    reset_sorry_locations();

    // Create a sorry term to record a location
    let env = Environment::new();
    let goal_ty = Expr::prop();
    let sorry_term = create_sorry_term(&env, &goal_ty);
    assert!(
        matches!(sorry_term.kind(), ExprKind::App(..)),
        "sorry term should be an App, got {:?}",
        sorry_term.kind()
    );

    // Check that locations were recorded
    let locations = sorry_locations();
    assert!(
        locations.is_some(),
        "locations should be Some after enabling tracking"
    );

    let map = locations.unwrap();
    // We should have at least one location recorded
    assert!(
        !map.is_empty(),
        "should have at least one location recorded: {:?}",
        map
    );
}
