// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::instances::extract_class_app;
use crate::unify::MetaState;
use clean_kernel::{Environment, Expr, ExprKind, Level};

#[test]
fn test_meta_ctx_new() {
    let env = Environment::new();
    let ctx = MetaCtx::new(&env);
    assert_eq!(ctx.transparency(), TransparencyMode::Default);
}

#[test]
fn test_is_def_eq_identical() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);

    let e = Expr::sort(Level::zero());
    assert!(ctx.is_def_eq(&e, &e));
}

#[test]
fn test_is_def_eq_different() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);

    let e1 = Expr::sort(Level::zero());
    let e2 = Expr::sort(Level::succ(Level::zero()));
    assert!(!ctx.is_def_eq(&e1, &e2));
}

#[test]
fn test_is_def_eq_with_meta() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);

    // Create a metavariable
    let meta = ctx.fresh_meta(Expr::sort(Level::zero()));
    let concrete = Expr::prop();

    // Should unify
    assert!(ctx.is_def_eq(&meta, &concrete));

    // After unification, meta should be assigned
    let instantiated = ctx.instantiate_mvars(&meta);
    assert_eq!(instantiated, concrete);
}

#[test]
fn test_is_def_eq_pure_no_side_effects() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);

    let meta = ctx.fresh_meta(Expr::sort(Level::zero()));
    let concrete = Expr::prop();

    // Pure check should succeed but not modify state
    assert!(ctx.is_def_eq_pure(&meta, &concrete));

    // Meta should still be unassigned
    let instantiated = ctx.instantiate_mvars(&meta);
    assert_eq!(instantiated, meta); // Still the metavariable
}

#[test]
fn test_with_reducible() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);

    assert_eq!(ctx.transparency(), TransparencyMode::Default);

    ctx.with_reducible(|inner| {
        assert_eq!(inner.transparency(), TransparencyMode::Reducible);
    });

    assert_eq!(ctx.transparency(), TransparencyMode::Default);
}

#[test]
fn test_with_new_mctx_depth_rollback() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);

    let meta = ctx.fresh_meta(Expr::sort(Level::zero()));

    ctx.with_new_mctx_depth(|inner| {
        // Assign the meta inside the depth
        inner.is_def_eq(&meta, &Expr::prop());
        // Check it's assigned
        assert_eq!(inner.instantiate_mvars(&meta), Expr::prop());
    });

    // Outside, the assignment should be rolled back
    assert_eq!(ctx.instantiate_mvars(&meta), meta);
}

#[test]
fn test_runtime_match_success() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);

    // Create pattern: ?x where ?x is a metavariable
    let meta_ty = Expr::sort(Level::zero());
    let meta = ctx.fresh_meta(meta_ty);
    let pattern_vars = if let ExprKind::FVar(fvar_id) = meta.kind() {
        vec![("x".to_string(), *fvar_id)]
    } else {
        panic!("expected FVar");
    };

    // Scrutinee
    let scrutinee = Expr::prop();

    let result = try_runtime_match(&mut ctx, &scrutinee, &meta, &pattern_vars);

    assert!(result.matched);
    assert_eq!(result.bindings.len(), 1);
    assert_eq!(result.bindings[0].0, "x");
    assert_eq!(result.bindings[0].1, Expr::prop());
}

#[test]
fn test_runtime_match_failure() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);

    // Pattern: Sort 0
    let pattern = Expr::sort(Level::zero());

    // Scrutinee: Sort 1 (different)
    let scrutinee = Expr::sort(Level::succ(Level::zero()));

    let result = try_runtime_match(&mut ctx, &scrutinee, &pattern, &[]);

    assert!(!result.matched);
    assert!(result.bindings.is_empty());
}

// ════════════════════════════════════════════════════════════════════════
// Runtime Interpreter Tests
// ════════════════════════════════════════════════════════════════════════

#[test]
fn test_interpreter_new() {
    let env = Environment::new();
    let interp = RuntimeInterpreter::new(&env);
    assert!(interp.bindings().is_empty());
}

#[test]
fn test_interpret_passthrough() {
    let env = Environment::new();
    let mut interp = RuntimeInterpreter::new(&env);

    // Simple expressions (sorts, constants) are values
    let e = Expr::sort(Level::zero());
    match interp.interpret(&e) {
        RuntimeInterpretResult::Value(result) => {
            assert_eq!(result, e);
        }
        _ => panic!("Expected Value"),
    }

    // FVars pass through as NotInterpreted
    let fvar = Expr::fvar(clean_kernel::FVarId::new(42));
    match interp.interpret(&fvar) {
        RuntimeInterpretResult::NotInterpreted(result) => {
            assert_eq!(result, fvar);
        }
        _ => panic!("Expected NotInterpreted for FVar"),
    }
}

#[test]
fn test_interpret_qq_runtime_check_match() {
    use clean_kernel::{MDataValue, Name};

    let env = Environment::new();
    let mut interp = RuntimeInterpreter::new(&env);

    // Create a simple check: isDefEq(Prop, Prop) should succeed
    let scrutinee = Expr::prop();
    let pattern = Expr::prop();

    // Build: Prod.mk scrutinee pattern
    let pair = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Prod.mk"), vec![]),
            scrutinee,
        ),
        pattern,
    );

    // Tag with qq_runtime_check
    let metadata = vec![(
        Name::from_string("qq_runtime_check"),
        MDataValue::Bool(true),
    )];
    let check_expr = Expr::mdata(metadata, pair);

    match interp.interpret(&check_expr) {
        RuntimeInterpretResult::Value(result) => {
            if let ExprKind::Const(name, _) = result.kind() {
                assert_eq!(*name, Name::from_string("Bool.true"));
            } else {
                panic!("Expected Bool.true constant");
            }
        }
        _ => panic!("Expected Value result"),
    }
}

#[test]
fn test_interpret_qq_runtime_check_no_match() {
    use clean_kernel::{MDataValue, Name};

    let env = Environment::new();
    let mut interp = RuntimeInterpreter::new(&env);

    // Create a check: isDefEq(Sort 0, Sort 1) should fail
    let scrutinee = Expr::sort(Level::zero());
    let pattern = Expr::sort(Level::succ(Level::zero()));

    // Build: Prod.mk scrutinee pattern
    let pair = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Prod.mk"), vec![]),
            scrutinee,
        ),
        pattern,
    );

    // Tag with qq_runtime_check
    let metadata = vec![(
        Name::from_string("qq_runtime_check"),
        MDataValue::Bool(true),
    )];
    let check_expr = Expr::mdata(metadata, pair);

    match interp.interpret(&check_expr) {
        RuntimeInterpretResult::Value(result) => {
            if let ExprKind::Const(name, _) = result.kind() {
                assert_eq!(*name, Name::from_string("Bool.false"));
            } else {
                panic!("Expected Bool.false constant");
            }
        }
        _ => panic!("Expected Value result"),
    }
}

#[test]
fn test_interpret_qq_match_failure() {
    use clean_kernel::{MDataValue, Name};

    let env = Environment::new();
    let mut interp = RuntimeInterpreter::new(&env);

    // Create match failure marker
    let metadata = vec![(
        Name::from_string("qq_match_failure"),
        MDataValue::Bool(true),
    )];
    let failure_expr = Expr::mdata(
        metadata,
        Expr::const_(Name::from_string("Lean.Expr.panic"), vec![]),
    );

    match interp.interpret(&failure_expr) {
        RuntimeInterpretResult::MatchFailure => {
            // Expected
        }
        _ => panic!("Expected MatchFailure result"),
    }
}

#[test]
fn test_interpret_ite_true_branch() {
    use clean_kernel::Name;

    let env = Environment::new();
    let mut interp = RuntimeInterpreter::new(&env);

    // Build: ite Bool.true "then" "else"
    let cond = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let then_branch = Expr::sort(Level::zero());
    let else_branch = Expr::sort(Level::succ(Level::zero()));

    let ite_expr = Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("ite"), vec![]), cond),
            then_branch.clone(),
        ),
        else_branch,
    );

    match interp.interpret(&ite_expr) {
        RuntimeInterpretResult::Value(result) => {
            assert_eq!(result, then_branch);
        }
        _ => panic!("Expected Value with then_branch"),
    }
}

#[test]
fn test_interpret_ite_false_branch() {
    use clean_kernel::Name;

    let env = Environment::new();
    let mut interp = RuntimeInterpreter::new(&env);

    // Build: ite Bool.false "then" "else"
    let cond = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let then_branch = Expr::sort(Level::zero());
    let else_branch = Expr::sort(Level::succ(Level::zero()));

    let ite_expr = Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("ite"), vec![]), cond),
            then_branch,
        ),
        else_branch.clone(),
    );

    match interp.interpret(&ite_expr) {
        RuntimeInterpretResult::Value(result) => {
            assert_eq!(result, else_branch);
        }
        _ => panic!("Expected Value with else_branch"),
    }
}

#[test]
fn test_interpret_runtime_match_public_api() {
    use clean_kernel::{MDataValue, Name};

    let env = Environment::new();

    // Create a simple matching check
    let scrutinee = Expr::prop();
    let pattern = Expr::prop();

    let pair = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Prod.mk"), vec![]),
            scrutinee,
        ),
        pattern,
    );

    let metadata = vec![(
        Name::from_string("qq_runtime_check"),
        MDataValue::Bool(true),
    )];
    let check_expr = Expr::mdata(metadata, pair);

    // Use public API
    let result = interpret_runtime_match(&env, &check_expr);

    match result {
        RuntimeInterpretResult::Value(v) => {
            if let ExprKind::Const(name, _) = v.kind() {
                assert_eq!(*name, Name::from_string("Bool.true"));
            } else {
                panic!("Expected Bool.true");
            }
        }
        _ => panic!("Expected Value"),
    }
}

#[test]
fn test_interpret_substitute_bvar() {
    let env = Environment::new();
    let interp = RuntimeInterpreter::new(&env);

    // Test substitution: substitute Prop for BVar(0) in BVar(0)
    let body = Expr::bvar(0);
    let replacement = Expr::prop();
    let result = interp.substitute_bvar(&body, 0, &replacement);
    assert_eq!(result, Expr::prop());

    // Test: BVar(1) should not be replaced when substituting for depth 0
    let body2 = Expr::bvar(1);
    let result2 = interp.substitute_bvar(&body2, 0, &replacement);
    assert_eq!(result2, Expr::bvar(1));
}

// ════════════════════════════════════════════════════════════════════════
// Phase 5: Mathlib Metaprogramming Tests
// ════════════════════════════════════════════════════════════════════════

#[test]
fn test_mk_fresh_expr_mvar_q_creates_metavar() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);

    // Create a fresh metavariable with type Nat
    let nat_type = Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]);
    let result = ctx.mk_fresh_expr_mvar_q(nat_type.clone());

    // Should get back a metavariable (FVar with meta tag)
    assert!(matches!(result.mvar.kind(), ExprKind::FVar(_)));

    // The quoted type should be what we passed in
    assert_eq!(result.quoted_type, nat_type);
}

#[test]
fn test_mk_fresh_expr_mvar_q_unique_ids() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);

    let ty = Expr::const_(clean_kernel::Name::from_string("Bool"), vec![]);

    // Create multiple metavariables
    let mvar1 = ctx.mk_fresh_expr_mvar_q(ty.clone());
    let mvar2 = ctx.mk_fresh_expr_mvar_q(ty.clone());
    let mvar3 = ctx.mk_fresh_expr_mvar_q(ty.clone());

    // Each should be different
    assert_ne!(mvar1.mvar, mvar2.mvar);
    assert_ne!(mvar2.mvar, mvar3.mvar);
    assert_ne!(mvar1.mvar, mvar3.mvar);
}

#[test]
fn test_assign_mvar_q_success() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);

    // Create a metavariable
    let ty = Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]);
    let mvar_result = ctx.mk_fresh_expr_mvar_q(ty);

    // Assign a value
    let value = Expr::nat_lit(42);
    let success = ctx.assign_mvar_q(&mvar_result.mvar, value.clone());
    assert!(success);

    // Check it was assigned by instantiating
    let instantiated = ctx.instantiate_mvars(&mvar_result.mvar);
    assert_eq!(instantiated, value);
}

#[test]
fn test_assign_mvar_q_non_metavar_fails() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);

    // Try to assign to a non-metavariable
    let non_mvar = Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]);
    let value = Expr::nat_lit(42);

    let success = ctx.assign_mvar_q(&non_mvar, value);
    assert!(!success);
}

#[test]
fn test_synth_instance_q_not_found_for_empty_env() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);

    // Try to synthesize Add Nat in an empty environment
    let add_nat = Expr::app(
        Expr::const_(clean_kernel::Name::from_string("Add"), vec![]),
        Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]),
    );

    let result = ctx.synth_instance_q(&add_nat);
    // Should return NotFound since no instances are registered
    assert!(matches!(result, SynthInstanceQResult::NotFound));
}

#[test]
fn test_synth_instance_q_stuck_on_metas() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);

    // Create a type class goal with an unresolved metavariable
    // Add ?α where ?α is a fresh metavar
    let meta_ty = Expr::type_();
    let meta = ctx.fresh_meta(meta_ty);
    let add_meta = Expr::app(
        Expr::const_(clean_kernel::Name::from_string("Add"), vec![]),
        meta,
    );

    let result = ctx.synth_instance_q(&add_meta);
    // Should return Stuck since there's an unresolved metavariable
    assert!(matches!(result, SynthInstanceQResult::Stuck));
}

#[test]
fn test_goal_has_unresolved_metas_simple() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);

    // A constant has no metavariables
    let nat = Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]);
    assert!(!ctx.goal_has_unresolved_metas(&nat));

    // A fresh metavariable has an unresolved meta
    let meta = ctx.fresh_meta(Expr::type_());
    assert!(ctx.goal_has_unresolved_metas(&meta));
}

#[test]
fn test_goal_has_unresolved_metas_after_assignment() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);

    // Create and assign a metavariable
    let meta = ctx.fresh_meta(Expr::type_());

    // Before assignment, has unresolved meta
    assert!(ctx.goal_has_unresolved_metas(&meta));

    // Assign it
    let nat = Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]);
    if let ExprKind::FVar(fvar) = meta.kind() {
        if let Some(meta_id) = MetaState::from_fvar(*fvar) {
            ctx.metas_mut().assign(meta_id, nat.clone());
        }
    }

    // After assignment, the meta expression itself still points to the meta ID
    // but when we instantiate, we get the assigned value
    let instantiated = ctx.instantiate_mvars(&meta);
    assert!(!ctx.goal_has_unresolved_metas(&instantiated));
}

#[test]
fn test_mk_fresh_expr_mvar_q_with_name() {
    let env = Environment::new();
    let mut ctx = MetaCtx::new(&env);

    let ty = Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]);
    let result = ctx.mk_fresh_expr_mvar_q_with_name(ty.clone(), Some("my_goal"));

    // Should create a metavariable just like the unnamed version
    assert!(matches!(result.mvar.kind(), ExprKind::FVar(_)));
    assert_eq!(result.quoted_type, ty);
}

#[test]
fn test_extract_class_app_simple() {
    // Test extracting class name from simple application
    let add_nat = Expr::app(
        Expr::const_(clean_kernel::Name::from_string("Add"), vec![]),
        Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]),
    );

    let result = extract_class_app(&add_nat);
    let (name, args) = result.expect("extract_class_app should find Add Nat");
    assert_eq!(name, clean_kernel::Name::from_string("Add"));
    assert_eq!(args.len(), 1);
}

#[test]
fn test_extract_class_app_multiple_args() {
    // Test extracting from HAdd α β γ
    let hadd = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(clean_kernel::Name::from_string("HAdd"), vec![]),
                Expr::const_(clean_kernel::Name::from_string("Nat"), vec![]),
            ),
            Expr::const_(clean_kernel::Name::from_string("Int"), vec![]),
        ),
        Expr::const_(clean_kernel::Name::from_string("Int"), vec![]),
    );

    let result = extract_class_app(&hadd);
    let (name, args) = result.expect("extract_class_app should find HAdd Nat Int Int");
    assert_eq!(name, clean_kernel::Name::from_string("HAdd"));
    assert_eq!(args.len(), 3);
}

#[test]
fn test_extract_class_app_not_const_head() {
    // Test that non-const heads return None
    let app_with_bvar = Expr::app(Expr::bvar(0), Expr::nat_lit(1));

    let result = extract_class_app(&app_with_bvar);
    assert!(result.is_none(), "BVar head should not be a class app");
}

#[test]
fn test_interpret_qq_runtime_check_with_binding_extraction() {
    use clean_kernel::{MDataValue, Name};

    let env = Environment::new();
    let mut interp = RuntimeInterpreter::new(&env);

    // Create a fresh metavariable (simulating a pattern variable placeholder)
    let mvar_ty = Expr::sort(Level::zero()); // Type is Type
    let meta_id = interp.meta_ctx_mut().metas_mut().fresh(mvar_ty);
    let fvar_id = MetaState::to_fvar(meta_id);
    let mvar_fvar = Expr::fvar(fvar_id);

    // The scrutinee we want to match against: Prop
    let scrutinee = Expr::prop();

    // The pattern contains the metavariable (which will unify with Prop)
    let pattern = mvar_fvar.clone();

    // Build: Prod.mk scrutinee pattern
    let pair = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Prod.mk"), vec![]),
            scrutinee.clone(),
        ),
        pattern,
    );

    // Build metadata with:
    // 1. qq_runtime_check = true
    // 2. qq_binding_x = fvar_id (binding for variable "x")
    let metadata = vec![
        (
            Name::from_string("qq_runtime_check"),
            MDataValue::Bool(true),
        ),
        (
            Name::from_string("qq_binding_x"),
            MDataValue::Nat(fvar_id.as_u64()),
        ),
    ];
    let check_expr = Expr::mdata(metadata, pair);

    // Run the interpretation - this should:
    // 1. Call isDefEq(scrutinee, pattern) - succeeds, assigns mvar to Prop
    // 2. Extract bindings from metadata using qq_binding_x
    // 3. Store binding "x" -> Prop
    let result = interp.interpret(&check_expr);

    // Verify match succeeded
    match result {
        RuntimeInterpretResult::Value(result) => {
            if let ExprKind::Const(name, _) = result.kind() {
                assert_eq!(*name, Name::from_string("Bool.true"));
            } else {
                panic!("Expected Bool.true constant");
            }
        }
        _ => panic!("Expected Value result"),
    }

    // Verify binding was extracted with correct name
    let bindings = interp.bindings();
    assert!(
        bindings.contains_key("x"),
        "Binding 'x' should be present. Got bindings: {:?}",
        bindings.keys().collect::<Vec<_>>()
    );

    // Verify the binding value is Prop
    let bound_value = bindings.get("x").unwrap();
    assert_eq!(
        *bound_value, scrutinee,
        "Binding 'x' should be Prop, got {:?}",
        bound_value
    );
}

/// Build a runtime check expression with two pattern variable bindings.
/// Returns (check_expr, fvar_a_id, fvar_b_id).
fn build_two_binding_check(interp: &mut RuntimeInterpreter<'_>) -> Expr {
    use clean_kernel::{MDataValue, Name};

    let ty = Expr::sort(Level::zero());
    let meta_a_id = interp.meta_ctx_mut().metas_mut().fresh(ty.clone());
    let meta_b_id = interp.meta_ctx_mut().metas_mut().fresh(ty);
    let fvar_a_id = MetaState::to_fvar(meta_a_id);
    let fvar_b_id = MetaState::to_fvar(meta_b_id);

    // Scrutinee: (Prop, Type 0), Pattern: (mvar_a, mvar_b)
    let scrutinee = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Prod.mk"), vec![]),
            Expr::prop(),
        ),
        Expr::sort(Level::succ(Level::zero())),
    );
    let pattern = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Prod.mk"), vec![]),
            Expr::fvar(fvar_a_id),
        ),
        Expr::fvar(fvar_b_id),
    );

    let pair = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Prod.mk"), vec![]),
            scrutinee,
        ),
        pattern,
    );
    let metadata = vec![
        (
            Name::from_string("qq_runtime_check"),
            MDataValue::Bool(true),
        ),
        (
            Name::from_string("qq_binding_a"),
            MDataValue::Nat(fvar_a_id.as_u64()),
        ),
        (
            Name::from_string("qq_binding_b"),
            MDataValue::Nat(fvar_b_id.as_u64()),
        ),
    ];
    Expr::mdata(metadata, pair)
}

#[test]
fn test_interpret_qq_runtime_check_multiple_bindings() {
    use clean_kernel::Name;

    let env = Environment::new();
    let mut interp = RuntimeInterpreter::new(&env);
    let check_expr = build_two_binding_check(&mut interp);

    let result = interp.interpret(&check_expr);

    // Verify match succeeded
    match result {
        RuntimeInterpretResult::Value(v) => {
            if let ExprKind::Const(name, _) = v.kind() {
                assert_eq!(*name, Name::from_string("Bool.true"));
            } else {
                panic!("Expected Bool.true constant");
            }
        }
        _ => panic!("Expected Value result"),
    }

    // Verify both bindings were extracted with correct values
    let bindings = interp.bindings();
    assert!(bindings.contains_key("a"), "Binding 'a' should be present");
    assert!(bindings.contains_key("b"), "Binding 'b' should be present");
    assert_eq!(*bindings.get("a").unwrap(), Expr::prop());
    assert_eq!(
        *bindings.get("b").unwrap(),
        Expr::sort(Level::succ(Level::zero()))
    );
}

#[test]
fn test_interpret_qq_runtime_binding_not_found() {
    use clean_kernel::{MDataValue, Name};

    let env = Environment::new();
    let mut interp = RuntimeInterpreter::new(&env);

    // Create a qq_runtime_binding for a variable that was never bound
    // This tests the error path in eval_runtime_binding
    let metadata = vec![(
        Name::from_string("qq_runtime_binding"),
        MDataValue::String(std::sync::Arc::from("nonexistent_var")),
    )];
    let binding_expr = Expr::mdata(
        metadata,
        Expr::const_(Name::from_string("Lean.Expr.hole"), vec![]),
    );

    // The binding "nonexistent_var" was never populated, so we expect NotInterpreted
    let result = interp.interpret(&binding_expr);

    match result {
        RuntimeInterpretResult::NotInterpreted(e) => {
            // Should return a hole expression
            if let ExprKind::Const(name, _) = e.kind() {
                assert_eq!(
                    *name,
                    Name::from_string("Lean.Expr.hole"),
                    "Should return hole for missing binding"
                );
            } else {
                panic!("Expected Lean.Expr.hole constant for missing binding");
            }
        }
        RuntimeInterpretResult::Value(_) => {
            panic!("Should not return Value for missing binding");
        }
        RuntimeInterpretResult::MatchFailure => {
            panic!("Should not return MatchFailure for missing binding");
        }
    }
}
