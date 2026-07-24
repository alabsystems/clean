// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

// ===== VerificationArena core API tests =====
// Tests for push, verify_all, get_result, get_expr, get_type, is_valid, clear.

/// Test VerificationArena: basic push/verify/get workflow.
#[test]
fn test_verification_arena_basic() {
    use crate::tc::batch::{BatchVerifier, VerificationArena};

    let env = fixture_env();
    let verifier = BatchVerifier::new(&env);

    let mut arena = VerificationArena::new();
    assert!(arena.is_empty());
    assert_eq!(arena.len(), 0);

    // Use NotAFunction as invalid (TypeMismatch passes infer_type with infer_only=true)
    let idx0 = arena.push(valid_lambda_expr());
    let idx1 = arena.push(invalid_not_a_function_expr());
    let idx2 = arena.push(valid_id_alias_expr());

    assert_eq!(arena.len(), 3);
    assert!(!arena.is_empty());
    assert_eq!(idx0, 0);
    assert_eq!(idx1, 1);
    assert_eq!(idx2, 2);

    // Before verify_all, results should be None
    assert!(
        arena.get_result(0).is_none(),
        "result should be None before verify_all"
    );

    arena.verify_all(&verifier);

    // After verify_all, all slots should have results with expected types
    assert_valid_result(
        &arena,
        0,
        &valid_lambda_type(),
        "lambda slot should retain the exact inferred Pi type",
    );
    assert_invalid_result(
        &arena,
        1,
        "not-a-function application should fail type-check",
    );
    assert_valid_result(
        &arena,
        2,
        &alias_prop_type(),
        "id_alias p should infer the alias codomain, not merely Some(_)",
    );

    // Check validity (consistency with get_result)
    assert!(arena.is_valid(0), "lambda should be valid");
    assert!(
        !arena.is_valid(1),
        "not-a-function application should be invalid"
    );
    assert!(
        arena.is_valid(2),
        "alias-backed application should be valid"
    );
}

/// Test VerificationArena: push_many adds consecutive entries.
#[test]
fn test_verification_arena_push_many() {
    use crate::tc::batch::{BatchVerifier, VerificationArena};

    let env = fixture_env();
    let verifier = BatchVerifier::new(&env);

    let mut arena = VerificationArena::with_capacity(10);
    arena.push(valid_ft_expr()); // idx 0
                                 // Use NotAFunction as invalid (TypeMismatch passes infer_type with infer_only=true)
    let first = arena.push_many(vec![valid_id_alias_expr(), invalid_not_a_function_expr()]);
    assert_eq!(first, 1, "push_many should return first index");
    assert_eq!(arena.len(), 3);

    arena.verify_all(&verifier);
    assert!(arena.is_valid(0));
    assert!(arena.is_valid(1));
    assert!(!arena.is_valid(2));
    assert_eq!(arena.get_type(0), Some(&u_type()));
    assert_eq!(arena.get_type(1), Some(&alias_prop_type()));
}

/// Test VerificationArena: clear resets the arena.
#[test]
fn test_verification_arena_clear() {
    use crate::tc::batch::{BatchVerifier, VerificationArena};

    let env = fixture_env();
    let verifier = BatchVerifier::new(&env);

    let mut arena = VerificationArena::new();
    arena.push(valid_ft_expr());
    arena.verify_all(&verifier);
    assert!(!arena.is_empty());

    arena.clear();
    assert!(arena.is_empty());
    assert_eq!(arena.len(), 0);
    assert!(
        arena.get_result(0).is_none(),
        "clear should drop old verification results"
    );

    arena.push(invalid_not_a_function_expr());
    arena.push(valid_id_alias_expr());
    arena.verify_all(&verifier);
    assert_eq!(arena.len(), 2, "arena should be reusable after clear");
    assert!(
        !arena.is_valid(0),
        "reused slot 0 should reflect new invalid expr"
    );
    assert_eq!(
        arena.get_type(1),
        Some(&alias_prop_type()),
        "reused slot 1 should infer the alias type on the second verify_all"
    );
}

/// Test VerificationArena: get_expr returns correct expression.
#[test]
fn test_verification_arena_get_expr() {
    use crate::tc::batch::VerificationArena;

    let mut arena = VerificationArena::new();
    let lambda = valid_lambda_expr();
    let alias_app = valid_id_alias_expr();
    arena.push(lambda.clone());
    arena.push(alias_app.clone());

    assert_eq!(arena.get_expr(0), Some(&lambda));
    assert_eq!(arena.get_expr(1), Some(&alias_app));
    assert_eq!(arena.get_expr(2), None, "Out of bounds should return None");
}

/// Test VerificationArena: get_type returns inferred type for valid slots.
#[test]
fn test_verification_arena_get_type() {
    use crate::tc::batch::{BatchVerifier, VerificationArena};

    let env = fixture_env();
    let verifier = BatchVerifier::new(&env);
    let expected_lambda_ty = valid_lambda_type();

    let mut arena = VerificationArena::new();
    // Use NotAFunction as invalid (TypeMismatch passes infer_type with infer_only=true)
    arena.push(valid_lambda_expr());
    arena.push(invalid_not_a_function_expr());

    arena.verify_all(&verifier);

    assert_eq!(
        arena.get_type(0),
        Some(&expected_lambda_ty),
        "get_type should return the exact inferred Pi type for the lambda slot"
    );
    assert!(
        arena.get_type(1).is_none(),
        "Invalid expression should return None for get_type"
    );
}
