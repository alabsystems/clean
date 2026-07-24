// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

// ===== VerificationArena query/aggregate tests =====
// Tests for valid_pairs, valid_indices, stats.

/// Test VerificationArena: valid_pairs yields only well-typed expressions.
#[test]
fn test_verification_arena_valid_pairs() {
    use crate::tc::batch::{BatchVerifier, VerificationArena};

    let env = fixture_env();
    let verifier = BatchVerifier::new(&env);

    let mut arena = VerificationArena::new();
    arena.push(invalid_not_a_function_expr());
    arena.push(valid_lambda_expr());
    arena.push(valid_id_alias_expr());

    arena.verify_all(&verifier);

    let pairs: Vec<_> = arena
        .valid_pairs()
        .map(|(expr, ty)| (expr.clone(), ty.clone()))
        .collect();
    assert_eq!(
        pairs,
        vec![
            (valid_lambda_expr(), valid_lambda_type()),
            (valid_id_alias_expr(), alias_prop_type()),
        ],
        "valid_pairs should preserve the exact verified expression/type pairs"
    );
}

/// Test VerificationArena: valid_indices returns sorted indices.
#[test]
fn test_verification_arena_valid_indices() {
    use crate::tc::batch::{BatchVerifier, VerificationArena};

    let env = fixture_env();
    let verifier = BatchVerifier::new(&env);

    let mut arena = VerificationArena::new();
    // Use NotAFunction and BVar as invalid (TypeMismatch passes infer_type with infer_only=true)
    arena.push(invalid_not_a_function_expr());
    arena.push(valid_lambda_expr());
    arena.push(Expr::bvar(0));
    arena.push(valid_id_alias_expr());
    arena.push(valid_ft_expr());

    arena.verify_all(&verifier);

    let indices = arena.valid_indices();
    assert_eq!(indices, vec![1, 3, 4], "Valid indices should be [1, 3, 4]");
}

/// Test VerificationArena: stats after verification.
#[test]
fn test_verification_arena_stats() {
    use crate::tc::batch::{BatchVerifier, VerificationArena};

    let env = fixture_env();
    let verifier = BatchVerifier::new(&env);

    let mut arena = VerificationArena::new();
    arena.push(valid_lambda_expr());
    arena.push(invalid_not_a_function_expr());
    arena.push(valid_id_alias_expr());

    arena.verify_all(&verifier);

    let stats = arena.stats();
    assert_eq!(stats.total, 3, "Total should be 3");
    assert_eq!(stats.valid, 2, "Valid should be 2");
    assert_eq!(stats.invalid, 1, "Invalid should be 1");
    assert!(stats.wall_time_ns > 0, "Wall time should be positive");
}
