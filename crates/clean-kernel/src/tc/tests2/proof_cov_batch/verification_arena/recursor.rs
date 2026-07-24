// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

// ===== VerificationArena recursor-specific tests =====
// Uses fixture_nat_env() and Nat.rec expressions.

/// Test VerificationArena: exact inferred type survives Nat.rec verification.
#[test]
fn test_verification_arena_nat_recursor_exact_type() {
    use crate::tc::batch::{BatchVerifier, VerificationArena};

    let env = fixture_nat_env();
    let verifier = BatchVerifier::new(&env);
    let tc = TypeChecker::new(&env);
    let expected_recursor_ty = nat_rec_inferred_type();

    // invalid_nat_rec_zero_case_expr now passes infer_type (infer_only=true skips
    // App arg check). Use NotAFunction (Prop applied as function) as invalid.
    let mut arena = VerificationArena::new();
    let valid_idx = arena.push(valid_nat_rec_expr());
    let invalid_idx = arena.push(Expr::app(Expr::prop(), Expr::prop()));

    arena.verify_all(&verifier);

    assert_valid_result(
        &arena,
        valid_idx,
        &expected_recursor_ty,
        "Nat.rec slot should preserve the exact substituted motive application",
    );
    assert_invalid_result(
        &arena,
        invalid_idx,
        "not-a-function application should remain invalid",
    );
    assert_eq!(
        arena.get_type(valid_idx),
        Some(&expected_recursor_ty),
        "get_type should expose the exact raw inferred type for a verified recursor application"
    );
    assert_eq!(
        tc.whnf(
            arena
                .get_type(valid_idx)
                .expect("valid recursor slot should have an inferred type"),
        ),
        nat_type(),
        "The recursor slot type should normalize to Nat"
    );
}
