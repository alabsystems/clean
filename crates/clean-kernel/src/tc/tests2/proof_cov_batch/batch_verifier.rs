// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::fixtures::*;
use super::*;

// ===== BatchVerifier targeted coverage =====
// Complements the existing `tc/batch.rs` unit tests with env-backed expressions,
// reducible definitions, and exact inferred-type assertions.

/// Test stream_check: calls callback for each expression.
#[test]
fn test_batch_stream_check() {
    use crate::tc::batch::BatchVerifier;

    let env = fixture_env();
    let verifier = BatchVerifier::new(&env);
    // Use NotAFunction (App(t, t) where t : T, T is not Pi) as the invalid expr.
    // TypeMismatch exprs now pass infer_type (Lean 4 infer_only=true parity).
    let exprs = vec![
        invalid_not_a_function_expr(),
        valid_id_alias_expr(),
        valid_let_expr(),
    ];
    let mut seen = Vec::new();
    verifier.stream_check(exprs.into_iter(), |_expr, result| {
        seen.push((result.valid, result.inferred_type.clone()));
        true // continue
    });

    assert_eq!(
        seen,
        vec![
            (false, None),
            (true, Some(alias_prop_type())),
            (true, Some(Expr::type_())),
        ],
        "stream_check should report precise validity and inferred types"
    );
}

/// Test stream_check: early termination when callback returns false.
#[test]
fn test_batch_stream_check_early_termination() {
    use crate::tc::batch::BatchVerifier;

    let env = fixture_env();
    let verifier = BatchVerifier::new(&env);

    // Use NotAFunction as invalid (TypeMismatch passes infer_type with infer_only=true)
    let exprs = vec![
        invalid_not_a_function_expr(),
        valid_lambda_expr(),
        valid_ft_expr(),
    ];
    let mut seen = Vec::new();
    verifier.stream_check(exprs.into_iter(), |_expr, result| {
        seen.push(result.valid);
        false // stop after first
    });

    assert_eq!(
        seen,
        vec![false],
        "stream_check should stop after callback returns false"
    );
}

/// Test find_first_valid: returns first well-typed expression.
#[test]
fn test_batch_find_first_valid() {
    use crate::tc::batch::BatchVerifier;

    let env = fixture_env();
    let verifier = BatchVerifier::new(&env);

    // Use NotAFunction as invalid (TypeMismatch passes infer_type with infer_only=true)
    let valid1 = valid_lambda_expr();
    let valid2 = valid_id_alias_expr();
    let exprs = vec![invalid_not_a_function_expr(), valid1.clone(), valid2];
    let (found_expr, found_ty) = verifier
        .find_first_valid(exprs.into_iter())
        .expect("Should find a valid expression");
    assert_eq!(
        found_expr, valid1,
        "Should return the first expression that needs real lambda inference"
    );
    assert_eq!(
        found_ty,
        valid_lambda_type(),
        "The lambda should infer to Prop -> Prop"
    );
}

/// Test find_first_valid: returns None when all invalid.
#[test]
fn test_batch_find_first_valid_none() {
    use crate::tc::batch::BatchVerifier;

    let env = fixture_env();
    let verifier = BatchVerifier::new(&env);

    // All structurally invalid: NotAFunction errors (not affected by infer_only).
    // TypeMismatch exprs now pass infer_type (Lean 4 infer_only=true parity).
    let exprs = vec![
        invalid_not_a_function_expr(),
        Expr::app(Expr::prop(), Expr::prop()),
        Expr::bvar(0),
    ];
    let result = verifier.find_first_valid(exprs.into_iter());
    assert!(
        result.is_none(),
        "Should return None when all expressions are invalid"
    );
}

/// Test find_first_valid: handles inductive recursors, not just reducible aliases.
#[test]
fn test_batch_find_first_valid_nat_recursor() {
    use crate::tc::batch::BatchVerifier;

    let env = fixture_nat_env();
    let verifier = BatchVerifier::new(&env);
    let tc = TypeChecker::new(&env);

    // invalid_nat_rec_zero_case_expr now passes infer_type (infer_only=true skips
    // App arg check). Use NotAFunction (Prop applied as function) as the invalid expr.
    let nat_rec = valid_nat_rec_expr();
    let exprs = vec![
        Expr::app(Expr::prop(), Expr::prop()),
        Expr::bvar(0),
        nat_rec.clone(),
    ];
    let (found_expr, found_ty) = verifier
        .find_first_valid(exprs.into_iter())
        .expect("Should find the recursor application after invalid candidates");

    assert_eq!(
        found_expr, nat_rec,
        "Should return the first well-typed Nat.rec application, not just a trivial constant"
    );
    assert_eq!(
        found_ty,
        nat_rec_inferred_type(),
        "Nat.rec motive/case checking should preserve the exact substituted motive application"
    );
    assert_eq!(
        tc.whnf(&found_ty),
        nat_type(),
        "The inferred recursor result type should normalize to Nat"
    );
}

/// Test count_valid: counts well-typed expressions.
#[test]
fn test_batch_count_valid() {
    use crate::tc::batch::BatchVerifier;

    let env = fixture_env();
    let verifier = BatchVerifier::new(&env);

    // Use NotAFunction and BVar(0) as invalid (TypeMismatch passes infer_type now)
    let exprs = vec![
        invalid_not_a_function_expr(),
        valid_lambda_expr(),
        valid_id_alias_expr(),
        Expr::bvar(0),
        valid_ft_expr(),
    ];
    let count = verifier.count_valid(&exprs);
    assert_eq!(
        count, 3,
        "Should count all nontrivial well-typed expressions"
    );
}

/// Test valid_indices: returns sorted indices of well-typed expressions.
#[test]
fn test_batch_valid_indices() {
    use crate::tc::batch::BatchVerifier;

    let env = fixture_env();
    let verifier = BatchVerifier::new(&env);

    // Use NotAFunction and BVar(0) as invalid (TypeMismatch passes infer_type now)
    let exprs = vec![
        invalid_not_a_function_expr(),
        valid_lambda_expr(),
        Expr::bvar(0),
        valid_id_alias_expr(),
        valid_ft_expr(),
    ];
    let indices = verifier.valid_indices(&exprs);
    assert_eq!(
        indices,
        vec![1, 3, 4],
        "Valid indices should point at the lambda, reducible alias app, and env-backed app"
    );
}

/// Test find_first_valid_parallel: finds a valid expression.
#[test]
fn test_batch_find_first_valid_parallel() {
    use crate::tc::batch::BatchVerifier;

    let env = fixture_env();
    let verifier = BatchVerifier::new(&env);

    // Use structurally invalid exprs (NotAFunction, unbound BVar)
    let exprs = vec![
        Expr::app(Expr::prop(), Expr::prop()),
        invalid_not_a_function_expr(),
        valid_id_alias_expr(),
        valid_ft_expr(),
    ];
    let result = verifier.find_first_valid_parallel(&exprs);
    assert!(
        result.is_some(),
        "Should find a valid expression in parallel"
    );
    let (found_expr, found_ty) =
        result.expect("find_first_valid_parallel should return a valid expression");
    if found_expr == valid_id_alias_expr() {
        assert_eq!(
            found_ty,
            alias_prop_type(),
            "id_alias p should infer AliasProp"
        );
    } else {
        assert_eq!(
            found_expr,
            valid_ft_expr(),
            "parallel search should return one of the known valid expressions"
        );
        assert_eq!(found_ty, u_type(), "f t should infer U");
    }
}

/// Test find_first_valid_parallel: returns None when all candidates fail type checking.
#[test]
fn test_batch_find_first_valid_parallel_none() {
    use crate::tc::batch::BatchVerifier;

    let env = fixture_env();
    let verifier = BatchVerifier::new(&env);

    // All structurally invalid: NotAFunction and unbound BVar.
    // TypeMismatch and App-arg-mismatch exprs now pass infer_type
    // (infer_only=true). `Lam(BVar(0), BVar(0))` also passes the fast
    // path because the kernel only flags the unbound domain when
    // forced to check it.
    let exprs = vec![
        invalid_not_a_function_expr(),
        Expr::app(Expr::prop(), Expr::prop()),
        Expr::bvar(0),
    ];
    assert!(
        verifier.find_first_valid_parallel(&exprs).is_none(),
        "parallel search should return None when every expression is structurally invalid"
    );
}

// ===== stream_valid tests =====

/// Test stream_valid: only yields valid expressions with their types.
#[test]
fn test_batch_stream_valid() {
    use crate::tc::batch::BatchVerifier;

    let env = fixture_env();
    let verifier = BatchVerifier::new(&env);

    // Use NotAFunction as invalid (TypeMismatch passes infer_type with infer_only=true)
    let exprs = vec![
        invalid_not_a_function_expr(),
        valid_lambda_expr(),
        Expr::app(Expr::prop(), Expr::prop()),
        valid_id_alias_expr(),
    ];
    let mut valid_exprs = Vec::new();
    verifier.stream_valid(exprs.into_iter(), |expr, ty| {
        valid_exprs.push((expr.clone(), ty.clone()));
        true // continue
    });

    assert_eq!(
        valid_exprs,
        vec![
            (valid_lambda_expr(), valid_lambda_type()),
            (valid_id_alias_expr(), alias_prop_type()),
        ],
        "stream_valid should yield the exact valid expression/type pairs in order"
    );
}

/// Test stream_valid: early termination after first valid.
#[test]
fn test_batch_stream_valid_early_stop() {
    use crate::tc::batch::BatchVerifier;

    let env = fixture_env();
    let verifier = BatchVerifier::new(&env);

    // Use NotAFunction as invalid (TypeMismatch passes infer_type with infer_only=true)
    let exprs = vec![
        invalid_not_a_function_expr(),
        valid_id_alias_expr(),
        valid_lambda_expr(),
    ];
    let mut seen = Vec::new();
    verifier.stream_valid(exprs.into_iter(), |expr, ty| {
        seen.push((expr.clone(), ty.clone()));
        false // stop after first valid
    });

    assert_eq!(
        seen,
        vec![(valid_id_alias_expr(), alias_prop_type())],
        "stream_valid should stop after callback returns false"
    );
}
