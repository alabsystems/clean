// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Performance proof tests for stack_safe overflow prevention.
//!
//! These tests verify that stacker::maybe_grow (via stack_safe) prevents
//! stack overflow on deeply nested expressions, for both "already in WHNF"
//! (constructor chains) and "needs reduction" (Let chains) cases.
//!
//! Env initialization is isolated from the deep-recursion behavior under
//! test, so failures clearly indicate which phase failed. See #1468.

use super::tests::helpers::{run_with_timeout, SCALING_TEST_TIMEOUT};
use super::*;

/// Performance proof: stack_safe prevents overflow on deep constructor chains.
///
/// stack_safe wraps stacker::maybe_grow which grows the stack as needed.
/// This test verifies whnf handles deeply nested constructor applications
/// without stack overflow and returns a semantically correct result.
///
/// Nat.succ^500(Nat.zero) is a deep constructor application chain. With
/// reduce_nat active in WHNF, the chain is collapsed to Nat literal 500.
/// The primary safety property is no stack overflow; the semantic check
/// verifies the result represents the same natural number.
///
/// Environment initialization is done outside the timeout boundary so that
/// init-path failures (e.g., init_sorry) are clearly separated from the
/// deep-recursion behavior under test. See #1468.
#[test]
fn test_stack_safe_deep_recursion() {
    // Phase 1: Environment setup (outside timeout — not the behavior under test)
    let mut env = Environment::new();
    env.init_nat()
        .expect("invariant: Nat init required for test");

    // Phase 2: Deep-path stack safety (inside timeout)
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_stack_safe_deep_recursion",
        move || {
            // Build a deeply nested App chain: Nat.succ (Nat.succ (... (Nat.zero)))
            let f = Expr::const_(Name::from_string("Nat.succ"), vec![]);
            let x = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let depth: u64 = 500;
            let mut deep = x;
            for _ in 0..depth {
                deep = Expr::app(f.clone(), deep);
            }

            let tc = TypeChecker::new(&env);
            let result = tc.whnf(&deep);

            // Primary safety property: no stack overflow (reaching here means success).
            // Semantic check: result represents the same Nat value (500).
            // With reduce_nat in WHNF, Nat.succ^500(Nat.zero) collapses to Nat.lit(500).
            // Without reduce_nat, it would be identity. Accept both forms.
            match result.kind() {
                ExprKind::Lit(crate::expr::Literal::Nat(n)) => {
                    assert_eq!(
                        n.to_u64(),
                        Some(depth),
                        "Nat literal should be {depth}, got: {n:?}"
                    );
                }
                ExprKind::App(..) => {
                    // Constructor chain form: verify outermost structure
                    assert_eq!(
                        result.get_app_num_args(),
                        1,
                        "outermost App should be Nat.succ applied to 1 arg"
                    );
                    let head_fn = result.get_app_fn();
                    assert!(
                        matches!(&head_fn.kind, ExprKind::Const(name, _) if name == &Name::from_string("Nat.succ")),
                        "head function of result must be Nat.succ, got: {:?}",
                        head_fn.kind
                    );
                }
                _ => panic!(
                    "expected Nat literal or Nat.succ chain, got: {:?}",
                    result.kind()
                ),
            }
        },
    );
}

/// Performance proof: stack_safe prevents overflow on deep Let reduction.
///
/// Unlike the constructor chain test above, this forces actual WHNF reduction
/// work (zeta reduction of Let bindings). Each Let layer substitutes a value
/// into its body, requiring real traversal — not just "already in WHNF".
///
/// Builds: let _ := Nat.zero in (let _ := Nat.zero in (... Nat.zero ...))
/// Each Let body is BVar(0) which references the bound value, so every layer
/// performs a real instantiation during WHNF reduction. The final result must
/// be Nat.zero.
///
/// This test catches:
/// - Stack overflow in deep zeta reduction (the primary stack-safety property)
/// - Incorrect Let reduction producing wrong values
/// - Performance regression in Let chains
///
/// See #1468.
#[test]
fn test_stack_safe_deep_let_reduction() {
    // No env needed — Let reduction is purely syntactic.
    // Uses empty Environment to prove complete isolation from init paths.
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_stack_safe_deep_let_reduction",
        || {
            let nat = Expr::const_(Name::from_string("Nat"), vec![]);
            let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let depth = 500;

            // Build: let _ : Nat := Nat.zero in (let _ : Nat := #0 in (... #0 ...))
            // Innermost body is BVar(0), each Let substitutes the value.
            // After full zeta reduction, result should be Nat.zero.
            let mut deep_let = Expr::bvar(0);
            for _ in 0..depth {
                deep_let =
                    Expr::let_named(Name::anon(), nat.clone(), zero.clone(), deep_let, false);
            }

            assert!(
                matches!(&deep_let.kind, ExprKind::Let(..)),
                "test expression must be a Let chain"
            );

            // Empty env — Let reduction doesn't look up definitions
            let env = Environment::new();
            let tc = TypeChecker::new(&env);
            let result = tc.whnf(&deep_let);

            // The result must be Nat.zero — not a Let, not a BVar, not corrupted
            assert_eq!(result, zero, "deep Let chain must reduce to Nat.zero");
            assert!(
                matches!(&result.kind, ExprKind::Const(name, _) if name == &Name::from_string("Nat.zero")),
                "result must be Const(Nat.zero), got: {:?}",
                result.kind
            );
        },
    );
}
