// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the batch verification module.

use super::*;
use crate::env::{Declaration, Environment};
use crate::expr::BinderInfo;
use crate::level::Level;
use crate::micro::CrossValidationError;
use crate::name::Name;
use crate::tc::{TcCaches, TypeError};
use crate::ExprKind;

fn succ_n(n: usize) -> Level {
    let mut level = Level::Zero;
    for _ in 0..n {
        level = Level::succ(level);
    }
    level
}

#[test]
fn test_batch_check_sorts() {
    let env = Environment::new();
    let verifier = BatchVerifier::new(&env);

    let exprs: Vec<Expr> = (0..10)
        .map(|i| Expr::from_kind(ExprKind::Sort(succ_n(i))))
        .collect();
    let results = verifier.batch_check(&exprs);

    assert_eq!(results.len(), 10);
    for (i, r) in results.iter().enumerate() {
        assert!(r.valid, "Sort({i}) should be valid");
        let ty = r
            .inferred_type
            .as_ref()
            .expect("valid result should have inferred_type");
        // typeof(Sort(i)) = Sort(i+1)
        let expected = Expr::from_kind(ExprKind::Sort(succ_n(i + 1)));
        assert_eq!(*ty, expected, "typeof(Sort({i})) should be Sort({})", i + 1);
    }

    // Verify invalid expressions are correctly rejected
    let invalid = Expr::from_kind(ExprKind::BVar(0));
    let mixed = vec![Expr::from_kind(ExprKind::Sort(Level::Zero)), invalid];
    let mixed_results = verifier.batch_check(&mixed);
    assert_eq!(mixed_results.len(), 2);
    assert!(
        mixed_results[0].valid,
        "Sort(0) should be valid in mixed batch"
    );
    assert!(
        !mixed_results[1].valid,
        "BVar(0) should be invalid in mixed batch"
    );
}

#[test]
fn test_new_inherits_environment_mode() {
    let env = Environment::with_mode(CleanMode::Cubical);
    let verifier = BatchVerifier::new(&env);
    let interval = Expr::from_kind(ExprKind::CubicalInterval);

    let ty = verifier
        .check_one(&interval)
        .expect("BatchVerifier::new should preserve cubical mode");

    assert_eq!(
        ty,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    );
}

#[test]
fn test_with_config_preset_inherits_environment_mode() {
    let env = Environment::with_mode(CleanMode::Cubical);
    let interval = Expr::from_kind(ExprKind::CubicalInterval);
    for (preset_name, config) in [
        ("default", BatchConfig::default()),
        ("low_latency", BatchConfig::low_latency()),
        ("high_throughput", BatchConfig::high_throughput()),
    ] {
        let verifier = BatchVerifier::with_config(&env, config);
        let ty = verifier.check_one(&interval).unwrap_or_else(|err| {
            panic!("{preset_name} preset should inherit cubical mode: {err:?}")
        });

        assert_eq!(
            ty,
            Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            "{preset_name} preset should preserve cubical mode",
        );
    }
}

#[test]
fn test_with_config_explicit_mode_overrides_environment() {
    let env = Environment::with_mode(CleanMode::Cubical);
    let verifier = BatchVerifier::with_config(
        &env,
        BatchConfig {
            parallel_threshold: 4,
            num_threads: None,
            mode: Some(CleanMode::Constructive),
        },
    );
    let interval = Expr::from_kind(ExprKind::CubicalInterval);

    let result = verifier.check_one(&interval);

    assert!(
        matches!(
            result,
            Err(TypeError::ModeRequired { ref feature, ref mode })
                if feature == "CubicalInterval" && mode == "Cubical"
        ),
        "explicit constructive override should require cubical mode, got: {result:?}"
    );
}

#[test]
fn test_find_first_valid() {
    let env = Environment::new();
    let verifier = BatchVerifier::new(&env);

    // Create some expressions - all should be valid
    let exprs: Vec<Expr> = (0..5)
        .map(|i| Expr::from_kind(ExprKind::Sort(succ_n(i))))
        .collect();

    let (_, ty) = verifier
        .find_first_valid(exprs.into_iter())
        .expect("should find at least one valid expression");
    // Type of Sort(0) is Sort(1)
    assert_eq!(ty, Expr::from_kind(ExprKind::Sort(succ_n(1))));
}

#[test]
fn test_find_first_valid_parallel() {
    let env = Environment::new();
    let verifier = BatchVerifier::new(&env);

    let exprs: Vec<Expr> = (0..100)
        .map(|i| Expr::from_kind(ExprKind::Sort(succ_n(i))))
        .collect();

    let _result = verifier
        .find_first_valid_parallel(&exprs)
        .expect("parallel search should find at least one valid expression");
}

#[test]
fn test_count_valid() {
    let env = Environment::new();
    let verifier = BatchVerifier::new(&env);

    // All-valid case
    let all_valid: Vec<Expr> = (0..50)
        .map(|i| Expr::from_kind(ExprKind::Sort(succ_n(i))))
        .collect();
    let count = verifier.count_valid(&all_valid);
    assert_eq!(count, 50, "all 50 Sort expressions should be valid");

    // Mixed valid/invalid — must not just return exprs.len()
    let mixed = vec![
        Expr::from_kind(ExprKind::Sort(Level::Zero)), // valid
        Expr::from_kind(ExprKind::BVar(0)),           // invalid
        Expr::from_kind(ExprKind::BVar(5)),           // invalid
        Expr::prop(),                                 // valid
        Expr::from_kind(ExprKind::BVar(99)),          // invalid
    ];
    let mixed_count = verifier.count_valid(&mixed);
    assert_eq!(mixed_count, 2, "only 2 of 5 expressions are valid");
}

#[test]
fn test_arena() {
    let env = Environment::new();
    let verifier = BatchVerifier::new(&env);

    let mut arena = VerificationArena::with_capacity(10);

    // Add expressions
    for i in 0..10 {
        arena.push(Expr::from_kind(ExprKind::Sort(succ_n(i))));
    }

    assert_eq!(arena.len(), 10);

    // Verify all
    arena.verify_all(&verifier);

    // Check results
    for i in 0..10u32 {
        assert!(arena.is_valid(i));
        let _ty = arena
            .get_type(i)
            .expect("valid arena entry should have type");
    }

    // Check stats
    let stats = arena.stats();
    assert_eq!(stats.total, 10);
    assert_eq!(stats.valid, 10);
    assert_eq!(stats.invalid, 0);
}

#[test]
fn test_batch_check_with_stats() {
    let env = Environment::new();
    let verifier = BatchVerifier::new(&env);

    let exprs: Vec<Expr> = (0..20)
        .map(|i| Expr::from_kind(ExprKind::Sort(succ_n(i))))
        .collect();

    let (results, stats) = verifier.batch_check_with_stats(&exprs);

    assert_eq!(results.len(), 20);
    assert_eq!(stats.total, 20);
    assert_eq!(stats.valid, 20);
    assert!(stats.wall_time_ns > 0);
}

#[test]
fn test_stream_valid_early_termination() {
    let env = Environment::new();
    let verifier = BatchVerifier::new(&env);

    let exprs: Vec<Expr> = (0..100)
        .map(|i| Expr::from_kind(ExprKind::Sort(succ_n(i))))
        .collect();

    let mut count = 0;
    verifier.stream_valid(exprs.into_iter(), |_, _| {
        count += 1;
        count < 5 // Stop after 5 valid expressions
    });

    assert_eq!(count, 5);
}

#[test]
fn test_valid_indices() {
    let env = Environment::new();
    let verifier = BatchVerifier::new(&env);

    let exprs: Vec<Expr> = (0..10)
        .map(|i| Expr::from_kind(ExprKind::Sort(succ_n(i))))
        .collect();

    let indices = verifier.valid_indices(&exprs);
    assert_eq!(indices.len(), 10);
    assert_eq!(indices, (0..10).collect::<Vec<_>>());
}

#[test]
fn test_config_presets() {
    let default = BatchConfig::default();
    let low = BatchConfig::low_latency();
    let high = BatchConfig::high_throughput();

    assert!(default.mode.is_none());
    assert!(low.mode.is_none());
    assert!(high.mode.is_none());
    assert!(low.parallel_threshold < high.parallel_threshold);
}

#[test]
fn test_invalid_expressions() {
    let env = Environment::new();
    let verifier = BatchVerifier::new(&env);

    // BVar(0) without enclosing binder is invalid
    let invalid_expr = Expr::from_kind(ExprKind::BVar(0));
    let result = verifier.check_one(&invalid_expr);
    assert!(
        matches!(result, Err(TypeError::UnboundVariable(0))),
        "expected UnboundVariable(0), got: {result:?}"
    );

    // Batch with mix of valid and invalid
    let exprs = vec![
        Expr::from_kind(ExprKind::Sort(Level::Zero)), // valid
        Expr::from_kind(ExprKind::BVar(0)),           // invalid - unbound variable
        Expr::prop(),                                 // valid
    ];
    let results = verifier.batch_check(&exprs);
    assert_eq!(results.len(), 3);
    assert!(results[0].valid);
    assert!(!results[1].valid);
    let _err = results[1]
        .error
        .as_ref()
        .expect("invalid result should have error");
    assert!(results[2].valid);

    // count_valid should only count valid ones
    let count = verifier.count_valid(&exprs);
    assert_eq!(count, 2);

    // valid_indices should only return valid indices
    let indices = verifier.valid_indices(&exprs);
    assert_eq!(indices, vec![0, 2]);
}

#[test]
fn test_cross_validation_failure_maps_to_batch_failure() {
    let err = TypeError::CrossValidationFailure(Box::new(CrossValidationError::Disagreement {
        expr: "Sort(0)".to_string(),
        main_type: "Sort(1)".to_string(),
        micro_type: "Sort(2)".to_string(),
    }));

    let result = BatchVerifier::infer_result_to_batch_result(Err(err), 123);

    assert!(!result.valid);
    assert!(
        result.inferred_type.is_none(),
        "failed batch result should have no inferred_type"
    );
    assert_eq!(result.time_ns, 123);
    let msg = result
        .error
        .expect("failed result should include error message");
    assert!(
        msg.contains("Cross-validation failure"),
        "expected TypeError wrapper in message, got: {msg}"
    );
    assert!(
        msg.contains("MICRO-CHECKER DISAGREEMENT"),
        "expected disagreement payload in message, got: {msg}"
    );
}

#[test]
fn test_find_first_valid_with_invalid_prefix() {
    let env = Environment::new();
    let verifier = BatchVerifier::new(&env);

    // First few are invalid, then valid ones
    let exprs = vec![
        Expr::from_kind(ExprKind::BVar(0)), // invalid
        Expr::from_kind(ExprKind::BVar(1)), // invalid
        Expr::prop(),                       // valid - should be returned
        Expr::type_(),                      // valid
    ];

    let (expr, _ty) = verifier
        .find_first_valid(exprs.into_iter())
        .expect("should find first valid expression (Prop)");
    assert!(expr.is_prop());
}

#[test]
fn test_arena_wall_time_reset_on_push() {
    // Tests that adding expressions invalidates stale wall time
    let env = Environment::new();
    let verifier = BatchVerifier::new(&env);

    let mut arena = VerificationArena::new();
    arena.push(Expr::prop());
    arena.verify_all(&verifier);

    // After verify_all, stats should have wall time
    let stats1 = arena.stats();
    assert!(stats1.wall_time_ns > 0);

    // Adding a new expression should invalidate wall time
    arena.push(Expr::type_());

    // Now stats reports no wall-clock time because verification is stale
    let stats2 = arena.stats();
    // Both should report something, but the new expression isn't verified
    assert_eq!(stats2.total, 1); // Only 1 verified result
    assert_eq!(stats2.wall_time_ns, 0);
}

/// Test stream_check directly: callback receives expression and result,
/// early termination via returning false stops iteration.
/// Part of #1357 — stream_check was the only untested streaming method.
#[test]
fn test_stream_check_collects_results() {
    let env = Environment::new();
    let verifier = BatchVerifier::new(&env);

    let exprs = vec![
        Expr::from_kind(ExprKind::Sort(Level::Zero)),
        Expr::from_kind(ExprKind::Sort(succ_n(1))),
        Expr::from_kind(ExprKind::BVar(0)), // invalid
        Expr::from_kind(ExprKind::Sort(succ_n(2))),
    ];

    let mut collected: Vec<(bool, bool)> = Vec::new();
    verifier.stream_check(exprs.into_iter(), |_expr, result| {
        collected.push((result.valid, result.error.is_some()));
        true // continue
    });

    assert_eq!(
        collected.len(),
        4,
        "stream_check should visit all expressions"
    );
    assert_eq!(collected[0], (true, false), "Sort(0) is valid");
    assert_eq!(collected[1], (true, false), "Sort(1) is valid");
    assert_eq!(collected[2], (false, true), "BVar(0) is invalid with error");
    assert_eq!(collected[3], (true, false), "Sort(2) is valid");
}

/// Test stream_check early termination: returning false stops iteration
/// before processing all expressions.
#[test]
fn test_stream_check_early_termination() {
    let env = Environment::new();
    let verifier = BatchVerifier::new(&env);

    let exprs = (0..100).map(|i| Expr::from_kind(ExprKind::Sort(succ_n(i))));

    let mut count = 0;
    verifier.stream_check(exprs, |_expr, result| {
        assert!(result.valid, "all Sort expressions should be valid");
        count += 1;
        count < 3 // stop after 3
    });

    assert_eq!(
        count, 3,
        "stream_check should stop after callback returns false"
    );
}

/// Test batch_check_parallel with custom num_threads configuration.
/// Verifies thread pool configuration path works correctly.
#[test]
fn test_batch_check_parallel_custom_threads() {
    let env = Environment::new();
    let config = BatchConfig {
        parallel_threshold: 1,
        num_threads: Some(2),
        mode: Some(CleanMode::default()),
    };
    let verifier = BatchVerifier::with_config(&env, config);

    let exprs: Vec<Expr> = (0..20)
        .map(|i| Expr::from_kind(ExprKind::Sort(succ_n(i))))
        .collect();

    let results = verifier.batch_check_parallel(&exprs);
    assert_eq!(
        results.len(),
        20,
        "should return result for each expression"
    );
    for (i, r) in results.iter().enumerate() {
        assert!(r.valid, "Sort({i}) should be valid");
        assert!(
            r.inferred_type.is_some(),
            "valid result must have inferred type"
        );
    }
}

/// Test batch_check dispatches to parallel when above threshold.
/// With threshold=2 and 10 exprs, should use parallel path.
#[test]
fn test_batch_check_dispatch_above_threshold() {
    let env = Environment::new();
    let config = BatchConfig {
        parallel_threshold: 2,
        num_threads: None,
        mode: Some(CleanMode::default()),
    };
    let verifier = BatchVerifier::with_config(&env, config);

    let exprs: Vec<Expr> = (0..10)
        .map(|i| Expr::from_kind(ExprKind::Sort(succ_n(i))))
        .collect();

    // batch_check should dispatch to parallel path (10 >= 2)
    let results = verifier.batch_check(&exprs);
    assert_eq!(results.len(), 10);
    assert!(results.iter().all(|r| r.valid));
}

/// Test batch_check dispatches to sequential when below threshold.
#[test]
fn test_batch_check_dispatch_below_threshold() {
    let env = Environment::new();
    let config = BatchConfig {
        parallel_threshold: 100, // high threshold
        num_threads: None,
        mode: Some(CleanMode::default()),
    };
    let verifier = BatchVerifier::with_config(&env, config);

    let exprs: Vec<Expr> = (0..3)
        .map(|i| Expr::from_kind(ExprKind::Sort(succ_n(i))))
        .collect();

    // batch_check should use sequential path (3 < 100)
    let results = verifier.batch_check(&exprs);
    assert_eq!(results.len(), 3);
    assert!(results.iter().all(|r| r.valid));
}

/// Verify cache sharing produces identical results to fresh-TC-per-expression.
///
/// Creates duplicate expressions in a batch so that the second occurrence can
/// hit caches populated by the first. Compares results from the cache-sharing
/// batch path against individual `check_one` calls (which use fresh TCs).
/// Part of #2382 AC5: correctness — cache sharing does not affect results.
#[test]
fn test_cache_sharing_correctness() {
    let env = Environment::new();
    let verifier = BatchVerifier::new(&env);

    // Build a batch with repeated expressions: cache hits are possible
    // for the duplicates but must produce identical results.
    let base_exprs: Vec<Expr> = (0..5)
        .map(|i| Expr::from_kind(ExprKind::Sort(succ_n(i))))
        .collect();
    let mut exprs = base_exprs.clone();
    exprs.extend(base_exprs.iter().cloned()); // duplicate all
    exprs.push(Expr::from_kind(ExprKind::BVar(0))); // invalid

    // Get results via batch (uses shared caches)
    let batch_results = verifier.batch_check(&exprs);

    // Get results via individual check_one (fresh TC each time)
    let individual_results: Vec<Result<Expr, TypeError>> =
        exprs.iter().map(|e| verifier.check_one(e)).collect();

    assert_eq!(batch_results.len(), individual_results.len());
    for (i, (batch_r, indiv_r)) in batch_results
        .iter()
        .zip(individual_results.iter())
        .enumerate()
    {
        match indiv_r {
            Ok(ty) => {
                assert!(
                    batch_r.valid,
                    "expr[{i}]: individual says Ok but batch says invalid"
                );
                assert_eq!(
                    batch_r.inferred_type.as_ref().unwrap(),
                    ty,
                    "expr[{i}]: inferred types differ"
                );
            }
            Err(_) => {
                assert!(
                    !batch_r.valid,
                    "expr[{i}]: individual says Err but batch says valid"
                );
            }
        }
    }
}

/// Test batch verification with Let expressions.
///
/// Let expressions exercise FVar creation (the TypeChecker allocates FVars
/// for let-bound variables) and WHNF caching (reducing FVar to its let-value).
/// This is the exact expression kind that enabled the P1 soundness bug #2382:
/// zero batch tests used Let, so the FVarId collision went undetected.
///
/// Part of #2397 AC1.
#[test]
fn test_batch_let_expression() {
    let env = Environment::new();
    let verifier = BatchVerifier::new(&env);

    // let x : Type := Prop in x
    // Body BVar(0) refers to the let-bound variable with type Type.
    let let_simple = Expr::let_named(
        Name::anon(),
        Expr::type_(),
        Expr::prop(),
        Expr::bvar(0),
        false,
    );

    // let x : Type 1 := Type in x
    // Type 1 = Sort(2), Type = Sort(1), typeof(Sort(1)) = Sort(2)
    let type_1 = Expr::from_kind(ExprKind::Sort(succ_n(2)));
    let let_higher = Expr::let_named(
        Name::anon(),
        type_1.clone(),
        Expr::type_(),
        Expr::bvar(0),
        false,
    );

    // Nested let: let x : Type := Prop in (let y : Type := x in y)
    // Inner let binds y to x (BVar(0) from outer scope), body returns y.
    let inner_let = Expr::let_named(
        Name::anon(),
        Expr::type_(),
        Expr::bvar(0),
        Expr::bvar(0),
        false,
    );
    let nested_let = Expr::let_named(Name::anon(), Expr::type_(), Expr::prop(), inner_let, false);

    let exprs = vec![let_simple, let_higher, nested_let];
    let results = verifier.batch_check(&exprs);

    assert_eq!(results.len(), 3);
    for (i, r) in results.iter().enumerate() {
        assert!(r.valid, "let expression [{i}] should be valid");
        assert!(
            r.inferred_type.is_some(),
            "let expression [{i}] should have inferred type"
        );
    }

    assert_eq!(
        results[0].inferred_type.as_ref().unwrap(),
        &Expr::type_(),
        "let x : Type := Prop in x should have type Type"
    );
    assert_eq!(
        results[1].inferred_type.as_ref().unwrap(),
        &type_1,
        "let x : Type 1 := Type in x should have type Type 1"
    );
    assert_eq!(
        results[2].inferred_type.as_ref().unwrap(),
        &Expr::type_(),
        "nested let should have type Type"
    );
}

/// Test batch verification with Const expressions.
///
/// Const expressions require environment lookups (delta-reduction infrastructure)
/// to retrieve the declaration's type. No previous batch test exercised this path,
/// since Sort/BVar are environment-independent.
///
/// Part of #2397 AC2.
#[test]
fn test_batch_const_expression() {
    let mut env = Environment::new();

    // axiom A : Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("adding axiom A should succeed");

    // def id_prop : Prop -> Prop := fun p => p
    let id_type = Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop());
    let id_value = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    env.add_decl(Declaration::Definition {
        name: Name::from_string("id_prop"),
        level_params: vec![],
        type_: id_type.clone(),
        value: id_value,
        is_reducible: true,
    })
    .expect("adding definition id_prop should succeed");

    let verifier = BatchVerifier::new(&env);

    // Const("A") should type-check to Prop (env lookup)
    let a_const = Expr::const_(Name::from_string("A"), vec![]);
    // Const("id_prop") should type-check to Prop -> Prop (env lookup)
    let id_const = Expr::const_(Name::from_string("id_prop"), vec![]);
    // App(Const("id_prop"), Const("A")) should type-check to Prop
    let app_expr = Expr::app(id_const.clone(), a_const.clone());

    let exprs = vec![a_const, id_const, app_expr];
    let results = verifier.batch_check(&exprs);

    assert_eq!(results.len(), 3);
    for (i, r) in results.iter().enumerate() {
        assert!(r.valid, "const expression [{i}] should be valid");
    }

    assert_eq!(
        results[0].inferred_type.as_ref().unwrap(),
        &Expr::prop(),
        "Const(A) should have type Prop"
    );
    assert_eq!(
        results[1].inferred_type.as_ref().unwrap(),
        &id_type,
        "Const(id_prop) should have type Prop -> Prop"
    );
    assert_eq!(
        results[2].inferred_type.as_ref().unwrap(),
        &Expr::prop(),
        "App(id_prop, A) should have type Prop"
    );
}

/// Test batch verification with App(Lambda, Arg) expressions.
///
/// Beta-reduction (applying a lambda to an argument) exercises the WHNF
/// cache during type inference. The type checker must reduce
/// `(fun x : T => body) arg` by substituting `arg` into `body`.
///
/// Part of #2397 AC3.
#[test]
fn test_batch_app_lambda_expression() {
    let env = Environment::new();
    let verifier = BatchVerifier::new(&env);

    // (fun (A : Type) => A) Prop
    // Identity on Type applied to Prop. Beta-reduces to Prop. Type is Type.
    let id_fn = Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0));
    let beta_simple = Expr::app(id_fn, Expr::prop());

    // (fun (A : Type) (B : Type) => A) Prop Prop
    // Constant function on Types, applied to Prop twice. Result type is Type.
    let const_fn = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(1)),
    );
    let beta_nested = Expr::app(Expr::app(const_fn, Expr::prop()), Expr::prop());

    // Mixed batch: lambda applications alongside Sort for cross-kind cache sharing
    let sort_expr = Expr::from_kind(ExprKind::Sort(Level::Zero));
    let exprs = vec![beta_simple, beta_nested, sort_expr];
    let results = verifier.batch_check(&exprs);

    assert_eq!(results.len(), 3);
    for (i, r) in results.iter().enumerate() {
        assert!(r.valid, "expression [{i}] should be valid");
    }

    assert_eq!(
        results[0].inferred_type.as_ref().unwrap(),
        &Expr::type_(),
        "(fun A : Type => A) Prop should have type Type"
    );
    assert_eq!(
        results[1].inferred_type.as_ref().unwrap(),
        &Expr::type_(),
        "(fun A B : Type => A) Prop Prop should have type Type"
    );
}

/// Test cache sharing across Let, Const, and App(Lambda) expressions in a batch.
///
/// Exercises the batch verifier's cache sharing when heterogeneous expression
/// kinds (Let + Const + App(Lambda) + Sort) are interleaved. Verifies that
/// cache state accumulated from one expression kind does not corrupt results
/// for subsequent expressions of different kinds.
///
/// Part of #2397 — validates cache sharing is sound across expression kinds.
#[test]
fn test_batch_cache_sharing_mixed_expression_kinds() {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let verifier = BatchVerifier::new(&env);

    // Mix all expression kinds in one batch
    let exprs = vec![
        // Sort: trivial baseline
        Expr::from_kind(ExprKind::Sort(Level::Zero)),
        // Let: allocates FVar, exercises WHNF let-reduction
        Expr::let_named(
            Name::anon(),
            Expr::type_(),
            Expr::prop(),
            Expr::bvar(0),
            false,
        ),
        // Const: environment lookup
        Expr::const_(Name::from_string("P"), vec![]),
        // App(Lambda): beta-reduction
        Expr::app(
            Expr::lam(BinderInfo::Default, Expr::type_(), Expr::bvar(0)),
            Expr::prop(),
        ),
        // Another Let after App — tests that App's cache state doesn't
        // corrupt subsequent Let FVar allocation
        Expr::let_named(
            Name::anon(),
            Expr::from_kind(ExprKind::Sort(succ_n(2))),
            Expr::type_(),
            Expr::bvar(0),
            false,
        ),
    ];

    // Batch path (shared caches)
    let batch_results = verifier.batch_check(&exprs);

    // Individual path (fresh TC each time) — the ground truth
    let individual_results: Vec<_> = exprs.iter().map(|e| verifier.check_one(e)).collect();

    assert_eq!(batch_results.len(), individual_results.len());
    for (i, (batch_r, indiv_r)) in batch_results
        .iter()
        .zip(individual_results.iter())
        .enumerate()
    {
        match indiv_r {
            Ok(ty) => {
                assert!(batch_r.valid, "expr[{i}]: individual Ok but batch invalid");
                assert_eq!(
                    batch_r.inferred_type.as_ref().unwrap(),
                    ty,
                    "expr[{i}]: inferred types differ between batch and individual"
                );
            }
            Err(_) => {
                assert!(!batch_r.valid, "expr[{i}]: individual Err but batch valid");
            }
        }
    }
}

/// Verify the cache save/restore cycle in check_single_with_caches is sound.
///
/// Processes the same expressions twice through shared caches: the second
/// pass reuses caches accumulated from the first. Verifies that the
/// save/restore mechanism (take + reinject via with_mode_and_caches)
/// does not corrupt state or produce incorrect results on reuse.
/// Part of #2382 AC4: functional verification of cache save/restore.
#[test]
fn test_cache_save_restore_produces_correct_results() {
    let env = Environment::new();
    let verifier = BatchVerifier::new(&env);

    let valid_exprs: Vec<Expr> = (0..5)
        .map(|i| Expr::from_kind(ExprKind::Sort(succ_n(i))))
        .collect();
    let invalid_expr = Expr::from_kind(ExprKind::BVar(0));

    // First pass: accumulate caches across valid and invalid expressions
    let mut caches = TcCaches::default();
    for expr in &valid_exprs {
        let result = verifier.check_single_with_caches(expr, &mut caches);
        assert!(result.valid, "first pass: Sort should be valid");
    }
    let invalid_result = verifier.check_single_with_caches(&invalid_expr, &mut caches);
    assert!(
        !invalid_result.valid,
        "first pass: BVar(0) should be invalid"
    );

    // Second pass: same expressions through accumulated caches
    // This verifies the save/restore cycle doesn't corrupt state
    for (i, expr) in valid_exprs.iter().enumerate() {
        let result = verifier.check_single_with_caches(expr, &mut caches);
        assert!(result.valid, "second pass: Sort({i}) should still be valid");
        let ty = result.inferred_type.as_ref().expect("valid must have type");
        let expected = Expr::from_kind(ExprKind::Sort(succ_n(i + 1)));
        assert_eq!(
            *ty,
            expected,
            "second pass: Sort({i}) type should be Sort({})",
            i + 1
        );
    }
    let invalid_result2 = verifier.check_single_with_caches(&invalid_expr, &mut caches);
    assert!(
        !invalid_result2.valid,
        "second pass: BVar(0) should still be invalid"
    );
}
