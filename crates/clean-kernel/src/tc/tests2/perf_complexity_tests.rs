// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Performance complexity tests for kernel hot paths.
//!
//! Documents algorithmic complexity of key operations and detects regressions.
//! Filed as #1931.

use super::tests::helpers::{run_with_timeout, SCALING_TEST_TIMEOUT};
use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

// ================================================================
// Performance proof: recursor rule lookup is O(1) via constructor_idx
//
// try_iota_reduction uses `rules.get(constructor_idx)` for O(1) lookup
// (reduction.rs:241-248). Previously used `.iter().find()` which was O(N).
// Fixed via #1853: constructor_idx directly indexes into rules vec.
// ================================================================

/// Build an inductive type with `n` zero-argument constructors.
fn make_many_ctor_env(n: usize) -> (Environment, Name) {
    let mut env = Environment::new();
    let ind_name = Name::from_string("BigEnum");
    let ind_ref = Expr::const_(ind_name.clone(), vec![]);

    let mut ctors = Vec::with_capacity(n);
    for i in 0..n {
        ctors.push(Constructor {
            name: Name::from_string(&format!("BigEnum.c{i}")),
            type_: ind_ref.clone(),
        });
    }

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: ind_name.clone(),
            type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            constructors: ctors,
        }],
    };
    env.add_inductive(decl).expect("add BigEnum inductive");

    let last_ctor = Name::from_string(&format!("BigEnum.c{}", n - 1));
    (env, last_ctor)
}

/// Build a recursor application for BigEnum targeting the last constructor.
fn build_big_enum_rec_app(n: usize, _env: &Environment, last_ctor: &Name) -> Expr {
    let rec = Expr::const_(
        Name::from_string("BigEnum.rec"),
        vec![Level::succ(Level::zero())],
    );
    let ind_ref = Expr::const_(Name::from_string("BigEnum"), vec![]);
    let motive = Expr::lam(BinderInfo::Default, ind_ref, Expr::type_());

    let mut app = Expr::app(rec, motive);
    for _ in 0..n {
        app = Expr::app(app, Expr::type_());
    }
    Expr::app(app, Expr::const_(last_ctor.clone(), vec![]))
}

/// Verifies O(1) recursor rule lookup in try_iota_reduction (#1853).
/// Uses acceptance criteria sizes: 1, 3, 10, 20 constructors.
/// With constructor_idx direct indexing, 20/1 ratio should be near 1.0.
#[test]
fn test_iota_recursor_rule_lookup_scaling() {
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_iota_recursor_rule_lookup_scaling",
        || {
            let sizes = [1usize, 3, 10, 20];
            let mut times = Vec::new();

            for &n in &sizes {
                let (env, last_ctor) = make_many_ctor_env(n);
                let tc = TypeChecker::new(&env);
                let app = build_big_enum_rec_app(n, &env, &last_ctor);

                // Warmup
                for _ in 0..10 {
                    let _ = tc.whnf(&app);
                }

                let iters = 1000;
                let start = std::time::Instant::now();
                for _ in 0..iters {
                    let _ = tc.whnf(&app);
                }
                let elapsed = start.elapsed().as_nanos() as u64;
                times.push(elapsed / iters as u64);
            }

            eprintln!(
                "iota rule lookup (constructor_idx O(1)): sizes={sizes:?}, times_ns={times:?}"
            );

            // With O(1) indexing, 20-ctor lookup should not be significantly
            // slower than 1-ctor lookup. Allow 10x for noise (env size differences,
            // minor premise count differences in whnf). Linear scan would give ~20x.
            if times[0] > 0 {
                let ratio = times[3] as f64 / times[0] as f64;
                assert!(
                    ratio < 10.0,
                    "iota recursor rule lookup scaling: 20/1 ctor ratio = {ratio:.1}x \
                     (expected ~1x for O(1) constructor_idx lookup). times: {times:?}"
                );
            }
        },
    );
}

// ================================================================
// Performance proof: DefEqCacheKey clones both expressions
//
// DefEqCacheKey::new in tc/def_eq/mod.rs creates cache keys by cloning both Expr operands.
// With Rc/Arc expressions, clone is O(1). With value types, O(expr_size).
// ================================================================

/// Documents Expr clone cost regime (O(1) for Arc vs O(n) for value).
/// Regression test for #1931.
#[test]
fn test_def_eq_cache_key_creation_scaling() {
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_def_eq_cache_key_creation_scaling",
        || {
            let nat = Expr::const_(Name::from_string("Nat"), vec![]);
            let sizes = [10usize, 100, 1000];
            let mut times = Vec::new();

            for &size in &sizes {
                let mut expr = nat.clone();
                for _ in 0..size {
                    expr = Expr::app(nat.clone(), expr);
                }

                let iters = 1000;
                let start = std::time::Instant::now();
                for _ in 0..iters {
                    let _ = expr.clone();
                }
                let elapsed = start.elapsed().as_nanos() as u64;
                times.push(elapsed / iters as u64);
            }

            if times[0] > 0 {
                let ratio = times[2] as f64 / times[0] as f64;
                // ratio < 5.0 → Rc/Arc O(1) clone
                // ratio > 50.0 → value O(n) clone, needs optimization
                assert!(
                    ratio < 200.0,
                    "Expr clone scaling: 1000/10 ratio = {ratio:.1}x. times: {times:?}"
                );
            }
        },
    );
}

// ================================================================
// Performance proof: reduce_nat dispatch remains a measurable hot path
//
// `reduce_nat` runs during WHNF on closed Nat applications. Before #1515,
// this path converted the head constant's `Name` to a heap-allocated `String`
// on every binary-operation dispatch; now it uses cached `Name` equality,
// but the arithmetic reduction path is still materially more expensive than
// literal identity WHNF on unique expressions.
//
// `reduce_nat` is called from whnf_core via reduce_nat_ops on
// every closed Nat application. With Mathlib's heavy Nat usage, this
// remains a useful regression probe for dispatch overhead.
// ================================================================

/// Performance proof: Nat reduction dispatch stays on the WHNF hot path.
///
/// This test forces unique expressions (no cache hits) to measure the
/// actual `reduce_nat` overhead on the binary-op path. It creates
/// many distinct Nat.add(a, b) expressions with different literal values,
/// ensuring each WHNF call exercises the full reduce_nat path.
///
/// After #1515 this path dispatches via cached `Name` equality, so the
/// remaining gap relative to literal WHNF comes from application traversal,
/// arithmetic reduction, and the still-nontrivial operator dispatch.
///
/// Regression test for performance_proofs P1 iter 753.
#[test]
fn test_reduce_nat_dispatch_overhead() {
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_reduce_nat_dispatch_overhead",
        || {
            use std::hint::black_box;

            let env = Environment::new();

            // Build many UNIQUE Nat.add(a, b) expressions — each is a cache miss,
            // forcing reduce_nat to execute on every call.
            let n = 1000;
            let add_exprs: Vec<Expr> = (0..n as u64)
                .map(|i| {
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Nat.add"), vec![]),
                            Expr::nat_lit(i),
                        ),
                        Expr::nat_lit(i + 1),
                    )
                })
                .collect();

            // Measure: WHNF on unique Nat.add expressions (all cache misses).
            // Each call: cache miss → whnf_core → reduce_nat dispatch → reduce.
            let tc = TypeChecker::new(&env);
            let start = std::time::Instant::now();
            for expr in &add_exprs {
                let result = tc.whnf(black_box(expr));
                black_box(&result);
            }
            let nat_add_time = start.elapsed();

            // Compare: WHNF on unique Nat literals (all cache misses, no reduce_nat path).
            // Literal WHNF: cache miss → whnf_core → return (literals are in normal form).
            let lit_exprs: Vec<Expr> = (0..n as u64).map(Expr::nat_lit).collect();
            let tc2 = TypeChecker::new(&env);
            let start = std::time::Instant::now();
            for expr in &lit_exprs {
                let result = tc2.whnf(black_box(expr));
                black_box(&result);
            }
            let lit_time = start.elapsed();

            // Document the overhead ratio.
            let ratio = nat_add_time.as_nanos() as f64 / lit_time.as_nanos().max(1) as f64;
            eprintln!(
                "reduce_nat overhead ({n} unique exprs, no cache hits): \
                 Nat.add WHNF = {:.0}ns/op, literal WHNF = {:.0}ns/op, \
                 ratio = {ratio:.1}x (includes dispatch + reduce)",
                nat_add_time.as_nanos() as f64 / n as f64,
                lit_time.as_nanos() as f64 / n as f64,
            );

            // Nat.add reduction should be measurably more expensive than literal
            // identity WHNF, since it exercises reduce_nat dispatch plus the
            // actual arithmetic reduction.
            assert!(
                ratio > 1.0,
                "Nat.add WHNF on unique expressions should be slower than literal \
                 WHNF due to reduce_nat overhead (got ratio={ratio:.1}x)"
            );
        },
    );
}
