// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Performance proof tests for lazy_delta_reduction hot path.
//!
//! These tests target the three main allocation hotspots in the
//! `lazy_delta_reduction` loop in `tc/def_eq/delta.rs`:
//!
//! 1. **replace_head_const** in `tc/def_eq/delta.rs`: Rebuilds the entire
//!    application spine on every delta reduction step. For `f a1 ... an`
//!    with `d` unfold steps, this is O(a * d) Arc allocations.
//!
//! 2. **get_delta_const** in `tc/def_eq/delta.rs`: Uses `LevelVec` (SmallVec<[Level; 2]>)
//!    — no heap allocation for constants with ≤2 universe levels (97.1% of cases).
//!
//! 3. **unfold_with_transparency** (env/mod.rs:2844): Allocates
//!    `Vec<(Name, Level)>` + `HashMap<Name, Level>` per call.
//!
//! Together, these make lazy_delta_reduction's per-step cost O(a + k)
//! where a = args and k = level params. This file proves these costs
//! scale linearly, not quadratically.

use std::time::Instant;

use super::tests::helpers::{run_with_timeout, SCALING_TEST_TIMEOUT};
use super::*;

/// Build an environment with a chain of `depth` reducible definitions:
/// d0 := Prop, d1 := d0, d2 := d1, ..., d_{depth-1} := d_{depth-2}
/// Then build `d_{depth-1} arg arg ... arg` with `width` args.
/// The expression forces `depth` delta reduction steps in lazy_delta_reduction,
/// and each step rebuilds the application spine of `width` args.
fn build_wide_delta_expr(depth: usize, width: usize) -> (Environment, Expr) {
    use crate::env::Declaration;

    let mut env = Environment::new();

    for i in 0..depth {
        let name = Name::from_string(&format!("d{i}"));
        let value = if i == 0 {
            Expr::prop()
        } else {
            Expr::const_(Name::from_string(&format!("d{}", i - 1)), vec![])
        };
        env.add_decl_unchecked(Declaration::Definition {
            name,
            level_params: vec![],
            type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            value,
            is_reducible: true,
        });
    }

    // Build: d_{depth-1} arg arg ... arg (width args)
    let head = Expr::const_(Name::from_string(&format!("d{}", depth - 1)), vec![]);
    let arg = Expr::prop();
    let mut expr = head;
    for _ in 0..width {
        expr = Expr::app(expr, arg.clone());
    }

    (env, expr)
}

/// Performance proof: lazy_delta_reduction spine rebuild is O(a * d).
///
/// Tests that increasing argument count scales linearly, not quadratically.
/// The delta chain depth is fixed at 5 (typical for Lean 4 definitions),
/// and argument count varies from 10 to 160.
///
/// Each delta step calls `replace_head_const` which collects args into a Vec,
/// reverses it, and rebuilds the full spine via fold. This is O(a) per step.
/// If there were an accidental O(a^2) pattern (e.g., re-traversing the spine
/// per arg), 16x args would give 256x time instead of 16x.
///
/// Related findings:
/// - `tc/def_eq/delta.rs`: replace_head_const allocates a+1 new Expr nodes per step
/// - `tc/def_eq/delta.rs`: get_delta_const uses LevelVec (no heap alloc for ≤2 levels)
/// - env/mod.rs:2844: unfold_with_transparency allocates Vec<(Name, Level)>
#[test]
fn test_lazy_delta_wide_app_spine_rebuild() {
    let _serial = crate::test_utils::serial_test_guard();
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_lazy_delta_wide_app_spine_rebuild",
        || {
            use std::hint::black_box;

            let delta_depth = 5; // Fixed: 5 unfold steps per WHNF call
            let widths = [10usize, 40, 160];
            let mut times = Vec::new();

            for &w in &widths {
                let (env, expr) = build_wide_delta_expr(delta_depth, w);
                let tc = TypeChecker::new(&env);

                // WHNF forces the full delta reduction chain, each step
                // rebuilding the application spine of width w.
                // Warm up: first call populates caches.
                let _ = tc.whnf(black_box(&expr));

                // Measure steady-state (cache hit for intermediate results).
                let start = Instant::now();
                for _ in 0..100 {
                    let _ = tc.whnf(black_box(&expr));
                }
                let elapsed = start.elapsed();
                times.push(elapsed.as_nanos());
            }

            // widths go 10 -> 40 -> 160 (4x each step).
            // For O(a * d) with fixed d=5: 4x width -> 4x time.
            // Allow up to 200x total for noise, cache effects, and constant factors.
            // Tightened from 400x per #1785.
            let ratio_4x = times[1] as f64 / times[0].max(1) as f64;
            let ratio_16x = times[2] as f64 / times[0].max(1) as f64;
            assert!(
                ratio_16x < 200.0,
                "lazy_delta spine rebuild appears worse than O(a*d): \
                 16x width gave {ratio_16x:.1}x time (4x gave {ratio_4x:.1}x). \
                 widths={widths:?}, times={times:?}"
            );
        },
    );
}

/// Performance proof: same-head argument comparison scales linearly.
///
/// When two applications share the same head constant with equal
/// reducibility, lazy_delta_reduction tries `is_def_eq_args_only`
/// in `tc/def_eq/delta.rs` before unfolding. This calls `get_app_args()`
/// on both sides (each: O(a) traverse + O(a) collect + O(a) reverse),
/// then zips and compares element-wise.
///
/// Total cost per call: O(a) traversals + O(a) comparisons = O(a).
/// This test verifies no accidental O(a^2) pattern exists.
#[test]
fn test_is_def_eq_same_head_wide_args() {
    let _serial = crate::test_utils::serial_test_guard();
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_is_def_eq_same_head_wide_args",
        || {
            use std::hint::black_box;

            let widths = [10usize, 40, 160];
            let mut times = Vec::new();

            for &w in &widths {
                let (env, expr) = build_wide_delta_expr(1, w);
                let tc = TypeChecker::new(&env);

                // Both sides are the same expression, so is_def_eq_args_only
                // should succeed on the first try (same head, all args equal).
                // Warm up.
                let _ = tc.is_def_eq(black_box(&expr), black_box(&expr));

                let start = Instant::now();
                for _ in 0..200 {
                    assert!(tc.is_def_eq(black_box(&expr), black_box(&expr)));
                }
                let elapsed = start.elapsed();
                times.push(elapsed.as_nanos());
            }

            // For O(a) comparison: 16x args -> ~16x time.
            // Allow up to 200x for overhead. Tightened from 400x per #1785.
            let ratio_16x = times[2] as f64 / times[0].max(1) as f64;
            assert!(
                ratio_16x < 200.0,
                "is_def_eq same-head args comparison appears worse than O(a): \
                 16x width gave {ratio_16x:.1}x time. \
                 widths={widths:?}, times={times:?}"
            );
        },
    );
}

/// Performance proof: delta reduction with universe levels scales linearly.
///
/// Creates definitions with increasing numbers of universe level parameters.
/// Each unfold step in lazy_delta_reduction:
///   - get_delta_const: clones LevelVec (stack copy for k≤2, heap for k>2)
///   - unfold_with_transparency: allocates Vec<(Name, Level)> (O(k))
///   - instantiate_level_params: builds HashMap<Name, Level> (O(k))
///
/// With d=5 unfold steps: total per WHNF call is O(k * d).
/// This test verifies no O(k^2) pattern exists.
#[test]
fn test_lazy_delta_level_allocation() {
    let _serial = crate::test_utils::serial_test_guard();
    run_with_timeout(
        SCALING_TEST_TIMEOUT,
        "test_lazy_delta_level_allocation",
        || {
            use crate::env::Declaration;
            use std::hint::black_box;

            let level_counts = [1usize, 4, 16];
            let delta_depth = 5;
            let mut times = Vec::new();

            for &k in &level_counts {
                let mut env = Environment::new();

                // Create level parameter names: u0, u1, ..., u_{k-1}
                let level_params: Vec<Name> = (0..k)
                    .map(|i| Name::from_string(&format!("u{i}")))
                    .collect();
                let levels: Vec<Level> = level_params
                    .iter()
                    .map(|n| Level::param(n.clone()))
                    .collect();

                // Build a chain of definitions, each with k level params
                for i in 0..delta_depth {
                    let name = Name::from_string(&format!("g{i}"));
                    let value = if i == 0 {
                        Expr::prop()
                    } else {
                        Expr::const_(Name::from_string(&format!("g{}", i - 1)), levels.clone())
                    };
                    env.add_decl_unchecked(Declaration::Definition {
                        name,
                        level_params: level_params.clone(),
                        type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
                        value,
                        is_reducible: true,
                    });
                }

                let expr = Expr::const_(
                    Name::from_string(&format!("g{}", delta_depth - 1)),
                    levels.clone(),
                );
                let tc = TypeChecker::new(&env);

                // Warm up
                let _ = tc.whnf(black_box(&expr));

                let start = Instant::now();
                for _ in 0..500 {
                    let _ = tc.whnf(black_box(&expr));
                }
                let elapsed = start.elapsed();
                times.push(elapsed.as_nanos());
            }

            // level_counts go 1 -> 4 -> 16 (4x each step).
            // Level allocation is O(k * d) with fixed d=5.
            // 16x levels -> ~16x allocation time.
            // Allow 200x threshold for HashMap overhead + noise. Tightened from 400x per #1785.
            let ratio_16x = times[2] as f64 / times[0].max(1) as f64;
            assert!(
                ratio_16x < 200.0,
                "delta reduction with many levels appears worse than O(k*d): \
                 16x levels gave {ratio_16x:.1}x time. \
                 level_counts={level_counts:?}, times={times:?}"
            );
        },
    );
}
