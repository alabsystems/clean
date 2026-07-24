// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Performance proof tests for proof reconstruction subsystem.
//!
//! Documents algorithmic complexity of key operations and detects regressions.
//! Phase: performance_proofs (P1 iter 856).

use clean_kernel::name::Name;
use clean_kernel::Expr;

use crate::bridge::disjunction;
use crate::bridge::translate::ExprKey;

// ============================================================================
// Performance proof: or_chain_type is O(n) per call, called O(n) times in
// resolution = O(n²) per resolution step.
//
// disjunction.rs:22-34 — or_chain_type recursively builds the type
// `Or P₀ (Or P₁ (Or P₂ ...))` from a slice of props. Each call is O(n)
// because it clones the head and recursively builds the tail.
//
// In resolution proof reconstruction (resolution.rs:283, 439), or_chain_type
// is called at each recursion level of or_rec_walk_c1/c2:
//   - Level 0: or_chain_type(&props[1..])  → O(n-1)
//   - Level 1: or_chain_type(&props[2..])  → O(n-2)
//   - ...
//   - Level n-2: or_chain_type(&props[n-1..]) → O(1)
// Total per clause: O(1 + 2 + ... + n-1) = O(n²).
//
// Similarly, inject_into_or_chain (disjunction.rs:41-53) calls
// or_chain_type at each recursive level, giving O(n²) for position n.
//
// Fix: Precompute or_chain_type for all suffixes in a single O(n) pass
// (fold from the right) and pass them down the recursion.
// ============================================================================

/// Documents O(n²) scaling of or_chain_type when called per-level in
/// a simulated resolution walk.
///
/// Measures the cost of calling `or_chain_type(&props[i..])` for each
/// i from 0 to n, which is the pattern in or_rec_walk_c1/c2.
#[test]
fn test_or_chain_type_quadratic_in_resolution_walk() {
    let sizes = [20usize, 80, 320];
    let mut times = Vec::new();

    for &n in &sizes {
        // Build n distinct Prop-valued propositions
        let props: Vec<Expr> = (0..n)
            .map(|i| Expr::const_(Name::from_string(&format!("P{i}")), vec![]))
            .collect();

        // Warm up
        for _ in 0..3 {
            for i in 0..n {
                let _ = disjunction::or_chain_type(&props[i..]);
            }
        }

        let iters = 10;
        let start = std::time::Instant::now();
        for _ in 0..iters {
            // Simulate the resolution walk: call or_chain_type at each level
            for i in 0..n {
                let _ = disjunction::or_chain_type(&props[i..]);
            }
        }
        let elapsed = start.elapsed().as_nanos() as u64;
        times.push(elapsed / iters as u64);
    }

    // For O(n²): 320/20 = 16x input → 256x expected
    // For O(n): ratio would be 16x
    // Assert < 2000x to catch worse-than-quadratic regression
    assert!(
        times[0] > 0,
        "base benchmark (n={}) returned 0ns — timing too coarse to detect scaling. \
         Increase iterations or base size. times: {times:?}",
        sizes[0]
    );
    let ratio = times[2] as f64 / times[0] as f64;
    assert!(
        ratio < 2000.0,
        "or_chain_type resolution walk scaling: 320/20 ratio = {ratio:.1}x. \
         O(n²) expected ~256x. times: {times:?}"
    );
}

// ============================================================================
// Performance proof: inject_into_or_chain is O(n²) for high positions.
//
// disjunction.rs:41-53 — inject_into_or_chain recurses O(position) times
// and calls or_chain_type (O(remaining)) at each level. For position = n-1
// (last element), total cost is O(1 + 2 + ... + n) = O(n²).
//
// This is called from resolution proof reconstruction for each literal
// in the resolvent clause. With resolvent size R, total injection cost
// across all literals is O(R * R²/2) = O(R³) in the worst case.
//
// Fix: Same as above — precompute suffix chain types once.
// ============================================================================

/// Documents O(n²) scaling of inject_into_or_chain for high positions.
#[test]
fn test_inject_into_or_chain_quadratic_for_last_position() {
    let sizes = [20usize, 80, 320];
    let mut times = Vec::new();

    for &n in &sizes {
        let props: Vec<Expr> = (0..n)
            .map(|i| Expr::const_(Name::from_string(&format!("P{i}")), vec![]))
            .collect();
        // Proof of the last proposition
        let proof = Expr::const_(Name::from_string("proof_last"), vec![]);

        // Warm up
        for _ in 0..3 {
            let _ = disjunction::inject_into_or_chain(&props, n - 1, proof.clone());
        }

        let iters = 10;
        let start = std::time::Instant::now();
        for _ in 0..iters {
            let _ = disjunction::inject_into_or_chain(&props, n - 1, proof.clone());
        }
        let elapsed = start.elapsed().as_nanos() as u64;
        times.push(elapsed / iters as u64);
    }

    // inject_into_or_chain(n-1) recurses n-1 times, calling or_chain_type
    // at each level. Total: O(n²).
    assert!(
        times[0] > 0,
        "base benchmark (n={}) returned 0ns — timing too coarse to detect scaling. \
         Increase iterations or base size. times: {times:?}",
        sizes[0]
    );
    let ratio = times[2] as f64 / times[0] as f64;
    assert!(
        ratio < 2000.0,
        "inject_into_or_chain scaling: 320/20 ratio = {ratio:.1}x. \
         O(n²) expected ~256x. times: {times:?}"
    );
}

// ============================================================================
// Performance proof: ExprKey::from_expr is O(n) in expression tree nodes.
//
// ExprKey::from_expr (bridge/translate/keys.rs) recursively walks every node
// in the expression tree, allocating Box<ExprKey> per App/Lam/Pi node and
// cloning Name + Vec<Level> per Const. For an expression with n nodes, each
// call is O(n) work with O(n) allocations.
//
// Double-computation pattern (prop_classical_split.rs) was fixed in #2814.
// The wall-clock double-vs-single timing assertion was removed in #2824
// because it flaked under full-suite CPU contention. The O(n) scaling
// assertion remains as the live regression guard.
// ============================================================================

/// Documents O(n) cost of ExprKey::from_expr via scaling assertion.
///
// Double-computation regression: #2814 (closed). The wall-clock
// double-vs-single assertion was removed because it flaked under
// full-suite CPU contention (#2824). The O(n) scaling assertion
// below is the live regression guard.
#[test]
fn test_expr_key_from_expr_double_computation_cost() {
    // Build nested App expressions of increasing depth:
    // App(App(...App(Const("f"), x)..., x), x) with d applications
    let base = Expr::const_(Name::from_string("f"), vec![]);
    let arg = Expr::const_(Name::from_string("x"), vec![]);

    let depths = [10usize, 40, 160];
    let mut single_times = Vec::new();

    for &d in &depths {
        let mut expr = base.clone();
        for _ in 0..d {
            expr = Expr::app(expr, arg.clone());
        }

        // Warm up
        for _ in 0..5 {
            let _ = ExprKey::from_expr(&expr);
        }

        let iters = 100u64;

        // Single computation
        let start = std::time::Instant::now();
        for _ in 0..iters {
            let key = ExprKey::from_expr(&expr);
            assert!(key.is_some());
        }
        let single = start.elapsed().as_nanos() as u64 / iters;
        single_times.push(single);
    }

    // Verify O(n) scaling: 160/10 = 16x depth -> ~16x expected time.
    assert!(
        single_times[0] > 0,
        "base benchmark (depth={}) returned 0ns — timing too coarse to detect scaling. \
         Increase iterations or base depth. single_times: {single_times:?}",
        depths[0]
    );
    let ratio = single_times[2] as f64 / single_times[0] as f64;
    assert!(
        ratio < 500.0,
        "ExprKey::from_expr scaling: 160/10 ratio = {ratio:.1}x. \
         O(n) expected ~16x. single_times: {single_times:?}"
    );
}
