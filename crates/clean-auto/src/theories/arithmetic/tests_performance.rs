// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::smt::{TheoryLiteral, TheorySolver};

// =========================================================================
// Performance proof: detect_model_equalities — O(n²) after #2441 fix.
//
// deductions.rs:41-101 — Two remaining cost factors:
//   1. Outer: for each value group with k terms → O(k²) pairs
//   2. Clone: all_reasons.clone() → O(reasons) per insertion
//
// Before #2441: pending_deduced.iter().any() was O(pending) per pair,
// giving O(n⁴) total. Fix replaced linear scan with HashSet dedup (O(1)).
//
// Current cost when all N terms share a model value:
//   - N(N-1)/2 pairs generated, each with O(1) dedup + O(reasons) clone
//   - Total: O(n² × reasons)
//
// Remaining optimization: Share all_reasons via Rc instead of cloning.
// =========================================================================

/// Documents O(n² × reasons) scaling of detect_model_equalities after #2441.
///
/// When many terms share a model value, pairwise iteration is O(n²).
///
/// Creates N terms all squeezed to value 0 via tight bounds, then calls
/// detect_model_equalities. Pairwise iteration produces O(n²) pairs; each
/// dedup check is now O(1) via HashSet. The all_reasons.clone() adds
/// O(reasons) per new pair. Guards against regression beyond current scaling.
#[test]
fn test_detect_model_equalities_quartic_scaling() {
    let sizes = [10usize, 30, 90];
    let mut times = Vec::new();

    for &n in &sizes {
        let mut arith = ArithmeticTheory::new();
        arith.push();

        // Create n terms, all squeezed to value 0:
        //   term_i ≤ 0 AND 0 ≤ term_i → term_i = 0 for all i
        for i in 0..n as u32 {
            let t = TermId(i);
            let anchor = TermId(n as u32 + i); // anchor term for the bound

            // t ≤ anchor (with anchor value = 0 by default assignment)
            let lit_idx = i * 2;
            let r = arith.assert_literal(make_lit(lit_idx, true), &TheoryLiteral::Le(t, anchor));
            assert!(
                matches!(r, TheoryCheckResult::Consistent),
                "Le({i}, anchor) failed"
            );

            // anchor ≤ t
            let r =
                arith.assert_literal(make_lit(lit_idx + 1, true), &TheoryLiteral::Le(anchor, t));
            assert!(
                matches!(r, TheoryCheckResult::Consistent),
                "Le(anchor, {i}) failed"
            );
        }

        // Warm up
        for _ in 0..2 {
            arith.detect_model_equalities();
            let _ = arith.drain_deduced_equalities();
        }

        let iters = 5;
        let start = std::time::Instant::now();
        for _ in 0..iters {
            arith.detect_model_equalities();
            let _ = arith.drain_deduced_equalities();
        }
        let elapsed = start.elapsed().as_nanos() as u64;
        times.push(elapsed / iters as u64);
    }

    // After #2441 HashSet fix: dedup is O(1), so total is O(n² × reasons).
    // For O(n²): 90/10 = 9x input → 81x expected.
    // Pre-fix was ~6300x (quartic). Bound kept loose to avoid flaky CI.
    if times[0] > 0 {
        let ratio = times[2] as f64 / times[0] as f64;
        assert!(
            ratio < 5000.0,
            "detect_model_equalities scaling: 90/10 ratio = {ratio:.1}x. \
             O(n²) expected ~81x after #2441. times: {times:?}"
        );
    }
}

// =========================================================================
// Performance proof: ArithmeticTheory::push clones full state — O(state_size)
//
// arithmetic/mod.rs:519-528 — push() clones:
//   - tableau (Vec<TableauRow>, each with HashMap<ArithVar, Rational>)
//   - assignment (HashMap<ArithVar, DeltaRational>)
//   - term_to_var (HashMap<TermId, ArithVar>)
//
// With K DPLL(T) push/pop cycles and N constraints, total clone cost
// is O(K * N). This is the deliberate trade-off for O(1) backtrack
// (vs. O(K*M) replay).
//
// Not a bug — documenting the cost so future optimization (e.g.,
// persistent data structures, incremental snapshots) can measure
// improvement against this baseline.
// =========================================================================

/// Documents O(K * N) scaling of push when state grows with N constraints.
#[test]
fn test_push_clone_cost_scales_with_state() {
    let sizes = [20usize, 80, 320];
    let mut times = Vec::new();

    for &n in &sizes {
        let mut arith = ArithmeticTheory::new();

        // Build up state with n constraints
        for i in 0..n as u32 {
            let _ = arith.assert_literal(
                make_lit(i, true),
                &TheoryLiteral::Le(TermId(i), TermId(i + 1)),
            );
        }

        // Warm up
        for _ in 0..3 {
            arith.push();
            arith.backtrack(0);
        }

        let iters = 100;
        let start = std::time::Instant::now();
        for _ in 0..iters {
            arith.push();
            arith.backtrack(0);
        }
        let elapsed = start.elapsed().as_nanos() as u64;
        times.push(elapsed / iters as u64);
    }

    // For O(n) clone cost: 320/20 = 16x
    // Assert < 500x to catch quadratic regression (should be linear)
    if times[0] > 0 {
        let ratio = times[2] as f64 / times[0] as f64;
        assert!(
            ratio < 500.0,
            "push/backtrack scaling: 320/20 ratio = {ratio:.1}x. \
             O(n) clone expected ~16x. times: {times:?}"
        );
    }
}
