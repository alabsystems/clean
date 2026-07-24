// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scaling tests for level.rs performance (#1110)
//!
//! These tests verify that is_geq and other level operations scale
//! reasonably on deeply nested IMax expressions.

#[cfg(test)]
mod tests {
    use crate::level::Level;
    use crate::name::Name;
    use std::time::Instant;

    /// Build a deeply nested IMax: imax(p1, imax(p2, imax(p3, ...)))
    fn build_nested_imax(depth: usize) -> Level {
        let mut level = Level::succ(Level::zero()); // Start with 1 (nonzero, triggers reduction)
        for i in 0..depth {
            let param = Level::Param(Name::from_string(&format!("p{i}")));
            level = Level::imax(param, level);
        }
        level
    }

    #[test]
    fn test_is_geq_imax_scaling() {
        let _serial = crate::test_utils::serial_test_guard();
        // Part of #1110: Verify is_geq scales reasonably on nested IMax levels.
        // The current impl clones when reducing imax(a,b) to max(a,b), which
        // can cause memory pressure on deeply nested expressions.

        // Test sizes: 10, 40, 160 depth
        let sizes = [10usize, 40, 160];
        let mut times = Vec::new();

        for &n in &sizes {
            let l1 = build_nested_imax(n);
            let l2 = Level::succ(Level::zero()); // Compare against 1

            // Warm up
            let _ = Level::is_geq(&l1, &l2);

            let start = Instant::now();
            // Multiple iterations for stable timing
            for _ in 0..100 {
                let _ = Level::is_geq(&l1, &l2);
            }
            let elapsed = start.elapsed();
            times.push(elapsed.as_nanos());
        }

        // For is_geq with IMax reduction:
        // If clone-based, each level of nesting creates 2 clones
        // This could be O(2^n) in worst case, but with memoization/short-circuit
        // it should be closer to linear.
        //
        // Threshold 100x for 16x input catches both:
        // - O(n^2) behavior (which gives 256x)
        // - Exponential blowup (which gives >> 256x)
        // while allowing generous margin for linear behavior with noise.
        let ratio = times[2] as f64 / times[0] as f64;
        assert!(
            ratio < 100.0,
            "is_geq on nested IMax shows poor scaling: 16x input gave {ratio:.1}x time"
        );
    }

    #[test]
    fn test_is_geq_imax_correctness() {
        // Verify correctness: nested imax with nonzero should be >= 1
        let l1 = build_nested_imax(10);
        let l2 = Level::succ(Level::zero()); // 1
        assert!(
            Level::is_geq(&l1, &l2),
            "imax with nonzero component should be >= 1"
        );
    }
}
