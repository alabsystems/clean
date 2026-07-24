// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#[path = "tests_core.rs"]
mod tests_core;
#[path = "tests_regressions.rs"]
mod tests_regressions;
#[path = "tests_reset.rs"]
mod tests_reset;

use super::*;
use crate::cdcl::{Lit, Var};
use crate::egraph::Symbol;
use crate::smt::{SmtTerm, TermId, TheoryCheckResult, TheoryLiteral, TheorySolver};

fn make_lit(var_idx: u32, positive: bool) -> Lit {
    let var = Var::new(var_idx);
    if positive {
        Lit::pos(var)
    } else {
        Lit::neg(var)
    }
}

/// Performance proof: `recompute_array_term_closure` runs a fixed-point
/// loop over ALL equalities and disequalities on EVERY `assert_literal`.
///
/// In `inference.rs` (lines 18-35):
///
///     loop {
///         for &(t1, t2, _) in self.equalities.iter().chain(self.disequalities.iter()) {
///             // HashSet::contains + insert per entry
///         }
///         if !changed { break; }
///     }
///
/// Called from `refresh_extensionality_requests()` which is called on every
/// `assert_literal` (lines 149, 165 of `theory.rs`). Each pass is O(E + D)
/// where E = equalities, D = disequalities. The loop runs up to T times
/// (T = new terms discovered per pass). Total per assertion: O(T * (E + D)).
/// Over M assertions: O(M * T * (E + D)).
///
/// A worklist/BFS approach would reduce per-assertion cost to O(new_terms)
/// instead of scanning all equalities.
///
/// This test documents the quadratic cost and catches regressions.
///
/// Regression test for performance_proofs P1 iter 1230.
#[test]
fn test_recompute_array_term_closure_scaling() {
    use std::time::Instant;

    // Build an array theory with S structural array terms and then assert
    // E equalities, each triggering recompute_array_term_closure.
    let measure = |n: u32| -> u128 {
        let mut theory = ArrayTheory::new();

        // Create terms: n array constants, n index constants, n value constants,
        // n select operations, n store operations.
        // Total = 5n terms.
        let mut terms = Vec::new();
        for i in 0..n {
            terms.push(SmtTerm::Const(Symbol::new(format!("arr{i}"))));
        }
        for i in 0..n {
            terms.push(SmtTerm::Const(Symbol::new(format!("idx{i}"))));
        }
        for i in 0..n {
            terms.push(SmtTerm::Const(Symbol::new(format!("val{i}"))));
        }
        // select(arr_i, idx_i)
        for i in 0..n {
            let arr = TermId(i);
            let idx = TermId(n + i);
            terms.push(SmtTerm::App(Symbol::new("select"), vec![arr, idx]));
        }
        // store(arr_i, idx_i, val_i)
        for i in 0..n {
            let arr = TermId(i);
            let idx = TermId(n + i);
            let val = TermId(2 * n + i);
            terms.push(SmtTerm::App(Symbol::new("store"), vec![arr, idx, val]));
        }
        theory.set_terms(terms);

        // Assert n equalities between array constants: arr_0 = arr_1, arr_1 = arr_2, ...
        // Each triggers recompute_array_term_closure scanning all accumulated eqs.
        let start = Instant::now();
        for i in 0..(n - 1) {
            let lit = make_lit(i, true);
            let t1 = TermId(i);
            let t2 = TermId(i + 1);
            let _ = theory.assert_literal(lit, &TheoryLiteral::Eq(t1, t2));
        }
        start.elapsed().as_nanos()
    };

    let t_small = measure(10);
    let t_large = measure(50);

    // 5x input: each assertion scans all prior equalities -> O(E^2) total.
    // Expected ratio: ~25x for quadratic, ~5x for linear.
    let ratio = t_large as f64 / t_small.max(1) as f64;
    eprintln!(
        "recompute_array_term_closure: 5x input gave {ratio:.1}x time \
         (small={t_small}ns, large={t_large}ns)"
    );
    // Generous threshold: allow up to 500x for quadratic + constant overhead.
    assert!(
        ratio < 500.0,
        "recompute_array_term_closure scaling: 5x input gave {ratio:.1}x time \
         (expected <500x; catastrophic regression)"
    );
}
