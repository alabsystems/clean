// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{SmtResult, SmtSolver, TermId, TheoryCheckResult, TheoryLiteral, TheorySolver};
use crate::cdcl::Lit;
use crate::smt::SmtTerm;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Arc;

/// Verify that `solve()` replays SAT decisions through `push()` and uses
/// `reset()` for teardown between DPLL(T) attempts (#2371).
#[test]
fn test_solve_uses_scoped_pushes_and_reset_hook() {
    struct ResetTrackingTheory {
        push_calls: Arc<AtomicU32>,
        reset_calls: Arc<AtomicU32>,
        backtrack_calls: Arc<AtomicU32>,
    }

    impl TheorySolver for ResetTrackingTheory {
        fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn backtrack(&mut self, _level: u32) {
            self.backtrack_calls.fetch_add(1, Ordering::Relaxed);
        }

        fn push(&mut self) {
            self.push_calls.fetch_add(1, Ordering::Relaxed);
        }

        fn name(&self) -> &'static str {
            "ResetTracking"
        }

        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

        fn reset(&mut self) {
            self.reset_calls.fetch_add(1, Ordering::Relaxed);
        }

        fn as_any(&self) -> &dyn std::any::Any {
            self
        }

        fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
            self
        }
    }

    let push_calls = Arc::new(AtomicU32::new(0));
    let reset_calls = Arc::new(AtomicU32::new(0));
    let backtrack_calls = Arc::new(AtomicU32::new(0));

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(ResetTrackingTheory {
        push_calls: Arc::clone(&push_calls),
        reset_calls: Arc::clone(&reset_calls),
        backtrack_calls: Arc::clone(&backtrack_calls),
    }));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");
    let _ = smt.add_clause(vec![TheoryLiteral::Eq(a, b), TheoryLiteral::Eq(b, c)]);

    let result = smt.solve();
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "expected SAT for standalone reset-tracking theory"
    );
    assert_eq!(
        reset_calls.load(Ordering::Relaxed),
        2,
        "solve() should reset theories once before replay and once after the model check"
    );
    assert!(
        push_calls.load(Ordering::Relaxed) >= 1,
        "SAT decisions should advance theory scopes with push()"
    );
    assert_eq!(
        backtrack_calls.load(Ordering::Relaxed),
        1,
        "the production path should backtrack scoped theory assignments to level 0 before reset()"
    );
}

/// Verify that the production DPLL(T) path tears down with `reset()` even if a
/// theory overrides `soft_reset()` (#2371).
#[test]
fn test_solve_does_not_use_soft_reset_for_theory_teardown() {
    struct SoftResetTrackingTheory {
        push_calls: Arc<AtomicU32>,
        soft_reset_calls: Arc<AtomicU32>,
        reset_calls: Arc<AtomicU32>,
        backtrack_calls: Arc<AtomicU32>,
    }

    impl TheorySolver for SoftResetTrackingTheory {
        fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn backtrack(&mut self, _level: u32) {
            self.backtrack_calls.fetch_add(1, Ordering::Relaxed);
        }

        fn push(&mut self) {
            self.push_calls.fetch_add(1, Ordering::Relaxed);
        }

        fn name(&self) -> &'static str {
            "SoftResetTracking"
        }

        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

        fn reset(&mut self) {
            self.reset_calls.fetch_add(1, Ordering::Relaxed);
        }

        fn soft_reset(&mut self) {
            self.soft_reset_calls.fetch_add(1, Ordering::Relaxed);
        }

        fn as_any(&self) -> &dyn std::any::Any {
            self
        }

        fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
            self
        }
    }

    let push_calls = Arc::new(AtomicU32::new(0));
    let soft_reset_calls = Arc::new(AtomicU32::new(0));
    let reset_calls = Arc::new(AtomicU32::new(0));
    let backtrack_calls = Arc::new(AtomicU32::new(0));

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(SoftResetTrackingTheory {
        push_calls: Arc::clone(&push_calls),
        soft_reset_calls: Arc::clone(&soft_reset_calls),
        reset_calls: Arc::clone(&reset_calls),
        backtrack_calls: Arc::clone(&backtrack_calls),
    }));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");
    let _ = smt.add_clause(vec![TheoryLiteral::Eq(a, b), TheoryLiteral::Eq(b, c)]);

    let result = smt.solve();
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "expected SAT for standalone soft-reset-tracking theory"
    );
    assert_eq!(
        reset_calls.load(Ordering::Relaxed),
        2,
        "solve() should use reset() before and after the scoped SAT-trail replay"
    );
    assert!(
        push_calls.load(Ordering::Relaxed) >= 1,
        "SAT decisions should still drive push() even when soft_reset() is overridden"
    );
    assert_eq!(
        soft_reset_calls.load(Ordering::Relaxed),
        0,
        "the production path should not call soft_reset() anymore"
    );
    assert_eq!(
        backtrack_calls.load(Ordering::Relaxed),
        1,
        "the production path should still unwind scoped levels via backtrack(0) before reset()"
    );
}

/// Demonstrates that the default `TheorySolver::reset()` → `backtrack(0)` keeps
/// root-level assertions alive. This documents why stateful theories must
/// override `reset()` with explicit cleanup.
#[test]
fn test_default_reset_keeps_root_level_assertions() {
    use crate::egraph::Symbol;

    /// A theory that intentionally uses the default `reset()` delegation to
    /// `backtrack(0)`. This simulates what would happen if a new theory
    /// implementation forgot to override reset().
    struct DefaultResetTheory {
        assertion_count: u32,
    }

    impl TheorySolver for DefaultResetTheory {
        fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            self.assertion_count += 1;
            TheoryCheckResult::Consistent
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn backtrack(&mut self, _level: u32) {
            // In the default reset() path, backtrack(0) is called. A real
            // theory with `level: u32` would guard `if level >= self.level
            // { return; }` and never reach the cleanup code when self.level
            // is already 0. We simulate that by simply not clearing state.
        }

        fn push(&mut self) {}

        fn name(&self) -> &'static str {
            "DefaultReset"
        }

        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

        // reset() is NOT overridden — uses default which calls backtrack(0)

        fn as_any(&self) -> &dyn std::any::Any {
            self
        }

        fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
            self
        }
    }

    let mut theory = DefaultResetTheory { assertion_count: 0 };
    theory.set_terms(Arc::from(vec![
        SmtTerm::Const(Symbol::new("a")),
        SmtTerm::Const(Symbol::new("b")),
    ]));

    // Assert at level 0 so reset() only has root-level state to clear.
    let lit = Lit::pos(crate::cdcl::Var::new(1));
    let result = theory.assert_literal(lit, &TheoryLiteral::Eq(TermId(0), TermId(1)));
    assert!(matches!(result, TheoryCheckResult::Consistent));
    assert_eq!(theory.assertion_count, 1, "precondition: one assertion");

    // The default reset() calls backtrack(0), which keeps root-level assertions.
    theory.reset();

    assert_eq!(
        theory.assertion_count, 1,
        "default reset() via backtrack(0) keeps root-level assertions alive. \
         Production theories MUST override reset() with explicit cleanup."
    );
}
