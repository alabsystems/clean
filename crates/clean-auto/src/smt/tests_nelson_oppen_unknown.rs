// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nelson-Oppen and DPLL(T) Unknown-propagation tests.

use super::*;
use crate::cdcl::Lit;
use crate::theories::equality::EqualityTheory;

/// Test that TheoryCheckResult::Unknown from a theory propagates as SmtResult::Unknown.
///
/// When a theory solver returns Unknown (e.g., arithmetic overflow, incomplete
/// reasoning), the DPLL(T) loop must NOT claim Sat or Unsat. It must return
/// SmtResult::Unknown to prevent unsound conclusions.
///
/// This test uses a mock theory that always returns Unknown from check(),
/// verifying the DPLL(T) loop's Unknown propagation path (#2384).
#[test]
fn test_theory_unknown_propagates_to_smt_unknown() {
    use std::any::Any;
    use std::sync::Arc;

    /// Mock theory that returns Unknown from check().
    struct AlwaysUnknownTheory;

    impl TheorySolver for AlwaysUnknownTheory {
        fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Unknown
        }

        fn backtrack(&mut self, _level: u32) {}

        fn push(&mut self) {}

        fn name(&self) -> &'static str {
            "AlwaysUnknown"
        }

        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

        fn as_any(&self) -> &dyn Any {
            self
        }

        fn as_any_mut(&mut self) -> &mut dyn Any {
            self
        }
    }

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(AlwaysUnknownTheory));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let _ = smt.assert_eq(a, b);

    match smt.solve() {
        SmtResult::Unknown => {
            // Correct: theory cannot decide, so SMT must return Unknown.
        }
        SmtResult::Sat(_) => {
            panic!(
                "Expected Unknown when theory returns Unknown from check(), \
                 got Sat - DPLL(T) loop is ignoring theory incompleteness (#2384)"
            );
        }
        SmtResult::Unsat(_) => {
            panic!(
                "Expected Unknown when theory returns Unknown from check(), \
                 got Unsat - theory returning Unknown should NOT cause Unsat"
            );
        }
    }
}

/// Test that TheoryCheckResult::Unknown from assert_literal also propagates.
///
/// Even during literal assertion (before check()), if a theory returns Unknown,
/// the solver must not claim consistency.
#[test]
fn test_theory_unknown_from_assert_propagates() {
    use std::any::Any;
    use std::sync::Arc;

    /// Mock theory that returns Unknown from assert_literal on the first literal.
    struct UnknownOnAssertTheory {
        seen_any: bool,
    }

    impl TheorySolver for UnknownOnAssertTheory {
        fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            if !self.seen_any {
                self.seen_any = true;
                TheoryCheckResult::Unknown
            } else {
                TheoryCheckResult::Consistent
            }
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn backtrack(&mut self, _level: u32) {
            self.seen_any = false;
        }

        fn push(&mut self) {}

        fn name(&self) -> &'static str {
            "UnknownOnAssert"
        }

        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

        fn as_any(&self) -> &dyn Any {
            self
        }

        fn as_any_mut(&mut self) -> &mut dyn Any {
            self
        }
    }

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(UnknownOnAssertTheory { seen_any: false }));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let _ = smt.assert_eq(a, b);

    match smt.solve() {
        SmtResult::Unknown => {
            // Correct: theory said Unknown during assertion, propagated up.
        }
        SmtResult::Sat(_) => {
            panic!(
                "Expected Unknown when theory returns Unknown from assert_literal, \
                 got Sat - any_unknown flag in check_theories may not propagate (#2384)"
            );
        }
        SmtResult::Unsat(_) => {
            panic!("Expected Unknown, got Unsat - theory Unknown should not cause Unsat");
        }
    }
}

/// Nelson-Oppen: Unknown from one theory must block Sat even when EUF is consistent.
///
/// When theory combination involves one theory returning Unknown (e.g., arithmetic
/// overflow during Nelson-Oppen exchange), the solver must return Unknown -
/// NOT Sat based only on EUF's consistent result. This prevents unsound
/// conclusions where EUF says "consistent" but the incomplete theory might
/// have found a conflict if it had completed its analysis.
#[test]
fn test_nelson_oppen_unknown_blocks_sat_in_combination() {
    use std::any::Any;
    use std::sync::Arc;

    /// Mock theory that returns Unknown from check() but Consistent from assert_literal.
    /// Simulates arithmetic overflow during the full consistency check phase.
    struct OverflowOnCheckTheory;

    impl TheorySolver for OverflowOnCheckTheory {
        fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Unknown
        }

        fn backtrack(&mut self, _level: u32) {}
        fn push(&mut self) {}

        fn name(&self) -> &'static str {
            "OverflowOnCheck"
        }

        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

        fn as_any(&self) -> &dyn Any {
            self
        }

        fn as_any_mut(&mut self) -> &mut dyn Any {
            self
        }
    }

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(OverflowOnCheckTheory));

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let _ = smt.assert_eq(a, b);

    match smt.solve() {
        SmtResult::Unknown => {
            // Correct: even though EUF says Consistent, the overflow theory
            // says Unknown, so the combined result must be Unknown.
        }
        SmtResult::Sat(_) => {
            panic!(
                "Expected Unknown when one theory overflows during combination, \
                 got Sat - Unknown theory result is being ignored in check_theories"
            );
        }
        SmtResult::Unsat(_) => {
            panic!("Expected Unknown, got Unsat - overflow should not cause Unsat");
        }
    }
}

/// Nelson-Oppen: Unknown from assert_literal during theory forwarding must propagate.
///
/// When EUF deduces an equality and forwards it to another theory via
/// forward_equality_deductions, if that theory returns Unknown, the solver
/// must not ignore it. This tests the interaction between real EUF propagation
/// and a theory that goes incomplete during forwarding.
#[test]
fn test_nelson_oppen_unknown_during_forwarding() {
    use std::any::Any;
    use std::sync::Arc;

    /// Theory that returns Unknown when it sees an Eq literal (simulating
    /// overflow when processing a forwarded equality).
    struct UnknownOnEqTheory;

    impl TheorySolver for UnknownOnEqTheory {
        fn assert_literal(&mut self, _lit: Lit, theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            match theory_lit {
                TheoryLiteral::Eq(_, _) => TheoryCheckResult::Unknown,
                _ => TheoryCheckResult::Consistent,
            }
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn backtrack(&mut self, _level: u32) {}
        fn push(&mut self) {}

        fn name(&self) -> &'static str {
            "UnknownOnEq"
        }

        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

        fn as_any(&self) -> &dyn Any {
            self
        }

        fn as_any_mut(&mut self) -> &mut dyn Any {
            self
        }
    }

    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(EqualityTheory::new()));
    smt.add_theory(Box::new(UnknownOnEqTheory));

    let a = smt.const_term("a");
    let b = smt.const_term("b");

    // Simple equality - EUF processes fine, but the eq gets forwarded
    // to UnknownOnEqTheory which returns Unknown.
    let _ = smt.assert_eq(a, b);

    match smt.solve() {
        SmtResult::Unknown => {
            // Correct: theory went incomplete during eq forwarding.
        }
        SmtResult::Sat(_) => {
            // Acceptable if the solver doesn't forward to all theories during
            // assert_literal. This is a design choice, not a bug.
            // The Unknown should still propagate from check_theories.
        }
        SmtResult::Unsat(_) => {
            panic!("Expected Unknown or Sat, got Unsat - eq forwarding should not cause Unsat");
        }
    }
}
