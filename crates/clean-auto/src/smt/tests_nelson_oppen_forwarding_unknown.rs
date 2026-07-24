// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused Nelson-Oppen forwarding-Unknown regression (#2386, #2366).

use super::*;
use crate::cdcl::Lit;
use std::any::Any;
use std::sync::Arc;

/// Regression test: `Unknown` from `assert_shared_equality` must propagate.
///
/// This isolates the forwarding path itself. The peer theory stays
/// `Consistent` for direct `assert_literal` calls, but returns `Unknown`
/// only when it receives a shared equality through Nelson-Oppen forwarding.
/// The solver must bubble that incompleteness up as `SmtResult::Unknown`.
#[test]
fn test_unknown_from_forwarded_shared_equality_propagates() {
    struct DeducingTheory {
        pair: (TermId, TermId),
        emitted: bool,
    }

    impl TheorySolver for DeducingTheory {
        fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn backtrack(&mut self, _level: u32) {
            self.emitted = false;
        }

        fn push(&mut self) {}

        fn name(&self) -> &'static str {
            "ForwardingSource"
        }

        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

        fn drain_deduced_equalities(&mut self) -> Vec<(TermId, TermId, Vec<Lit>)> {
            if !self.emitted {
                self.emitted = true;
                vec![(self.pair.0, self.pair.1, vec![])]
            } else {
                Vec::new()
            }
        }

        fn as_any(&self) -> &dyn Any {
            self
        }

        fn as_any_mut(&mut self) -> &mut dyn Any {
            self
        }
    }

    struct UnknownOnSharedTheory;

    impl TheorySolver for UnknownOnSharedTheory {
        fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn assert_shared_equality(
            &mut self,
            _t1: TermId,
            _t2: TermId,
            _reason: Lit,
        ) -> TheoryCheckResult {
            TheoryCheckResult::Unknown
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn backtrack(&mut self, _level: u32) {}

        fn push(&mut self) {}

        fn name(&self) -> &'static str {
            "UnknownOnShared"
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
    let a = smt.const_term("a");
    let b = smt.const_term("b");

    smt.add_theory(Box::new(DeducingTheory {
        pair: (a, b),
        emitted: false,
    }));
    smt.add_theory(Box::new(UnknownOnSharedTheory));

    match smt.solve() {
        SmtResult::Unknown => {}
        SmtResult::Sat(_) => {
            panic!(
                "Expected Unknown when a peer theory returns Unknown from \
                 assert_shared_equality. Forwarded incompleteness is being \
                 dropped inside Nelson-Oppen propagation."
            );
        }
        SmtResult::Unsat(_) => {
            panic!(
                "Expected Unknown, got Unsat — shared-equality forwarding \
                 incompleteness should not fabricate a contradiction."
            );
        }
    }
}
