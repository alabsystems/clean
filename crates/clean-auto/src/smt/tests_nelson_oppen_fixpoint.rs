// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nelson-Oppen generic collector and fixpoint regressions (#2366).
//!
//! Covers the trait-driven propagation surface that is independent of any
//! specific production theory implementation:
//! - name-independent deduced-equality collection
//! - same-pass multi-hop forwarding
//! - pass-cap fallback to `Unknown`

use super::*;
use crate::cdcl::Lit;
use std::any::Any;
use std::sync::Arc;

/// Regression test: theory propagation is name-independent (#2366).
///
/// A theory with a custom name (not "EUF", "Arrays", or "LRA") produces
/// deduced equalities through the trait hooks. The solver must surface
/// them as SAT propagations regardless of the theory's name — collection
/// depends on trait hooks, not string names.
#[test]
fn test_name_independent_propagation_collector() {
    struct CustomTheory {
        eq_pair: (TermId, TermId),
        drained: bool,
    }

    impl TheorySolver for CustomTheory {
        fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn backtrack(&mut self, _level: u32) {
            self.drained = false;
        }

        fn push(&mut self) {}

        fn name(&self) -> &'static str {
            "CustomBV"
        }

        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

        fn drain_deduced_equalities(&mut self) -> Vec<(TermId, TermId, Vec<Lit>)> {
            if !self.drained {
                self.drained = true;
                vec![(self.eq_pair.0, self.eq_pair.1, vec![])]
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

    let mut smt = SmtSolver::new();
    let x = smt.const_term("x");
    let y = smt.const_term("y");

    smt.add_theory(Box::new(CustomTheory {
        eq_pair: (x, y),
        drained: false,
    }));

    // Assert x != y. CustomTheory deduces x = y -> contradiction -> UNSAT.
    let _ = smt.assert_neq(x, y);

    match smt.solve() {
        SmtResult::Unsat(_) => {
            // Correct: CustomTheory (name "CustomBV") deduced x = y,
            // which contradicts x != y. Propagation works regardless
            // of theory name — this is the #2366 regression.
        }
        SmtResult::Sat(_) => {
            panic!(
                "Expected UNSAT: CustomTheory deduces x = y but x != y is asserted. \
                 Theory propagation may still filter by name instead of using \
                 trait hooks (#2366)."
            );
        }
        SmtResult::Unknown => {
            panic!(
                "Expected UNSAT, got Unknown — theory deduction may not be reaching \
                 the SAT solver through the generic collector (#2366)."
            );
        }
    }
    assert!(
        smt.proof_trail().iter().any(|entry| matches!(
            entry,
            ProofTrailEntry::TheoryPropagation {
                theory_name: "CustomBV",
                ..
            }
        )),
        "proof trail should retain the deducing theory name for generic Nelson-Oppen propagations"
    );
}

/// Regression test: same-pass multi-hop equality propagation (#2366).
///
/// Two fake theories form a chain:
/// - DeducingTheory emits a = b on first drain
/// - ChainTheory, when it receives a = b via assert_literal (forwarding),
///   emits c = d on its next drain
///
/// One `check_theories_attributed` call must surface both propagated
/// equalities via the bounded fixpoint loop. c != d is asserted, so
/// the full chain should produce UNSAT.
#[test]
fn test_multi_hop_equality_propagation() {
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
            "DeducingA"
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

    struct ChainTheory {
        trigger: (TermId, TermId),
        result: (TermId, TermId),
        triggered: bool,
        emitted: bool,
    }

    impl TheorySolver for ChainTheory {
        fn assert_literal(&mut self, _lit: Lit, theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            if let TheoryLiteral::Eq(t1, t2) = theory_lit {
                let (a, b) = self.trigger;
                if (*t1 == a && *t2 == b) || (*t1 == b && *t2 == a) {
                    self.triggered = true;
                }
            }
            TheoryCheckResult::Consistent
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn backtrack(&mut self, _level: u32) {
            self.triggered = false;
            self.emitted = false;
        }

        fn push(&mut self) {}

        fn name(&self) -> &'static str {
            "ChainB"
        }

        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

        fn drain_deduced_equalities(&mut self) -> Vec<(TermId, TermId, Vec<Lit>)> {
            if self.triggered && !self.emitted {
                self.emitted = true;
                vec![(self.result.0, self.result.1, vec![])]
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

    let mut smt = SmtSolver::new();
    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");
    let d = smt.const_term("d");

    smt.add_theory(Box::new(DeducingTheory {
        pair: (a, b),
        emitted: false,
    }));
    smt.add_theory(Box::new(ChainTheory {
        trigger: (a, b),
        result: (c, d),
        triggered: false,
        emitted: false,
    }));

    // Assert c != d. Chain: DeducingA deduces a=b -> forwarding triggers
    // ChainB -> ChainB deduces c=d -> contradicts c!=d -> UNSAT.
    let _ = smt.assert_neq(c, d);

    match smt.solve() {
        SmtResult::Unsat(_) => {
            // Correct: DeducingA deduces a=b, forwarding triggers ChainB,
            // ChainB deduces c=d within the same check_theories_attributed
            // call via the fixpoint loop, contradicts c!=d -> UNSAT.
        }
        SmtResult::Sat(_) => {
            panic!(
                "Expected UNSAT: DeducingA->ChainB multi-hop should propagate c=d \
                 within one pass, contradicting c!=d. Either the fixpoint loop \
                 is not iterating (#2366) or forwarding is not cursor-driven."
            );
        }
        SmtResult::Unknown => {
            panic!(
                "Expected UNSAT, got Unknown — multi-hop equality chain may not be \
                 converging in the fixpoint loop (#2366)."
            );
        }
    }
}

/// Regression test: hitting the Nelson-Oppen pass cap must return Unknown.
///
/// This theory emits one fresh equality on each prepare/drain cycle. With
/// 101 pairs and MAX_PASSES=100, the solver cannot reach the final equality
/// that would contradict the asserted disequality. The correct result is
/// Unknown — treating a truncated propagation prefix as convergence would
/// incorrectly report Sat.
#[test]
fn test_nelson_oppen_pass_cap_returns_unknown() {
    struct LongChainTheory {
        pairs: Vec<(TermId, TermId)>,
        emitted: usize,
        pending: Vec<(TermId, TermId, Vec<Lit>)>,
    }

    impl TheorySolver for LongChainTheory {
        fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn backtrack(&mut self, _level: u32) {
            self.emitted = 0;
            self.pending.clear();
        }

        fn push(&mut self) {}

        fn name(&self) -> &'static str {
            "LongChain"
        }

        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

        fn prepare_deduced_equalities(&mut self) {
            if let Some(&(lhs, rhs)) = self.pairs.get(self.emitted) {
                self.pending.push((lhs, rhs, vec![]));
                self.emitted += 1;
            }
        }

        fn drain_deduced_equalities(&mut self) -> Vec<(TermId, TermId, Vec<Lit>)> {
            std::mem::take(&mut self.pending)
        }

        fn as_any(&self) -> &dyn Any {
            self
        }

        fn as_any_mut(&mut self) -> &mut dyn Any {
            self
        }
    }

    let mut smt = SmtSolver::new();
    let mut pairs = Vec::new();
    for idx in 0..101 {
        let lhs = smt.const_term(format!("lhs_{idx}"));
        let rhs = smt.const_term(format!("rhs_{idx}"));
        pairs.push((lhs, rhs));
    }

    let final_pair = pairs[100];
    smt.add_theory(Box::new(LongChainTheory {
        pairs,
        emitted: 0,
        pending: Vec::new(),
    }));
    let _ = smt.assert_neq(final_pair.0, final_pair.1);

    match smt.solve() {
        SmtResult::Unknown => {
            // Correct: the solver hit the pass cap before it could deduce the
            // final equality, so it must not claim SAT.
        }
        SmtResult::Sat(_) => {
            panic!(
                "Expected Unknown when Nelson-Oppen hits the pass cap before \
                 reaching the contradiction. Returning Sat here means the solver \
                 treated a truncated propagation prefix as full convergence."
            );
        }
        SmtResult::Unsat(_) => {
            panic!(
                "Expected Unknown, got Unsat — this regression is about the \
                 pass-cap fallback, not a fully completed fixpoint."
            );
        }
    }
}
