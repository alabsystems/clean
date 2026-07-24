// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nelson-Oppen disequality forwarding proof coverage (#2422).
//!
//! The `forward_equality_deductions` method in propagation.rs dispatches
//! positive Eq propagations via `assert_shared_equality` and negative Eq
//! propagations via `assert_shared_disequality`. All existing tests only
//! exercise the positive (equality) path. This test isolates the negative
//! (disequality) forwarding path.
//!
//! # Contract under test
//!
//! VERIFIES: When a theory returns a negative-polarity Eq propagation during
//! N-O forwarding, `assert_shared_disequality` is called on peer theories
//! (not `assert_shared_equality`).
//!
//! VERIFIES: The source-skip logic (don't forward back to originator) still
//! applies correctly for disequality propagations.

use super::*;
use crate::cdcl::Lit;
use std::any::Any;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

/// Mock theory that deduces an equality and records whether it receives
/// a shared disequality callback.
struct DisequaliSource {
    pair: (TermId, TermId),
    emitted: bool,
    received_disequality: Arc<AtomicBool>,
    received_equality: Arc<AtomicBool>,
}

impl TheorySolver for DisequaliSource {
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
        "DisequaliSource"
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

    fn assert_shared_disequality(
        &mut self,
        _t1: TermId,
        _t2: TermId,
        _reason: Lit,
    ) -> TheoryCheckResult {
        self.received_disequality.store(true, Ordering::SeqCst);
        TheoryCheckResult::Consistent
    }

    fn assert_shared_equality(
        &mut self,
        _t1: TermId,
        _t2: TermId,
        _reason: Lit,
    ) -> TheoryCheckResult {
        self.received_equality.store(true, Ordering::SeqCst);
        TheoryCheckResult::Consistent
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

/// Mock theory that captures a SAT variable for a target Eq literal during
/// `assert_literal`, then produces a negative propagation for that variable
/// when it receives a shared equality.
struct DisequaliRelay {
    target_terms: (TermId, TermId),
    captured_var: Option<crate::cdcl::Var>,
    forwarded: bool,
}

impl TheorySolver for DisequaliRelay {
    fn assert_literal(&mut self, lit: Lit, theory_lit: &TheoryLiteral) -> TheoryCheckResult {
        // Capture the SAT variable for our target Eq literal.
        if let TheoryLiteral::Eq(t1, t2) = theory_lit {
            if (*t1, *t2) == self.target_terms || (*t2, *t1) == self.target_terms {
                self.captured_var = Some(lit.var());
            }
        }
        TheoryCheckResult::Consistent
    }

    fn check(&self) -> TheoryCheckResult {
        TheoryCheckResult::Consistent
    }

    fn backtrack(&mut self, _level: u32) {
        // Don't clear captured_var — we need it across DPLL(T) iterations.
        self.forwarded = false;
    }

    fn push(&mut self) {}

    fn name(&self) -> &'static str {
        "DisequaliRelay"
    }

    fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

    fn assert_shared_equality(
        &mut self,
        _t1: TermId,
        _t2: TermId,
        _reason: Lit,
    ) -> TheoryCheckResult {
        // When we receive a shared equality (from Source's deduction),
        // propagate a NEGATIVE literal for our target Eq variable.
        // This triggers the disequality forwarding path in
        // forward_equality_deductions.
        if !self.forwarded {
            if let Some(var) = self.captured_var {
                self.forwarded = true;
                return TheoryCheckResult::Propagation(vec![(Lit::neg(var), vec![])]);
            }
        }
        TheoryCheckResult::Consistent
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

/// Verify that negative-polarity Eq propagations during N-O forwarding
/// are dispatched via `assert_shared_disequality`, not `assert_shared_equality`.
///
/// # Mechanism
///
/// 1. Source deduces equality (a, b) → positive Eq(a,b) propagation
/// 2. Relay receives assert_shared_equality(a, b) → returns Propagation
///    with Lit::neg(eq_cd_var) where eq_cd_var maps to Eq(c, d)
/// 3. Forwarding loop processes the negative Eq(c,d) literal and calls
///    assert_shared_disequality(c, d) on Source (not assert_shared_equality)
/// 4. Source's received_disequality flag is set
#[test]
fn test_negative_eq_propagation_calls_assert_shared_disequality() {
    let received_disequality = Arc::new(AtomicBool::new(false));
    let received_equality = Arc::new(AtomicBool::new(false));

    let mut smt = SmtSolver::new();
    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");
    let d = smt.const_term("d");

    // Pre-register Eq(c, d) as a SAT variable by adding a unit clause.
    // The SAT solver will decide Eq(c,d) = true, making it available
    // to Relay's assert_literal for variable capture.
    smt.add_clause(vec![TheoryLiteral::Eq(c, d)]);

    // Source deduces (a, b) and records disequality callbacks.
    smt.add_theory(Box::new(DisequaliSource {
        pair: (a, b),
        emitted: false,
        received_disequality: Arc::clone(&received_disequality),
        received_equality: Arc::clone(&received_equality),
    }));

    // Relay captures Eq(c,d) SAT var, then produces negative propagation.
    smt.add_theory(Box::new(DisequaliRelay {
        target_terms: (c, d),
        captured_var: None,
        forwarded: false,
    }));

    // The solver may return any result — we care about the callback, not the answer.
    let _ = smt.solve();

    assert!(
        received_disequality.load(Ordering::SeqCst),
        "Source should have received assert_shared_disequality for the \
         negative Eq(c,d) propagation from Relay. The disequality forwarding \
         path in forward_equality_deductions may be broken."
    );

    // Negative polarity must NOT trigger the equality path.
    // A double-dispatch bug (calling both assert_shared_equality AND
    // assert_shared_disequality for the same propagation) would be a
    // soundness hole: the receiving theory would simultaneously learn
    // a = b and a ≠ b from the same evidence.
    assert!(
        !received_equality.load(Ordering::SeqCst),
        "Source should NOT have received assert_shared_equality for a \
         negative Eq propagation. If both equality and disequality paths \
         fire for the same propagation, polarity dispatch is broken."
    );
}
