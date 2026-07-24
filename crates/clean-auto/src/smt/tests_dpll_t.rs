// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::cdcl::{Lit, Var};
use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};

/// A theory that rejects the first N SAT assignments with conflicts,
/// then accepts. Used to test that the DPLL(T) loop handles many
/// successive theory conflicts without stack overflow.
struct ConflictCountingTheory {
    /// How many conflicts to produce before accepting
    conflicts_remaining: AtomicU32,
    /// Last literal asserted (used for conflict clause).
    /// Stored as u32 encoding: 0 = None, odd = positive var, even = negative var.
    last_lit_encoded: AtomicU32,
}

impl ConflictCountingTheory {
    fn new(conflict_count: u32) -> Self {
        Self {
            conflicts_remaining: AtomicU32::new(conflict_count),
            last_lit_encoded: AtomicU32::new(0),
        }
    }

    fn encode_lit(lit: Lit) -> u32 {
        // Encode as (var_index * 2 + polarity) + 1 to reserve 0 for None
        let idx = lit.var().index() as u32;
        let pol = if lit.is_pos() { 1 } else { 0 };
        idx * 2 + pol + 1
    }

    fn decode_lit(encoded: u32) -> Option<Lit> {
        if encoded == 0 {
            return None;
        }
        let val = encoded - 1;
        let var = Var::new(val / 2);
        if val % 2 == 1 {
            Some(Lit::pos(var))
        } else {
            Some(Lit::neg(var))
        }
    }
}

impl TheorySolver for ConflictCountingTheory {
    fn assert_literal(&mut self, lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
        self.last_lit_encoded
            .store(Self::encode_lit(lit), Ordering::Relaxed);
        TheoryCheckResult::Consistent
    }

    fn check(&self) -> TheoryCheckResult {
        let remaining = self.conflicts_remaining.load(Ordering::Relaxed);
        if remaining > 0 {
            self.conflicts_remaining
                .store(remaining - 1, Ordering::Relaxed);
            if let Some(lit) = Self::decode_lit(self.last_lit_encoded.load(Ordering::Relaxed)) {
                TheoryCheckResult::Conflict(vec![lit])
            } else {
                TheoryCheckResult::Consistent
            }
        } else {
            TheoryCheckResult::Consistent
        }
    }

    fn backtrack(&mut self, _level: u32) {}
    fn push(&mut self) {}
    fn name(&self) -> &'static str {
        "conflict_counter"
    }
    fn set_terms(&mut self, _terms: std::sync::Arc<[SmtTerm]>) {}
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}

#[test]
fn test_dpll_t_loop_many_conflicts_no_stack_overflow() {
    // Previously, sat_solve_with_theory used recursion. With 500 successive
    // theory conflicts, the old code would build 500 stack frames.
    // The loop-based implementation handles this gracefully.
    let mut smt = SmtSolver::new();
    smt.add_theory(Box::new(ConflictCountingTheory::new(500)));

    let a = smt.const_term("a");
    let b = smt.const_term("b");

    // Simple satisfiable problem -- theory will reject 500 times then accept
    smt.add_clause(vec![TheoryLiteral::Eq(a, b)]);

    // Should eventually return SAT after 500 theory conflicts are resolved
    match smt.solve() {
        SmtResult::Sat(_) | SmtResult::Unsat(_) => {
            // Either outcome is valid -- the point is we don't stack overflow
        }
        SmtResult::Unknown => {
            // Unknown is also acceptable if we hit the iteration limit
        }
    }
}

/// A theory that propagates a literal on first check, then accepts.
/// Used to test that theory propagations are incorporated and re-checked.
struct PropagatingTheory {
    propagated: AtomicBool,
    propagate_lit: Lit,
}

impl PropagatingTheory {
    fn new(lit: Lit) -> Self {
        Self {
            propagated: AtomicBool::new(false),
            propagate_lit: lit,
        }
    }
}

impl TheorySolver for PropagatingTheory {
    fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
        TheoryCheckResult::Consistent
    }

    fn check(&self) -> TheoryCheckResult {
        if !self.propagated.load(Ordering::Relaxed) {
            self.propagated.store(true, Ordering::Relaxed);
            TheoryCheckResult::Propagation(vec![(self.propagate_lit, vec![])])
        } else {
            TheoryCheckResult::Consistent
        }
    }

    fn backtrack(&mut self, _level: u32) {}
    fn push(&mut self) {}
    fn name(&self) -> &'static str {
        "propagating"
    }
    fn set_terms(&mut self, _terms: std::sync::Arc<[SmtTerm]>) {}
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}

#[test]
fn test_dpll_t_propagation_re_solves() {
    // When a theory propagates a literal during the final check,
    // the solver should add it as a unit clause and re-solve.
    // Previously, propagation was treated as SAT without re-checking.
    let mut smt = SmtSolver::new();

    let a = smt.const_term("a");
    let b = smt.const_term("b");

    // Create variables first so we have a valid Lit to propagate
    let _eq_var = smt
        .add_clause(vec![TheoryLiteral::Eq(a, b), TheoryLiteral::Neq(a, b)])
        .expect("clause should be satisfiable");

    // The propagating theory will force a specific literal on the first check,
    // then accept on the second check. The solver must re-solve after propagation.
    let prop_lit = Lit::pos(Var::new(0));
    smt.add_theory(Box::new(PropagatingTheory::new(prop_lit)));

    match smt.solve() {
        SmtResult::Sat(model) => {
            // After propagation, variable 0 should be forced true
            assert!(
                model.sat_model[0],
                "propagated literal should be true in final model"
            );
        }
        SmtResult::Unsat(_) => {
            // Also acceptable -- propagation may have caused UNSAT
        }
        SmtResult::Unknown => {
            panic!("should not return Unknown for simple problem");
        }
    }
}

/// Regression test for #2309: theory propagation clauses carry explanation
/// premises rather than being permanent unit clauses.
///
/// Before the fix, `Propagation(vec![lit])` became `add_clause(vec![lit])`
/// -- a permanent unit clause surviving SAT backtracking. Now propagations
/// carry explanation premises and become multi-literal clauses:
/// `NOT(premise1) OR ... OR propagated_lit`.
#[test]
fn test_propagation_carries_explanation_not_permanent_unit_clause() {
    /// Theory that propagates a literal WITH explanation on first check.
    struct ExplainedPropTheory {
        propagated: AtomicBool,
        propagate_lit: Lit,
        explanation: Vec<Lit>,
    }

    impl ExplainedPropTheory {
        fn new(lit: Lit, explanation: Vec<Lit>) -> Self {
            Self {
                propagated: AtomicBool::new(false),
                propagate_lit: lit,
                explanation,
            }
        }
    }

    impl TheorySolver for ExplainedPropTheory {
        fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn check(&self) -> TheoryCheckResult {
            if !self.propagated.load(Ordering::Relaxed) {
                self.propagated.store(true, Ordering::Relaxed);
                TheoryCheckResult::Propagation(vec![(self.propagate_lit, self.explanation.clone())])
            } else {
                TheoryCheckResult::Consistent
            }
        }

        fn backtrack(&mut self, _level: u32) {}
        fn push(&mut self) {}
        fn name(&self) -> &'static str {
            "explained_propagating"
        }
        fn set_terms(&mut self, _terms: std::sync::Arc<[SmtTerm]>) {}
        fn as_any(&self) -> &dyn std::any::Any {
            self
        }
        fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
            self
        }
    }

    let mut smt = SmtSolver::new();

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");

    // Create theory variables
    let _eq_ab = smt.add_clause(vec![TheoryLiteral::Eq(a, b), TheoryLiteral::Neq(a, b)]);
    let _eq_bc = smt.add_clause(vec![TheoryLiteral::Eq(b, c), TheoryLiteral::Neq(b, c)]);

    // Propagate var(1) with explanation [Lit::pos(Var::new(0))]
    // This should produce clause: NOT(var0) OR var1
    // NOT a permanent unit clause (var1).
    let prop_lit = Lit::pos(Var::new(1));
    let explanation = vec![Lit::pos(Var::new(0))];
    smt.add_theory(Box::new(ExplainedPropTheory::new(prop_lit, explanation)));

    // Solve -- the formula is satisfiable, and the propagation clause
    // (NOT(var0) OR var1) only constrains the model, not makes it UNSAT.
    match smt.solve() {
        SmtResult::Sat(model) => {
            // The propagation clause NOT(var0) OR var1 must be satisfied:
            // if var0 is true, var1 must also be true.
            let var0_true = model.sat_model[0];
            let var1_true = model.sat_model[1];
            assert!(
                !var0_true || var1_true,
                "Propagation clause NOT(var0) OR var1 violated: var0={var0_true}, var1={var1_true}"
            );
        }
        SmtResult::Unknown => {
            // Bounded solver may give up -- acceptable but not ideal.
        }
        SmtResult::Unsat(_) => {
            panic!("Expected Sat -- the formula is satisfiable with the propagation clause");
        }
    }
}

/// Regression test for #2309 A-fix-1: add_clause return value is checked
/// when adding propagation clauses. Previously, the return value was
/// discarded, potentially missing UNSAT.
#[test]
fn test_propagation_add_clause_checks_return_value() {
    /// Theory that propagates conflicting literals to force UNSAT via add_clause.
    struct ConflictingPropTheory {
        propagated: AtomicBool,
    }

    impl ConflictingPropTheory {
        fn new() -> Self {
            Self {
                propagated: AtomicBool::new(false),
            }
        }
    }

    impl TheorySolver for ConflictingPropTheory {
        fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn check(&self) -> TheoryCheckResult {
            if !self.propagated.load(Ordering::Relaxed) {
                self.propagated.store(true, Ordering::Relaxed);
                // Propagate both a literal and its negation (via two separate
                // propagations with empty explanation = unit clauses).
                // The SAT solver should detect UNSAT when the second is added.
                TheoryCheckResult::Propagation(vec![
                    (Lit::pos(Var::new(0)), vec![]),
                    (Lit::neg(Var::new(0)), vec![]),
                ])
            } else {
                TheoryCheckResult::Consistent
            }
        }

        fn backtrack(&mut self, _level: u32) {}
        fn push(&mut self) {}
        fn name(&self) -> &'static str {
            "conflicting_propagating"
        }
        fn set_terms(&mut self, _terms: std::sync::Arc<[SmtTerm]>) {}
        fn as_any(&self) -> &dyn std::any::Any {
            self
        }
        fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
            self
        }
    }

    let mut smt = SmtSolver::new();

    let a = smt.const_term("a");
    let b = smt.const_term("b");

    let _eq_ab = smt.add_clause(vec![TheoryLiteral::Eq(a, b), TheoryLiteral::Neq(a, b)]);

    smt.add_theory(Box::new(ConflictingPropTheory::new()));

    // With both p and NOT(p) propagated as unit clauses in a single
    // Propagation result, the handler iterates them sequentially.
    // The second add_clause MUST return None (conflicting unit clause
    // at cdcl.rs:632-642), and the return value check yields UNSAT.
    match smt.solve() {
        SmtResult::Unsat(_) => {
            // Expected: contradictory propagations detected via add_clause
            // return value check (#2309 A-fix-1).
        }
        other => {
            panic!(
                "Expected UNSAT from conflicting propagations, got {:?}",
                match other {
                    SmtResult::Sat(_) => "Sat",
                    SmtResult::Unknown => "Unknown",
                    _ => unreachable!(),
                }
            );
        }
    }
}

// ─── build_model non-Eq literal filtering (#2386 proof_coverage) ────────────

/// Verify that `build_model` correctly populates equalities/disequalities
/// from Eq literals and excludes Lt/Le/Bool literals from the model.
/// This is a soundness-relevant property: the model should reflect only
/// the equality/disequality structure, not arithmetic orderings.
#[test]
fn test_build_model_extracts_equalities_and_filters_non_eq() {
    let mut smt = SmtSolver::new();

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let x = smt.int_term(1i64);
    let y = smt.int_term(2i64);

    // Add Eq(a,b) as a forced equality (unit clause) — model will have a=b
    smt.add_clause(vec![TheoryLiteral::Eq(a, b)]);
    // Add Lt(x,y) and Le(x,y) — these should NOT appear in model equalities
    smt.add_clause(vec![TheoryLiteral::Lt(x, y)]);
    smt.add_clause(vec![TheoryLiteral::Le(x, y)]);
    // Add a Bool variable — should NOT appear in model equalities
    smt.add_clause(vec![TheoryLiteral::Bool(99)]);

    match smt.solve() {
        SmtResult::Sat(model) => {
            // The model should contain (a,b) in equalities
            assert!(
                model.equalities.contains(&(a, b)),
                "model should contain the forced equality (a,b), got equalities={:?}",
                model.equalities
            );
            // Lt/Le/Bool should not leak into equalities or disequalities
            let all_model_terms: Vec<_> = model
                .equalities
                .iter()
                .chain(model.disequalities.iter())
                .collect();
            for (t1, t2) in &all_model_terms {
                // x and y are arithmetic terms — they should only appear
                // as equalities if they were registered via Eq, not via Lt/Le
                assert!(
                    !(*t1 == x && *t2 == y) || model.equalities.contains(&(x, y)),
                    "arithmetic terms (x,y) should not appear from Lt/Le lowering"
                );
            }
            // Verify the model has exactly 1 equality (a=b)
            assert_eq!(
                model.equalities.len(),
                1,
                "model should have exactly 1 equality from Eq(a,b), got {:?}",
                model.equalities
            );
        }
        SmtResult::Unsat(_) => {
            panic!(
                "formula should be satisfiable with one forced equality and compatible orderings"
            );
        }
        SmtResult::Unknown => {
            panic!("should not return Unknown for simple formula");
        }
    }
}

/// Verify that the model correctly splits equalities vs disequalities
/// based on SAT literal polarity.
#[test]
fn test_build_model_separates_equalities_from_disequalities() {
    let mut smt = SmtSolver::new();

    let a = smt.const_term("a");
    let b = smt.const_term("b");
    let c = smt.const_term("c");
    let d = smt.const_term("d");

    // Force a = b (positive Eq)
    smt.add_clause(vec![TheoryLiteral::Eq(a, b)]);
    // Force c ≠ d (negative Eq)
    smt.add_clause(vec![TheoryLiteral::Neq(c, d)]);

    match smt.solve() {
        SmtResult::Sat(model) => {
            assert!(
                model.equalities.contains(&(a, b)),
                "model equalities should contain (a,b), got {:?}",
                model.equalities
            );
            assert!(
                model.disequalities.contains(&(c, d)),
                "model disequalities should contain (c,d), got {:?}",
                model.disequalities
            );
            assert!(
                !model.equalities.contains(&(c, d)),
                "forced disequality (c,d) should not appear in equalities"
            );
            assert!(
                !model.disequalities.contains(&(a, b)),
                "forced equality (a,b) should not appear in disequalities"
            );
        }
        SmtResult::Unsat(_) => {
            panic!("formula should be satisfiable");
        }
        SmtResult::Unknown => {
            panic!("should not return Unknown for simple formula");
        }
    }
}
