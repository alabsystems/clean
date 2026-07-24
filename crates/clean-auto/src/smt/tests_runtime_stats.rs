// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::cdcl::Lit;
use std::any::Any;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

struct StatsConflictTheory {
    conflict_lit: Lit,
}

impl TheorySolver for StatsConflictTheory {
    fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
        TheoryCheckResult::Consistent
    }

    fn check(&self) -> TheoryCheckResult {
        TheoryCheckResult::Conflict(vec![self.conflict_lit])
    }

    fn backtrack(&mut self, _level: u32) {}

    fn push(&mut self) {}

    fn name(&self) -> &'static str {
        "StatsConflictTheory"
    }

    fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

struct StatsPropagationTheory {
    propagate_lit: Lit,
    propagated: AtomicBool,
}

impl StatsPropagationTheory {
    fn new(propagate_lit: Lit) -> Self {
        Self {
            propagate_lit,
            propagated: AtomicBool::new(false),
        }
    }
}

impl TheorySolver for StatsPropagationTheory {
    fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
        TheoryCheckResult::Consistent
    }

    fn check(&self) -> TheoryCheckResult {
        if self.propagated.swap(true, Ordering::Relaxed) {
            TheoryCheckResult::Consistent
        } else {
            TheoryCheckResult::Propagation(vec![(self.propagate_lit, vec![])])
        }
    }

    fn backtrack(&mut self, _level: u32) {}

    fn push(&mut self) {}

    fn name(&self) -> &'static str {
        "StatsPropagationTheory"
    }

    fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

#[test]
fn test_smt_stats_track_theory_conflict_runtime_totals() {
    let mut smt = SmtSolver::new();
    let trigger = TheoryLiteral::Bool(0);
    let _ = smt.add_clause(vec![trigger.clone()]);
    let trigger_lit = smt
        .theory_literal_to_sat_literal(&trigger)
        .expect("bool atom should lower to a SAT literal");
    smt.add_theory(Box::new(StatsConflictTheory {
        conflict_lit: trigger_lit,
    }));

    assert!(
        matches!(smt.solve(), SmtResult::Unsat(_)),
        "conflicting check theory should make the formula UNSAT"
    );

    let stats = smt.stats();
    assert!(
        stats.theory_check_calls >= 1,
        "theory conflict path should call check() at least once"
    );
    assert!(
        stats.theory_conflicts >= 1,
        "theory conflict path should increment theory_conflicts"
    );
    assert_eq!(
        stats.theory_propagated_literals, 0,
        "conflict-only path should not report theory propagations"
    );
    assert_eq!(
        stats.theory_unknowns, 0,
        "conflict-only path should not report unknown results"
    );
}

#[test]
fn test_smt_stats_track_theory_propagation_runtime_totals() {
    let mut smt = SmtSolver::new();
    let trigger = TheoryLiteral::Bool(1);
    let _ = smt.add_clause(vec![trigger.clone()]);
    let trigger_lit = smt
        .theory_literal_to_sat_literal(&trigger)
        .expect("bool atom should lower to a SAT literal");
    smt.add_theory(Box::new(StatsPropagationTheory::new(trigger_lit)));

    assert!(
        matches!(smt.solve(), SmtResult::Sat(_)),
        "redundant theory propagation should still converge to SAT"
    );

    let stats = smt.stats();
    assert!(
        stats.theory_check_calls >= 1,
        "theory propagation path should call check() at least once"
    );
    assert_eq!(
        stats.theory_conflicts, 0,
        "propagation-only path should not report theory conflicts"
    );
    assert_eq!(
        stats.theory_propagated_literals, 1,
        "one propagated literal should be counted exactly once"
    );
    assert_eq!(
        stats.theory_unknowns, 0,
        "propagation-only path should not report unknown results"
    );
}
