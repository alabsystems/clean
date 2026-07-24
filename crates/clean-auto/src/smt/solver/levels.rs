// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::SmtSolver;
use crate::cdcl::{CdclTrailEntry, CdclTrailKind, Lit};
use crate::smt::{LeveledTheoryState, TheoryLiteral};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct DecisionLevel {
    pub(super) level: u32,
    pub(super) decided: Vec<Lit>,
    pub(super) propagated: Vec<Lit>,
}

impl DecisionLevel {
    pub(super) fn new(level: u32) -> Self {
        Self {
            level,
            decided: Vec::new(),
            propagated: Vec::new(),
        }
    }

    fn record(&mut self, lit: Lit, kind: AssignmentKind) {
        match kind {
            AssignmentKind::Decision => self.decided.push(lit),
            AssignmentKind::Propagation => self.propagated.push(lit),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum AssignmentKind {
    Decision,
    Propagation,
}

impl From<CdclTrailKind> for AssignmentKind {
    fn from(kind: CdclTrailKind) -> Self {
        match kind {
            CdclTrailKind::Decision => Self::Decision,
            CdclTrailKind::Propagation => Self::Propagation,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct LevelAnnotatedAssignment {
    pub(super) lit: Lit,
    pub(super) level: u32,
    pub(super) kind: AssignmentKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct LeveledAssertion {
    pub(super) lit: Lit,
    pub(super) theory_lit: TheoryLiteral,
    pub(super) level: u32,
}

impl SmtSolver {
    pub(super) fn rebuild_assignment_stack_from_sat(&mut self) {
        self.assignment_trail.clear();
        self.theory_assertion_trail.clear();
        self.decision_levels.clear();
        self.decision_levels.push(DecisionLevel::new(0));
        for entry in self.sat.trail_entries() {
            self.record_assignment(entry);
        }
    }

    pub(super) fn reset_theory_assignment_state(&mut self) {
        self.backtrack_assignment_stack_to(0);
        for theory in &mut self.theories {
            theory.reset();
        }
        self.assignment_trail.clear();
        self.theory_assertion_trail.clear();
        self.decision_levels.clear();
        self.decision_levels.push(DecisionLevel::new(0));
        self.theory_scope_level = 0;
    }

    pub(super) fn push_theories_to_level(&mut self, target_level: u32) {
        if target_level <= self.theory_scope_level {
            return;
        }
        let current_level = self.theory_scope_level;
        for theory in &mut self.theories {
            theory.push_to_level(current_level, target_level);
        }
        self.theory_scope_level = target_level;
    }

    pub(super) fn backtrack_assignment_stack_to(&mut self, level: u32) {
        while self
            .assignment_trail
            .last()
            .is_some_and(|assignment| assignment.level > level)
        {
            self.assignment_trail.pop();
        }
        self.decision_levels.truncate(level as usize + 1);
        if self.decision_levels.is_empty() {
            self.decision_levels.push(DecisionLevel::new(0));
        }
        self.backtrack_theory_assertions_to(level);
    }

    pub(super) fn record_theory_assertion(
        &mut self,
        lit: Lit,
        theory_lit: TheoryLiteral,
        level: u32,
    ) {
        self.theory_assertion_trail.push(LeveledAssertion {
            lit,
            theory_lit,
            level,
        });
    }

    pub(super) fn conflict_level(&self, conflict_lits: &[Lit]) -> u32 {
        conflict_lits
            .iter()
            .filter_map(|lit| self.assignment_level(*lit))
            .max()
            .unwrap_or(0)
    }

    fn record_assignment(&mut self, entry: CdclTrailEntry) {
        let kind = AssignmentKind::from(entry.kind);
        self.ensure_decision_level(entry.level);
        self.decision_levels[entry.level as usize].record(entry.lit, kind);
        self.assignment_trail.push(LevelAnnotatedAssignment {
            lit: entry.lit,
            level: entry.level,
            kind,
        });
    }

    fn ensure_decision_level(&mut self, level: u32) {
        while self.decision_levels.len() <= level as usize {
            let next = self.decision_levels.len() as u32;
            self.decision_levels.push(DecisionLevel::new(next));
        }
    }

    fn backtrack_theory_assertions_to(&mut self, level: u32) {
        while self
            .theory_assertion_trail
            .last()
            .is_some_and(|assertion| assertion.level > level)
        {
            self.theory_assertion_trail.pop();
        }
        if level >= self.theory_scope_level {
            return;
        }
        let current_level = self.theory_scope_level;
        for theory in &mut self.theories {
            theory.pop_to_level(current_level, level);
        }
        self.theory_scope_level = level;
    }

    fn assignment_level(&self, lit: Lit) -> Option<u32> {
        self.assignment_trail
            .iter()
            .rev()
            .find(|assignment| assignment.lit == lit)
            .map(|assignment| assignment.level)
            .or_else(|| {
                self.assignment_trail
                    .iter()
                    .rev()
                    .find(|assignment| assignment.lit.var() == lit.var())
                    .map(|assignment| assignment.level)
            })
    }
}

#[cfg(test)]
mod tests {
    use super::{AssignmentKind, DecisionLevel, SmtSolver};
    use crate::cdcl::{CdclTrailEntry, CdclTrailKind, Lit, Var};
    use crate::smt::{SmtTerm, TheoryCheckResult, TheoryLiteral, TheorySolver};
    use std::sync::Arc;

    #[derive(Default)]
    struct TrackingTheory {
        pushes: u32,
        backtracks: Vec<u32>,
    }

    impl TheorySolver for TrackingTheory {
        fn assert_literal(&mut self, _lit: Lit, _theory_lit: &TheoryLiteral) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn check(&self) -> TheoryCheckResult {
            TheoryCheckResult::Consistent
        }

        fn backtrack(&mut self, level: u32) {
            self.backtracks.push(level);
        }

        fn push(&mut self) {
            self.pushes += 1;
        }

        fn name(&self) -> &'static str {
            "Tracking"
        }

        fn set_terms(&mut self, _terms: Arc<[SmtTerm]>) {}

        fn as_any(&self) -> &dyn std::any::Any {
            self
        }

        fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
            self
        }
    }

    #[test]
    fn test_assignment_stack_groups_decisions_and_propagations_by_level() {
        let mut smt = SmtSolver::new();
        smt.record_assignment(CdclTrailEntry {
            lit: Lit::pos(Var::new(0)),
            level: 0,
            kind: CdclTrailKind::Propagation,
        });
        smt.record_assignment(CdclTrailEntry {
            lit: Lit::pos(Var::new(1)),
            level: 1,
            kind: CdclTrailKind::Decision,
        });
        smt.record_assignment(CdclTrailEntry {
            lit: Lit::neg(Var::new(2)),
            level: 1,
            kind: CdclTrailKind::Propagation,
        });
        smt.record_assignment(CdclTrailEntry {
            lit: Lit::pos(Var::new(3)),
            level: 2,
            kind: CdclTrailKind::Decision,
        });

        assert_eq!(smt.decision_levels.len(), 3);
        assert_eq!(
            smt.decision_levels[0],
            DecisionLevel {
                level: 0,
                decided: Vec::new(),
                propagated: vec![Lit::pos(Var::new(0))],
            }
        );
        assert_eq!(smt.decision_levels[1].decided, vec![Lit::pos(Var::new(1))]);
        assert_eq!(
            smt.decision_levels[1].propagated,
            vec![Lit::neg(Var::new(2))]
        );
        assert_eq!(smt.assignment_trail.len(), 4);
        assert_eq!(smt.assignment_trail[1].kind, AssignmentKind::Decision);
        assert_eq!(smt.assignment_trail[2].kind, AssignmentKind::Propagation);
    }

    #[test]
    fn test_backtrack_assignment_stack_truncates_higher_levels() {
        let mut smt = SmtSolver::new();
        for entry in [
            CdclTrailEntry {
                lit: Lit::pos(Var::new(0)),
                level: 0,
                kind: CdclTrailKind::Propagation,
            },
            CdclTrailEntry {
                lit: Lit::pos(Var::new(1)),
                level: 1,
                kind: CdclTrailKind::Decision,
            },
            CdclTrailEntry {
                lit: Lit::pos(Var::new(2)),
                level: 1,
                kind: CdclTrailKind::Propagation,
            },
            CdclTrailEntry {
                lit: Lit::neg(Var::new(3)),
                level: 2,
                kind: CdclTrailKind::Decision,
            },
        ] {
            smt.record_assignment(entry);
        }

        smt.theory_scope_level = 2;
        smt.backtrack_assignment_stack_to(1);

        assert_eq!(smt.theory_scope_level, 1);
        assert_eq!(smt.decision_levels.len(), 2);
        assert_eq!(smt.assignment_trail.len(), 3);
        assert!(smt
            .assignment_trail
            .iter()
            .all(|assignment| assignment.level <= 1));
        assert_eq!(
            smt.decision_levels[1].propagated,
            vec![Lit::pos(Var::new(2))]
        );
    }

    #[test]
    fn test_push_theories_to_level_replays_each_missing_scope() {
        let mut smt = SmtSolver::new();
        smt.add_theory(Box::new(TrackingTheory::default()));

        smt.push_theories_to_level(2);

        let theory = smt
            .get_theory_typed::<TrackingTheory>(0)
            .expect("tracking theory should be present");
        assert_eq!(theory.pushes, 2);
        assert_eq!(smt.theory_scope_level, 2);
    }

    #[test]
    fn test_backtrack_assignment_stack_retracts_theory_assertions() {
        let mut smt = SmtSolver::new();
        smt.add_theory(Box::new(TrackingTheory::default()));
        for (var, level) in [(0, 0), (1, 1), (2, 2)] {
            smt.record_assignment(CdclTrailEntry {
                lit: Lit::pos(Var::new(var)),
                level,
                kind: CdclTrailKind::Propagation,
            });
            smt.record_theory_assertion(Lit::pos(Var::new(var)), TheoryLiteral::Bool(var), level);
        }
        smt.push_theories_to_level(2);

        smt.backtrack_assignment_stack_to(1);

        let theory = smt
            .get_theory_typed::<TrackingTheory>(0)
            .expect("tracking theory should be present");
        assert_eq!(theory.backtracks, vec![1]);
        assert_eq!(smt.theory_scope_level, 1);
        assert_eq!(smt.theory_assertion_trail.len(), 2);
        assert!(smt
            .theory_assertion_trail
            .iter()
            .all(|assertion| assertion.level <= 1));
    }

    #[test]
    fn test_conflict_level_uses_highest_participating_assignment_level() {
        let mut smt = SmtSolver::new();
        for (lit, level, kind) in [
            (Lit::pos(Var::new(0)), 0, CdclTrailKind::Propagation),
            (Lit::pos(Var::new(1)), 1, CdclTrailKind::Decision),
            (Lit::neg(Var::new(2)), 2, CdclTrailKind::Propagation),
        ] {
            smt.record_assignment(CdclTrailEntry { lit, level, kind });
        }

        assert_eq!(smt.conflict_level(&[Lit::pos(Var::new(0))]), 0);
        assert_eq!(
            smt.conflict_level(&[Lit::pos(Var::new(1)), Lit::neg(Var::new(2))]),
            2
        );
        assert_eq!(smt.conflict_level(&[Lit::pos(Var::new(9))]), 0);
    }
}
