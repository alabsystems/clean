// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use ay_core::ProofId;

use super::trace::{ProofTrace, StepView};

impl<'a> ProofTrace<'a> {
    /// Return the last proof step whose clause is empty.
    pub(crate) fn root_empty_clause_step(&self) -> Option<usize> {
        (0..self.step_count())
            .rev()
            .find(|&idx| self.step_derives_empty_clause(idx))
    }

    /// Mark the proof steps reachable from the chosen contradiction root.
    pub(crate) fn reachable_from(&self, root_idx: usize) -> Vec<bool> {
        let step_count = self.step_count();
        let mut reachable = vec![false; step_count];
        if root_idx >= step_count {
            return reachable;
        }

        let mut stack = vec![root_idx];
        while let Some(idx) = stack.pop() {
            if std::mem::replace(&mut reachable[idx], true) {
                continue;
            }

            match self.step(idx) {
                StepView::Resolution {
                    clause1, clause2, ..
                } => {
                    Self::push_reachable_premise(&mut stack, step_count, clause1);
                    Self::push_reachable_premise(&mut stack, step_count, clause2);
                }
                StepView::Step { premises, .. } => {
                    for &premise in premises.iter().rev() {
                        Self::push_reachable_premise(&mut stack, step_count, premise);
                    }
                }
                StepView::Assume(_)
                | StepView::TheoryLemma { .. }
                | StepView::Anchor
                | StepView::Unknown => {}
            }
        }

        reachable
    }

    /// Whether the step's clause is empty, without allocating a flattened clause.
    pub(crate) fn step_derives_empty_clause(&self, idx: usize) -> bool {
        matches!(
            self.step(idx),
            StepView::Resolution { clause, .. }
                | StepView::TheoryLemma { clause, .. }
                | StepView::Step { clause, .. }
                if clause.is_empty()
        )
    }

    fn push_reachable_premise(stack: &mut Vec<usize>, step_count: usize, premise: ProofId) {
        let premise_idx = premise.0 as usize;
        if premise_idx < step_count {
            stack.push(premise_idx);
        }
    }
}
