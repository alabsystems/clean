// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Runtime-stat bookkeeping for `SmtSolver` (#2386).

use super::SmtSolver;
use crate::smt::{SmtStats, TheoryCheckResult};

/// Cumulative solver-owned theory runtime totals for `SmtStats` (#2386).
#[derive(Clone, Copy, Debug, Default)]
pub(in crate::smt) struct TheoryRuntimeTotals {
    check_calls: u64,
    conflicts: u64,
    propagated_literals: u64,
    unknowns: u64,
}

impl TheoryRuntimeTotals {
    pub(in crate::smt) fn record_check_call(&mut self) {
        self.check_calls += 1;
    }

    pub(in crate::smt) fn record_result(&mut self, result: &TheoryCheckResult) {
        match result {
            TheoryCheckResult::Conflict(_) => {
                self.conflicts += 1;
            }
            TheoryCheckResult::Propagation(lits) => {
                self.propagated_literals += lits.len() as u64;
            }
            TheoryCheckResult::Unknown => {
                self.unknowns += 1;
            }
            TheoryCheckResult::Consistent => {}
        }
    }
}

impl SmtSolver {
    /// Get statistics
    pub(crate) fn stats(&self) -> SmtStats {
        let sat_stats = self.sat.stats();
        let mut theory_stats = Vec::new();
        for theory in &self.theories {
            theory_stats.extend(theory.collect_statistics());
        }
        theory_stats.sort_unstable_by_key(|(name, _)| *name);
        SmtStats {
            num_vars: self.sat.num_vars(),
            num_clauses: self.sat.num_clauses(),
            num_terms: self.terms.len(),
            sat_conflicts: sat_stats.conflicts,
            sat_decisions: sat_stats.decisions,
            sat_propagations: sat_stats.propagations,
            sat_learned_clauses: sat_stats.learned_clauses,
            theory_check_calls: self.theory_runtime_totals.check_calls,
            theory_conflicts: self.theory_runtime_totals.conflicts,
            theory_propagated_literals: self.theory_runtime_totals.propagated_literals,
            theory_unknowns: self.theory_runtime_totals.unknowns,
            theory_stats,
        }
    }
}
