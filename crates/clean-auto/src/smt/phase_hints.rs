// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theory-guided polarity seeding for outer DPLL(T) iterations.

use super::solver::SmtSolver;

impl SmtSolver {
    /// Seed CDCL phase-saving from the just-checked theory state (#2386).
    ///
    /// This is intentionally lightweight: clean's theories are checked only
    /// after the SAT solver produces a full model, so hints apply to the next
    /// outer DPLL(T) iteration rather than to in-flight CDCL propagation.
    ///
    /// Hints are fail-closed on shared atoms. If multiple theories disagree on
    /// the preferred polarity for the same registered atom, the SMT solver
    /// keeps the existing SAT phase instead of forcing an arbitrary choice.
    pub(super) fn apply_theory_phase_hints(&mut self) {
        let updates: Vec<_> = self
            .var_to_theory
            .iter()
            .filter_map(|(&var, theory_lit)| {
                let mut consensus = None;
                let mut conflict = false;
                for theory in &self.theories {
                    let Some(phase) = theory.suggest_phase(theory_lit) else {
                        continue;
                    };
                    match consensus {
                        None => consensus = Some(phase),
                        Some(existing) if existing == phase => {}
                        Some(_) => {
                            conflict = true;
                            break;
                        }
                    }
                }
                if conflict {
                    None
                } else {
                    consensus.map(|phase| (var, phase))
                }
            })
            .collect();
        for (var, phase) in updates {
            self.set_sat_phase_hint(var, phase);
        }
    }

    #[cfg(test)]
    pub(super) fn phase_hint_for_literal(&self, theory_lit: &super::TheoryLiteral) -> Option<bool> {
        let (base_lit, positive) = match theory_lit {
            super::TheoryLiteral::Eq(lhs, rhs) => (super::TheoryLiteral::Eq(*lhs, *rhs), true),
            super::TheoryLiteral::Neq(lhs, rhs) => (super::TheoryLiteral::Eq(*lhs, *rhs), false),
            super::TheoryLiteral::Lt(lhs, rhs) => (super::TheoryLiteral::Lt(*lhs, *rhs), true),
            super::TheoryLiteral::Le(lhs, rhs) => (super::TheoryLiteral::Le(*lhs, *rhs), true),
            super::TheoryLiteral::Bool(var) => (super::TheoryLiteral::Bool(*var), true),
            super::TheoryLiteral::NegBool(var) => (super::TheoryLiteral::Bool(*var), false),
        };
        let var = self.theory_var_for_literal(&base_lit)?;
        let phase = self.sat_phase_hint(var);
        Some(if positive { phase } else { !phase })
    }
}
