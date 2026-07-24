// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Simplex algorithm operations for the arithmetic theory solver.
//!
//! Contains the core dual simplex routines: pivot, bound repair,
//! violation detection, and conflict explanation.

use super::types::{ArithVar, TableauRow};
use super::ArithmeticTheory;
use crate::cdcl::Lit;
use crate::smt::TheoryCheckResult;
use crate::theories::rational::{DeltaRational, Rational};
use std::collections::BTreeMap;

impl ArithmeticTheory {
    /// Check bounds and repair assignment using simplex.
    ///
    /// With delta-rationals (#2334), all bounds are non-strict, so the simplex
    /// terminates without degenerate pivot cycles. A safety limit is kept for
    /// defensive programming but should never be hit.
    pub(super) fn check_and_repair(&mut self) -> TheoryCheckResult {
        // If a previous pivot overflow left the tableau in a corrupted state (#2399),
        // skip all checks to prevent false conflicts from corrupted coefficients.
        if self.overflow_corrupted {
            return TheoryCheckResult::Unknown; // #2384: corrupted → cannot decide
        }

        self.fix_nonbasic_bounds();

        // Safety limit — delta-rationals guarantee no degenerate pivots,
        // so this should never be reached in practice.
        let max_pivots = 10_000;
        for _ in 0..max_pivots {
            match self.find_violated_basic() {
                None => return TheoryCheckResult::Consistent,
                Some((basic_var, is_lower_violation)) => {
                    if let Some(non_basic) = self.find_pivot(basic_var, is_lower_violation) {
                        if !self.pivot(basic_var, non_basic) {
                            // Arithmetic overflow during pivot (#2324) — return
                            // Unknown (incomplete) rather than false Consistent (#2384).
                            return TheoryCheckResult::Unknown;
                        }
                    } else {
                        let conflict = self.explain_conflict(basic_var, is_lower_violation);
                        return TheoryCheckResult::Conflict(conflict);
                    }
                }
            }
        }
        // Safety limit reached — return Unknown (incompleteness) rather than
        // false Consistent (unsoundness) (#2384).
        TheoryCheckResult::Unknown
    }

    /// Fix non-basic variable assignments to satisfy their bounds.
    /// With delta-rationals, comparison is uniform — no strict/non-strict branches.
    fn fix_nonbasic_bounds(&mut self) {
        let vars: Vec<ArithVar> = self.assignment.keys().copied().collect();
        for var in vars {
            if self.basic_var_index.contains_key(&var) {
                continue;
            }

            let current = self
                .assignment
                .get(&var)
                .copied()
                .unwrap_or(DeltaRational::ZERO);

            // Clamp to lower bound
            if let Some(lower) = self.lower_bounds.get(&var) {
                if current < lower.value {
                    self.assignment.insert(var, lower.value);
                }
            }

            // Clamp to upper bound (after possibly updating from lower)
            let current = self
                .assignment
                .get(&var)
                .copied()
                .unwrap_or(DeltaRational::ZERO);
            if let Some(upper) = self.upper_bounds.get(&var) {
                if current > upper.value {
                    self.assignment.insert(var, upper.value);
                }
            }
        }
    }

    /// Find a basic variable that violates its bounds.
    /// With delta-rationals, comparison is uniform — no strict/non-strict branches.
    /// Skips rows where evaluation overflows (#2324).
    fn find_violated_basic(&self) -> Option<(ArithVar, bool)> {
        for row in &self.tableau {
            let basic_var = row.basic_var;
            let Some(value) = row.evaluate(&self.assignment) else {
                // Overflow during evaluation — skip this row (sound: we might
                // miss a violation but won't report a false conflict).
                continue;
            };

            if let Some(lower) = self.lower_bounds.get(&basic_var) {
                if value < lower.value {
                    return Some((basic_var, true)); // lower violation
                }
            }

            if let Some(upper) = self.upper_bounds.get(&basic_var) {
                if value > upper.value {
                    return Some((basic_var, false)); // upper violation
                }
            }
        }
        None
    }

    /// Find a non-basic variable to pivot with — O(1) row lookup via index (#2042 F4).
    fn find_pivot(&self, basic_var: ArithVar, is_lower_violation: bool) -> Option<ArithVar> {
        let &row_idx = self.basic_var_index.get(&basic_var)?;
        let row = &self.tableau[row_idx];

        for (&non_basic, coeff) in &row.coeffs {
            if coeff.is_zero() {
                continue;
            }

            let can_increase = self.can_increase(non_basic);
            let can_decrease = self.can_decrease(non_basic);

            if is_lower_violation {
                if (coeff.is_positive() && can_increase) || (coeff.is_negative() && can_decrease) {
                    return Some(non_basic);
                }
            } else if (coeff.is_positive() && can_decrease) || (coeff.is_negative() && can_increase)
            {
                return Some(non_basic);
            }
        }

        None
    }

    /// Check if a non-basic variable can increase (is below its upper bound).
    fn can_increase(&self, var: ArithVar) -> bool {
        let current = self
            .assignment
            .get(&var)
            .copied()
            .unwrap_or(DeltaRational::ZERO);
        match self.upper_bounds.get(&var) {
            None => true,
            Some(bound) => current < bound.value,
        }
    }

    /// Check if a non-basic variable can decrease (is above its lower bound).
    fn can_decrease(&self, var: ArithVar) -> bool {
        let current = self
            .assignment
            .get(&var)
            .copied()
            .unwrap_or(DeltaRational::ZERO);
        match self.lower_bounds.get(&var) {
            None => true,
            Some(bound) => current > bound.value,
        }
    }

    /// Compute the target value for the basic variable during a pivot.
    /// Returns the bound value that the basic variable is violating.
    fn compute_pivot_target(&self, basic_var: ArithVar, basic_val: DeltaRational) -> DeltaRational {
        if let Some(lower) = self.lower_bounds.get(&basic_var) {
            if basic_val < lower.value {
                return lower.value;
            }
        }
        if let Some(upper) = self.upper_bounds.get(&basic_var) {
            if basic_val > upper.value {
                return upper.value;
            }
        }
        basic_val
    }

    /// Substitute a newly pivoted row into all other tableau rows.
    /// Returns None on arithmetic overflow (#2324).
    fn substitute_pivot_row(
        &mut self,
        row_idx: usize,
        non_basic: ArithVar,
        new_row: &TableauRow,
    ) -> Option<()> {
        for i in 0..self.tableau.len() {
            if i == row_idx {
                continue;
            }

            if let Some(&c) = self.tableau[i].coeffs.get(&non_basic) {
                if c.is_zero() {
                    continue;
                }

                self.tableau[i].coeffs.remove(&non_basic);
                self.tableau[i].constant =
                    self.tableau[i].constant.add(&c.mul(&new_row.constant)?)?;

                for (&var, &coef) in &new_row.coeffs {
                    let existing = self.tableau[i]
                        .coeffs
                        .get(&var)
                        .copied()
                        .unwrap_or(Rational::ZERO);
                    let new_val = existing.add(&c.mul(&coef)?)?;
                    if new_val.is_zero() {
                        self.tableau[i].coeffs.remove(&var);
                    } else {
                        self.tableau[i].coeffs.insert(var, new_val);
                    }
                }
            }
        }
        Some(())
    }

    /// Perform a pivot operation: swap basic and non-basic variables.
    /// Returns false if arithmetic overflow prevents the pivot (#2324).
    pub(super) fn pivot(&mut self, basic_var: ArithVar, non_basic: ArithVar) -> bool {
        let Some(&row_idx) = self.basic_var_index.get(&basic_var) else {
            return false;
        };

        let coeff = match self.tableau[row_idx].coeffs.get(&non_basic).copied() {
            Some(c) if !c.is_zero() => c,
            _ => return false,
        };

        // All arithmetic in the pivot can overflow — use checked operations.
        let pivot_result = (|| -> Option<()> {
            // Evaluate the basic variable's current value and compute target
            let basic_val = self.tableau[row_idx].evaluate(&self.assignment)?;
            let target = self.compute_pivot_target(basic_var, basic_val);

            // Compute assignment changes (DeltaRational arithmetic)
            let delta = target.sub(&basic_val)?;
            let non_basic_delta = delta.div_rational(&coeff)?;
            let non_basic_val = self
                .assignment
                .get(&non_basic)
                .copied()
                .unwrap_or(DeltaRational::ZERO);
            let new_non_basic_val = non_basic_val.add(&non_basic_delta)?;

            // Rewrite row: express non_basic in terms of basic_var and other non-basics
            let inv_coeff = Rational::ONE.div(&coeff)?;
            let old_constant = self.tableau[row_idx].constant;

            let mut new_coeffs = BTreeMap::new();
            new_coeffs.insert(basic_var, inv_coeff);

            for (&var, &c) in &self.tableau[row_idx].coeffs {
                if var != non_basic {
                    new_coeffs.insert(var, c.checked_neg()?.mul(&inv_coeff)?);
                }
            }

            let new_row = TableauRow {
                basic_var: non_basic,
                constant: old_constant.checked_neg()?.mul(&inv_coeff)?,
                coeffs: new_coeffs,
            };

            self.tableau[row_idx] = new_row.clone();
            // Update basic_var_index: old basic_var removed, new one inserted (#2042 F4)
            self.basic_var_index.remove(&basic_var);
            self.basic_var_index.insert(non_basic, row_idx);

            // Substitute the new row into all other rows.
            // If this overflows, the tableau is partially corrupted (#2399):
            // the pivot row (above) is already rewritten, some dependent rows
            // may have coefficients removed but constants not updated.
            if self
                .substitute_pivot_row(row_idx, non_basic, &new_row)
                .is_none()
            {
                self.overflow_corrupted = true;
                return None;
            }

            // Update assignments (DeltaRational)
            self.assignment.insert(non_basic, new_non_basic_val);
            self.assignment.insert(basic_var, target);
            Some(())
        })();

        pivot_result.is_some()
    }

    /// Explain a conflict: return the literals that led to it (#2292).
    ///
    /// Uses the specific `basic_var` and `is_lower_violation` to produce a
    /// conflict clause scoped to the violated bound and its tableau row,
    /// instead of the previous over-approximate "all bounds" approach.
    pub(super) fn explain_conflict(
        &self,
        basic_var: ArithVar,
        is_lower_violation: bool,
    ) -> Vec<Lit> {
        let mut conflict = Vec::new();

        // Include the violated bound on the basic variable
        if is_lower_violation {
            if let Some(bound) = self.lower_bounds.get(&basic_var) {
                conflict.push(bound.reason);
            }
        } else if let Some(bound) = self.upper_bounds.get(&basic_var) {
            conflict.push(bound.reason);
        }

        // Include only the *blocking* bound per non-basic variable (#2315).
        let row_opt = self
            .basic_var_index
            .get(&basic_var)
            .map(|&idx| &self.tableau[idx]);
        if let Some(row) = row_opt {
            for (&non_basic, coeff) in &row.coeffs {
                let blocking_bound = if is_lower_violation {
                    if coeff.is_positive() {
                        self.upper_bounds.get(&non_basic)
                    } else {
                        self.lower_bounds.get(&non_basic)
                    }
                } else if coeff.is_positive() {
                    self.lower_bounds.get(&non_basic)
                } else {
                    self.upper_bounds.get(&non_basic)
                };
                if let Some(bound) = blocking_bound {
                    if bound.level <= self.level {
                        conflict.push(bound.reason);
                    }
                }
            }
        }

        conflict
    }
}
