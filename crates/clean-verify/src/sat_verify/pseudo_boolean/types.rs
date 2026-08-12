// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pseudo-Boolean constraint types.
//!
//! A PB constraint has the form: sum(a_i * l_i) >= k, where l_i are literals
//! (positive integer = positive literal, negative = negation) and a_i are
//! integer coefficients. The variable index for a literal l is |l|.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use std::collections::HashMap;

/// A pseudo-Boolean constraint: sum(a_i * l_i) >= k.
///
/// Literals use DIMACS convention: positive integer for the variable,
/// negative for its negation. Variable indices are 1-based (|literal|).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PbConstraint {
    /// (coefficient, literal) pairs.
    pub terms: Vec<(i64, i32)>,
    /// RHS threshold (degree).
    pub degree: i64,
}

impl PbConstraint {
    /// Create a new PB constraint.
    #[must_use]
    pub fn new(terms: Vec<(i64, i32)>, degree: i64) -> Self {
        Self { terms, degree }
    }

    /// True if all coefficients are 1 and degree is 1, i.e., this is a clause.
    #[must_use]
    pub fn is_clause(&self) -> bool {
        self.degree == 1 && self.terms.iter().all(|&(c, _)| c == 1)
    }

    /// True if all coefficients are 1 and degree > 1 (cardinality constraint).
    #[must_use]
    pub fn is_cardinality(&self) -> bool {
        self.degree > 1 && self.terms.iter().all(|&(c, _)| c == 1)
    }

    /// Convert to a clause (list of literals) if this is a clause constraint.
    #[must_use]
    pub fn to_clause(&self) -> Option<Vec<i32>> {
        if self.is_clause() {
            Some(self.terms.iter().map(|&(_, lit)| lit).collect())
        } else {
            None
        }
    }

    /// Create a PB constraint from a clause (list of literals).
    #[must_use]
    pub fn from_clause(literals: &[i32]) -> Self {
        let terms = literals.iter().map(|&lit| (1i64, lit)).collect();
        Self { terms, degree: 1 }
    }

    /// Normalize the constraint: remove zero coefficients, combine duplicate
    /// literals, ensure coefficients are non-negative by flipping literals.
    pub fn normalize(&mut self) {
        // Combine duplicate literals.
        let mut combined: HashMap<i32, i64> = HashMap::new();
        for &(coeff, lit) in &self.terms {
            *combined.entry(lit).or_insert(0) += coeff;
        }

        // Flip negative coefficients: -a * l becomes a * ~l, degree += a.
        // For literal l, ~l = -l in DIMACS convention.
        let mut new_terms = Vec::with_capacity(combined.len());
        let mut degree_adjust = 0i64;
        for (lit, coeff) in combined {
            if coeff == 0 {
                continue;
            }
            if coeff < 0 {
                // -a * l  ===  a * ~l - a  >=  k  becomes  a * ~l >= k + a
                new_terms.push((-coeff, -lit));
                degree_adjust += -coeff;
            } else {
                new_terms.push((coeff, lit));
            }
        }

        // Sort by absolute literal value for canonical form.
        new_terms.sort_by_key(|&(_, lit)| (lit.unsigned_abs(), lit < 0));

        self.terms = new_terms;
        self.degree += degree_adjust;
    }

    /// Evaluate the constraint under a partial assignment.
    ///
    /// Assignment is 1-indexed: `assignment[v]` is the value of variable `v`.
    /// Returns `Some(true)` if satisfied, `Some(false)` if falsified,
    /// `None` if undetermined.
    #[must_use]
    pub fn evaluate(&self, assignment: &[Option<bool>]) -> Option<bool> {
        let mut sum = 0i64;
        let mut max_remaining = 0i64;

        for &(coeff, lit) in &self.terms {
            let var = lit.unsigned_abs() as usize;
            let polarity = lit > 0;

            match assignment.get(var).copied().flatten() {
                Some(val) => {
                    if val == polarity {
                        sum += coeff;
                    }
                }
                None => {
                    // Unassigned: assume the best case for satisfiability.
                    max_remaining += coeff;
                }
            }
        }

        if sum >= self.degree {
            Some(true)
        } else if sum + max_remaining < self.degree {
            Some(false)
        } else {
            None
        }
    }

    /// Compute the slack of the constraint under a partial assignment.
    ///
    /// Slack = (sum of satisfied term coefficients) - degree.
    /// Positive slack means the constraint is satisfied with room to spare.
    /// Only counts assigned literals; unassigned are treated as 0.
    #[must_use]
    pub fn slack(&self, assignment: &[Option<bool>]) -> i64 {
        let sum: i64 = self
            .terms
            .iter()
            .map(|&(coeff, lit)| {
                let var = lit.unsigned_abs() as usize;
                let polarity = lit > 0;
                match assignment.get(var).copied().flatten() {
                    Some(val) if val == polarity => coeff,
                    _ => 0,
                }
            })
            .sum();
        sum - self.degree
    }

    /// Unit propagation: find literals that must be true given the assignment.
    ///
    /// A literal l_i with coefficient a_i must be set to true if the slack
    /// from all other assigned+unassigned literals is less than a_i.
    /// Returns literals that are forced.
    #[must_use]
    pub fn propagate(&self, assignment: &[Option<bool>]) -> Vec<i32> {
        // First compute sum of assigned-true terms and sum of unassigned coefficients.
        let mut assigned_sum = 0i64;
        let mut unassigned: Vec<(i64, i32)> = Vec::new();

        for &(coeff, lit) in &self.terms {
            let var = lit.unsigned_abs() as usize;
            let polarity = lit > 0;
            match assignment.get(var).copied().flatten() {
                Some(val) if val == polarity => {
                    assigned_sum += coeff;
                }
                Some(_) => {
                    // Assigned to opposite polarity: contributes 0.
                }
                None => {
                    unassigned.push((coeff, lit));
                }
            }
        }

        let total_unassigned: i64 = unassigned.iter().map(|&(c, _)| c).sum();

        // For each unassigned literal, check if NOT setting it would violate
        // the constraint even if all other unassigned are set.
        let mut forced = Vec::new();
        for &(coeff, lit) in &unassigned {
            // If we don't set this literal, the maximum possible sum is:
            //   assigned_sum + (total_unassigned - coeff)
            // This must be >= degree, otherwise the literal is forced.
            if assigned_sum + total_unassigned - coeff < self.degree {
                forced.push(lit);
            }
        }

        forced
    }

    /// Return the maximum variable index referenced by this constraint.
    #[must_use]
    pub fn max_var(&self) -> u32 {
        self.terms
            .iter()
            .map(|&(_, lit)| lit.unsigned_abs())
            .max()
            .unwrap_or(0)
    }

    /// Check if the constraint is trivially false (empty LHS, positive degree).
    #[must_use]
    pub fn is_contradiction(&self) -> bool {
        // After normalization, a contradiction is: 0 >= k where k > 0,
        // i.e., no terms (or all zero coefficients) and positive degree.
        let coeff_sum: i64 = self.terms.iter().map(|&(c, _)| c.max(0)).sum();
        coeff_sum < self.degree
    }
}

/// A PB formula: a set of PB constraints over a fixed number of variables.
#[derive(Debug, Clone)]
pub struct PbFormula {
    /// Number of variables (1-indexed: variables 1..=num_vars).
    pub num_vars: u32,
    /// The constraints.
    pub constraints: Vec<PbConstraint>,
    /// Optional optimization objective.
    pub objective: Option<PbObjective>,
}

impl PbFormula {
    /// Create a new formula with the given number of variables.
    #[must_use]
    pub fn new(num_vars: u32) -> Self {
        Self {
            num_vars,
            constraints: Vec::new(),
            objective: None,
        }
    }

    /// Add a constraint to the formula. Returns its index.
    pub fn add_constraint(&mut self, constraint: PbConstraint) -> usize {
        let idx = self.constraints.len();
        self.constraints.push(constraint);
        idx
    }

    /// Set the optimization objective.
    pub fn set_objective(&mut self, objective: PbObjective) {
        self.objective = Some(objective);
    }
}

/// Optimization objective: minimize or maximize a linear function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PbObjective {
    /// (coefficient, literal) pairs for the objective function.
    pub terms: Vec<(i64, i32)>,
    /// If true, minimize; if false, maximize.
    pub minimize: bool,
}

impl PbObjective {
    /// Create a new minimization objective.
    #[must_use]
    pub fn minimize(terms: Vec<(i64, i32)>) -> Self {
        Self {
            terms,
            minimize: true,
        }
    }

    /// Create a new maximization objective.
    #[must_use]
    pub fn maximize(terms: Vec<(i64, i32)>) -> Self {
        Self {
            terms,
            minimize: false,
        }
    }

    /// Evaluate the objective under a complete assignment.
    ///
    /// Assignment is 1-indexed. Unassigned variables contribute 0.
    #[must_use]
    pub fn evaluate(&self, assignment: &[Option<bool>]) -> i64 {
        self.terms
            .iter()
            .map(|&(coeff, lit)| {
                let var = lit.unsigned_abs() as usize;
                let polarity = lit > 0;
                match assignment.get(var).copied().flatten() {
                    Some(val) if val == polarity => coeff,
                    _ => 0,
                }
            })
            .sum()
    }
}
