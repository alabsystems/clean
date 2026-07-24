// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Linear Rational Arithmetic (LRA) theory solver using Simplex
//!
//! This module implements a theory solver for linear arithmetic over rationals
//! using the dual simplex algorithm (as used in Z3 and CVC5).
//!
//! # Theory of Linear Rational Arithmetic (LRA)
//!
//! LRA handles:
//! - Linear constraints: `a₁x₁ + a₂x₂ + ... + aₙxₙ ≤ c`
//! - Strict inequalities: `a₁x₁ + a₂x₂ + ... + aₙxₙ < c`
//! - Equalities: `a₁x₁ + a₂x₂ + ... + aₙxₙ = c`
//!
//! # Simplex Algorithm
//!
//! The solver maintains a tableau in the form:
//! ```text
//! s₁ = a₁₁x₁ + a₁₂x₂ + ... (slack variable for row 1)
//! s₂ = a₂₁x₁ + a₂₂x₂ + ... (slack variable for row 2)
//! ```
//!
//! Basic variables (left side) have their values determined by non-basic variables.
//! The algorithm pivots variables between basic and non-basic to satisfy bounds.
//!
//! # Implementation Notes
//!
//! - Uses rational arithmetic for exactness (no floating point errors)
//! - Strict inequalities encoded via delta-rationals (no degenerate pivots)
//! - Supports incremental solving with backtracking
//! - Detects conflicts and generates explanations
//!
//! # References
//!
//! - Dutertre & de Moura, "A Fast Linear-Arithmetic Solver for DPLL(T)", CAV 2006
//!   (Section 3.2: infinitesimals for strict inequalities)

pub mod types;

mod deductions;
mod simplex;
mod solver_impl;

use super::rational::{DeltaRational, Rational};
use crate::cdcl::Lit;
use crate::smt::{TermId, TheoryCheckResult};
use std::collections::{HashMap, HashSet};
use types::{ArithStats, ArithVar, Bound, LinearExpr, TableauRow};

#[cfg(test)]
mod tests;

/// Linear Rational Arithmetic theory solver
pub struct ArithmeticTheory {
    /// Next variable ID — single counter for both user and slack vars (#2297)
    next_id: u32,
    /// Tableau rows (one per basic variable)
    tableau: Vec<TableauRow>,
    /// Current variable assignment (DeltaRational for strict bound support, #2334)
    assignment: HashMap<ArithVar, DeltaRational>,
    /// Lower bounds on variables
    lower_bounds: HashMap<ArithVar, Bound>,
    /// Upper bounds on variables
    upper_bounds: HashMap<ArithVar, Bound>,
    /// Trail of bounds for backtracking: (level, var, was_lower, old_bound)
    bound_trail: Vec<(u32, ArithVar, bool, Option<Bound>)>,
    /// Tableau snapshots per level for backtracking (#2296)
    tableau_trail: Vec<Vec<TableauRow>>,
    /// Assignment snapshots per level for backtracking (#2296)
    assignment_trail: Vec<HashMap<ArithVar, DeltaRational>>,
    /// Variable counter snapshots per level for backtracking (#2296)
    next_id_trail: Vec<u32>,
    /// Saved `next_id` values per level for term_to_var backtracking (#2312, #2406).
    /// On backtrack, entries with var.id() >= saved next_id are removed from
    /// term_to_var, avoiding the O(N) full HashMap clone in push().
    term_to_var_trail: Vec<u32>,
    /// Current decision level
    level: u32,
    /// Mapping from SMT term IDs to arithmetic variables
    term_to_var: HashMap<TermId, ArithVar>,
    /// Deduced equalities for Nelson-Oppen forwarding (#2364).
    /// Populated when model values show two term variables are equal
    /// and constraints force this equality (both constrained, same value).
    pending_deduced: Vec<(TermId, TermId, Vec<Lit>)>,
    /// O(1) lookup set for dedup in detect_model_equalities (#2441).
    /// Stores normalized (min, max) pairs to avoid both (a,b) and (b,a) checks.
    deduced_set: HashSet<(TermId, TermId)>,
    /// Set when `substitute_pivot_row` overflows after partially modifying
    /// the tableau (#2399). When true, `check_and_repair` returns `Consistent`
    /// immediately to prevent false conflicts from corrupted state.
    overflow_corrupted: bool,
    /// Trail for `overflow_corrupted` flag for backtracking (#2399)
    overflow_corrupted_trail: Vec<bool>,
    /// Structural level-0 terms registered by `internalize_atom()` that
    /// survive `reset()`. Replayed on reset to avoid cloning the growing
    /// term/assignment maps on every pre-solve internalization.
    reset_base_terms: Vec<TermId>,
    /// Dedup set for `reset_base_terms`.
    reset_base_term_set: HashSet<TermId>,
    /// O(1) lookup from basic_var to tableau row index (#2042 F4).
    basic_var_index: HashMap<ArithVar, usize>,
}

impl ArithmeticTheory {
    /// Create a new arithmetic theory solver
    pub fn new() -> Self {
        ArithmeticTheory {
            next_id: 0,
            tableau: Vec::new(),
            assignment: HashMap::new(),
            lower_bounds: HashMap::new(),
            upper_bounds: HashMap::new(),
            bound_trail: Vec::new(),
            tableau_trail: Vec::new(),
            assignment_trail: Vec::new(),
            next_id_trail: Vec::new(),
            term_to_var_trail: Vec::new(),
            level: 0,
            term_to_var: HashMap::new(),
            pending_deduced: Vec::new(),
            deduced_set: HashSet::new(),
            overflow_corrupted: false,
            overflow_corrupted_trail: Vec::new(),
            reset_base_terms: Vec::new(),
            reset_base_term_set: HashSet::new(),
            basic_var_index: HashMap::new(),
        }
    }

    /// Rebuild `basic_var_index` from the current `tableau`.
    /// Called after backtracking restores a tableau snapshot or test setup.
    pub(crate) fn rebuild_basic_var_index(&mut self) {
        self.basic_var_index.clear();
        for (i, row) in self.tableau.iter().enumerate() {
            self.basic_var_index.insert(row.basic_var, i);
        }
    }

    fn can_extend_reset_base(&self) -> bool {
        self.level == 0
            && self.bound_trail.is_empty()
            && self.tableau.is_empty()
            && self.lower_bounds.is_empty()
            && self.upper_bounds.is_empty()
    }

    fn record_reset_base_term(&mut self, term_id: TermId) {
        if !self.can_extend_reset_base() {
            return;
        }
        if self.reset_base_term_set.insert(term_id) {
            self.reset_base_terms.push(term_id);
        }
    }

    /// Allocate the next variable ID (#2297: single counter prevents collisions)
    fn next_var_id(&mut self) -> ArithVar {
        let var = ArithVar::new(self.next_id);
        self.next_id += 1;
        var
    }

    /// Create or get a variable for an SMT term
    fn get_or_create_var(&mut self, term_id: TermId) -> ArithVar {
        if let Some(&var) = self.term_to_var.get(&term_id) {
            return var;
        }

        let var = self.next_var_id();
        self.term_to_var.insert(term_id, var);

        // Initialize assignment to 0
        self.assignment.insert(var, DeltaRational::ZERO);

        var
    }

    /// Create a new slack variable
    fn new_slack_var(&mut self) -> ArithVar {
        let var = self.next_var_id();
        self.assignment.insert(var, DeltaRational::ZERO);
        var
    }

    /// Add a constraint: expr ≤ bound (bound is DeltaRational, strictness encoded in delta)
    fn add_upper_constraint(
        &mut self,
        expr: LinearExpr,
        bound: DeltaRational,
        reason: Lit,
    ) -> TheoryCheckResult {
        // Create slack variable: s = expr
        let slack = self.new_slack_var();

        // Build coefficients, substituting any basic variables with their
        // tableau row expressions so that the new row only references
        // non-basic variables (simplex invariant).
        let mut coeffs = expr.coeffs.clone();
        let mut constant = Rational::ZERO;
        let mut overflow = false;
        for row in &self.tableau {
            if let Some(c) = coeffs.remove(&row.basic_var) {
                let Some(prod) = c.mul(&row.constant) else {
                    overflow = true;
                    break;
                };
                let Some(sum) = constant.add(&prod) else {
                    overflow = true;
                    break;
                };
                constant = sum;
                for (&var, &coef) in &row.coeffs {
                    let existing = coeffs.get(&var).copied().unwrap_or(Rational::ZERO);
                    let Some(prod) = c.mul(&coef) else {
                        overflow = true;
                        break;
                    };
                    let Some(new_val) = existing.add(&prod) else {
                        overflow = true;
                        break;
                    };
                    if new_val.is_zero() {
                        coeffs.remove(&var);
                    } else {
                        coeffs.insert(var, new_val);
                    }
                }
                if overflow {
                    break;
                }
            }
        }
        // On overflow (#2324), return Unknown (incomplete) rather than
        // false Consistent (#2384).
        if overflow {
            return TheoryCheckResult::Unknown;
        }

        let row = TableauRow {
            basic_var: slack,
            constant,
            coeffs,
        };
        self.basic_var_index.insert(slack, self.tableau.len());
        self.tableau.push(row);

        // Add upper bound on slack
        self.assert_upper_bound(slack, bound, reason)
    }

    /// Assert an upper bound: var ≤ bound (DeltaRational)
    fn assert_upper_bound(
        &mut self,
        var: ArithVar,
        bound: DeltaRational,
        reason: Lit,
    ) -> TheoryCheckResult {
        // Check for immediate conflict with lower bound
        if let Some(lower) = self.lower_bounds.get(&var) {
            if bound < lower.value {
                return TheoryCheckResult::Conflict(vec![lower.reason, reason]);
            }
        }

        // Save old bound for backtracking
        let old_bound = self.upper_bounds.get(&var).cloned();
        self.bound_trail
            .push((self.level, var, false, old_bound.clone()));

        // Update bound if tighter (smaller DeltaRational = tighter upper bound).
        let should_update = match &old_bound {
            None => true,
            Some(old) => bound < old.value,
        };

        if should_update {
            self.upper_bounds
                .insert(var, Bound::new(bound, reason, self.level));
        }

        // Check if we need to repair assignment
        self.check_and_repair()
    }

    /// Process theory literal for less-than or less-equal.
    /// Strict bounds are encoded via delta-rationals (#2334).
    fn handle_comparison(
        &mut self,
        t1: TermId,
        t2: TermId,
        is_le: bool,
        lit: Lit,
    ) -> TheoryCheckResult {
        let v1 = self.get_or_create_var(t1);
        let v2 = self.get_or_create_var(t2);

        let mut expr = LinearExpr::new();
        // Constants ONE and NEG_ONE have den=1, add_term with these cannot overflow.
        expr.add_term(v1, Rational::ONE)
            .expect("invariant: add_term with den=1 ONE cannot overflow");
        expr.add_term(v2, Rational::ONE.neg())
            .expect("invariant: add_term with den=1 NEG_ONE cannot overflow");

        // t1 - t2 ≤ 0  → bound = (0, 0)
        // t1 - t2 < 0  → bound = (0, -1) meaning 0 - epsilon
        let bound = if is_le {
            DeltaRational::from_rational(Rational::ZERO)
        } else {
            DeltaRational::new(Rational::ZERO, Rational::NEG_ONE)
        };
        self.add_upper_constraint(expr, bound, lit)
    }

    /// Read-only diagnostic: do all bounds hold? Used by `debug_assert!` in `check()`.
    fn is_consistent(&self) -> bool {
        for row in &self.tableau {
            let Some(value) = row.evaluate(&self.assignment) else {
                // Overflow during diagnostic — conservatively report inconsistent
                // so the debug_assert fires and the issue is surfaced (#2324).
                return false;
            };

            if let Some(lower) = self.lower_bounds.get(&row.basic_var) {
                if value < lower.value {
                    return false;
                }
            }

            if let Some(upper) = self.upper_bounds.get(&row.basic_var) {
                if value > upper.value {
                    return false;
                }
            }
        }

        // Skip basic vars: their assignment entries may be stale after pivots.
        let basic_vars: HashSet<ArithVar> = self.tableau.iter().map(|r| r.basic_var).collect();
        for (&var, &value) in &self.assignment {
            if basic_vars.contains(&var) {
                continue;
            }
            if let Some(lower) = self.lower_bounds.get(&var) {
                if value < lower.value {
                    return false;
                }
            }

            if let Some(upper) = self.upper_bounds.get(&var) {
                if value > upper.value {
                    return false;
                }
            }
        }

        true
    }

    /// Get statistics
    pub fn stats(&self) -> ArithStats {
        ArithStats {
            num_vars: self.next_id as usize,
            num_rows: self.tableau.len(),
            num_lower_bounds: self.lower_bounds.len(),
            num_upper_bounds: self.upper_bounds.len(),
        }
    }
}
