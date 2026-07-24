// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Conflict analysis for pseudo-Boolean CDCL.
//!
//! This module implements a lightweight RoundingSat-style analysis loop on top
//! of the existing `PbConstraint`/`PbRule` proof kernel. The learned
//! constraint is derived by replayable PB proof steps, while local arithmetic
//! helpers mirror the same transformations to keep the analysis logic simple.

use std::collections::HashMap;

use super::{verify_rule, PbConstraint, PbError, PbFormula, PbRule};

/// A single assignment on the PB trail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PbTrailEntry {
    /// Assigned literal in DIMACS convention.
    pub literal: i32,
    /// Decision level where the assignment was made.
    pub decision_level: u32,
    /// Reason constraint index in the formula, or `None` for decisions.
    pub reason: Option<usize>,
}

/// A CDCL-style assignment trail for PB reasoning.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PbTrail {
    /// Number of variables in the trail.
    pub num_vars: u32,
    /// Current assignment, 1-indexed.
    pub assignment: Vec<Option<bool>>,
    /// Ordered trail entries.
    pub trail: Vec<PbTrailEntry>,
    /// Trail cut points for decisions.
    pub trail_lim: Vec<usize>,
    /// Current decision level.
    pub decision_level: u32,
}

impl PbTrail {
    /// Create an empty trail for `num_vars` variables.
    #[must_use]
    pub(crate) fn new(num_vars: u32) -> Self {
        Self {
            num_vars,
            assignment: vec![None; (num_vars + 1) as usize],
            trail: Vec::new(),
            trail_lim: Vec::new(),
            decision_level: 0,
        }
    }

    /// Assign a literal at the current decision level.
    pub(crate) fn assign(&mut self, literal: i32, reason: Option<usize>) -> Result<(), PbError> {
        let var = validate_literal(literal, self.num_vars)?;
        let slot = self
            .assignment
            .get_mut(var as usize)
            .ok_or(PbError::VariableOutOfRange {
                var,
                num_vars: self.num_vars,
            })?;

        if slot.is_some() {
            return Err(analysis_error(format!(
                "variable {var} is already assigned on the PB trail"
            )));
        }

        *slot = Some(literal > 0);
        self.trail.push(PbTrailEntry {
            literal,
            decision_level: self.decision_level,
            reason,
        });
        Ok(())
    }

    /// Start a new decision level and assign a decision literal.
    pub(crate) fn decide(&mut self, literal: i32) -> Result<(), PbError> {
        self.decision_level += 1;
        self.trail_lim.push(self.trail.len());
        self.assign(literal, None)
    }

    /// Backtrack to the given decision level.
    pub(crate) fn backtrack_to(&mut self, level: u32) -> Result<(), PbError> {
        if level > self.decision_level {
            return Err(analysis_error(format!(
                "cannot backtrack PB trail from level {} to level {level}",
                self.decision_level
            )));
        }

        while self
            .trail
            .last()
            .is_some_and(|entry| entry.decision_level > level)
        {
            if let Some(entry) = self.trail.pop() {
                let var = entry.literal.unsigned_abs() as usize;
                if let Some(slot) = self.assignment.get_mut(var) {
                    *slot = None;
                }
            }
        }

        self.trail_lim.truncate(level as usize);
        self.decision_level = level;
        Ok(())
    }

    /// Evaluate a literal under the current assignment.
    pub(crate) fn literal_value(&self, literal: i32) -> Result<Option<bool>, PbError> {
        let var = validate_literal(literal, self.num_vars)?;
        let polarity = literal > 0;
        Ok(self
            .assignment
            .get(var as usize)
            .copied()
            .flatten()
            .map(|value| value == polarity))
    }

    /// Return the decision level for an assigned variable.
    #[must_use]
    pub(crate) fn level_of(&self, var: u32) -> Option<u32> {
        self.trail
            .iter()
            .find(|entry| entry.literal.unsigned_abs() == var)
            .map(|entry| entry.decision_level)
    }

    /// Return the trail position for an assigned variable.
    #[must_use]
    pub(crate) fn trail_index_of(&self, var: u32) -> Option<usize> {
        self.trail
            .iter()
            .position(|entry| entry.literal.unsigned_abs() == var)
    }

    /// Return the reason constraint for the complement of a falsified literal.
    pub(crate) fn reason_for_false_literal(
        &self,
        falsified_literal: i32,
    ) -> Result<usize, PbError> {
        let assigned_literal = -falsified_literal;
        let entry = self
            .trail
            .iter()
            .find(|entry| entry.literal == assigned_literal)
            .ok_or_else(|| {
                analysis_error(format!(
                    "no PB trail entry found for falsified literal {falsified_literal}"
                ))
            })?;

        entry.reason.ok_or_else(|| {
            analysis_error(format!(
                "no reason constraint available for falsified literal {falsified_literal}"
            ))
        })
    }
}

/// A detected PB conflict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PbConflict {
    /// Index of the conflicting input constraint.
    pub index: usize,
    /// The conflicting constraint itself.
    pub constraint: PbConstraint,
}

/// A replayable chain of PB proof rules.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct ProofChain {
    /// The emitted rules.
    pub rules: Vec<PbRule>,
    derived: Vec<PbConstraint>,
}

impl ProofChain {
    /// Create an empty proof chain.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Append a new proof rule and verify the derived constraint eagerly.
    pub(crate) fn push(&mut self, formula: &PbFormula, rule: PbRule) -> Result<usize, PbError> {
        let constraint = verify_rule(&self.derived, formula, &rule)?;
        let next_idx = self.derived.len();
        self.rules.push(rule);
        self.derived.push(constraint);
        Ok(next_idx)
    }

    /// Introduce an input constraint.
    pub(crate) fn input(&mut self, formula: &PbFormula, index: usize) -> Result<usize, PbError> {
        self.push(formula, PbRule::Input(index))
    }

    /// Borrow a previously derived constraint.
    pub(crate) fn constraint(&self, index: usize) -> Result<&PbConstraint, PbError> {
        self.derived.get(index).ok_or(PbError::IndexOutOfBounds {
            index,
            count: self.derived.len(),
        })
    }

    /// Consume the chain and return its rules.
    #[must_use]
    pub(crate) fn into_rules(self) -> Vec<PbRule> {
        self.rules
    }
}

/// Result of PB conflict analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PbConflictAnalysisResult {
    /// Learned PB constraint.
    pub learned_constraint: PbConstraint,
    /// Backtrack level for the learned constraint.
    pub backtrack_level: u32,
    /// Proof steps deriving `learned_constraint`.
    pub proof_chain: Vec<PbRule>,
}

/// PB conflict analysis engine.
#[derive(Debug, Clone)]
pub(crate) struct PbConflictAnalyzer<'a> {
    formula: &'a PbFormula,
    use_rounding: bool,
}

impl<'a> PbConflictAnalyzer<'a> {
    /// Create a conflict analyzer with RoundingSat-style rounding enabled.
    #[must_use]
    pub(crate) fn new(formula: &'a PbFormula) -> Self {
        Self {
            formula,
            use_rounding: true,
        }
    }

    /// Create a conflict analyzer with explicit rounding policy.
    #[must_use]
    pub(crate) fn with_rounding(formula: &'a PbFormula, use_rounding: bool) -> Self {
        Self {
            formula,
            use_rounding,
        }
    }

    /// Detect the first conflicting constraint under the current partial assignment.
    pub(crate) fn detect_conflict(&self, trail: &PbTrail) -> Result<Option<PbConflict>, PbError> {
        validate_trail_compatibility(trail, self.formula.num_vars)?;

        for (index, constraint) in self.formula.constraints.iter().enumerate() {
            validate_constraint(constraint, self.formula.num_vars)?;
            let slack = conflict_slack(constraint, &trail.assignment, self.formula.num_vars)?;
            if slack < 0 {
                return Ok(Some(PbConflict {
                    index,
                    constraint: constraint.clone(),
                }));
            }
        }
        Ok(None)
    }

    /// Cancellation-based weakening on a pivot literal.
    ///
    /// If both `literal` and `-literal` are present, the method cancels the
    /// common amount using the identity `l + ~l = 1`, decreasing the degree
    /// accordingly. If only `literal` is present, it is weakened away by
    /// removing the term and lowering the degree by its coefficient.
    pub(crate) fn weaken(
        &self,
        constraint: &PbConstraint,
        literal: i32,
    ) -> Result<PbConstraint, PbError> {
        let exact = coefficient_of(constraint, literal);
        let complement = coefficient_of(constraint, -literal);

        let cancel_amount = match (exact, complement) {
            (Some(coeff), Some(other)) => coeff.min(other),
            (Some(coeff), None) => coeff,
            (None, _) => {
                return Err(analysis_error(format!(
                    "cannot weaken literal {literal}: pivot not present"
                )));
            }
        };

        let mut terms = Vec::with_capacity(constraint.terms.len());
        for &(coeff, lit) in &constraint.terms {
            let next_coeff = if lit == literal || (lit == -literal && complement.is_some()) {
                coeff - cancel_amount
            } else {
                coeff
            };

            if next_coeff != 0 {
                terms.push((next_coeff, lit));
            }
        }

        let mut weakened = PbConstraint {
            terms,
            degree: constraint.degree - cancel_amount,
        };
        weakened
            .terms
            .sort_by_key(|&(_, lit)| (lit.unsigned_abs(), lit < 0));
        Ok(weakened)
    }

    /// Round a constraint so that the pivot literal has coefficient `1`.
    pub(crate) fn round_to_one(
        &self,
        constraint: &PbConstraint,
        pivot_literal: i32,
    ) -> Result<PbConstraint, PbError> {
        let coeff = coefficient_of(constraint, pivot_literal).ok_or_else(|| {
            analysis_error(format!(
                "cannot round on literal {pivot_literal}: pivot not present"
            ))
        })?;

        if coeff <= 0 {
            return Err(analysis_error(format!(
                "cannot round on literal {pivot_literal}: coefficient {coeff} is not positive"
            )));
        }

        if coeff == 1 {
            return Ok(constraint.clone());
        }

        Ok(divide_constraint(constraint, coeff))
    }

    /// Saturate a PB constraint after weakening or resolution.
    #[must_use]
    pub(crate) fn saturate(&self, constraint: &PbConstraint) -> PbConstraint {
        saturate_constraint(constraint)
    }

    /// Run the full PB conflict analysis loop and return a learned constraint.
    pub(crate) fn analyze_conflict(
        &self,
        trail: &PbTrail,
        conflict_index: usize,
    ) -> Result<PbConflictAnalysisResult, PbError> {
        validate_trail_compatibility(trail, self.formula.num_vars)?;

        let conflict_constraint =
            self.formula
                .constraints
                .get(conflict_index)
                .ok_or(PbError::IndexOutOfBounds {
                    index: conflict_index,
                    count: self.formula.constraints.len(),
                })?;

        validate_constraint(conflict_constraint, self.formula.num_vars)?;

        let mut proof = ProofChain::new();
        let mut current_step = proof.input(self.formula, conflict_index)?;
        let max_iterations = trail.trail.len().max(1);
        let mut iterations = 0usize;

        loop {
            let current_constraint = proof.constraint(current_step)?.clone();

            if is_uip(&current_constraint, trail)? {
                let backtrack_level = compute_backtrack_level(&current_constraint, trail)?;
                return Ok(PbConflictAnalysisResult {
                    learned_constraint: current_constraint,
                    backtrack_level,
                    proof_chain: proof.into_rules(),
                });
            }

            iterations += 1;
            if iterations > max_iterations {
                return Err(analysis_error(
                    "PB conflict analysis exceeded the trail-length resolution bound",
                ));
            }

            let highest_level =
                highest_falsified_level(&current_constraint, trail)?.ok_or_else(|| {
                    analysis_error("PB conflict analysis did not find a falsified pivot level")
                })?;

            let pivot = last_assigned_falsified_literal_at_level(
                &current_constraint,
                trail,
                highest_level,
            )?
            .ok_or_else(|| analysis_error("PB conflict analysis did not find a pivot literal"))?;

            let reason_index = trail.reason_for_false_literal(pivot)?;
            let reason_constraint = self
                .formula
                .constraints
                .get(reason_index)
                .ok_or(PbError::IndexOutOfBounds {
                    index: reason_index,
                    count: self.formula.constraints.len(),
                })?
                .clone();
            validate_constraint(&reason_constraint, self.formula.num_vars)?;

            let mut local_left = current_constraint;
            let mut local_right = reason_constraint;
            let mut left_step = current_step;
            let mut right_step = proof.input(self.formula, reason_index)?;

            if self.use_rounding {
                let left_coeff = coefficient_of(&local_left, pivot).ok_or_else(|| {
                    analysis_error(format!(
                        "current PB constraint lost pivot literal {pivot} before rounding"
                    ))
                })?;
                if left_coeff > 1 {
                    local_left = self.round_to_one(&local_left, pivot)?;
                    left_step = proof.push(
                        self.formula,
                        PbRule::Division {
                            constraint: left_step,
                            divisor: left_coeff,
                        },
                    )?;
                }

                let reason_pivot = -pivot;
                let right_coeff = coefficient_of(&local_right, reason_pivot).ok_or_else(|| {
                    analysis_error(format!(
                        "reason constraint does not contain complementary pivot {reason_pivot}"
                    ))
                })?;
                if right_coeff > 1 {
                    local_right = self.round_to_one(&local_right, reason_pivot)?;
                    right_step = proof.push(
                        self.formula,
                        PbRule::Division {
                            constraint: right_step,
                            divisor: right_coeff,
                        },
                    )?;
                }
            }

            let resolved_local = self.resolve_with_weaken(&local_left, &local_right, pivot)?;
            let resolution_rule = generalized_resolution_rule(
                &local_left,
                left_step,
                &local_right,
                right_step,
                pivot,
            )?;
            current_step = proof.push(self.formula, resolution_rule)?;
            let resolved_proof = proof.constraint(current_step)?.clone();
            if resolved_proof != resolved_local {
                return Err(analysis_error(
                    "local PB resolution diverged from the proof-kernel result",
                ));
            }

            let saturated_local = self.saturate(&resolved_local);
            if saturated_local != resolved_local {
                current_step = proof.push(self.formula, PbRule::Saturation(current_step))?;
                let saturated_proof = proof.constraint(current_step)?.clone();
                if saturated_proof != saturated_local {
                    return Err(analysis_error(
                        "local PB saturation diverged from the proof-kernel result",
                    ));
                }
            }
        }
    }

    fn resolve_with_weaken(
        &self,
        conflict: &PbConstraint,
        reason: &PbConstraint,
        pivot: i32,
    ) -> Result<PbConstraint, PbError> {
        let conflict_coeff = coefficient_of(conflict, pivot).ok_or_else(|| {
            analysis_error(format!(
                "cannot resolve on literal {pivot}: missing from conflict constraint"
            ))
        })?;
        let reason_coeff = coefficient_of(reason, -pivot).ok_or_else(|| {
            analysis_error(format!(
                "cannot resolve on literal {pivot}: missing complement in reason constraint"
            ))
        })?;

        if conflict_coeff <= 0 || reason_coeff <= 0 {
            return Err(analysis_error(format!(
                "cannot resolve on literal {pivot}: non-positive pivot coefficients"
            )));
        }

        let scaled_conflict = multiply_constraint(conflict, reason_coeff);
        let scaled_reason = multiply_constraint(reason, conflict_coeff);
        let combined = add_constraints(&scaled_conflict, &scaled_reason);
        self.weaken(&combined, pivot)
    }
}

fn highest_falsified_level(
    constraint: &PbConstraint,
    trail: &PbTrail,
) -> Result<Option<u32>, PbError> {
    let mut highest = None;

    for entry in &trail.trail {
        let falsified_literal = -entry.literal;
        if coefficient_of(constraint, falsified_literal).is_some() {
            highest = Some(highest.map_or(entry.decision_level, |level: u32| {
                level.max(entry.decision_level)
            }));
        }
    }

    Ok(highest)
}

fn count_falsified_at_level(
    constraint: &PbConstraint,
    trail: &PbTrail,
    level: u32,
) -> Result<usize, PbError> {
    let mut count = 0usize;

    for entry in &trail.trail {
        if entry.decision_level != level {
            continue;
        }

        let falsified_literal = -entry.literal;
        if coefficient_of(constraint, falsified_literal).is_some()
            && trail.literal_value(falsified_literal)? == Some(false)
        {
            count += 1;
        }
    }

    Ok(count)
}

fn is_uip(constraint: &PbConstraint, trail: &PbTrail) -> Result<bool, PbError> {
    match highest_falsified_level(constraint, trail)? {
        Some(level) => Ok(count_falsified_at_level(constraint, trail, level)? <= 1),
        None => Ok(constraint.is_contradiction()),
    }
}

fn last_assigned_falsified_literal_at_level(
    constraint: &PbConstraint,
    trail: &PbTrail,
    level: u32,
) -> Result<Option<i32>, PbError> {
    for entry in trail.trail.iter().rev() {
        if entry.decision_level != level {
            continue;
        }

        let falsified_literal = -entry.literal;
        if coefficient_of(constraint, falsified_literal).is_some()
            && trail.literal_value(falsified_literal)? == Some(false)
        {
            return Ok(Some(falsified_literal));
        }
    }

    Ok(None)
}

fn compute_backtrack_level(constraint: &PbConstraint, trail: &PbTrail) -> Result<u32, PbError> {
    let highest_level = highest_falsified_level(constraint, trail)?.unwrap_or(0);
    let mut backtrack_level = 0u32;

    for entry in &trail.trail {
        let falsified_literal = -entry.literal;
        if coefficient_of(constraint, falsified_literal).is_none() {
            continue;
        }

        if trail.literal_value(falsified_literal)? != Some(false) {
            continue;
        }

        if entry.decision_level != highest_level {
            backtrack_level = backtrack_level.max(entry.decision_level);
        }
    }

    Ok(backtrack_level)
}

fn generalized_resolution_rule(
    left_constraint: &PbConstraint,
    left_index: usize,
    right_constraint: &PbConstraint,
    right_index: usize,
    pivot: i32,
) -> Result<PbRule, PbError> {
    let var = pivot.unsigned_abs();

    if coefficient_of(left_constraint, pivot).is_some()
        && coefficient_of(right_constraint, -pivot).is_some()
    {
        if pivot > 0 {
            Ok(PbRule::GeneralizedResolution {
                left: left_index,
                right: right_index,
                var,
            })
        } else {
            Ok(PbRule::GeneralizedResolution {
                left: right_index,
                right: left_index,
                var,
            })
        }
    } else {
        Err(analysis_error(format!(
            "cannot emit PB generalized resolution on pivot literal {pivot}"
        )))
    }
}

fn validate_constraint(constraint: &PbConstraint, num_vars: u32) -> Result<(), PbError> {
    for &(_, literal) in &constraint.terms {
        validate_literal(literal, num_vars)?;
    }
    Ok(())
}

fn validate_trail_compatibility(trail: &PbTrail, num_vars: u32) -> Result<(), PbError> {
    if trail.num_vars < num_vars {
        return Err(PbError::VariableOutOfRange {
            var: num_vars,
            num_vars: trail.num_vars,
        });
    }
    Ok(())
}

fn validate_literal(literal: i32, num_vars: u32) -> Result<u32, PbError> {
    let var = literal.unsigned_abs();
    if var == 0 || var > num_vars {
        return Err(PbError::LiteralOutOfBounds { literal });
    }
    Ok(var)
}

fn conflict_slack(
    constraint: &PbConstraint,
    assignment: &[Option<bool>],
    num_vars: u32,
) -> Result<i64, PbError> {
    let mut slack = -constraint.degree;

    for &(coeff, literal) in &constraint.terms {
        validate_literal(literal, num_vars)?;
        let var = literal.unsigned_abs() as usize;
        let polarity = literal > 0;
        match assignment.get(var).copied().flatten() {
            Some(value) if value == polarity => {
                slack += coeff;
            }
            Some(_) => {}
            None => {
                slack += coeff;
            }
        }
    }

    Ok(slack)
}

fn coefficient_of(constraint: &PbConstraint, literal: i32) -> Option<i64> {
    let coeff: i64 = constraint
        .terms
        .iter()
        .filter(|&&(_, lit)| lit == literal)
        .map(|&(coeff, _)| coeff)
        .sum();

    if coeff == 0 {
        None
    } else {
        Some(coeff)
    }
}

fn add_constraints(left: &PbConstraint, right: &PbConstraint) -> PbConstraint {
    let mut term_map: HashMap<i32, i64> = HashMap::new();

    for &(coeff, lit) in &left.terms {
        *term_map.entry(lit).or_insert(0) += coeff;
    }
    for &(coeff, lit) in &right.terms {
        *term_map.entry(lit).or_insert(0) += coeff;
    }

    let mut terms: Vec<(i64, i32)> = term_map
        .into_iter()
        .filter(|&(_, coeff)| coeff != 0)
        .map(|(lit, coeff)| (coeff, lit))
        .collect();
    terms.sort_by_key(|&(_, lit)| (lit.unsigned_abs(), lit < 0));

    PbConstraint {
        terms,
        degree: left.degree + right.degree,
    }
}

fn multiply_constraint(constraint: &PbConstraint, scalar: i64) -> PbConstraint {
    PbConstraint {
        terms: constraint
            .terms
            .iter()
            .map(|&(coeff, lit)| (coeff * scalar, lit))
            .collect(),
        degree: constraint.degree * scalar,
    }
}

fn divide_constraint(constraint: &PbConstraint, divisor: i64) -> PbConstraint {
    PbConstraint {
        terms: constraint
            .terms
            .iter()
            .map(|&(coeff, lit)| (div_ceil_signed(coeff, divisor), lit))
            .collect(),
        degree: div_ceil_signed(constraint.degree, divisor),
    }
}

fn saturate_constraint(constraint: &PbConstraint) -> PbConstraint {
    if constraint.degree <= 0 {
        return constraint.clone();
    }

    PbConstraint {
        terms: constraint
            .terms
            .iter()
            .map(|&(coeff, lit)| (coeff.min(constraint.degree), lit))
            .collect(),
        degree: constraint.degree,
    }
}

fn div_ceil_signed(a: i64, b: i64) -> i64 {
    debug_assert!(b > 0);
    if a >= 0 {
        (a + b - 1) / b
    } else {
        -((-a) / b)
    }
}

fn analysis_error(message: impl Into<String>) -> PbError {
    PbError::ConversionError(message.into())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pb_trail_backtrack_restores_assignment_expected() {
        let mut trail = PbTrail::new(3);
        trail.decide(1).expect("decision should succeed");
        trail
            .assign(-2, Some(0))
            .expect("propagation should succeed");
        trail.decide(3).expect("second decision should succeed");

        assert_eq!(trail.decision_level, 2);
        assert_eq!(trail.literal_value(3).expect("literal lookup"), Some(true));
        assert_eq!(trail.literal_value(-2).expect("literal lookup"), Some(true));

        trail.backtrack_to(1).expect("backtrack should succeed");

        assert_eq!(trail.decision_level, 1);
        assert_eq!(trail.literal_value(3).expect("literal lookup"), None);
        assert_eq!(trail.literal_value(-2).expect("literal lookup"), Some(true));
    }

    #[test]
    fn test_pb_conflict_analyzer_detect_conflict_partial_assignment_expected() {
        let mut formula = PbFormula::new(2);
        formula.add_constraint(PbConstraint::new(vec![(1, 1), (1, 2)], 1));
        formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));

        let analyzer = PbConflictAnalyzer::new(&formula);
        let mut trail = PbTrail::new(2);
        trail.assign(-1, None).expect("assignment should succeed");

        let conflict = analyzer
            .detect_conflict(&trail)
            .expect("conflict detection should succeed")
            .expect("a conflict should be detected");

        assert_eq!(conflict.index, 1);
        assert_eq!(conflict.constraint, PbConstraint::new(vec![(1, 1)], 1));
    }

    #[test]
    fn test_pb_conflict_analyzer_weaken_cancellation_expected() {
        let formula = PbFormula::new(2);
        let analyzer = PbConflictAnalyzer::new(&formula);
        let constraint = PbConstraint::new(vec![(2, 1), (1, -1), (1, 2)], 3);

        let weakened = analyzer
            .weaken(&constraint, 1)
            .expect("weakening should succeed");

        assert_eq!(weakened.degree, 2);
        assert_eq!(coefficient_of(&weakened, 1), Some(1));
        assert_eq!(coefficient_of(&weakened, -1), None);
        assert_eq!(coefficient_of(&weakened, 2), Some(1));
    }

    #[test]
    fn test_pb_conflict_analyzer_round_to_one_divides_coefficients_expected() {
        let formula = PbFormula::new(2);
        let analyzer = PbConflictAnalyzer::new(&formula);
        let constraint = PbConstraint::new(vec![(3, -1), (4, 2)], 5);

        let rounded = analyzer
            .round_to_one(&constraint, -1)
            .expect("rounding should succeed");

        assert_eq!(coefficient_of(&rounded, -1), Some(1));
        assert_eq!(coefficient_of(&rounded, 2), Some(2));
        assert_eq!(rounded.degree, 2);
    }

    #[test]
    fn test_pb_conflict_analyzer_analyze_conflict_clause_chain_expected() {
        let mut formula = PbFormula::new(3);
        formula.add_constraint(PbConstraint::from_clause(&[-1, 2]));
        formula.add_constraint(PbConstraint::from_clause(&[-1, 3]));
        formula.add_constraint(PbConstraint::from_clause(&[-2, -3]));

        let analyzer = PbConflictAnalyzer::new(&formula);
        let mut trail = PbTrail::new(3);
        trail.decide(1).expect("decision should succeed");
        trail
            .assign(2, Some(0))
            .expect("propagation should succeed");
        trail
            .assign(3, Some(1))
            .expect("propagation should succeed");

        let result = analyzer
            .analyze_conflict(&trail, 2)
            .expect("conflict analysis should succeed");

        assert_eq!(result.learned_constraint, PbConstraint::from_clause(&[-1]));
        assert_eq!(result.backtrack_level, 0);

        let mut derived = Vec::new();
        for rule in &result.proof_chain {
            let constraint =
                verify_rule(&derived, &formula, rule).expect("proof step should verify");
            derived.push(constraint);
        }

        assert_eq!(derived.last(), Some(&result.learned_constraint));
    }
}
