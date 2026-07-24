// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! VeriPB proof format compiler.
//!
//! Compiles PB proof derivations into the VeriPB text format for external
//! checker interoperability. Supports the core VeriPB operations:
//! - `p` (polynomial addition / derivation)
//! - `d` (delete constraint)
//! - `u` (undo / backtrack)
//! - `c` (conclude: empty constraint derived = UNSAT)
//!
//! ## Reference
//!
//! Gocht, Nordstrom, "Certifying Parity Reasoning Efficiently Using
//! Pseudo-Boolean Proofs", AAAI 2021.
//! VeriPB format: <https://github.com/StephanGocht/VeriPB>

use std::fmt::Write;

use super::normalize::normalize;
use super::rules::{verify_rule, PbRule};
use super::types::{PbConstraint, PbFormula};
use super::PbError;
use crate::sat_verify::proof_complexity::cutting_planes::{CpStep, CuttingPlanesProof};

/// A single step in a VeriPB proof.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum VeriPbStep {
    /// Derive a new constraint via a proof rule.
    PolynomialAddition { result: PbConstraint, rule: PbRule },
    /// Derive a new constraint via reverse unit propagation.
    ReverseUnitPropagation { result: PbConstraint },
    /// Derive a new constraint via a redundancy argument.
    ///
    /// This is currently checked with the same conservative UP-based check as
    /// `ReverseUnitPropagation`.
    RedundantAddition { result: PbConstraint },
    /// Undo: backtrack to a given level, removing derived constraints.
    Undo { level: u32 },
    /// Delete a constraint by ID (0-indexed into the derived sequence).
    Delete { id: usize },
    /// Conclude: the empty constraint (contradiction) has been derived.
    Conclude,
}

/// A complete VeriPB proof.
#[derive(Debug, Clone)]
pub struct VeriPbProof {
    /// The formula being refuted.
    pub formula: PbFormula,
    /// The proof steps.
    pub steps: Vec<VeriPbStep>,
}

impl VeriPbProof {
    /// Create a new proof for the given formula.
    #[must_use]
    pub fn new(formula: PbFormula) -> Self {
        Self {
            formula,
            steps: Vec::new(),
        }
    }

    /// Add a derivation step. Returns the step index.
    pub fn add_step(&mut self, step: VeriPbStep) -> usize {
        let idx = self.steps.len();
        self.steps.push(step);
        idx
    }

    /// Verify the proof: replay all derivation steps and check for contradiction.
    ///
    /// SOUNDNESS NOTE: Deletion steps mark constraints as unavailable. The
    /// `verify_rule` function receives `Option<PbConstraint>` entries: `None`
    /// for deleted constraints, `Some(...)` for live ones. References to
    /// deleted constraints fail with `IndexOutOfBounds`.
    pub fn verify(&self) -> Result<(), PbError> {
        let mut derived: Vec<Option<PbConstraint>> = Vec::new();
        let mut concluded = false;

        for step in &self.steps {
            match step {
                VeriPbStep::PolynomialAddition { result: _, rule } => {
                    let live = dense_live_constraints(&derived);
                    // SOUNDNESS FIX: Check that all constraint references in the rule
                    // point to non-deleted constraints.
                    check_rule_references_live(rule, &derived)?;
                    let constraint = verify_rule(&live, &self.formula, rule)?;
                    derived.push(Some(constraint));
                }
                VeriPbStep::ReverseUnitPropagation { result } => {
                    verify_rup_constraint(&self.formula, &derived, result)?;
                    derived.push(Some(result.clone()));
                }
                VeriPbStep::RedundantAddition { result } => {
                    verify_rup_constraint(&self.formula, &derived, result)?;
                    derived.push(Some(result.clone()));
                }
                VeriPbStep::Delete { id } => {
                    // SOUNDNESS FIX: VeriPB deletion marks a constraint as
                    // unavailable. Previously we just checked the index was in
                    // range but never actually invalidated the constraint,
                    // allowing subsequent rules to reference deleted constraints.
                    if *id >= derived.len() {
                        return Err(PbError::IndexOutOfBounds {
                            index: *id,
                            count: derived.len(),
                        });
                    }
                    derived[*id] = None;
                }
                VeriPbStep::Undo { level: _ } => {
                    // Undo operations are for solver integration and don't
                    // affect proof soundness verification.
                }
                VeriPbStep::Conclude => {
                    // Check that the last derived constraint is a contradiction.
                    match derived.last() {
                        Some(Some(c)) if c.is_contradiction() => {
                            concluded = true;
                        }
                        _ => return Err(PbError::NoContradiction),
                    }
                }
            }
        }

        if concluded {
            Ok(())
        } else {
            Err(PbError::NoContradiction)
        }
    }

    /// Output the proof in VeriPB text format.
    #[must_use]
    pub fn to_veripb_format(&self) -> String {
        let mut out = String::new();

        // Header: pseudo-Boolean proof version.
        let _ = writeln!(out, "pseudo-Boolean proof version 2.0");

        // Output formula constraints as "f" lines.
        let _ = writeln!(out, "f {}", self.formula.constraints.len());

        for step in &self.steps {
            match step {
                VeriPbStep::PolynomialAddition { result, rule: _ } => {
                    let _ = writeln!(out, "p {}", format_pb_constraint(result));
                }
                VeriPbStep::ReverseUnitPropagation { result } => {
                    let _ = writeln!(out, "rup {}", format_pb_constraint(result));
                }
                VeriPbStep::RedundantAddition { result } => {
                    let _ = writeln!(out, "red {}", format_pb_constraint(result));
                }
                VeriPbStep::Undo { level } => {
                    let _ = writeln!(out, "u {level}");
                }
                VeriPbStep::Delete { id } => {
                    // VeriPB uses 1-indexed IDs (formula constraints first).
                    let veripb_id = self.formula.constraints.len() + id + 1;
                    let _ = writeln!(out, "d {veripb_id}");
                }
                VeriPbStep::Conclude => {
                    let _ = writeln!(out, "c");
                }
            }
        }

        let _ = writeln!(out, "end pseudo-Boolean proof");
        out
    }

    /// Certificate size in bytes (VeriPB text format size).
    #[must_use]
    pub fn certificate_size(&self) -> usize {
        self.to_veripb_format().len()
    }
}

/// Format a PB constraint in VeriPB notation.
///
/// Format: `a1 x1 a2 x2 ... >= k ;`
/// Negated literals are written as `~xi`.
fn format_pb_constraint(c: &PbConstraint) -> String {
    let mut out = String::new();
    for &(coeff, lit) in &c.terms {
        if lit > 0 {
            let _ = write!(out, "{coeff} x{lit} ");
        } else {
            let _ = write!(out, "{coeff} ~x{} ", -lit);
        }
    }
    let _ = write!(out, ">= {} ;", c.degree);
    out
}

/// Compile a cutting planes proof into VeriPB format.
///
/// Maps CpInequality (variable-indexed coefficients) to PbConstraint
/// (literal-based terms), and CpStep to PbRule/VeriPbStep.
pub(crate) fn cutting_planes_to_veripb(
    cp_proof: &CuttingPlanesProof,
    formula: &PbFormula,
) -> Result<VeriPbProof, PbError> {
    let mut veripb = VeriPbProof::new(formula.clone());
    let num_cp_steps = cp_proof.len();

    for step_idx in 0..num_cp_steps {
        let cp_ineq = cp_proof
            .inequality_at(step_idx)
            .ok_or_else(|| PbError::ConversionError(format!("missing CP step {step_idx}")))?;

        // Convert CpInequality to PbConstraint.
        let pb_constraint = cp_inequality_to_pb(cp_ineq);

        // Determine the PbRule based on CpStep type.
        // We need to inspect the CP proof to figure out what rule was used.
        // Since CuttingPlanesProof doesn't expose steps directly, we
        // reconstruct rules by matching against input constraints.
        let rule = reconstruct_cp_rule(cp_proof, formula, step_idx)?;

        veripb.add_step(VeriPbStep::PolynomialAddition {
            result: pb_constraint,
            rule,
        });
    }

    // Add conclude step if the proof derives a contradiction.
    if cp_proof.verify() {
        veripb.add_step(VeriPbStep::Conclude);
    }

    Ok(veripb)
}

/// Convert a CpInequality (variable-indexed coefficients) to a PbConstraint.
fn cp_inequality_to_pb(
    cp: &crate::sat_verify::proof_complexity::cutting_planes::CpInequality,
) -> PbConstraint {
    let terms: Vec<(i64, i32)> = cp
        .coeffs
        .iter()
        .enumerate()
        .filter(|&(_, &c)| c != 0)
        .map(|(i, &c)| {
            // CpInequality uses 0-indexed variables; PB uses 1-indexed literals.
            // Positive coefficient -> positive literal (variable i+1).
            // Negative coefficient -> negate: -|c| * x becomes |c| * ~x, adjust degree.
            // For simplicity in this conversion, keep as-is and let normalize handle it.
            (c, (i + 1) as i32)
        })
        .collect();

    PbConstraint {
        terms,
        degree: cp.rhs,
    }
}

/// Reconstruct the PbRule for a given CP step by pattern-matching.
///
/// Since `CuttingPlanesProof` exposes `inequality_at` but not the step type
/// directly, we try to match input constraints first, then check if the
/// constraint can be derived by known rules.
fn reconstruct_cp_rule(
    cp_proof: &CuttingPlanesProof,
    formula: &PbFormula,
    step_idx: usize,
) -> Result<PbRule, PbError> {
    let cp_ineq = cp_proof
        .inequality_at(step_idx)
        .ok_or_else(|| PbError::ConversionError(format!("missing CP step {step_idx}")))?;

    let pb = cp_inequality_to_pb(cp_ineq);

    // Try to match as an input constraint.
    for (i, fc) in formula.constraints.iter().enumerate() {
        if constraints_equivalent(fc, &pb) {
            return Ok(PbRule::Input(i));
        }
    }

    // For non-input steps, try to reconstruct from prior derived constraints.
    // Check if it's an addition of two prior constraints.
    if step_idx >= 2 {
        for l in 0..step_idx {
            for r in (l + 1)..step_idx {
                if let (Some(lc), Some(rc)) = (cp_proof.inequality_at(l), cp_proof.inequality_at(r))
                {
                    let sum_degree = lc.rhs + rc.rhs;
                    if sum_degree == cp_ineq.rhs {
                        // Check coefficient-wise sum.
                        let n = lc.coeffs.len().max(rc.coeffs.len());
                        let mut match_ok = true;
                        for i in 0..n.max(cp_ineq.coeffs.len()) {
                            let lv = lc.coeffs.get(i).copied().unwrap_or(0);
                            let rv = rc.coeffs.get(i).copied().unwrap_or(0);
                            let sv = cp_ineq.coeffs.get(i).copied().unwrap_or(0);
                            if lv + rv != sv {
                                match_ok = false;
                                break;
                            }
                        }
                        if match_ok {
                            return Ok(PbRule::Addition { left: l, right: r });
                        }
                    }
                }
            }
        }
    }

    // Fallback: treat as a derived constraint from the first prior step.
    // This is a simplification; a full implementation would analyze all CP
    // step types. For the initial kernel, we report what we can.
    if step_idx > 0 {
        // Check for scalar multiplication.
        for prior in 0..step_idx {
            if let Some(pc) = cp_proof.inequality_at(prior) {
                if !pc.coeffs.is_empty() && cp_ineq.rhs != 0 && pc.rhs != 0 {
                    let ratio = cp_ineq.rhs / pc.rhs;
                    if ratio > 0
                        && cp_ineq.rhs == pc.rhs * ratio
                        && pc
                            .coeffs
                            .iter()
                            .enumerate()
                            .all(|(i, &c)| cp_ineq.coeffs.get(i).copied().unwrap_or(0) == c * ratio)
                        && cp_ineq.coeffs.len() <= pc.coeffs.len()
                    {
                        return Ok(PbRule::Multiplication {
                            constraint: prior,
                            scalar: ratio,
                        });
                    }
                }
            }
        }
    }

    // Last resort: we know the constraint is valid because the CP proof verified it,
    // but we can't reconstruct the exact rule. Report it as input 0 with a note.
    // In a production system this would be an error; for the initial kernel we
    // accept this limitation.
    Err(PbError::ConversionError(format!(
        "cannot reconstruct PB rule for CP step {step_idx}"
    )))
}

fn dense_live_constraints(derived: &[Option<PbConstraint>]) -> Vec<PbConstraint> {
    derived
        .iter()
        .map(|opt| opt.clone().unwrap_or_else(|| PbConstraint::new(vec![], 0)))
        .collect()
}

fn verify_rup_constraint(
    formula: &PbFormula,
    derived: &[Option<PbConstraint>],
    result: &PbConstraint,
) -> Result<(), PbError> {
    let normalized = normalize(result);
    validate_constraint_vars(&normalized, formula.num_vars)?;

    let mut constraints = formula.constraints.clone();
    constraints.extend(derived.iter().filter_map(Clone::clone));

    let negated = negate_constraint_for_rup(&normalized);
    if negated.is_contradiction() {
        return Ok(());
    }
    constraints.push(negated);

    if unit_propagates_to_conflict(&constraints, formula.num_vars)? {
        Ok(())
    } else {
        Err(PbError::ConversionError(
            "RUP check did not derive a contradiction".to_string(),
        ))
    }
}

fn negate_constraint_for_rup(constraint: &PbConstraint) -> PbConstraint {
    let total_coeff: i64 = constraint
        .terms
        .iter()
        .map(|&(coeff, _)| coeff.max(0))
        .sum();
    PbConstraint {
        terms: constraint
            .terms
            .iter()
            .map(|&(coeff, lit)| (coeff.max(0), -lit))
            .collect(),
        degree: total_coeff - constraint.degree + 1,
    }
}

fn unit_propagates_to_conflict(
    constraints: &[PbConstraint],
    num_vars: u32,
) -> Result<bool, PbError> {
    let mut assignment = vec![None; num_vars as usize + 1];

    loop {
        for constraint in constraints {
            if matches!(constraint.evaluate(&assignment), Some(false)) {
                return Ok(true);
            }
        }

        let mut changed = false;
        for constraint in constraints {
            for literal in constraint.propagate(&assignment) {
                let var = literal.unsigned_abs();
                if var == 0 || var > num_vars {
                    return Err(PbError::LiteralOutOfBounds { literal });
                }

                let desired = literal > 0;
                let slot = assignment
                    .get_mut(var as usize)
                    .ok_or(PbError::VariableOutOfRange { var, num_vars })?;

                match *slot {
                    Some(current) if current != desired => return Ok(true),
                    Some(_) => {}
                    None => {
                        *slot = Some(desired);
                        changed = true;
                    }
                }
            }
        }

        if !changed {
            return Ok(false);
        }
    }
}

fn validate_constraint_vars(constraint: &PbConstraint, num_vars: u32) -> Result<(), PbError> {
    for &(_, lit) in &constraint.terms {
        let var = lit.unsigned_abs();
        if var == 0 || var > num_vars {
            return Err(PbError::LiteralOutOfBounds { literal: lit });
        }
    }
    Ok(())
}

/// Check that all constraint indices referenced by a PbRule point to
/// non-deleted (live) constraints. Returns an error if any referenced
/// constraint has been deleted.
fn check_rule_references_live(
    rule: &PbRule,
    derived: &[Option<PbConstraint>],
) -> Result<(), PbError> {
    let indices: Vec<usize> = match rule {
        PbRule::Input(_) => vec![],
        PbRule::Addition { left, right } => vec![*left, *right],
        PbRule::Multiplication { constraint, .. } => vec![*constraint],
        PbRule::Division { constraint, .. } => vec![*constraint],
        PbRule::Saturation(idx) => vec![*idx],
        PbRule::Rounding(idx) => vec![*idx],
        PbRule::GeneralizedResolution { left, right, .. } => vec![*left, *right],
    };

    for idx in indices {
        if idx >= derived.len() {
            return Err(PbError::IndexOutOfBounds {
                index: idx,
                count: derived.len(),
            });
        }
        if derived[idx].is_none() {
            return Err(PbError::IndexOutOfBounds {
                index: idx,
                count: derived.len(),
            });
        }
    }
    Ok(())
}

/// Check if two PB constraints are equivalent (same terms and degree).
fn constraints_equivalent(a: &PbConstraint, b: &PbConstraint) -> bool {
    if a.degree != b.degree || a.terms.len() != b.terms.len() {
        return false;
    }
    // Build term maps for comparison (order-independent).
    let map_a: std::collections::HashMap<i32, i64> = a.terms.iter().map(|&(c, l)| (l, c)).collect();
    let map_b: std::collections::HashMap<i32, i64> = b.terms.iter().map(|&(c, l)| (l, c)).collect();
    map_a == map_b
}
