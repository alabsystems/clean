// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! LIA (Linear Integer Arithmetic) checker.
//!
//! Validates `lia_generic` theory lemmas via integer Farkas certificates
//! with GCD tightening.
//!
//! ## Algorithm
//!
//! 1. Each clause literal is a blocking-clause literal (negation of conflict).
//! 2. Negate to get conflict literals.
//! 3. Each conflict literal is an integer inequality.
//! 4. Apply GCD tightening: if all variable coefficients share a GCD g > 1,
//!    divide through and floor the RHS.
//! 5. Multiply each inequality by its non-negative integer Farkas coefficient.
//! 6. Sum all weighted inequalities.
//! 7. The result must be a contradiction: `0 <= negative` (for integers, the
//!    derived bound must yield a non-negative constant, since the weakest
//!    integer contradiction is `0 <= -1`).
//!
//! ## LIA-specific reasoning
//!
//! Unlike LRA, strict inequalities in LIA are equivalent to non-strict:
//! `x < c` is equivalent to `x <= c - 1` for integers.
//!
//! GCD tightening strengthens bounds: `2x + 4y <= 7` becomes `x + 2y <= 3`
//! since the LHS is always even, so the effective bound is `floor(7/2) = 3`.
//!
//! Reference: ay's `~/ay/crates/ay-proof/src/checker/lia_farkas.rs`

use super::dag::{SmtProofDag, SmtStepId, SmtSymbol, SmtTerm, SmtTermId};
use super::trust::{StepTrustLevel, StepVerdict};

/// Name of this checker for trust ledger attribution.
pub(crate) const CHECKER_NAME: &str = "lia";

/// Comparison operator for an integer inequality.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LiaComparison {
    /// lhs <= rhs (normalized form for integers)
    Le,
    /// lhs = rhs
    Eq,
    /// lhs != rhs
    Distinct,
}

/// A linear integer inequality: sum of (coefficient * variable) + constant CMP 0.
///
/// Normalized form: `c1*x1 + c2*x2 + ... + constant CMP 0`.
/// All coefficients and constants are exact integers.
#[derive(Debug, Clone)]
pub(crate) struct LiaInequality {
    /// Variable coefficients: (variable_name, coefficient).
    pub(crate) coefficients: Vec<(String, i64)>,
    /// Constant term.
    pub(crate) constant: i64,
    /// Comparison type.
    pub(crate) comparison: LiaComparison,
}

/// Check a LIA `lia_generic` theory lemma with Farkas coefficients.
///
/// The clause contains blocking literals (negation of the conflict).
/// Farkas coefficients are non-negative integers; the weighted sum of
/// the conflict inequalities must yield a contradiction.
pub(crate) fn check_lia_generic(
    dag: &SmtProofDag,
    step_id: SmtStepId,
    clause: &[SmtTermId],
    coefficients: &[i64],
) -> StepVerdict {
    if clause.is_empty() {
        return fail(step_id, "lia_generic: empty clause");
    }

    if coefficients.len() != clause.len() {
        return fail(
            step_id,
            &format!(
                "lia_generic: {} coefficients for {} literals",
                coefficients.len(),
                clause.len()
            ),
        );
    }

    // Validate all coefficients are non-negative.
    for (i, &c) in coefficients.iter().enumerate() {
        if c < 0 {
            return fail(
                step_id,
                &format!("lia_generic: Farkas coefficient {i} is negative: {c}"),
            );
        }
    }

    // Extract integer inequalities from negated clause literals.
    let mut inequalities: Vec<LiaInequality> = Vec::with_capacity(clause.len());
    for &lit in clause {
        match extract_lia_inequality(dag, lit) {
            Some(ineq) => inequalities.push(ineq),
            None => {
                // Can't parse this literal as integer arithmetic; structurally accept.
                return StepVerdict {
                    step_id,
                    trust_level: StepTrustLevel::StructurallyAccepted,
                    checker: CHECKER_NAME,
                    detail: Some(
                        "lia_generic: could not parse all literals as integer arithmetic"
                            .to_string(),
                    ),
                };
            }
        }
    }

    // Apply GCD tightening to each inequality.
    let tightened: Vec<LiaInequality> = inequalities.iter().map(gcd_tighten).collect();

    // Verify the integer Farkas certificate.
    if verify_lia_farkas(&tightened, coefficients) {
        ok(step_id)
    } else {
        fail(
            step_id,
            "lia_generic: Farkas certificate does not yield contradiction",
        )
    }
}

/// Extract a conflict inequality from a blocking-clause literal.
///
/// A blocking clause literal is the negation of a conflict literal.
/// We negate it and normalize to `<= 0` form for integers.
///
/// For integers, strict inequalities become non-strict:
/// `x < c` becomes `x <= c - 1`, and `x > c` becomes `x >= c + 1`.
pub(crate) fn extract_lia_inequality(dag: &SmtProofDag, lit: SmtTermId) -> Option<LiaInequality> {
    let term = dag.term(lit)?;

    match term {
        // Positive literal in blocking clause: conflict is its negation.
        SmtTerm::App(SmtSymbol::Named(op), args) if args.len() == 2 => {
            extract_negated_relation(dag, op.as_str(), args[0], args[1])
        }
        // not(atom) in blocking clause: conflict is the atom itself.
        SmtTerm::Not(inner) => {
            let inner_term = dag.term(*inner)?;
            match inner_term {
                SmtTerm::App(SmtSymbol::Named(op), args) if args.len() == 2 => {
                    extract_direct_relation(dag, op.as_str(), args[0], args[1])
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Extract the negation of a relation as a `<= 0` integer inequality.
///
/// Given `(op lhs rhs)` as a blocking literal, the conflict is `not(lhs op rhs)`.
///
/// All results normalized to `<= 0` form with integer tightening:
/// - `not(lhs <= rhs)` = `lhs > rhs` = `lhs >= rhs + 1` => `-(lhs - rhs) + 1 <= 0`  (rhs - lhs + 1 <= 0)
/// - `not(lhs >= rhs)` = `lhs < rhs` = `lhs <= rhs - 1` => `(lhs - rhs) + 1 <= 0`
/// - `not(lhs < rhs)`  = `lhs >= rhs` => `-(lhs - rhs) <= 0` (rhs - lhs <= 0)
/// - `not(lhs > rhs)`  = `lhs <= rhs` => `(lhs - rhs) <= 0`
/// - `not(lhs = rhs)`  = `lhs != rhs` (disequality)
/// - `not(distinct)`    = `lhs = rhs` (equality)
fn extract_negated_relation(
    dag: &SmtProofDag,
    op: &str,
    lhs: SmtTermId,
    rhs: SmtTermId,
) -> Option<LiaInequality> {
    // extract_linear_int_atom(lhs, rhs, Le) produces `(lhs - rhs) + C <= 0`
    // where C is the constant part of (lhs - rhs).
    match op {
        "<=" => {
            // not(lhs <= rhs) => lhs >= rhs + 1 => rhs - lhs + 1 <= 0.
            // Start from (lhs - rhs) <= 0, negate to get (rhs - lhs) <= 0, then +1.
            let mut ineq = extract_linear_int_atom(dag, lhs, rhs, LiaComparison::Le)?;
            negate_coefficients(&mut ineq);
            ineq.constant += 1;
            Some(ineq)
        }
        ">=" => {
            // not(lhs >= rhs) => lhs <= rhs - 1 => (lhs - rhs) + 1 <= 0.
            let mut ineq = extract_linear_int_atom(dag, lhs, rhs, LiaComparison::Le)?;
            ineq.constant += 1;
            Some(ineq)
        }
        "<" => {
            // not(lhs < rhs) => lhs >= rhs => rhs - lhs <= 0.
            let mut ineq = extract_linear_int_atom(dag, lhs, rhs, LiaComparison::Le)?;
            negate_coefficients(&mut ineq);
            Some(ineq)
        }
        ">" => {
            // not(lhs > rhs) => lhs <= rhs => lhs - rhs <= 0.
            extract_linear_int_atom(dag, lhs, rhs, LiaComparison::Le)
        }
        "=" => {
            // not(lhs = rhs) => lhs != rhs.
            extract_linear_int_atom(dag, lhs, rhs, LiaComparison::Distinct)
        }
        "distinct" => {
            // not(lhs != rhs) => lhs = rhs.
            extract_linear_int_atom(dag, lhs, rhs, LiaComparison::Eq)
        }
        _ => None,
    }
}

/// Extract a relation directly (no negation) as a `<= 0` integer inequality.
///
/// Given `not((op lhs rhs))` as a blocking literal, the conflict is `(lhs op rhs)`.
fn extract_direct_relation(
    dag: &SmtProofDag,
    op: &str,
    lhs: SmtTermId,
    rhs: SmtTermId,
) -> Option<LiaInequality> {
    match op {
        "<=" => {
            // lhs <= rhs => lhs - rhs <= 0.
            extract_linear_int_atom(dag, lhs, rhs, LiaComparison::Le)
        }
        ">=" => {
            // lhs >= rhs => rhs - lhs <= 0.
            let mut ineq = extract_linear_int_atom(dag, lhs, rhs, LiaComparison::Le)?;
            negate_coefficients(&mut ineq);
            Some(ineq)
        }
        "<" => {
            // lhs < rhs => lhs <= rhs - 1 => (lhs - rhs) + 1 <= 0 (integer).
            let mut ineq = extract_linear_int_atom(dag, lhs, rhs, LiaComparison::Le)?;
            ineq.constant += 1;
            Some(ineq)
        }
        ">" => {
            // lhs > rhs => lhs >= rhs + 1 => rhs - lhs + 1 <= 0 (integer).
            let mut ineq = extract_linear_int_atom(dag, lhs, rhs, LiaComparison::Le)?;
            negate_coefficients(&mut ineq);
            ineq.constant += 1;
            Some(ineq)
        }
        "=" => extract_linear_int_atom(dag, lhs, rhs, LiaComparison::Eq),
        "distinct" => extract_linear_int_atom(dag, lhs, rhs, LiaComparison::Distinct),
        _ => None,
    }
}

/// Negate all coefficients and constant in an inequality.
fn negate_coefficients(ineq: &mut LiaInequality) {
    for (_, c) in ineq.coefficients.iter_mut() {
        *c = -*c;
    }
    ineq.constant = -ineq.constant;
}

/// Extract a linear integer inequality from `lhs REL rhs`, normalizing to `expr REL 0`.
fn extract_linear_int_atom(
    dag: &SmtProofDag,
    lhs: SmtTermId,
    rhs: SmtTermId,
    cmp: LiaComparison,
) -> Option<LiaInequality> {
    let mut lhs_terms = extract_linear_int_expr(dag, lhs)?;
    let rhs_terms = extract_linear_int_expr(dag, rhs)?;

    // Normalize: lhs - rhs CMP 0
    for (var, coeff) in &rhs_terms.0 {
        let entry = lhs_terms.0.iter_mut().find(|(v, _)| v == var);
        match entry {
            Some((_, c)) => *c -= coeff,
            None => lhs_terms.0.push((var.clone(), -coeff)),
        }
    }
    let constant = lhs_terms.1 - rhs_terms.1;

    Some(LiaInequality {
        coefficients: lhs_terms.0,
        constant,
        comparison: cmp,
    })
}

/// Extract linear expression coefficients from an integer term.
///
/// Returns (variable_coefficients, constant).
fn extract_linear_int_expr(
    dag: &SmtProofDag,
    term_id: SmtTermId,
) -> Option<(Vec<(String, i64)>, i64)> {
    let term = dag.term(term_id)?;
    match term {
        SmtTerm::Var(name, _) => Some((vec![(name.clone(), 1)], 0)),
        SmtTerm::Int(n) => Some((vec![], *n)),
        SmtTerm::App(SmtSymbol::Named(op), args) => match op.as_str() {
            "+" if args.len() == 2 => {
                let mut left = extract_linear_int_expr(dag, args[0])?;
                let right = extract_linear_int_expr(dag, args[1])?;
                for (var, coeff) in right.0 {
                    let entry = left.0.iter_mut().find(|(v, _)| *v == var);
                    match entry {
                        Some((_, c)) => *c += coeff,
                        None => left.0.push((var, coeff)),
                    }
                }
                left.1 += right.1;
                Some(left)
            }
            "-" if args.len() == 2 => {
                let mut left = extract_linear_int_expr(dag, args[0])?;
                let right = extract_linear_int_expr(dag, args[1])?;
                for (var, coeff) in right.0 {
                    let entry = left.0.iter_mut().find(|(v, _)| *v == var);
                    match entry {
                        Some((_, c)) => *c -= coeff,
                        None => left.0.push((var, -coeff)),
                    }
                }
                left.1 -= right.1;
                Some(left)
            }
            "-" if args.len() == 1 => {
                let mut inner = extract_linear_int_expr(dag, args[0])?;
                for (_, c) in inner.0.iter_mut() {
                    *c = -*c;
                }
                inner.1 = -inner.1;
                Some(inner)
            }
            "*" if args.len() == 2 => {
                let left = extract_linear_int_expr(dag, args[0]);
                let right = extract_linear_int_expr(dag, args[1]);
                match (left, right) {
                    (Some((ref lv, lc)), Some((ref rv, rc))) if lv.is_empty() => {
                        let scaled: Vec<_> = rv.iter().map(|(v, c)| (v.clone(), lc * c)).collect();
                        Some((scaled, lc * rc))
                    }
                    (Some((ref lv, lc)), Some((ref rv, rc))) if rv.is_empty() => {
                        let scaled: Vec<_> = lv.iter().map(|(v, c)| (v.clone(), rc * c)).collect();
                        Some((scaled, lc * rc))
                    }
                    _ => None, // Non-linear
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// Compute the GCD of a slice of integers (absolute values).
fn gcd_of_slice(values: &[i64]) -> i64 {
    values
        .iter()
        .copied()
        .filter(|&v| v != 0)
        .map(|v| v.unsigned_abs())
        .reduce(gcd)
        .map_or(0, |g| g as i64)
}

/// Euclidean GCD.
fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Integer floor division: floor(a / b) for b > 0.
fn floor_div(a: i64, b: i64) -> i64 {
    assert!(b > 0, "floor_div requires positive divisor");
    if a >= 0 {
        a / b
    } else {
        // For negative a: floor division rounds toward negative infinity.
        // E.g., floor(-7 / 2) = -4, not -3.
        (a - b + 1) / b
    }
}

/// Apply GCD tightening to an integer inequality.
///
/// If all variable coefficients share a GCD g > 1, divide all coefficients
/// and the constant by g, flooring the constant for `<=` inequalities.
///
/// Example: `2x + 4y <= 7` becomes `x + 2y <= 3` (floor(7/2) = 3).
///
/// This is sound because if all variable coefficients are divisible by g,
/// the LHS is always a multiple of g, so rounding down the RHS to the
/// nearest multiple of g does not exclude any integer solutions.
#[must_use]
pub(crate) fn gcd_tighten(ineq: &LiaInequality) -> LiaInequality {
    if ineq.comparison == LiaComparison::Distinct {
        // GCD tightening doesn't apply to disequalities.
        return ineq.clone();
    }

    let var_coeffs: Vec<i64> = ineq.coefficients.iter().map(|(_, c)| *c).collect();
    let g = gcd_of_slice(&var_coeffs);

    if g <= 1 {
        return ineq.clone();
    }

    let new_coefficients: Vec<(String, i64)> = ineq
        .coefficients
        .iter()
        .map(|(v, c)| (v.clone(), c / g))
        .collect();

    let new_constant = match ineq.comparison {
        LiaComparison::Le => {
            // For <= : floor the constant. sum/g <= floor(constant/g).
            // Our form is (sum + constant <= 0), so we need
            // sum/g + floor(constant / g) <= 0 when constant is not divisible.
            // Actually: our normalized form is `c1*x1 + ... + K <= 0`.
            // Dividing by g: `(c1/g)*x1 + ... + floor(K/g) <= 0`.
            // floor because the LHS is an integer and we are strengthening.
            floor_div(ineq.constant, g)
        }
        LiaComparison::Eq => {
            // For equality: if constant is not divisible by g, the system is UNSAT.
            // We return the original (caller will detect infeasibility).
            if ineq.constant % g != 0 {
                // Return an obviously contradictory inequality: 0 + 1 = 0 (impossible).
                return LiaInequality {
                    coefficients: vec![],
                    constant: 1,
                    comparison: LiaComparison::Eq,
                };
            }
            ineq.constant / g
        }
        LiaComparison::Distinct => unreachable!("handled above"),
    };

    LiaInequality {
        coefficients: new_coefficients,
        constant: new_constant,
        comparison: ineq.comparison,
    }
}

/// Verify an integer Farkas certificate.
///
/// Multiplies each inequality by its non-negative coefficient and sums.
/// The result must be a contradiction:
/// - For `<=`: all variable coefficients cancel to zero and constant > 0 (i.e., `K <= 0` with K > 0).
/// - For `=`: if any equality participates, the combined system is treated as `<= 0` (equality
///   splits into two `<=` directions, both with the same coefficient).
///
/// Returns `true` if the certificate is valid (proves UNSAT).
#[must_use]
pub(crate) fn verify_lia_farkas(inequalities: &[LiaInequality], coefficients: &[i64]) -> bool {
    verify_lia_farkas_inner(inequalities, coefficients).unwrap_or(false)
}

/// Inner implementation returning `Option` to handle arithmetic overflow gracefully.
fn verify_lia_farkas_inner(inequalities: &[LiaInequality], coefficients: &[i64]) -> Option<bool> {
    if inequalities.len() != coefficients.len() {
        return Some(false);
    }

    let mut sum_coeffs: Vec<(String, i64)> = Vec::new();
    let mut sum_constant: i64 = 0;

    for (ineq, &coeff) in inequalities.iter().zip(coefficients.iter()) {
        if coeff == 0 {
            continue;
        }

        match ineq.comparison {
            LiaComparison::Distinct => {
                // Disequalities cannot be directly used in Farkas; bail.
                return Some(false);
            }
            LiaComparison::Le | LiaComparison::Eq => {
                // For <= : multiply and add.
                // For = : treat as <= (the = direction is a stronger constraint, and
                // multiplying an equality by a positive coefficient preserves it as <=).
                for (var, var_coeff) in &ineq.coefficients {
                    let weighted = coeff.checked_mul(*var_coeff)?;
                    let entry = sum_coeffs.iter_mut().find(|(v, _)| v == var);
                    match entry {
                        Some((_, c)) => *c = c.checked_add(weighted)?,
                        None => sum_coeffs.push((var.clone(), weighted)),
                    }
                }
                sum_constant = sum_constant.checked_add(coeff.checked_mul(ineq.constant)?)?;
            }
        }
    }

    // All variable coefficients must cancel to zero.
    let all_zero = sum_coeffs.iter().all(|(_, c)| *c == 0);
    if !all_zero {
        return Some(false);
    }

    // For integer Farkas: the derived bound is `sum_constant <= 0`.
    // This is a contradiction iff `sum_constant > 0`.
    Some(sum_constant > 0)
}

fn ok(step_id: SmtStepId) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::KernelVerified,
        checker: CHECKER_NAME,
        detail: None,
    }
}

fn fail(step_id: SmtStepId, reason: &str) -> StepVerdict {
    StepVerdict {
        step_id,
        trust_level: StepTrustLevel::Trusted,
        checker: CHECKER_NAME,
        detail: Some(reason.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt_verify::dag::{SmtProofDag, SmtSort, SmtSymbol, SmtTerm};
    use crate::smt_verify::trust::StepTrustLevel;

    /// Helper: build a term `(op lhs rhs)` in the DAG.
    fn add_binop(dag: &mut SmtProofDag, op: &str, lhs: SmtTermId, rhs: SmtTermId) -> SmtTermId {
        dag.add_term(SmtTerm::App(
            SmtSymbol::Named(op.to_string()),
            vec![lhs, rhs],
        ))
    }

    // ─── GCD and floor_div tests ───

    #[test]
    fn test_gcd_basic() {
        assert_eq!(gcd(12, 8), 4);
        assert_eq!(gcd(7, 13), 1);
        assert_eq!(gcd(0, 5), 5);
        assert_eq!(gcd(5, 0), 5);
        assert_eq!(gcd(6, 6), 6);
    }

    #[test]
    fn test_gcd_of_slice_basic() {
        assert_eq!(gcd_of_slice(&[6, 12, 18]), 6);
        assert_eq!(gcd_of_slice(&[2, 4, 8]), 2);
        assert_eq!(gcd_of_slice(&[3, 5, 7]), 1);
        assert_eq!(gcd_of_slice(&[-6, 12, -18]), 6);
        assert_eq!(gcd_of_slice(&[0, 0, 0]), 0);
        assert_eq!(gcd_of_slice(&[0, 6, 0]), 6);
    }

    #[test]
    fn test_floor_div_positive() {
        assert_eq!(floor_div(7, 2), 3);
        assert_eq!(floor_div(6, 2), 3);
        assert_eq!(floor_div(0, 3), 0);
    }

    #[test]
    fn test_floor_div_negative() {
        assert_eq!(floor_div(-7, 2), -4);
        assert_eq!(floor_div(-6, 2), -3);
        assert_eq!(floor_div(-1, 3), -1);
    }

    // ─── GCD tightening tests ───

    #[test]
    fn test_gcd_tighten_basic() {
        // 2x + 4y <= 7 => x + 2y <= 3 (floor(7/2) = 3)
        let ineq = LiaInequality {
            coefficients: vec![("x".to_string(), 2), ("y".to_string(), 4)],
            constant: 7,
            comparison: LiaComparison::Le,
        };
        // Wait, our normalized form is (coeffs + constant) <= 0.
        // So 2x + 4y + 7 <= 0 represents 2x + 4y <= -7.
        // After tightening: x + 2y + floor(7/2) <= 0 => x + 2y + 3 <= 0.
        // That represents x + 2y <= -3.
        // Actually the point is: for the purpose of checking, we store things in
        // (expr + K) <= 0 form. Tightening divides all parts by GCD and floors the constant.

        let result = gcd_tighten(&ineq);
        assert_eq!(
            result.coefficients,
            vec![("x".to_string(), 1), ("y".to_string(), 2)]
        );
        assert_eq!(result.constant, 3); // floor(7/2) = 3
    }

    #[test]
    fn test_gcd_tighten_negative_constant() {
        // 2x + 4y + (-7) <= 0 => x + 2y + floor(-7/2) <= 0 => x + 2y - 4 <= 0
        let ineq = LiaInequality {
            coefficients: vec![("x".to_string(), 2), ("y".to_string(), 4)],
            constant: -7,
            comparison: LiaComparison::Le,
        };
        let result = gcd_tighten(&ineq);
        assert_eq!(result.constant, -4); // floor(-7/2) = -4
    }

    #[test]
    fn test_gcd_tighten_no_tightening_needed() {
        // Coefficients with GCD 1.
        let ineq = LiaInequality {
            coefficients: vec![("x".to_string(), 3), ("y".to_string(), 5)],
            constant: 7,
            comparison: LiaComparison::Le,
        };
        let result = gcd_tighten(&ineq);
        assert_eq!(result.coefficients, ineq.coefficients);
        assert_eq!(result.constant, 7);
    }

    #[test]
    fn test_gcd_tighten_equality_divisible() {
        // 2x + 4y + 6 = 0 => x + 2y + 3 = 0
        let ineq = LiaInequality {
            coefficients: vec![("x".to_string(), 2), ("y".to_string(), 4)],
            constant: 6,
            comparison: LiaComparison::Eq,
        };
        let result = gcd_tighten(&ineq);
        assert_eq!(result.constant, 3);
        assert_eq!(result.comparison, LiaComparison::Eq);
    }

    #[test]
    fn test_gcd_tighten_equality_not_divisible() {
        // 2x + 4y + 7 = 0 is UNSAT (LHS always even, 7 is odd).
        let ineq = LiaInequality {
            coefficients: vec![("x".to_string(), 2), ("y".to_string(), 4)],
            constant: 7,
            comparison: LiaComparison::Eq,
        };
        let result = gcd_tighten(&ineq);
        // Should produce a contradictory equality: 0 + 1 = 0.
        assert!(result.coefficients.is_empty());
        assert_eq!(result.constant, 1);
        assert_eq!(result.comparison, LiaComparison::Eq);
    }

    // ─── Integer Farkas verification tests ───

    #[test]
    fn test_verify_lia_farkas_simple_contradiction() {
        // x + 1 <= 0 AND -x <= 0
        // Sum with coefficients (1, 1): (x - x) + (1 + 0) = 1 <= 0 => contradiction!
        let ineq1 = LiaInequality {
            coefficients: vec![("x".to_string(), 1)],
            constant: 1,
            comparison: LiaComparison::Le,
        };
        let ineq2 = LiaInequality {
            coefficients: vec![("x".to_string(), -1)],
            constant: 0,
            comparison: LiaComparison::Le,
        };
        assert!(verify_lia_farkas(&[ineq1, ineq2], &[1, 1]));
    }

    #[test]
    fn test_verify_lia_farkas_non_contradiction() {
        // x - 1 <= 0 AND -x <= 0 => sum = -1 <= 0, which is true, NOT a contradiction.
        let ineq1 = LiaInequality {
            coefficients: vec![("x".to_string(), 1)],
            constant: -1,
            comparison: LiaComparison::Le,
        };
        let ineq2 = LiaInequality {
            coefficients: vec![("x".to_string(), -1)],
            constant: 0,
            comparison: LiaComparison::Le,
        };
        assert!(!verify_lia_farkas(&[ineq1, ineq2], &[1, 1]));
    }

    #[test]
    fn test_verify_lia_farkas_with_coefficients() {
        // 2x + 1 <= 0 AND -2x + 1 <= 0
        // Sum: (2x - 2x) + (1 + 1) = 2 <= 0 => contradiction
        let ineq1 = LiaInequality {
            coefficients: vec![("x".to_string(), 2)],
            constant: 1,
            comparison: LiaComparison::Le,
        };
        let ineq2 = LiaInequality {
            coefficients: vec![("x".to_string(), -2)],
            constant: 1,
            comparison: LiaComparison::Le,
        };
        assert!(verify_lia_farkas(&[ineq1, ineq2], &[1, 1]));
    }

    #[test]
    fn test_verify_lia_farkas_weighted() {
        // x + 1 <= 0 AND -x <= 0
        // With coefficients (2, 2): 2*(x+1) + 2*(-x) = 2 <= 0 => contradiction
        let ineq1 = LiaInequality {
            coefficients: vec![("x".to_string(), 1)],
            constant: 1,
            comparison: LiaComparison::Le,
        };
        let ineq2 = LiaInequality {
            coefficients: vec![("x".to_string(), -1)],
            constant: 0,
            comparison: LiaComparison::Le,
        };
        assert!(verify_lia_farkas(&[ineq1, ineq2], &[2, 2]));
    }

    #[test]
    fn test_verify_lia_farkas_equality_used() {
        // x = 0 (treated as x <= 0) AND -x + 1 <= 0
        // Sum: (x - x) + (0 + 1) = 1 <= 0 => contradiction
        let ineq1 = LiaInequality {
            coefficients: vec![("x".to_string(), 1)],
            constant: 0,
            comparison: LiaComparison::Eq,
        };
        let ineq2 = LiaInequality {
            coefficients: vec![("x".to_string(), -1)],
            constant: 1,
            comparison: LiaComparison::Le,
        };
        assert!(verify_lia_farkas(&[ineq1, ineq2], &[1, 1]));
    }

    #[test]
    fn test_verify_lia_farkas_disequality_rejected() {
        // x != 0 cannot participate in Farkas.
        let ineq1 = LiaInequality {
            coefficients: vec![("x".to_string(), 1)],
            constant: 0,
            comparison: LiaComparison::Distinct,
        };
        let ineq2 = LiaInequality {
            coefficients: vec![("x".to_string(), -1)],
            constant: 1,
            comparison: LiaComparison::Le,
        };
        assert!(!verify_lia_farkas(&[ineq1, ineq2], &[1, 1]));
    }

    #[test]
    fn test_verify_lia_farkas_variables_dont_cancel() {
        // x + 1 <= 0 AND x <= 0
        // Sum: 2x + 1 <= 0 -- variables don't cancel.
        let ineq1 = LiaInequality {
            coefficients: vec![("x".to_string(), 1)],
            constant: 1,
            comparison: LiaComparison::Le,
        };
        let ineq2 = LiaInequality {
            coefficients: vec![("x".to_string(), 1)],
            constant: 0,
            comparison: LiaComparison::Le,
        };
        assert!(!verify_lia_farkas(&[ineq1, ineq2], &[1, 1]));
    }

    // ─── Linear expression extraction tests ───

    #[test]
    fn test_extract_linear_int_expr_variable() {
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let (coeffs, constant) = extract_linear_int_expr(&dag, x).expect("should extract");
        assert_eq!(coeffs, vec![("x".to_string(), 1)]);
        assert_eq!(constant, 0);
    }

    #[test]
    fn test_extract_linear_int_expr_constant() {
        let mut dag = SmtProofDag::new();
        let c = dag.add_term(SmtTerm::Int(42));
        let (coeffs, constant) = extract_linear_int_expr(&dag, c).expect("should extract");
        assert!(coeffs.is_empty());
        assert_eq!(constant, 42);
    }

    #[test]
    fn test_extract_linear_int_expr_addition() {
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let three = dag.add_term(SmtTerm::Int(3));
        let sum = add_binop(&mut dag, "+", x, three);

        let (coeffs, constant) = extract_linear_int_expr(&dag, sum).expect("should extract");
        assert_eq!(coeffs, vec![("x".to_string(), 1)]);
        assert_eq!(constant, 3);
    }

    #[test]
    fn test_extract_linear_int_expr_subtraction() {
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let two = dag.add_term(SmtTerm::Int(2));
        let diff = add_binop(&mut dag, "-", x, two);

        let (coeffs, constant) = extract_linear_int_expr(&dag, diff).expect("should extract");
        assert_eq!(coeffs, vec![("x".to_string(), 1)]);
        assert_eq!(constant, -2);
    }

    #[test]
    fn test_extract_linear_int_expr_multiplication_by_constant() {
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let three = dag.add_term(SmtTerm::Int(3));
        let prod = add_binop(&mut dag, "*", three, x);

        let (coeffs, constant) = extract_linear_int_expr(&dag, prod).expect("should extract");
        assert_eq!(coeffs, vec![("x".to_string(), 3)]);
        assert_eq!(constant, 0);
    }

    #[test]
    fn test_extract_linear_int_expr_unary_minus() {
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let neg_x = dag.add_term(SmtTerm::App(SmtSymbol::Named("-".to_string()), vec![x]));

        let (coeffs, constant) = extract_linear_int_expr(&dag, neg_x).expect("should extract");
        assert_eq!(coeffs, vec![("x".to_string(), -1)]);
        assert_eq!(constant, 0);
    }

    // ─── Full integration: check_lia_generic with DAG ───

    #[test]
    fn test_check_lia_generic_simple_conflict() {
        // Conflict: x <= -1 AND x >= 0 (i.e., x <= -1 AND -x <= 0).
        // Blocking clause: not(x <= -1) OR not(x >= 0)
        // Farkas: 1*(x <= -1) + 1*(-x <= 0) => (x-x) + (-1+0) <= 0 => -1 <= 0
        // Wait, that's true, not a contradiction.
        //
        // Hmm. Let me think more carefully.
        // Conflict: x >= 1 AND x <= -1.
        // That means x >= 1 AND x <= -1. Normalizing to <= 0:
        //   -x + 1 <= 0 (from x >= 1)
        //   x + 1 <= 0  (from x <= -1, i.e., x - (-1) <= 0 which is x + 1 <= 0)
        // Wait, x <= -1 normalized: x - (-1) <= 0 => x + 1 <= 0. Yes.
        // -x + 1 <= 0 from x >= 1 => -x + 1 <= 0.
        // Sum: (-x + x) + (1 + 1) = 2 <= 0 => contradiction!
        //
        // Now blocking clause: not(x >= 1) OR not(x <= -1)
        // not(x >= 1) = x < 1 = x <= 0 (integer tightening)
        // not(x <= -1) = x > -1 = x >= 0 (integer tightening)
        // So blocking clause is: (x <= 0) OR (x >= 0)
        // As terms: (<= x 0) and (>= x 0).

        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let neg_one = dag.add_term(SmtTerm::Int(-1));
        let one = dag.add_term(SmtTerm::Int(1));

        // Blocking clause literals:
        // lit0: not(x >= 1)  -->  expressed as  not((>= x 1))
        let ge_x_1 = add_binop(&mut dag, ">=", x, one);
        let not_ge_x_1 = dag.add_term(SmtTerm::Not(ge_x_1));

        // lit1: not(x <= -1) --> expressed as  not((<= x -1))
        let le_x_neg1 = add_binop(&mut dag, "<=", x, neg_one);
        let not_le_x_neg1 = dag.add_term(SmtTerm::Not(le_x_neg1));

        let clause = vec![not_ge_x_1, not_le_x_neg1];
        let coefficients = vec![1_i64, 1_i64];

        let verdict = check_lia_generic(&dag, SmtStepId(0), &clause, &coefficients);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "verdict detail: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_check_lia_generic_with_gcd_tightening() {
        // Conflict: 2x >= 3 AND 2x <= 0.
        // Normalized: -2x + 3 <= 0 AND 2x <= 0.
        // After GCD tightening (g=2): -x + floor(3/2) <= 0 AND x <= 0
        //   => -x + 1 <= 0 AND x <= 0.
        // Sum: (-x + x) + (1 + 0) = 1 <= 0 => contradiction!
        //
        // Blocking clause: not(2x >= 3) OR not(2x <= 0)
        // not(2x >= 3): the term is (>= (* 2 x) 3), negated to not((>= (* 2 x) 3))
        // not(2x <= 0): the term is (<= (* 2 x) 0), negated to not((<= (* 2 x) 0))

        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let zero = dag.add_term(SmtTerm::Int(0));
        let two = dag.add_term(SmtTerm::Int(2));
        let three = dag.add_term(SmtTerm::Int(3));
        let two_x = add_binop(&mut dag, "*", two, x);

        // lit0: not((>= (* 2 x) 3)) => conflict is (2x >= 3)
        let ge = add_binop(&mut dag, ">=", two_x, three);
        let not_ge = dag.add_term(SmtTerm::Not(ge));

        // lit1: not((<= (* 2 x) 0)) => conflict is (2x <= 0)
        let le = add_binop(&mut dag, "<=", two_x, zero);
        let not_le = dag.add_term(SmtTerm::Not(le));

        let clause = vec![not_ge, not_le];
        let coefficients = vec![1_i64, 1_i64];

        let verdict = check_lia_generic(&dag, SmtStepId(0), &clause, &coefficients);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "verdict detail: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_check_lia_generic_empty_clause() {
        let dag = SmtProofDag::new();
        let verdict = check_lia_generic(&dag, SmtStepId(0), &[], &[]);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    #[test]
    fn test_check_lia_generic_mismatched_lengths() {
        let mut dag = SmtProofDag::new();
        let t = dag.add_term(SmtTerm::Bool(true));
        let verdict = check_lia_generic(&dag, SmtStepId(0), &[t], &[1, 2]);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    #[test]
    fn test_check_lia_generic_negative_coefficient() {
        let mut dag = SmtProofDag::new();
        let t = dag.add_term(SmtTerm::Bool(true));
        let verdict = check_lia_generic(&dag, SmtStepId(0), &[t], &[-1]);
        assert_eq!(verdict.trust_level, StepTrustLevel::Trusted);
    }

    #[test]
    fn test_check_lia_generic_unparseable_literal() {
        // Boolean term that can't be parsed as arithmetic.
        let mut dag = SmtProofDag::new();
        let t = dag.add_term(SmtTerm::Bool(true));
        let verdict = check_lia_generic(&dag, SmtStepId(0), &[t], &[1]);
        assert_eq!(verdict.trust_level, StepTrustLevel::StructurallyAccepted);
    }

    #[test]
    fn test_check_lia_generic_two_variable_system() {
        // Conflict: x + y >= 3 AND -x >= 0 AND -y >= 0.
        // Normalized:
        //   -x - y + 3 <= 0
        //   x <= 0
        //   y <= 0
        // Sum: (-x + x) + (-y + y) + 3 = 3 <= 0 => contradiction!

        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let y = dag.add_term(SmtTerm::Var("y".to_string(), SmtSort::Int));
        let zero = dag.add_term(SmtTerm::Int(0));
        let three = dag.add_term(SmtTerm::Int(3));
        let x_plus_y = add_binop(&mut dag, "+", x, y);
        let neg_x = dag.add_term(SmtTerm::App(SmtSymbol::Named("-".to_string()), vec![x]));
        let neg_y = dag.add_term(SmtTerm::App(SmtSymbol::Named("-".to_string()), vec![y]));

        // lit0: not((>= (+ x y) 3)) => conflict is (x + y >= 3)
        let ge_xy_3 = add_binop(&mut dag, ">=", x_plus_y, three);
        let not_ge_xy = dag.add_term(SmtTerm::Not(ge_xy_3));

        // lit1: not((>= (- x) 0)) => conflict is (-x >= 0)
        let ge_neg_x_0 = add_binop(&mut dag, ">=", neg_x, zero);
        let not_ge_neg_x = dag.add_term(SmtTerm::Not(ge_neg_x_0));

        // lit2: not((>= (- y) 0)) => conflict is (-y >= 0)
        let ge_neg_y_0 = add_binop(&mut dag, ">=", neg_y, zero);
        let not_ge_neg_y = dag.add_term(SmtTerm::Not(ge_neg_y_0));

        let clause = vec![not_ge_xy, not_ge_neg_x, not_ge_neg_y];
        let coefficients = vec![1_i64, 1_i64, 1_i64];

        let verdict = check_lia_generic(&dag, SmtStepId(0), &clause, &coefficients);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "verdict detail: {:?}",
            verdict.detail
        );
    }

    // ─── Integer tightening for strict inequalities ───

    #[test]
    fn test_lia_strict_x_lt_0_becomes_x_le_neg1() {
        // In LIA, x < 0 => x <= -1 (integer tightening).
        // Conflict: x >= 0 AND x < 0.
        // Blocking clause: not(x >= 0) OR not(x < 0)
        // not(x >= 0): negation of >=, which is x < 0, integer tightened to x <= -1.
        //   extract_negated_relation(">=", x, 0): (x - 0) + 1 <= 0 => x + 1 <= 0
        // not(x < 0): negation of <, which is x >= 0, i.e., -(x - 0) <= 0 => -x <= 0.
        //   extract_negated_relation("<", x, 0): negate_coefficients of (x - 0) <= 0 => -x <= 0
        //
        // Sum: (x - x) + (1 + 0) = 1 <= 0 => contradiction!
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let zero = dag.add_term(SmtTerm::Int(0));

        // lit0: (>= x 0) in blocking clause => conflict is not(x >= 0) = x < 0 = x <= -1
        let ge_x_0 = add_binop(&mut dag, ">=", x, zero);
        // lit1: (< x 0) in blocking clause => conflict is not(x < 0) = x >= 0
        let lt_x_0 = add_binop(&mut dag, "<", x, zero);

        let clause = vec![ge_x_0, lt_x_0];
        let coefficients = vec![1_i64, 1_i64];

        let verdict = check_lia_generic(&dag, SmtStepId(0), &clause, &coefficients);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "x >= 0 AND x < 0 must be contradictory in integers: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_lia_strict_x_gt_0_x_lt_0() {
        // Conflict: x > 0 AND x < 0.
        // In integers: x >= 1 AND x <= -1.
        // Blocking clause: not(x > 0) OR not(x < 0)
        //   not(x > 0) => x <= 0 => (x - 0) <= 0 => x <= 0
        //   not(x < 0) => x >= 0 => -(x - 0) <= 0 => -x <= 0
        //
        // Wait, these are not contradictory -- x = 0 satisfies both.
        // That's correct! In the blocking clause, we have the NEGATION of the conflict.
        // The conflict is x > 0 AND x < 0. Integer tightening gives x >= 1 AND x <= -1.
        //
        // Blocking clause: (> x 0) and (< x 0) -- positive blocking literals.
        // Negation for conflict:
        //   not(x > 0) = x <= 0 => x <= 0
        //   not(x < 0) = x >= 0 => -x <= 0
        // Sum: (x - x) + (0 + 0) = 0 <= 0 => not contradictory.
        //
        // But the real conflict needs different blocking clause form.
        // Use not-wrapped literals:
        //   lit0: not((> x 0)) => conflict is (x > 0) => integer: x >= 1 => -x + 1 <= 0
        //   lit1: not((< x 0)) => conflict is (x < 0) => integer: x <= -1 => x + 1 <= 0
        // Sum: (-x + x) + (1 + 1) = 2 <= 0 => contradiction!
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let zero = dag.add_term(SmtTerm::Int(0));

        let gt_x_0 = add_binop(&mut dag, ">", x, zero);
        let not_gt = dag.add_term(SmtTerm::Not(gt_x_0));
        let lt_x_0 = add_binop(&mut dag, "<", x, zero);
        let not_lt = dag.add_term(SmtTerm::Not(lt_x_0));

        let clause = vec![not_gt, not_lt];
        let coefficients = vec![1_i64, 1_i64];

        let verdict = check_lia_generic(&dag, SmtStepId(0), &clause, &coefficients);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "x > 0 AND x < 0 (integer) must be contradictory: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_lia_strict_with_equality() {
        // Conflict: x = 5 AND x > 5.
        // Integer tightened: x = 5 AND x >= 6.
        // Blocking clause: not(x = 5) OR not(x > 5)
        //   not((= x 5)) => x != 5 (disequality, can't use directly in Farkas)
        //
        // Better: Conflict: x <= 5 AND x > 5.
        // Integer tightened: x <= 5 AND x >= 6.
        // Blocking clause: not((<= x 5)) OR not((> x 5))
        //   not(x <= 5) => x > 5 => x >= 6 => -x + 6 <= 0
        //   not(x > 5)  => x <= 5 => x - 5 <= 0
        // Sum: (-x + x) + (6 + (-5)) = 1 <= 0 => contradiction!
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let five = dag.add_term(SmtTerm::Int(5));

        let le_x_5 = add_binop(&mut dag, "<=", x, five);
        let not_le = dag.add_term(SmtTerm::Not(le_x_5));
        let gt_x_5 = add_binop(&mut dag, ">", x, five);
        let not_gt = dag.add_term(SmtTerm::Not(gt_x_5));

        let clause = vec![not_le, not_gt];
        let coefficients = vec![1_i64, 1_i64];

        let verdict = check_lia_generic(&dag, SmtStepId(0), &clause, &coefficients);
        assert_eq!(
            verdict.trust_level,
            StepTrustLevel::KernelVerified,
            "x <= 5 AND x > 5 (integer) must be contradictory: {:?}",
            verdict.detail
        );
    }

    #[test]
    fn test_lia_integer_tightening_unit() {
        // Directly test that extract_negated_relation correctly tightens strict inequalities.
        // not(x >= 0) = x < 0 = x <= -1 in integers.
        // extract_negated_relation(">="...) should give (x - 0) + 1 <= 0 => x + 1 <= 0.
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let zero = dag.add_term(SmtTerm::Int(0));

        let ge_x_0 = add_binop(&mut dag, ">=", x, zero);

        // As a positive literal in blocking clause, we negate it:
        // not(x >= 0) => x < 0 => x <= -1 => x + 1 <= 0
        let ineq = extract_lia_inequality(&dag, ge_x_0).expect("should parse");
        assert_eq!(ineq.comparison, LiaComparison::Le);
        // x + 1 <= 0: coefficient of x is 1, constant is 1.
        assert_eq!(ineq.coefficients, vec![("x".to_string(), 1)]);
        assert_eq!(ineq.constant, 1);
    }

    #[test]
    fn test_lia_direct_strict_tightening() {
        // not((< x 5)) => x >= 5 => -x + 5 <= 0 => -(x-5) <= 0 => -x + 5 <= 0.
        let mut dag = SmtProofDag::new();
        let x = dag.add_term(SmtTerm::Var("x".to_string(), SmtSort::Int));
        let five = dag.add_term(SmtTerm::Int(5));

        let lt_x_5 = add_binop(&mut dag, "<", x, five);

        // As positive literal in blocking clause: negate => conflict is x < 5 => x >= 5 in NOT form.
        // Wait, not(x < 5) = x >= 5. For extract_negated_relation("<"...):
        //   not(lhs < rhs) => lhs >= rhs => -(lhs - rhs) <= 0 => rhs - lhs <= 0
        //   => -(x - 5) <= 0 => -x + 5 <= 0
        let ineq = extract_lia_inequality(&dag, lt_x_5).expect("should parse");
        assert_eq!(ineq.comparison, LiaComparison::Le);
        // -x + 5 <= 0: coefficient of x is -1, constant is 5.
        assert_eq!(ineq.coefficients, vec![("x".to_string(), -1)]);
        assert_eq!(ineq.constant, 5);
    }
}
