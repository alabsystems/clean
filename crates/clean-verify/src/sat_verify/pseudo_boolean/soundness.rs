// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness checks for pseudo-Boolean derivation rules.
//!
//! For constraints over at most 20 distinct variables, these routines verify
//! soundness by exhaustive enumeration of all 0/1 assignments.
//! For larger constraints, they rely on the standard algebraic arguments for
//! the corresponding rule and reject inputs when that argument does not apply.

use std::collections::{BTreeSet, HashMap};

use super::types::PbConstraint;
use super::PbError;

const MAX_EXHAUSTIVE_VARS: usize = 20;

/// Verify soundness of ceiling division by a positive divisor.
pub(crate) fn verify_division_soundness(
    constraint: &PbConstraint,
    divisor: i64,
) -> Result<(), PbError> {
    validate_constraint(constraint)?;
    let divided = divide_constraint(constraint, divisor)?;

    if uses_exhaustive_check(&[constraint, &divided])? {
        verify_implication_exhaustively(&[constraint], &divided, "division")
    } else {
        verify_division_soundness_algebraically(divisor)
    }
}

/// Verify soundness of rounding by the GCD of the coefficients.
pub(crate) fn verify_rounding_soundness(constraint: &PbConstraint) -> Result<(), PbError> {
    validate_constraint(constraint)?;
    let rounded = round_constraint(constraint)?;

    if uses_exhaustive_check(&[constraint, &rounded])? {
        verify_implication_exhaustively(&[constraint], &rounded, "rounding")
    } else {
        let divisor = coefficient_gcd(constraint);
        if divisor <= 1 {
            Ok(())
        } else {
            verify_division_soundness_algebraically(divisor as i64)
        }
    }
}

/// Verify soundness of saturation (capping positive coefficients at the degree).
pub(crate) fn verify_saturation_soundness(constraint: &PbConstraint) -> Result<(), PbError> {
    validate_constraint(constraint)?;
    let saturated = saturate_constraint(constraint);

    if uses_exhaustive_check(&[constraint, &saturated])? {
        verify_implication_exhaustively(&[constraint], &saturated, "saturation")
    } else {
        verify_saturation_soundness_algebraically(constraint)
    }
}

/// Verify soundness of generalized resolution on `var`.
pub(crate) fn verify_generalized_resolution_soundness(
    left: &PbConstraint,
    right: &PbConstraint,
    var: u32,
) -> Result<(), PbError> {
    validate_constraint(left)?;
    validate_constraint(right)?;

    let max_var = left.max_var().max(right.max_var());
    if var == 0 || var > max_var {
        return Err(PbError::VariableOutOfRange {
            var,
            num_vars: max_var,
        });
    }

    let resolvent = generalized_resolution_resolvent(left, right, var)?;

    if uses_exhaustive_check(&[left, right, &resolvent])? {
        verify_implication_exhaustively(&[left, right], &resolvent, "generalized resolution")
    } else {
        verify_generalized_resolution_soundness_algebraically(left, right, var)
    }
}

fn verify_division_soundness_algebraically(divisor: i64) -> Result<(), PbError> {
    if divisor <= 0 {
        return Err(PbError::NonPositiveDivisor(divisor));
    }

    // For every 0/1 assignment sigma and every coefficient a:
    //   ceil(a / d) * sigma(l) >= (a / d) * sigma(l)
    // because sigma(l) is either 0 or 1 and ceil(a / d) >= a / d.
    // Summing over all terms yields:
    //   lhs(ceil(C / d), sigma) >= lhs(C, sigma) / d.
    // Therefore lhs(C, sigma) >= k implies lhs(ceil(C / d), sigma) >= k / d.
    // The left-hand side is integral, so it is at least ceil(k / d).
    Ok(())
}

fn verify_saturation_soundness_algebraically(constraint: &PbConstraint) -> Result<(), PbError> {
    if constraint.degree <= 0 {
        return Ok(());
    }

    let needs_capping = constraint
        .terms
        .iter()
        .any(|&(coeff, _)| coeff > constraint.degree);
    if !needs_capping {
        return Ok(());
    }

    if constraint.terms.iter().all(|&(coeff, _)| coeff >= 0) {
        // Let k be the degree. If some capped term a_i * l_i with a_i > k is
        // satisfied, then the saturated term contributes k and the new
        // constraint is immediately satisfied. Otherwise every satisfied term
        // has coefficient at most k and saturation leaves the left-hand side
        // unchanged, so any satisfying assignment of the original also
        // satisfies the saturated constraint.
        Ok(())
    } else {
        Err(PbError::ConversionError(
            "cannot prove saturation soundness algebraically for constraints with negative coefficients"
                .to_string(),
        ))
    }
}

fn verify_generalized_resolution_soundness_algebraically(
    left: &PbConstraint,
    right: &PbConstraint,
    var: u32,
) -> Result<(), PbError> {
    let pos_lit = var as i32;
    let neg_lit = -(var as i32);

    let left_pos = nonzero_occurrences(left, pos_lit);
    let left_neg = nonzero_occurrences(left, neg_lit);
    let right_pos = nonzero_occurrences(right, pos_lit);
    let right_neg = nonzero_occurrences(right, neg_lit);

    if left_pos.len() != 1 || !left_neg.is_empty() || !right_pos.is_empty() || right_neg.len() != 1
    {
        return Err(PbError::ConversionError(
            "cannot prove generalized resolution soundness algebraically with duplicated or mixed occurrences of the resolution variable"
                .to_string(),
        ));
    }

    if left_pos[0] <= 0 || right_neg[0] <= 0 {
        return Err(PbError::ResolutionSignMismatch {
            var,
            left: 0,
            right: 1,
        });
    }

    // Write the premises as:
    //   left : alpha * x + A >= k_l
    //   right: beta  * ~x + B >= k_r
    // where A and B contain no occurrence of x or ~x.
    //
    // Multiply left by beta and right by alpha, then add:
    //   alpha*beta*x + beta*A + alpha*beta*~x + alpha*B >= beta*k_l + alpha*k_r
    //
    // Since x + ~x = 1 for 0/1 variables:
    //   alpha*beta*x + alpha*beta*~x = alpha*beta.
    //
    // Subtracting alpha*beta from the degree yields the resolvent:
    //   beta*A + alpha*B >= beta*k_l + alpha*k_r - alpha*beta.
    Ok(())
}

fn validate_constraint(constraint: &PbConstraint) -> Result<(), PbError> {
    for &(_, lit) in &constraint.terms {
        if lit == 0 {
            return Err(PbError::LiteralOutOfBounds { literal: lit });
        }
    }
    Ok(())
}

fn uses_exhaustive_check(constraints: &[&PbConstraint]) -> Result<bool, PbError> {
    Ok(collect_distinct_vars(constraints)?.len() <= MAX_EXHAUSTIVE_VARS)
}

fn verify_implication_exhaustively(
    premises: &[&PbConstraint],
    conclusion: &PbConstraint,
    rule_name: &str,
) -> Result<(), PbError> {
    let vars = collect_distinct_vars(premises)?;
    let positions: HashMap<u32, usize> = vars
        .iter()
        .enumerate()
        .map(|(idx, &var)| (var, idx))
        .collect();
    let total = 1u64 << vars.len();

    for mask in 0..total {
        let premises_hold = premises
            .iter()
            .all(|constraint| is_satisfied(constraint, mask, &positions));
        if premises_hold && !is_satisfied(conclusion, mask, &positions) {
            return Err(PbError::ConversionError(format!(
                "{rule_name} soundness failed on assignment {}",
                format_assignment(mask, &vars)
            )));
        }
    }

    Ok(())
}

fn collect_distinct_vars(constraints: &[&PbConstraint]) -> Result<Vec<u32>, PbError> {
    let mut vars = BTreeSet::new();
    for constraint in constraints {
        validate_constraint(constraint)?;
        for &(_, lit) in &constraint.terms {
            vars.insert(lit.unsigned_abs());
        }
    }
    Ok(vars.into_iter().collect())
}

fn is_satisfied(constraint: &PbConstraint, mask: u64, positions: &HashMap<u32, usize>) -> bool {
    lhs_value(constraint, mask, positions) >= constraint.degree
}

fn lhs_value(constraint: &PbConstraint, mask: u64, positions: &HashMap<u32, usize>) -> i64 {
    constraint
        .terms
        .iter()
        .map(|&(coeff, lit)| {
            if literal_is_true(lit, mask, positions) {
                coeff
            } else {
                0
            }
        })
        .sum()
}

fn literal_is_true(lit: i32, mask: u64, positions: &HashMap<u32, usize>) -> bool {
    let var = lit.unsigned_abs();
    let value = positions
        .get(&var)
        .map(|&pos| ((mask >> pos) & 1) == 1)
        .unwrap_or(false);
    if lit > 0 {
        value
    } else {
        !value
    }
}

fn format_assignment(mask: u64, vars: &[u32]) -> String {
    let values: Vec<String> = vars
        .iter()
        .enumerate()
        .map(|(idx, var)| {
            let bit = ((mask >> idx) & 1) == 1;
            format!("x{var}={}", if bit { 1 } else { 0 })
        })
        .collect();
    format!("[{}]", values.join(", "))
}

fn divide_constraint(constraint: &PbConstraint, divisor: i64) -> Result<PbConstraint, PbError> {
    if divisor <= 0 {
        return Err(PbError::NonPositiveDivisor(divisor));
    }

    Ok(PbConstraint {
        terms: constraint
            .terms
            .iter()
            .map(|&(coeff, lit)| (div_ceil_signed(coeff, divisor), lit))
            .collect(),
        degree: div_ceil_signed(constraint.degree, divisor),
    })
}

fn saturate_constraint(constraint: &PbConstraint) -> PbConstraint {
    if constraint.degree <= 0 {
        return constraint.clone();
    }

    PbConstraint {
        terms: constraint
            .terms
            .iter()
            .map(|&(coeff, lit)| {
                if coeff > 0 {
                    (coeff.min(constraint.degree), lit)
                } else {
                    (coeff, lit)
                }
            })
            .collect(),
        degree: constraint.degree,
    }
}

fn round_constraint(constraint: &PbConstraint) -> Result<PbConstraint, PbError> {
    let divisor = coefficient_gcd(constraint);
    if divisor <= 1 {
        return Ok(constraint.clone());
    }

    divide_constraint(constraint, divisor as i64)
}

fn generalized_resolution_resolvent(
    left: &PbConstraint,
    right: &PbConstraint,
    var: u32,
) -> Result<PbConstraint, PbError> {
    let pos_lit = var as i32;
    let neg_lit = -(var as i32);

    let coeff_left = first_nonzero_coeff(left, pos_lit);
    let coeff_right = first_nonzero_coeff(right, neg_lit);

    let (alpha, beta) = match (coeff_left, coeff_right) {
        (Some(alpha), Some(beta)) if alpha > 0 && beta > 0 => (alpha, beta),
        _ => {
            return Err(PbError::ResolutionSignMismatch {
                var,
                left: 0,
                right: 1,
            });
        }
    };

    let scaled_left = multiply_constraint(left, beta);
    let scaled_right = multiply_constraint(right, alpha);
    let mut resolvent = add_constraints(&scaled_left, &scaled_right);
    resolvent
        .terms
        .retain(|&(_, lit)| lit != pos_lit && lit != neg_lit);
    resolvent.degree -= alpha * beta;
    Ok(resolvent)
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

fn first_nonzero_coeff(constraint: &PbConstraint, lit: i32) -> Option<i64> {
    constraint
        .terms
        .iter()
        .find_map(|&(coeff, term_lit)| (term_lit == lit && coeff != 0).then_some(coeff))
}

fn nonzero_occurrences(constraint: &PbConstraint, lit: i32) -> Vec<i64> {
    constraint
        .terms
        .iter()
        .filter_map(|&(coeff, term_lit)| (term_lit == lit && coeff != 0).then_some(coeff))
        .collect()
}

fn coefficient_gcd(constraint: &PbConstraint) -> u64 {
    constraint
        .terms
        .iter()
        .map(|&(coeff, _)| coeff.unsigned_abs())
        .fold(0u64, gcd)
}

fn div_ceil_signed(a: i64, b: i64) -> i64 {
    debug_assert!(b > 0);
    if a >= 0 {
        (a + b - 1) / b
    } else {
        -((-a) / b)
    }
}

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verify_division_soundness_small_constraint_ok() {
        let constraint = PbConstraint::new(vec![(2, 1), (3, 2)], 5);
        assert!(verify_division_soundness(&constraint, 2).is_ok());
    }

    #[test]
    fn test_verify_division_soundness_nonpositive_divisor_err() {
        let constraint = PbConstraint::new(vec![(2, 1)], 1);
        assert!(matches!(
            verify_division_soundness(&constraint, 0),
            Err(PbError::NonPositiveDivisor(0))
        ));
    }

    #[test]
    fn test_verify_rounding_soundness_large_constraint_ok() {
        let terms: Vec<(i64, i32)> = (1..=21).map(|var| (2, var)).collect();
        let constraint = PbConstraint::new(terms, 21);
        assert!(verify_rounding_soundness(&constraint).is_ok());
    }

    #[test]
    fn test_verify_saturation_soundness_small_negative_counterexample_err() {
        let constraint = PbConstraint::new(vec![(100, 1), (-89, 2)], 10);
        assert!(matches!(
            verify_saturation_soundness(&constraint),
            Err(PbError::ConversionError(_))
        ));
    }

    #[test]
    fn test_verify_saturation_soundness_large_nonnegative_ok() {
        let mut terms = vec![(25, 1)];
        terms.extend((2..=21).map(|var| (1, var)));
        let constraint = PbConstraint::new(terms, 10);
        assert!(verify_saturation_soundness(&constraint).is_ok());
    }

    #[test]
    fn test_verify_generalized_resolution_soundness_small_instance_ok() {
        let left = PbConstraint::new(vec![(2, 1), (3, 2)], 4);
        let right = PbConstraint::new(vec![(1, -1), (2, 3)], 2);
        assert!(verify_generalized_resolution_soundness(&left, &right, 1).is_ok());
    }

    #[test]
    fn test_verify_generalized_resolution_soundness_large_structural_gap_err() {
        let mut left_terms = vec![(2, 1), (1, -1)];
        left_terms.extend((2..=21).map(|var| (1, var)));
        let left = PbConstraint::new(left_terms, 4);

        let mut right_terms = vec![(1, -1)];
        right_terms.extend((2..=21).map(|var| (1, -var)));
        let right = PbConstraint::new(right_terms, 3);

        assert!(matches!(
            verify_generalized_resolution_soundness(&left, &right, 1),
            Err(PbError::ConversionError(_))
        ));
    }
}
