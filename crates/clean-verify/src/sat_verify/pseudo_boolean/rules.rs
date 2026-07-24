// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! PB proof derivation rules with soundness verification.
//!
//! Each rule transforms one or two PB constraints into a new constraint that is
//! a logical consequence of the inputs. Soundness means: every 0/1 assignment
//! satisfying the premises also satisfies the derived constraint.
//!
//! ## Rules
//!
//! - **Addition**: `C1 + C2` — add coefficients and degrees.
//! - **Scalar multiplication**: `k * C` — multiply all coefficients and degree.
//! - **Division**: `ceil(C / d)` — divide coefficients and degree, rounding up.
//!   Soundness: if sum(a_i * x_i) >= k, then sum(ceil(a_i/d) * x_i) >= ceil(k/d).
//! - **Saturation**: `min(a_i, k)` — cap coefficients at the degree.
//!   Soundness: for 0/1 variables, min(a_i, k) * x_i <= a_i * x_i when x_i=1,
//!   and the excess beyond k cannot help satisfy the constraint.
//! - **Rounding**: divide all by GCD of coefficients, ceiling on degree.
//! - **Generalized resolution**: resolve two PB constraints on a variable.

use std::collections::HashMap;

use super::types::{PbConstraint, PbFormula};
use super::PbError;

/// A PB proof derivation rule.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PbRule {
    /// Introduce an input constraint from the formula.
    Input(usize),
    /// Add two derived constraints.
    Addition { left: usize, right: usize },
    /// Multiply a constraint by a positive scalar.
    Multiplication { constraint: usize, scalar: i64 },
    /// Divide a constraint by a positive divisor (ceiling).
    Division { constraint: usize, divisor: i64 },
    /// Saturate: cap each coefficient at the degree.
    Saturation(usize),
    /// Rounding: divide by GCD of coefficients, ceiling on degree.
    Rounding(usize),
    /// Generalized resolution: resolve two constraints on a variable.
    GeneralizedResolution { left: usize, right: usize, var: u32 },
}

/// Apply a single PB rule, returning the derived constraint.
///
/// `derived` contains all constraints derived so far (indexed by step number).
/// `formula` contains the original input constraints.
pub(crate) fn verify_rule(
    derived: &[PbConstraint],
    formula: &PbFormula,
    rule: &PbRule,
) -> Result<PbConstraint, PbError> {
    match rule {
        PbRule::Input(idx) => {
            formula
                .constraints
                .get(*idx)
                .cloned()
                .ok_or(PbError::IndexOutOfBounds {
                    index: *idx,
                    count: formula.constraints.len(),
                })
        }

        PbRule::Addition { left, right } => {
            let l = get_derived(derived, *left)?;
            let r = get_derived(derived, *right)?;
            Ok(add_constraints(l, r))
        }

        PbRule::Multiplication { constraint, scalar } => {
            if *scalar <= 0 {
                return Err(PbError::NonPositiveScalar(*scalar));
            }
            let c = get_derived(derived, *constraint)?;
            Ok(multiply_constraint(c, *scalar))
        }

        PbRule::Division {
            constraint,
            divisor,
        } => {
            if *divisor <= 0 {
                return Err(PbError::NonPositiveDivisor(*divisor));
            }
            let c = get_derived(derived, *constraint)?;
            Ok(divide_constraint(c, *divisor))
        }

        PbRule::Saturation(idx) => {
            let c = get_derived(derived, *idx)?;
            // Saturation is only sound when all coefficients are non-negative.
            // With negative coefficients, capping positive coefficients at the
            // degree can incorrectly strengthen the inequality.
            if let Some(&(coeff, lit)) = c.terms.iter().find(|&&(coeff, _)| coeff < 0) {
                return Err(PbError::NegativeCoefficientInSaturation {
                    coeff,
                    literal: lit,
                });
            }
            Ok(saturate_constraint(c))
        }

        PbRule::Rounding(idx) => {
            let c = get_derived(derived, *idx)?;
            Ok(round_constraint(c))
        }

        PbRule::GeneralizedResolution { left, right, var } => {
            let l = get_derived(derived, *left)?;
            let r = get_derived(derived, *right)?;
            generalized_resolution(l, r, *var, *left, *right)
        }
    }
}

/// Verify a full PB proof: apply each rule in sequence and check that the
/// final derived constraint is a contradiction (0 >= k for k > 0).
pub(crate) fn verify_pb_proof(formula: &PbFormula, proof: &[PbRule]) -> Result<(), PbError> {
    let mut derived: Vec<PbConstraint> = Vec::with_capacity(proof.len());

    for rule in proof {
        let constraint = verify_rule(&derived, formula, rule)?;
        derived.push(constraint);
    }

    // Check that the last derived constraint is a contradiction.
    match derived.last() {
        Some(c) if c.is_contradiction() => Ok(()),
        _ => Err(PbError::NoContradiction),
    }
}

// --- Rule implementations ---

/// Add two PB constraints: merge term maps, sum degrees, cancel complementary literals.
///
/// When both `a * x` and `b * ~x` appear in the sum, they represent
/// `a * x + b * (1 - x) = (a - b) * x + b`, which absorbs `b` into a
/// constant that adjusts the degree. This cancellation is essential for
/// detecting contradictions like `x + ~x >= 2` (which simplifies to `1 >= 2`).
fn add_constraints(left: &PbConstraint, right: &PbConstraint) -> PbConstraint {
    let mut term_map: HashMap<i32, i64> = HashMap::new();
    for &(coeff, lit) in &left.terms {
        *term_map.entry(lit).or_insert(0) += coeff;
    }
    for &(coeff, lit) in &right.terms {
        *term_map.entry(lit).or_insert(0) += coeff;
    }

    // Remove zero-coefficient terms.
    term_map.retain(|_, c| *c != 0);

    let mut degree = left.degree + right.degree;

    // Cancel complementary literal pairs: a*x + b*~x.
    // Since ~x = 1 - x: a*x + b*(1-x) = (a-b)*x + b.
    // The constant b is absorbed into the degree adjustment.
    let vars_with_both: Vec<u32> = term_map
        .keys()
        .filter(|&&lit| lit > 0 && term_map.contains_key(&-lit))
        .map(|&lit| lit as u32)
        .collect();

    for var in vars_with_both {
        let pos_lit = var as i32;
        let neg_lit = -(var as i32);
        let a = term_map.remove(&pos_lit).unwrap_or(0);
        let b = term_map.remove(&neg_lit).unwrap_or(0);
        // a*x + b*~x = a*x + b*(1-x) = (a-b)*x + b
        // Constraint: ... + (a-b)*x >= degree - b
        degree -= b;
        let net = a - b;
        if net != 0 {
            if net > 0 {
                term_map.insert(pos_lit, net);
            } else {
                // Negative coefficient on positive literal: express as ~x.
                // -c * x = c * ~x - c, so degree += c.
                term_map.insert(neg_lit, -net);
                degree += -net;
            }
        }
    }

    let mut terms: Vec<(i64, i32)> = term_map
        .into_iter()
        .filter(|&(_, c)| c != 0)
        .map(|(lit, coeff)| (coeff, lit))
        .collect();
    terms.sort_by_key(|&(_, lit)| (lit.unsigned_abs(), lit < 0));

    PbConstraint { terms, degree }
}

/// Multiply a PB constraint by a positive scalar.
fn multiply_constraint(c: &PbConstraint, scalar: i64) -> PbConstraint {
    PbConstraint {
        terms: c
            .terms
            .iter()
            .map(|&(coeff, lit)| (coeff * scalar, lit))
            .collect(),
        degree: c.degree * scalar,
    }
}

/// Divide a PB constraint by a positive divisor, ceiling on coefficients and degree.
///
/// Soundness: if sum(a_i * x_i) >= k, then sum(ceil(a_i / d) * x_i) >= ceil(k / d).
/// Proof: sum(ceil(a_i/d) * x_i) >= sum((a_i/d) * x_i) = (1/d) * sum(a_i * x_i)
///        >= k/d, and since the LHS is an integer, it >= ceil(k/d).
fn divide_constraint(c: &PbConstraint, divisor: i64) -> PbConstraint {
    PbConstraint {
        terms: c
            .terms
            .iter()
            .map(|&(coeff, lit)| (div_ceil_signed(coeff, divisor), lit))
            .collect(),
        degree: div_ceil_signed(c.degree, divisor),
    }
}

/// Saturate a PB constraint: cap each coefficient at the degree.
///
/// Soundness: for 0/1 variables, if a_i > k and x_i = 1, then a_i * x_i = a_i > k,
/// but we only need the variable to contribute at most k to satisfy sum >= k.
/// Replacing a_i with min(a_i, k) preserves the constraint validity.
fn saturate_constraint(c: &PbConstraint) -> PbConstraint {
    if c.degree <= 0 {
        return c.clone();
    }
    PbConstraint {
        terms: c
            .terms
            .iter()
            .map(|&(coeff, lit)| {
                if coeff > 0 {
                    (coeff.min(c.degree), lit)
                } else {
                    (coeff, lit)
                }
            })
            .collect(),
        degree: c.degree,
    }
}

/// Round a PB constraint: divide all coefficients and degree by GCD.
///
/// Soundness: same as division rule, but we choose d = gcd of all coefficients.
fn round_constraint(c: &PbConstraint) -> PbConstraint {
    if c.terms.is_empty() {
        return c.clone();
    }

    let g = c
        .terms
        .iter()
        .map(|&(coeff, _)| coeff.unsigned_abs())
        .fold(0u64, gcd);

    if g <= 1 {
        return c.clone();
    }

    let d = g as i64;
    divide_constraint(c, d)
}

/// Simplify mixed-polarity terms for a variable in a PB constraint.
///
/// If a constraint contains both `a * x` and `b * ~x` for the same variable,
/// replace them with a single term using the identity:
///   `a * x + b * ~x = a * x + b * (1 - x) = (a - b) * x + b`
///
/// This absorbs the constant `b` into the degree and leaves a single-polarity
/// term. If `a >= b`, the result is `(a - b) * x` with `degree -= b`.
/// If `b > a`, the result is `(b - a) * ~x` with `degree -= a`.
///
/// Returns `(simplified_constraint, degree_adjustment)` where `degree_adjustment`
/// is the amount to subtract from the degree.
fn simplify_mixed_polarity(c: &PbConstraint, var: u32) -> PbConstraint {
    let pos_lit = var as i32;
    let neg_lit = -(var as i32);

    let pos_coeff: i64 = c
        .terms
        .iter()
        .filter(|&&(_, lit)| lit == pos_lit)
        .map(|&(coeff, _)| coeff)
        .sum();
    let neg_coeff: i64 = c
        .terms
        .iter()
        .filter(|&&(_, lit)| lit == neg_lit)
        .map(|&(coeff, _)| coeff)
        .sum();

    // No mixed polarity — return unchanged.
    if pos_coeff == 0 || neg_coeff == 0 {
        return c.clone();
    }

    // Collect all terms except those involving var.
    let mut new_terms: Vec<(i64, i32)> = c
        .terms
        .iter()
        .filter(|&&(_, lit)| lit != pos_lit && lit != neg_lit)
        .copied()
        .collect();

    // a * x + b * ~x = (a - b) * x + b  (if a >= b)
    //                 = (b - a) * ~x + a  (if b > a)
    let mut degree = c.degree;
    if pos_coeff >= neg_coeff {
        // Net positive: keep positive literal, absorb neg_coeff into degree.
        degree -= neg_coeff;
        let net = pos_coeff - neg_coeff;
        if net != 0 {
            new_terms.push((net, pos_lit));
        }
    } else {
        // Net negative: keep negative literal, absorb pos_coeff into degree.
        degree -= pos_coeff;
        let net = neg_coeff - pos_coeff;
        if net != 0 {
            new_terms.push((net, neg_lit));
        }
    }

    new_terms.sort_by_key(|&(_, lit)| (lit.unsigned_abs(), lit < 0));
    PbConstraint {
        terms: new_terms,
        degree,
    }
}

/// Generalized resolution: resolve two PB constraints on a variable.
///
/// Given: L: sum(a_i * l_i) >= k_L, containing literal +v with coefficient c_L
///        R: sum(b_j * l_j) >= k_R, containing literal -v with coefficient c_R
///
/// If either constraint contains the resolution variable in both polarities
/// (mixed polarity), the constraint is first simplified using the identity
/// `a*x + b*~x = (a-b)*x + b` to produce a single-polarity form.
///
/// Then multiply L by c_R and R by c_L, and add. The variable v cancels out
/// (c_R * c_L * v + c_L * c_R * ~v = c_L * c_R, which gets absorbed into degree).
fn generalized_resolution(
    left: &PbConstraint,
    right: &PbConstraint,
    var: u32,
    left_idx: usize,
    right_idx: usize,
) -> Result<PbConstraint, PbError> {
    let pos_lit = var as i32;
    let neg_lit = -(var as i32);

    // Simplify mixed-polarity terms before resolution.
    // If left has both +v and -v, or right has both, simplify them first.
    let left_simplified = simplify_mixed_polarity(left, var);
    let right_simplified = simplify_mixed_polarity(right, var);

    // Find coefficients of the resolution variable after simplification.
    let coeff_l = left_simplified
        .terms
        .iter()
        .find(|&&(_, lit)| lit == pos_lit)
        .map(|&(c, _)| c);
    let coeff_r = right_simplified
        .terms
        .iter()
        .find(|&&(_, lit)| lit == neg_lit)
        .map(|&(c, _)| c);

    let (c_l, c_r) = match (coeff_l, coeff_r) {
        (Some(cl), Some(cr)) if cl > 0 && cr > 0 => (cl, cr),
        _ => {
            return Err(PbError::ResolutionSignMismatch {
                var,
                left: left_idx,
                right: right_idx,
            });
        }
    };

    // Multiply left by c_r, right by c_l, then add.
    // The add_constraints function handles complementary literal cancellation:
    // c_r*c_l * x + c_l*c_r * ~x cancels to a constant c_l*c_r absorbed into degree.
    let scaled_left = multiply_constraint(&left_simplified, c_r);
    let scaled_right = multiply_constraint(&right_simplified, c_l);
    let result = add_constraints(&scaled_left, &scaled_right);

    Ok(result)
}

fn get_derived(derived: &[PbConstraint], idx: usize) -> Result<&PbConstraint, PbError> {
    derived.get(idx).ok_or(PbError::IndexOutOfBounds {
        index: idx,
        count: derived.len(),
    })
}

/// Integer ceiling division for signed values.
fn div_ceil_signed(a: i64, b: i64) -> i64 {
    debug_assert!(b > 0);
    if a >= 0 {
        (a + b - 1) / b
    } else {
        // For negative a: ceiling division.
        // e.g., ceil(-5/3) = -1 (not -2).
        -((-a) / b)
    }
}

/// GCD of two unsigned integers (Euclidean algorithm).
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
    fn test_div_ceil_signed_positive() {
        assert_eq!(div_ceil_signed(5, 3), 2);
        assert_eq!(div_ceil_signed(6, 3), 2);
        assert_eq!(div_ceil_signed(7, 3), 3);
        assert_eq!(div_ceil_signed(0, 3), 0);
    }

    #[test]
    fn test_div_ceil_signed_negative() {
        assert_eq!(div_ceil_signed(-5, 3), -1);
        assert_eq!(div_ceil_signed(-6, 3), -2);
        assert_eq!(div_ceil_signed(-1, 3), 0);
    }

    #[test]
    fn test_gcd_basic() {
        assert_eq!(gcd(12, 8), 4);
        assert_eq!(gcd(7, 3), 1);
        assert_eq!(gcd(0, 5), 5);
        assert_eq!(gcd(10, 0), 10);
    }

    // --- Mixed-polarity simplification tests ---

    #[test]
    fn test_simplify_mixed_polarity_no_mixed() {
        // 2*x1 + 3*x2 >= 4 — no mixed polarity on any var.
        let c = PbConstraint::new(vec![(2, 1), (3, 2)], 4);
        let result = simplify_mixed_polarity(&c, 1);
        assert_eq!(result, c); // unchanged
    }

    #[test]
    fn test_simplify_mixed_polarity_pos_dominant() {
        // 5*x1 + 2*~x1 >= 6
        // After simplification: (5-2)*x1 >= 6 - 2 = 3*x1 >= 4
        let c = PbConstraint::new(vec![(5, 1), (2, -1)], 6);
        let result = simplify_mixed_polarity(&c, 1);
        assert_eq!(result.terms, vec![(3, 1)]);
        assert_eq!(result.degree, 4);
    }

    #[test]
    fn test_simplify_mixed_polarity_neg_dominant() {
        // 2*x1 + 5*~x1 >= 6
        // After simplification: (5-2)*~x1 >= 6 - 2 = 3*~x1 >= 4
        let c = PbConstraint::new(vec![(2, 1), (5, -1)], 6);
        let result = simplify_mixed_polarity(&c, 1);
        assert_eq!(result.terms, vec![(3, -1)]);
        assert_eq!(result.degree, 4);
    }

    #[test]
    fn test_simplify_mixed_polarity_equal_coefficients() {
        // 3*x1 + 3*~x1 + 2*x2 >= 5
        // After simplification: degree -= 3, var eliminated -> 2*x2 >= 2
        let c = PbConstraint::new(vec![(3, 1), (3, -1), (2, 2)], 5);
        let result = simplify_mixed_polarity(&c, 1);
        assert_eq!(result.terms, vec![(2, 2)]);
        assert_eq!(result.degree, 2);
    }

    #[test]
    fn test_simplify_mixed_polarity_preserves_other_terms() {
        // 4*x1 + 1*~x1 + 2*x2 + 3*x3 >= 7
        // After simplification: (4-1)*x1 + 2*x2 + 3*x3 >= 7 - 1 = 3*x1 + 2*x2 + 3*x3 >= 6
        let c = PbConstraint::new(vec![(4, 1), (1, -1), (2, 2), (3, 3)], 7);
        let result = simplify_mixed_polarity(&c, 1);
        let coeff_map: std::collections::HashMap<i32, i64> =
            result.terms.iter().map(|&(c, l)| (l, c)).collect();
        assert_eq!(coeff_map.get(&1), Some(&3));
        assert_eq!(coeff_map.get(&2), Some(&2));
        assert_eq!(coeff_map.get(&3), Some(&3));
        assert_eq!(result.degree, 6);
    }

    // --- Saturation guard tests ---

    #[test]
    fn test_saturation_all_positive_coefficients_succeeds() {
        // 5*x1 + 3*x2 + 1*x3 >= 3 — all positive, saturation should work.
        let formula = PbFormula::new(3);
        let derived = vec![PbConstraint::new(vec![(5, 1), (3, 2), (1, 3)], 3)];

        let result = verify_rule(&derived, &formula, &PbRule::Saturation(0))
            .expect("saturation with all-positive coefficients should succeed");

        // min(5,3)=3, min(3,3)=3, min(1,3)=1
        assert_eq!(result.terms[0], (3, 1));
        assert_eq!(result.terms[1], (3, 2));
        assert_eq!(result.terms[2], (1, 3));
        assert_eq!(result.degree, 3);
    }

    #[test]
    fn test_saturation_negative_coefficient_rejected() {
        // 100*x1 + (-89)*x2 >= 10 — negative coefficient, must be rejected.
        // Soundness violation: x1=1, x2=1 gives original sum=11 >= 10 (sat),
        // but saturated 10*x1 + (-89)*x2 >= 10 gives -79 < 10 (unsat).
        let formula = PbFormula::new(2);
        let derived = vec![PbConstraint::new(vec![(100, 1), (-89, 2)], 10)];

        let err = verify_rule(&derived, &formula, &PbRule::Saturation(0)).unwrap_err();

        assert!(
            matches!(
                err,
                PbError::NegativeCoefficientInSaturation {
                    coeff: -89,
                    literal: 2,
                }
            ),
            "expected NegativeCoefficientInSaturation, got: {err:?}"
        );
    }

    #[test]
    fn test_saturation_coefficient_equal_to_degree() {
        // 3*x1 + 3*x2 + 1*x3 >= 3 — coefficients equal to degree left unchanged.
        let formula = PbFormula::new(3);
        let derived = vec![PbConstraint::new(vec![(3, 1), (3, 2), (1, 3)], 3)];

        let result = verify_rule(&derived, &formula, &PbRule::Saturation(0))
            .expect("saturation with coeff == degree should succeed");

        // min(3,3)=3, min(3,3)=3, min(1,3)=1 — all unchanged
        assert_eq!(result.terms[0], (3, 1));
        assert_eq!(result.terms[1], (3, 2));
        assert_eq!(result.terms[2], (1, 3));
        assert_eq!(result.degree, 3);
    }

    #[test]
    fn test_saturation_mixed_with_negated_literal_rejected() {
        // 5*x1 + 3*~x2 + (-2)*x3 >= 4 — negative coeff on x3, must reject.
        let formula = PbFormula::new(3);
        let derived = vec![PbConstraint::new(vec![(5, 1), (3, -2), (-2, 3)], 4)];

        let err = verify_rule(&derived, &formula, &PbRule::Saturation(0)).unwrap_err();

        assert!(
            matches!(
                err,
                PbError::NegativeCoefficientInSaturation {
                    coeff: -2,
                    literal: 3,
                }
            ),
            "expected NegativeCoefficientInSaturation for negative coeff, got: {err:?}"
        );
    }

    #[test]
    fn test_saturation_soundness_exhaustive_positive_coefficients() {
        // Exhaustively verify that saturation preserves all satisfying assignments
        // when all coefficients are non-negative.
        // 7*x1 + 4*x2 + 2*x3 >= 5
        let c = PbConstraint::new(vec![(7, 1), (4, 2), (2, 3)], 5);
        let formula = PbFormula::new(3);
        let derived = vec![c.clone()];

        let saturated = verify_rule(&derived, &formula, &PbRule::Saturation(0))
            .expect("saturation with all-positive should succeed");

        // Exhaustive check: every satisfying assignment of original satisfies saturated.
        for x1 in [false, true] {
            for x2 in [false, true] {
                for x3 in [false, true] {
                    let orig_sum =
                        if x1 { 7 } else { 0 } + if x2 { 4 } else { 0 } + if x3 { 2 } else { 0 };
                    let sat_sum: i64 = saturated
                        .terms
                        .iter()
                        .map(|&(coeff, lit)| {
                            let val = match lit.unsigned_abs() {
                                1 => x1,
                                2 => x2,
                                3 => x3,
                                _ => unreachable!(),
                            };
                            let effective = if lit > 0 { val } else { !val };
                            if effective {
                                coeff
                            } else {
                                0
                            }
                        })
                        .sum();
                    if orig_sum >= 5 {
                        assert!(
                            sat_sum >= saturated.degree,
                            "saturation unsound for x1={x1}, x2={x2}, x3={x3}: \
                             orig_sum={orig_sum} >= 5 but sat_sum={sat_sum} < {}",
                            saturated.degree
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn test_simplify_mixed_polarity_soundness_exhaustive() {
        // Verify soundness: for all 2^1 = 2 assignments, the simplified
        // constraint is satisfied iff the original is.
        let c = PbConstraint::new(vec![(5, 1), (3, -1)], 4);
        let simplified = simplify_mixed_polarity(&c, 1);

        for x1 in [false, true] {
            let orig_sum = if x1 { 5 } else { 0 } + if !x1 { 3 } else { 0 };
            let orig_sat = orig_sum >= 4;

            // Simplified: 2*x1 >= 1
            let simp_sum: i64 = simplified
                .terms
                .iter()
                .map(|&(coeff, lit)| {
                    let var_val = if lit > 0 { x1 } else { !x1 };
                    if var_val {
                        coeff
                    } else {
                        0
                    }
                })
                .sum();
            let simp_sat = simp_sum >= simplified.degree;

            assert_eq!(
                orig_sat, simp_sat,
                "soundness violated for x1={x1}: orig_sum={orig_sum}>=4 is {orig_sat}, simp_sum={simp_sum}>={} is {simp_sat}",
                simplified.degree
            );
        }
    }
}
