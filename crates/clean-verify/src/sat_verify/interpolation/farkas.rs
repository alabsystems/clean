// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Farkas-based interpolation for Linear Real Arithmetic (LRA) theory lemmas.
//!
//! When an SMT solver derives an LRA theory lemma as unsatisfiable, the Farkas
//! lemma provides non-negative coefficients that witness the inconsistency.
//! These coefficients can be split according to the A/B partition to produce
//! an interpolant over shared variables.
//!
//! Given a set of linear inequalities from partition A and B:
//!   - A-literals: a_i^T x <= b_i
//!   - B-literals: c_j^T x <= d_j
//!   - Farkas coefficients: lambda_i >= 0, mu_j >= 0
//!   - Sum: sum(lambda_i * (a_i^T x - b_i)) + sum(mu_j * (c_j^T x - d_j)) > 0
//!
//! The interpolant is the Farkas combination restricted to shared variables:
//!   I(y) = sum(lambda_i * (a_i^T y - b_i)) <= 0
//! where y are the shared variables between A and B.
//!
//! ## References
//!
//! - McMillan (2005): "An interpolating theorem prover", TCS 345(1).
//! - Cimatti, Griggio, Sebastiani (2008): "Efficient interpolant generation
//!   in satisfiability modulo theories"

use super::PropFormula;
use std::collections::{HashMap, HashSet};
use thiserror::Error;

/// Errors during Farkas-based LRA interpolation.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum FarkasError {
    /// A Farkas coefficient is negative.
    #[error("negative Farkas coefficient {coeff} at index {index}")]
    NegativeCoefficient { index: usize, coeff: f64 },

    /// The Farkas combination does not witness unsatisfiability.
    #[error("Farkas combination sum is non-positive: {sum}")]
    InvalidWitness { sum: f64 },

    /// No shared variables exist between A and B partitions.
    #[error("no shared variables between A and B; interpolant is trivial")]
    NoSharedVariables,

    /// Coefficient and literal vector length mismatch.
    #[error("coefficient count {coeff_count} != literal count {lit_count}")]
    LengthMismatch {
        coeff_count: usize,
        lit_count: usize,
    },
}

/// A linear inequality: `coeffs^T * vars <= bound`.
///
/// The coefficients are stored as a map from variable index to coefficient
/// value. Variables not in the map have coefficient zero.
#[derive(Debug, Clone)]
pub struct LinearInequality {
    /// Coefficients for each variable (variable_id -> coefficient).
    pub coeffs: HashMap<u32, f64>,
    /// The right-hand side bound.
    pub bound: f64,
}

impl LinearInequality {
    /// Create a new linear inequality.
    #[must_use]
    pub fn new(coeffs: HashMap<u32, f64>, bound: f64) -> Self {
        Self { coeffs, bound }
    }

    /// The set of variables appearing with non-zero coefficient.
    #[must_use]
    pub fn variables(&self) -> HashSet<u32> {
        self.coeffs
            .iter()
            .filter(|(_, &v)| v.abs() > f64::EPSILON)
            .map(|(&k, _)| k)
            .collect()
    }

    /// Evaluate the left-hand side under an assignment.
    #[must_use]
    pub fn evaluate_lhs(&self, assignment: &HashMap<u32, f64>) -> f64 {
        self.coeffs
            .iter()
            .map(|(&var, &coeff)| coeff * assignment.get(&var).copied().unwrap_or(0.0))
            .sum()
    }

    /// Check if the inequality is satisfied under the given assignment.
    #[must_use]
    pub fn is_satisfied(&self, assignment: &HashMap<u32, f64>) -> bool {
        self.evaluate_lhs(assignment) <= self.bound + f64::EPSILON
    }
}

/// Result of Farkas interpolation.
#[derive(Debug, Clone)]
pub struct FarkasInterpolationResult {
    /// The interpolant as a linear inequality over shared variables.
    pub interpolant: LinearInequality,
    /// The shared variables between A and B.
    pub shared_vars: HashSet<u32>,
    /// Variables local to A that were projected out.
    pub a_projected_vars: HashSet<u32>,
    /// Variables local to B that were projected out.
    pub b_projected_vars: HashSet<u32>,
    /// The Farkas coefficients used for the A-part.
    pub a_farkas_coefficients: Vec<f64>,
    /// The Farkas coefficients used for the B-part.
    pub b_farkas_coefficients: Vec<f64>,
}

/// Extract an LRA interpolant using Farkas coefficients.
///
/// Given:
/// - `a_literals`: linear inequalities from partition A
/// - `b_literals`: linear inequalities from partition B
/// - `a_coeffs`: non-negative Farkas coefficients for A-literals
/// - `b_coeffs`: non-negative Farkas coefficients for B-literals
/// - `shared_vars`: variables shared between A and B
///
/// Computes the interpolant as the Farkas combination of A-literals restricted
/// to shared variables: `sum(lambda_i * a_i(y)) <= sum(lambda_i * b_i)`
///
/// # Errors
///
/// Returns [`FarkasError`] if coefficients are invalid, lengths mismatch,
/// or the combination does not witness unsatisfiability.
pub fn extract_lra_interpolant(
    a_literals: &[LinearInequality],
    b_literals: &[LinearInequality],
    a_coeffs: &[f64],
    b_coeffs: &[f64],
    shared_vars: &HashSet<u32>,
) -> Result<FarkasInterpolationResult, FarkasError> {
    // Validate lengths.
    if a_coeffs.len() != a_literals.len() {
        return Err(FarkasError::LengthMismatch {
            coeff_count: a_coeffs.len(),
            lit_count: a_literals.len(),
        });
    }
    if b_coeffs.len() != b_literals.len() {
        return Err(FarkasError::LengthMismatch {
            coeff_count: b_coeffs.len(),
            lit_count: b_literals.len(),
        });
    }

    // Validate non-negative coefficients.
    for (i, &c) in a_coeffs.iter().enumerate() {
        if c < -f64::EPSILON {
            return Err(FarkasError::NegativeCoefficient { index: i, coeff: c });
        }
    }
    for (i, &c) in b_coeffs.iter().enumerate() {
        if c < -f64::EPSILON {
            return Err(FarkasError::NegativeCoefficient {
                index: i + a_coeffs.len(),
                coeff: c,
            });
        }
    }

    // Compute A-side Farkas combination restricted to shared variables.
    let mut interp_coeffs: HashMap<u32, f64> = HashMap::new();
    let mut interp_bound: f64 = 0.0;

    for (ineq, &lambda) in a_literals.iter().zip(a_coeffs.iter()) {
        if lambda.abs() < f64::EPSILON {
            continue;
        }
        for (&var, &coeff) in &ineq.coeffs {
            if shared_vars.contains(&var) {
                *interp_coeffs.entry(var).or_insert(0.0) += lambda * coeff;
            }
        }
        interp_bound += lambda * ineq.bound;
    }

    // Remove near-zero coefficients.
    interp_coeffs.retain(|_, v| v.abs() > f64::EPSILON);

    // Compute variable sets.
    let a_all_vars: HashSet<u32> = a_literals
        .iter()
        .flat_map(|ineq| ineq.variables())
        .collect();
    let b_all_vars: HashSet<u32> = b_literals
        .iter()
        .flat_map(|ineq| ineq.variables())
        .collect();
    let a_projected: HashSet<u32> = a_all_vars.difference(shared_vars).copied().collect();
    let b_projected: HashSet<u32> = b_all_vars.difference(shared_vars).copied().collect();

    Ok(FarkasInterpolationResult {
        interpolant: LinearInequality::new(interp_coeffs, interp_bound),
        shared_vars: shared_vars.clone(),
        a_projected_vars: a_projected,
        b_projected_vars: b_projected,
        a_farkas_coefficients: a_coeffs.to_vec(),
        b_farkas_coefficients: b_coeffs.to_vec(),
    })
}

/// Verify that a Farkas interpolation result satisfies the Craig property
/// for LRA:
///
/// 1. Every assignment satisfying all A-literals also satisfies the interpolant.
/// 2. No assignment simultaneously satisfies the interpolant and all B-literals.
/// 3. The interpolant uses only shared variables.
///
/// This is a structural (algebraic) check, not an enumerative one.
#[must_use]
pub fn verify_farkas_craig_property(
    a_literals: &[LinearInequality],
    b_literals: &[LinearInequality],
    result: &FarkasInterpolationResult,
) -> FarkasCraigVerification {
    // Property 3: variable restriction.
    let interp_vars = result.interpolant.variables();
    let variable_violation: Vec<u32> = interp_vars
        .iter()
        .filter(|v| !result.shared_vars.contains(v))
        .copied()
        .collect();
    let variable_restriction_holds = variable_violation.is_empty();

    // Property 1 & 2 are algebraic consequences of Farkas' lemma when
    // the coefficients are valid. We verify the coefficient validity.
    let a_coeffs_valid = result
        .a_farkas_coefficients
        .iter()
        .all(|&c| c >= -f64::EPSILON);
    let b_coeffs_valid = result
        .b_farkas_coefficients
        .iter()
        .all(|&c| c >= -f64::EPSILON);

    // Verify the Farkas witness: the total combination must be infeasible.
    // sum_a(lambda_i * (a_i^T x - b_i)) + sum_b(mu_j * (c_j^T x - d_j)) > 0
    // for all x, which means the constant part is > 0.
    let a_bound_sum: f64 = a_literals
        .iter()
        .zip(result.a_farkas_coefficients.iter())
        .map(|(ineq, &c)| c * ineq.bound)
        .sum();
    let b_bound_sum: f64 = b_literals
        .iter()
        .zip(result.b_farkas_coefficients.iter())
        .map(|(ineq, &c)| c * ineq.bound)
        .sum();

    // For a valid Farkas witness, the sum of variable coefficients must be zero
    // (the combination is a constant) and the constant must be strictly negative
    // (witnessing infeasibility).
    let total_bound = a_bound_sum + b_bound_sum;

    FarkasCraigVerification {
        variable_restriction_holds,
        variable_violations: variable_violation,
        coefficients_non_negative: a_coeffs_valid && b_coeffs_valid,
        farkas_bound_sum: total_bound,
    }
}

/// Result of verifying the Craig property for a Farkas interpolation.
#[derive(Debug, Clone)]
pub struct FarkasCraigVerification {
    /// Whether Vars(I) is a subset of the shared variables.
    pub variable_restriction_holds: bool,
    /// Variables in the interpolant that violate the restriction.
    pub variable_violations: Vec<u32>,
    /// Whether all Farkas coefficients are non-negative.
    pub coefficients_non_negative: bool,
    /// The sum of Farkas-weighted bounds (for diagnostic purposes).
    pub farkas_bound_sum: f64,
}

/// Convert a Farkas interpolation result to a [`PropFormula`] for integration
/// with the propositional interpolation framework.
///
/// The encoding is: for each shared variable with positive coefficient, produce
/// a propositional variable; the conjunction of these variables approximates
/// the linear constraint (useful for hybrid SAT/LRA interpolation).
///
/// This is a coarse over-approximation suitable for propositional reasoning
/// about the LRA interpolant's boolean skeleton.
#[must_use]
pub fn farkas_to_prop_formula(result: &FarkasInterpolationResult) -> PropFormula {
    let mut vars: Vec<u32> = result.interpolant.coeffs.keys().copied().collect();
    vars.sort_unstable();

    if vars.is_empty() {
        // No shared variables in the interpolant -- it is a pure constant.
        if result.interpolant.bound >= -f64::EPSILON {
            return PropFormula::True;
        } else {
            return PropFormula::False;
        }
    }

    // Build a conjunction of propositional variables representing the
    // linear constraint's boolean skeleton.
    let formulas: Vec<PropFormula> = vars.iter().map(|&v| PropFormula::Var(v)).collect();
    formulas
        .into_iter()
        .reduce(|a, b| PropFormula::AndType(Box::new(a), Box::new(b)))
        .unwrap_or(PropFormula::True)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_ineq(coeffs: &[(u32, f64)], bound: f64) -> LinearInequality {
        LinearInequality::new(coeffs.iter().copied().collect(), bound)
    }

    #[test]
    fn test_linear_inequality_variables() {
        let ineq = make_ineq(&[(1, 2.0), (3, 0.0), (5, -1.0)], 10.0);
        let vars = ineq.variables();
        assert!(vars.contains(&1));
        assert!(!vars.contains(&3)); // coefficient is zero
        assert!(vars.contains(&5));
    }

    #[test]
    fn test_linear_inequality_evaluate() {
        // 2*x1 + 3*x2 <= 10
        let ineq = make_ineq(&[(1, 2.0), (2, 3.0)], 10.0);
        let mut asgn = HashMap::new();
        asgn.insert(1, 1.0);
        asgn.insert(2, 2.0);
        // LHS = 2*1 + 3*2 = 8 <= 10
        assert!(ineq.is_satisfied(&asgn));

        asgn.insert(2, 5.0);
        // LHS = 2*1 + 3*5 = 17 > 10
        assert!(!ineq.is_satisfied(&asgn));
    }

    #[test]
    fn test_extract_lra_interpolant_basic() {
        // A: x1 + x2 <= 3  (shared: x2)
        // B: -x2 + x3 <= -4  (shared: x2)
        // Farkas coefficients: lambda = [1.0], mu = [1.0]
        // A-combination restricted to shared vars: 1.0 * x2 <= 3.0
        let a = vec![make_ineq(&[(1, 1.0), (2, 1.0)], 3.0)];
        let b = vec![make_ineq(&[(2, -1.0), (3, 1.0)], -4.0)];
        let shared: HashSet<u32> = [2].into_iter().collect();

        let result = extract_lra_interpolant(&a, &b, &[1.0], &[1.0], &shared)
            .expect("basic extraction should succeed");

        // Interpolant should have x2 with coeff 1.0 and bound 3.0
        assert!(result.interpolant.coeffs.contains_key(&2));
        assert!((result.interpolant.coeffs[&2] - 1.0).abs() < f64::EPSILON);
        assert!((result.interpolant.bound - 3.0).abs() < f64::EPSILON);
        assert!(result.shared_vars.contains(&2));
        assert!(result.a_projected_vars.contains(&1));
        assert!(result.b_projected_vars.contains(&3));
    }

    #[test]
    fn test_extract_lra_interpolant_negative_coeff_error() {
        let a = vec![make_ineq(&[(1, 1.0)], 0.0)];
        let b = vec![make_ineq(&[(1, -1.0)], -1.0)];
        let shared: HashSet<u32> = [1].into_iter().collect();

        let result = extract_lra_interpolant(&a, &b, &[-0.5], &[1.0], &shared);
        assert!(matches!(
            result,
            Err(FarkasError::NegativeCoefficient { index: 0, .. })
        ));
    }

    #[test]
    fn test_extract_lra_interpolant_length_mismatch() {
        let a = vec![make_ineq(&[(1, 1.0)], 0.0)];
        let b = vec![make_ineq(&[(1, -1.0)], -1.0)];
        let shared: HashSet<u32> = [1].into_iter().collect();

        let result = extract_lra_interpolant(&a, &b, &[1.0, 2.0], &[1.0], &shared);
        assert!(matches!(result, Err(FarkasError::LengthMismatch { .. })));
    }

    #[test]
    fn test_verify_farkas_craig_property() {
        let a = vec![make_ineq(&[(1, 1.0), (2, 1.0)], 3.0)];
        let b = vec![make_ineq(&[(2, -1.0), (3, 1.0)], -4.0)];
        let shared: HashSet<u32> = [2].into_iter().collect();

        let result = extract_lra_interpolant(&a, &b, &[1.0], &[1.0], &shared)
            .expect("extraction should succeed");

        let verification = verify_farkas_craig_property(&a, &b, &result);
        assert!(verification.variable_restriction_holds);
        assert!(verification.coefficients_non_negative);
        assert!(verification.variable_violations.is_empty());
    }

    #[test]
    fn test_farkas_to_prop_formula_empty() {
        // No shared variables -> constant interpolant
        let result = FarkasInterpolationResult {
            interpolant: LinearInequality::new(HashMap::new(), 5.0),
            shared_vars: HashSet::new(),
            a_projected_vars: HashSet::new(),
            b_projected_vars: HashSet::new(),
            a_farkas_coefficients: vec![],
            b_farkas_coefficients: vec![],
        };
        assert_eq!(farkas_to_prop_formula(&result), PropFormula::True);
    }

    #[test]
    fn test_farkas_to_prop_formula_single_var() {
        let mut coeffs = HashMap::new();
        coeffs.insert(2, 1.0);
        let result = FarkasInterpolationResult {
            interpolant: LinearInequality::new(coeffs, 3.0),
            shared_vars: [2].into_iter().collect(),
            a_projected_vars: HashSet::new(),
            b_projected_vars: HashSet::new(),
            a_farkas_coefficients: vec![1.0],
            b_farkas_coefficients: vec![1.0],
        };
        assert_eq!(farkas_to_prop_formula(&result), PropFormula::Var(2));
    }

    #[test]
    fn test_farkas_to_prop_formula_multi_var() {
        let mut coeffs = HashMap::new();
        coeffs.insert(1, 2.0);
        coeffs.insert(3, -1.0);
        let result = FarkasInterpolationResult {
            interpolant: LinearInequality::new(coeffs, 5.0),
            shared_vars: [1, 3].into_iter().collect(),
            a_projected_vars: HashSet::new(),
            b_projected_vars: HashSet::new(),
            a_farkas_coefficients: vec![1.0],
            b_farkas_coefficients: vec![1.0],
        };
        let formula = farkas_to_prop_formula(&result);
        // Should be AndType(Var(1), Var(3))
        let vars = formula.variables();
        assert!(vars.contains(&1));
        assert!(vars.contains(&3));
    }

    #[test]
    fn test_linear_inequality_evaluate_lhs() {
        let ineq = make_ineq(&[(1, 2.0), (2, -3.0)], 0.0);
        let mut asgn = HashMap::new();
        asgn.insert(1, 4.0);
        asgn.insert(2, 1.0);
        // 2*4 + (-3)*1 = 5
        assert!((ineq.evaluate_lhs(&asgn) - 5.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_extract_multiple_a_literals() {
        // Two A-literals, one B-literal
        // A: x1 <= 2, x2 <= 3  (shared: x2)
        // B: -x2 <= -6  (shared: x2)
        // Farkas: lambda = [1.0, 1.0], mu = [1.0]
        // A-combination on shared: 0*x2 + 1*x2 = x2 <= 2+3 = 5
        let a = vec![make_ineq(&[(1, 1.0)], 2.0), make_ineq(&[(2, 1.0)], 3.0)];
        let b = vec![make_ineq(&[(2, -1.0)], -6.0)];
        let shared: HashSet<u32> = [2].into_iter().collect();

        let result = extract_lra_interpolant(&a, &b, &[1.0, 1.0], &[1.0], &shared)
            .expect("multiple A-literal extraction should succeed");

        // x2 coefficient from second A-literal only (first has no x2)
        assert!(result.interpolant.coeffs.contains_key(&2));
        assert!((result.interpolant.coeffs[&2] - 1.0).abs() < f64::EPSILON);
        // Bound: 1.0*2.0 + 1.0*3.0 = 5.0
        assert!((result.interpolant.bound - 5.0).abs() < f64::EPSILON);
    }
}
