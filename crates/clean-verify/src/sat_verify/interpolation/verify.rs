// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unified Craig property verification for interpolants.
//!
//! This module provides a single entry point [`verify_craig_property`] that
//! checks all three defining properties of Craig interpolation:
//!
//! 1. **Implication**: A |= I (every satisfying assignment of A satisfies I)
//! 2. **Contradiction**: I AND B is unsatisfiable
//! 3. **Variable restriction**: Vars(I) is a subset of Vars(A) intersection Vars(B)
//!
//! The verification uses brute-force enumeration over all 2^n assignments and
//! is therefore only practical for small variable counts (n <= ~20).
//!
//! ## Usage
//!
//! ```text
//! let result = verify_craig_property(
//!     &a_clauses,
//!     &b_clauses,
//!     &interpolant,
//! )?;
//! assert!(result.all_valid);
//! ```
//!
//! ## Relationship to `property.rs`
//!
//! The [`super::property`] module provides individual verification functions.
//! This module wraps them into a single unified API with structured error
//! reporting, suitable for use from the extraction pipeline.

use super::property::{
    compute_shared_variables, verify_contradiction, verify_implication, verify_variable_restriction,
};
use super::PropFormula;
use crate::sat_verify::cdcl::var_of;
use std::collections::{BTreeSet, HashMap, HashSet};
use thiserror::Error;

/// Errors from Craig property verification.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum CraigVerifyError {
    /// The implication property A |= I is violated.
    #[error("implication violated: assignment satisfies A but not I")]
    ImplicationViolated {
        /// A satisfying assignment of A that falsifies I.
        counterexample: HashMap<u32, bool>,
    },

    /// The contradiction property (I AND B is unsat) is violated.
    #[error("contradiction violated: assignment satisfies both I and B")]
    ContradictionViolated {
        /// An assignment that satisfies both I and all B-clauses.
        witness: HashMap<u32, bool>,
    },

    /// The variable restriction Vars(I) is a subset of Vars(A) intersection Vars(B) is violated.
    #[error("variable restriction violated: interpolant uses non-shared variables {0:?}")]
    VariableRestrictionViolated(BTreeSet<u32>),

    /// Multiple properties are violated simultaneously.
    #[error("multiple Craig properties violated")]
    MultipleViolations {
        /// Detailed verification result.
        detail: CraigVerifyResult,
    },
}

/// Detailed result of verifying all three Craig interpolation properties.
#[derive(Debug, Clone)]
pub struct CraigVerifyResult {
    /// Whether A |= I holds.
    pub implication_holds: bool,
    /// Whether I AND B is unsatisfiable.
    pub contradiction_holds: bool,
    /// Whether Vars(I) is a subset of Vars(A) intersection Vars(B).
    pub variable_restriction_holds: bool,
    /// True when all three properties hold.
    pub all_valid: bool,
    /// Variables in I outside Vars(A) intersection Vars(B).
    pub violating_variables: BTreeSet<u32>,
    /// Counterexample to the implication property, if any.
    pub implication_counterexample: Option<HashMap<u32, bool>>,
    /// Witness to the contradiction violation, if any.
    pub contradiction_witness: Option<HashMap<u32, bool>>,
    /// Variables shared between A and B.
    pub shared_variables: HashSet<u32>,
    /// Number of propositional variables in the problem.
    pub num_vars: u32,
}

/// Verify the Craig interpolation property for a propositional interpolant.
///
/// Given formulas A and B (as sets of clauses in CNF) and an interpolant I
/// (as a [`PropFormula`]), checks:
///
/// 1. A |= I
/// 2. I AND B is unsatisfiable
/// 3. Vars(I) is a subset of Vars(A) intersection Vars(B)
///
/// Returns `Ok(result)` with a detailed [`CraigVerifyResult`] if all properties
/// hold, or `Err` with the first violation found.
///
/// # Arguments
///
/// * `a_clauses` - Clauses of formula A in CNF (each clause is a `Vec<i32>` of literals)
/// * `b_clauses` - Clauses of formula B in CNF
/// * `interpolant` - The candidate interpolant formula
///
/// # Errors
///
/// Returns [`CraigVerifyError`] if any of the three Craig properties is violated.
pub fn verify_craig_property(
    a_clauses: &[Vec<i32>],
    b_clauses: &[Vec<i32>],
    interpolant: &PropFormula,
) -> Result<CraigVerifyResult, CraigVerifyError> {
    let num_vars = compute_num_vars(a_clauses, b_clauses, interpolant);
    let shared = compute_shared_variables(a_clauses, b_clauses);

    // Check variable restriction first (cheapest check).
    let var_result = verify_variable_restriction(a_clauses, b_clauses, interpolant);
    let variable_restriction_holds = var_result.is_ok();
    let violating_variables = var_result.err().unwrap_or_default();

    // Check implication: A |= I.
    let impl_result = verify_implication(a_clauses, interpolant, num_vars);
    let implication_holds = impl_result.is_ok();
    let implication_counterexample = impl_result.err();

    // Check contradiction: I AND B is unsat.
    let contra_result = verify_contradiction(b_clauses, interpolant, num_vars);
    let contradiction_holds = contra_result.is_ok();
    let contradiction_witness = contra_result.err();

    let all_valid = implication_holds && contradiction_holds && variable_restriction_holds;

    let result = CraigVerifyResult {
        implication_holds,
        contradiction_holds,
        variable_restriction_holds,
        all_valid,
        violating_variables: violating_variables.clone(),
        implication_counterexample: implication_counterexample.clone(),
        contradiction_witness: contradiction_witness.clone(),
        shared_variables: shared,
        num_vars,
    };

    if all_valid {
        return Ok(result);
    }

    // Return the most specific single error, or MultipleViolations if >1.
    let violation_count = [
        !variable_restriction_holds,
        !implication_holds,
        !contradiction_holds,
    ]
    .iter()
    .filter(|&&v| v)
    .count();

    if violation_count > 1 {
        return Err(CraigVerifyError::MultipleViolations { detail: result });
    }

    if !variable_restriction_holds {
        return Err(CraigVerifyError::VariableRestrictionViolated(
            violating_variables,
        ));
    }

    if !implication_holds {
        return Err(CraigVerifyError::ImplicationViolated {
            counterexample: implication_counterexample.expect("invariant: checked above"),
        });
    }

    Err(CraigVerifyError::ContradictionViolated {
        witness: contradiction_witness.expect("invariant: checked above"),
    })
}

/// Compute the number of propositional variables across A, B, and I.
fn compute_num_vars(
    a_clauses: &[Vec<i32>],
    b_clauses: &[Vec<i32>],
    interpolant: &PropFormula,
) -> u32 {
    let mut max_var: u32 = 0;
    for clause in a_clauses.iter().chain(b_clauses.iter()) {
        for &lit in clause {
            let v = var_of(lit);
            if v > max_var {
                max_var = v;
            }
        }
    }
    for &v in &interpolant.variables() {
        if v > max_var {
            max_var = v;
        }
    }
    max_var
}

/// Quick check: does the interpolant use only shared variables?
///
/// This is a fast pre-check that does not require enumerating assignments.
#[must_use]
pub fn quick_check_variable_restriction(
    a_clauses: &[Vec<i32>],
    b_clauses: &[Vec<i32>],
    interpolant: &PropFormula,
) -> bool {
    verify_variable_restriction(a_clauses, b_clauses, interpolant).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verify_craig_valid_interpolant() {
        // A = {x1}, B = {!x1}
        // Interpolant: x1 (shared variable)
        // A |= x1 (trivially, since A asserts x1)
        // x1 AND !x1 is unsat
        // Vars(x1) = {1} = Vars(A) intersection Vars(B)
        let a = vec![vec![1]];
        let b = vec![vec![-1]];
        let interp = PropFormula::Var(1);

        let result = verify_craig_property(&a, &b, &interp).expect("valid interpolant should pass");
        assert!(result.all_valid);
        assert!(result.shared_variables.contains(&1));
        assert_eq!(result.num_vars, 1);
    }

    #[test]
    fn test_verify_craig_true_interpolant() {
        // A = {x1}, B = {!x1}
        // Interpolant: True
        // A |= True (trivially)
        // True AND !x1 is SAT -> contradiction fails
        let a = vec![vec![1]];
        let b = vec![vec![-1]];
        let interp = PropFormula::True;

        let err = verify_craig_property(&a, &b, &interp)
            .expect_err("True interpolant should fail contradiction");
        assert!(matches!(
            err,
            CraigVerifyError::ContradictionViolated { .. }
        ));
    }

    #[test]
    fn test_verify_craig_false_interpolant() {
        // A = {x1}, B = {!x1}
        // Interpolant: False
        // A |= False fails (A is satisfiable)
        let a = vec![vec![1]];
        let b = vec![vec![-1]];
        let interp = PropFormula::False;

        let err = verify_craig_property(&a, &b, &interp)
            .expect_err("False interpolant should fail implication");
        assert!(matches!(err, CraigVerifyError::ImplicationViolated { .. }));
    }

    #[test]
    fn test_verify_craig_variable_restriction_violated() {
        // A = {x1, x2}, B = {!x2, x3}
        // Shared: {x2}
        // Interpolant uses x1 (A-local) -> violation
        let a = vec![vec![1, 2]];
        let b = vec![vec![-2, 3]];
        let interp =
            PropFormula::AndType(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));

        let err = verify_craig_property(&a, &b, &interp)
            .expect_err("non-shared variable in interpolant should fail");
        // This might be a MultipleViolations since implication may also fail
        match err {
            CraigVerifyError::VariableRestrictionViolated(vars) => {
                assert!(vars.contains(&1));
            }
            CraigVerifyError::MultipleViolations { detail } => {
                assert!(!detail.variable_restriction_holds);
                assert!(detail.violating_variables.contains(&1));
            }
            other => panic!("unexpected error variant: {other:?}"),
        }
    }

    #[test]
    fn test_verify_craig_multi_clause() {
        // A = {x1, x2}, {x1, !x2}  (equivalent to x1)
        // B = {!x1, x3}, {!x1, !x3}  (equivalent to !x1)
        // Interpolant: x1 (shared)
        let a = vec![vec![1, 2], vec![1, -2]];
        let b = vec![vec![-1, 3], vec![-1, -3]];
        let interp = PropFormula::Var(1);

        let result = verify_craig_property(&a, &b, &interp).expect("valid interpolant should pass");
        assert!(result.all_valid);
    }

    #[test]
    fn test_verify_craig_negated_variable() {
        // A = {!x1}, B = {x1}
        // Interpolant: !x1
        let a = vec![vec![-1]];
        let b = vec![vec![1]];
        let interp = PropFormula::Not(Box::new(PropFormula::Var(1)));

        let result =
            verify_craig_property(&a, &b, &interp).expect("negated interpolant should pass");
        assert!(result.all_valid);
    }

    #[test]
    fn test_quick_check_variable_restriction() {
        let a = vec![vec![1, 2]];
        let b = vec![vec![-2, 3]];

        // x2 is shared -- should pass
        assert!(quick_check_variable_restriction(
            &a,
            &b,
            &PropFormula::Var(2)
        ));

        // x1 is A-local -- should fail
        assert!(!quick_check_variable_restriction(
            &a,
            &b,
            &PropFormula::Var(1)
        ));
    }

    #[test]
    fn test_compute_num_vars() {
        let a = vec![vec![1, -3]];
        let b = vec![vec![2, 5]];
        let interp = PropFormula::Var(4);
        assert_eq!(compute_num_vars(&a, &b, &interp), 5);
    }

    #[test]
    fn test_verify_craig_property_result_diagnostics() {
        // Create a case where implication fails
        let a = vec![vec![1]];
        let b = vec![vec![-1]];
        // Interpolant: False -- fails implication
        let interp = PropFormula::False;

        let err = verify_craig_property(&a, &b, &interp).expect_err("should fail");
        match err {
            CraigVerifyError::ImplicationViolated { counterexample } => {
                // The counterexample should have x1=true (satisfies A but not False)
                assert_eq!(counterexample.get(&1), Some(&true));
            }
            other => panic!("expected ImplicationViolated, got: {other:?}"),
        }
    }

    #[test]
    fn test_verify_craig_or_interpolant() {
        // A = {x1, x2}, {!x1, x2}  (implies x2)
        // B = {!x2}
        // Shared: {x2}
        // Interpolant: x2
        let a = vec![vec![1, 2], vec![-1, 2]];
        let b = vec![vec![-2]];
        let interp = PropFormula::Var(2);

        let result =
            verify_craig_property(&a, &b, &interp).expect("x2 should be a valid interpolant");
        assert!(result.all_valid);
        assert!(result.shared_variables.contains(&2));
    }
}
