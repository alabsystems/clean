// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! CNF-to-PB bridge: convert between CNF clause sets and PB formulas.
//!
//! Every CNF clause `(l_1 OR l_2 OR ... OR l_k)` is equivalent to the
//! PB constraint `1*l_1 + 1*l_2 + ... + 1*l_k >= 1`. This module
//! provides bidirectional conversion:
//!
//! - **cnf_to_pb**: Convert DIMACS-style CNF clauses into a PB formula.
//! - **pb_to_cnf**: Convert back if all constraints are cardinality-1 (clauses).
//!
//! This bridge enables PB proof techniques (cutting planes, saturation) to
//! be applied to SAT instances, and allows clause-only PB formulas to be
//! exported to standard DIMACS format for SAT solvers.

// 2026-07-31: the `pub(crate)` items in this module are exercised only by its
// own `#[cfg(test)]` tests, so only the non-test `lib` build sees them as dead.
// Scoped to `not(test)` on purpose: the `lib test` build still enforces
// `dead_code` in full, so an item with no caller anywhere still fails the gate.
#![cfg_attr(not(test), allow(dead_code))]

use super::types::{PbConstraint, PbFormula};

/// Convert a CNF formula (list of clauses) to a PB formula.
///
/// Each clause is a `Vec<i32>` of literals in DIMACS convention:
/// positive integer = positive literal, negative = negation.
/// Variable indices are 1-based.
///
/// Each clause `[l_1, l_2, ..., l_k]` becomes the PB constraint
/// `1*l_1 + 1*l_2 + ... + 1*l_k >= 1`.
#[must_use]
pub(crate) fn cnf_to_pb(clauses: &[Vec<i32>]) -> PbFormula {
    // Determine the number of variables from the maximum literal index.
    let num_vars = clauses
        .iter()
        .flat_map(|clause| clause.iter())
        .map(|lit| lit.unsigned_abs())
        .max()
        .unwrap_or(0);

    let mut formula = PbFormula::new(num_vars);

    for clause in clauses {
        formula.add_constraint(PbConstraint::from_clause(clause));
    }

    formula
}

/// Convert a PB formula back to CNF if all constraints are clauses.
///
/// A constraint is convertible if it has degree 1 and all coefficients are 1.
/// Returns `None` if any constraint cannot be expressed as a clause.
#[must_use]
pub(crate) fn pb_to_cnf(formula: &PbFormula) -> Option<Vec<Vec<i32>>> {
    let mut clauses = Vec::with_capacity(formula.constraints.len());

    for constraint in &formula.constraints {
        let clause = constraint.to_clause()?;
        clauses.push(clause);
    }

    Some(clauses)
}

/// Convert a single CNF clause to a PB constraint.
///
/// Convenience wrapper around `PbConstraint::from_clause`.
#[must_use]
pub(crate) fn clause_to_pb(clause: &[i32]) -> PbConstraint {
    PbConstraint::from_clause(clause)
}

/// Check if a PB formula is representable as CNF.
///
/// Returns true if every constraint has degree 1 and all coefficients are 1.
#[must_use]
pub(crate) fn is_cnf_representable(formula: &PbFormula) -> bool {
    formula.constraints.iter().all(PbConstraint::is_clause)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cnf_to_pb_basic() {
        let clauses = vec![vec![1, 2, 3], vec![-1, 2], vec![1, -3]];

        let formula = cnf_to_pb(&clauses);
        assert_eq!(formula.num_vars, 3);
        assert_eq!(formula.constraints.len(), 3);

        // Each constraint should be a clause (degree 1, all coefficients 1).
        for constraint in &formula.constraints {
            assert!(constraint.is_clause());
        }
    }

    #[test]
    fn test_cnf_to_pb_preserves_literals() {
        let clauses = vec![vec![1, -2, 3]];
        let formula = cnf_to_pb(&clauses);

        assert_eq!(formula.constraints[0].terms, vec![(1, 1), (1, -2), (1, 3)]);
        assert_eq!(formula.constraints[0].degree, 1);
    }

    #[test]
    fn test_pb_to_cnf_clause_formula() {
        let mut formula = PbFormula::new(3);
        formula.add_constraint(PbConstraint::from_clause(&[1, 2]));
        formula.add_constraint(PbConstraint::from_clause(&[-1, 3]));

        let clauses = pb_to_cnf(&formula).expect("should convert to CNF");
        assert_eq!(clauses, vec![vec![1, 2], vec![-1, 3]]);
    }

    #[test]
    fn test_pb_to_cnf_non_clause_returns_none() {
        let mut formula = PbFormula::new(2);
        formula.add_constraint(PbConstraint::from_clause(&[1, 2]));
        formula.add_constraint(PbConstraint::new(vec![(2, 1), (3, 2)], 4)); // NOT a clause

        assert!(pb_to_cnf(&formula).is_none());
    }

    #[test]
    fn test_cnf_pb_roundtrip() {
        let original = vec![vec![1, 2, -3], vec![-1, 2], vec![3], vec![-2, -3]];

        let formula = cnf_to_pb(&original);
        let recovered = pb_to_cnf(&formula).expect("roundtrip should succeed");

        assert_eq!(recovered, original);
    }

    #[test]
    fn test_cnf_to_pb_empty() {
        let formula = cnf_to_pb(&[]);
        assert_eq!(formula.num_vars, 0);
        assert_eq!(formula.constraints.len(), 0);
    }

    #[test]
    fn test_cnf_to_pb_unit_clauses() {
        let clauses = vec![vec![1], vec![-2]];
        let formula = cnf_to_pb(&clauses);

        assert_eq!(formula.num_vars, 2);
        assert_eq!(formula.constraints.len(), 2);
        assert!(formula.constraints[0].is_clause());
        assert!(formula.constraints[1].is_clause());
    }

    #[test]
    fn test_clause_to_pb_convenience() {
        let pb = clause_to_pb(&[1, -2, 3]);
        assert!(pb.is_clause());
        assert_eq!(pb.terms.len(), 3);
        assert_eq!(pb.degree, 1);
    }

    #[test]
    fn test_is_cnf_representable_true() {
        let mut formula = PbFormula::new(2);
        formula.add_constraint(PbConstraint::from_clause(&[1, 2]));
        formula.add_constraint(PbConstraint::from_clause(&[-1]));

        assert!(is_cnf_representable(&formula));
    }

    #[test]
    fn test_is_cnf_representable_false() {
        let mut formula = PbFormula::new(2);
        formula.add_constraint(PbConstraint::from_clause(&[1, 2]));
        formula.add_constraint(PbConstraint::new(vec![(1, 1), (1, 2)], 2)); // cardinality

        assert!(!is_cnf_representable(&formula));
    }

    #[test]
    fn test_cnf_to_pb_num_vars_from_max_literal() {
        // Variables 5 and 10 referenced but not 1-4 or 6-9.
        let clauses = vec![vec![5, -10]];
        let formula = cnf_to_pb(&clauses);
        assert_eq!(formula.num_vars, 10);
    }

    #[test]
    fn test_pb_to_cnf_empty_formula() {
        let formula = PbFormula::new(0);
        let clauses = pb_to_cnf(&formula).expect("empty formula should convert");
        assert!(clauses.is_empty());
    }

    #[test]
    fn test_cnf_pb_cnf_roundtrip_preserves_structure() {
        // A more complex roundtrip test.
        let clauses = vec![
            vec![1, 2, 3, 4],
            vec![-1, -2],
            vec![3, -4],
            vec![1],
            vec![-3, 4, 2],
        ];

        let formula = cnf_to_pb(&clauses);
        assert!(is_cnf_representable(&formula));

        let recovered = pb_to_cnf(&formula).expect("roundtrip should succeed");
        assert_eq!(recovered, clauses);
    }
}
