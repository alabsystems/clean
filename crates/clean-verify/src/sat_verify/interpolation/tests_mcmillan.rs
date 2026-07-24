// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended tests for McMillan interpolation.

#[cfg(test)]
mod tests {
    use crate::sat_verify::interpolation::mcmillan::{
        extract_mcmillan_interpolant, verify_shared_variable_property, Partition, ResolutionDag,
    };
    use crate::sat_verify::interpolation::PropFormula;
    use std::collections::{HashMap, HashSet};

    #[test]
    fn test_craig_property_simple_refutation() {
        // A = {(1, 2)}, B = {(-1), (-2)} with shared vars {1, 2}.
        let mut dag = ResolutionDag::new();
        let n0 = dag.add_input(vec![1, 2], Partition::A);
        let n1 = dag.add_input(vec![-1], Partition::B);
        let n2 = dag.add_input(vec![-2], Partition::B);
        let n3 = dag.add_resolve(n0, n1, 1);
        let _n4 = dag.add_resolve(n3, n2, 2);
        let interp = extract_mcmillan_interpolant(&dag);

        verify_shared_variable_property(&dag, &interp).expect("shared variable property");

        let interp_vars = interp.variables();
        assert!(interp_vars.is_subset(&HashSet::from([1, 2])));
    }

    #[test]
    fn test_craig_a_implies_interpolant() {
        // A = {(1)}, B = {(-1)}.
        let mut dag = ResolutionDag::new();
        let a = dag.add_input(vec![1], Partition::A);
        let b = dag.add_input(vec![-1], Partition::B);
        dag.add_resolve(a, b, 1);
        let interp = extract_mcmillan_interpolant(&dag);

        let mut asgn = HashMap::new();
        asgn.insert(1, true);
        assert!(
            interp.evaluate(&asgn),
            "A satisfying assignment should satisfy interpolant: {interp}"
        );
    }

    #[test]
    fn test_craig_i_and_b_unsat() {
        // A = {(1)}, B = {(-1)}.
        let mut dag = ResolutionDag::new();
        let a = dag.add_input(vec![1], Partition::A);
        let b = dag.add_input(vec![-1], Partition::B);
        dag.add_resolve(a, b, 1);
        let interp = extract_mcmillan_interpolant(&dag);

        let mut asgn = HashMap::new();
        asgn.insert(1, false);
        assert!(
            !interp.evaluate(&asgn),
            "B satisfying assignment should falsify interpolant: {interp}"
        );
    }

    #[test]
    fn test_interpolant_with_a_only_pivot() {
        // A = {(1, 2), (-1, 2)}, B = {(-2)}.
        // Var 1 is A-only, var 2 is shared.
        let mut dag = ResolutionDag::new();
        let n0 = dag.add_input(vec![1, 2], Partition::A);
        let n1 = dag.add_input(vec![-1, 2], Partition::A);
        let n2 = dag.add_input(vec![-2], Partition::B);
        let n3 = dag.add_resolve(n0, n1, 1);
        let _n4 = dag.add_resolve(n3, n2, 2);
        let interp = extract_mcmillan_interpolant(&dag);

        verify_shared_variable_property(&dag, &interp).expect("shared variable property");
        assert!(!interp.variables().contains(&1));
    }

    #[test]
    fn test_interpolant_with_b_only_pivot() {
        // A = {(1)}, B = {(-1, 2), (-1, -2)}.
        // Var 1 is shared, var 2 is B-only.
        let mut dag = ResolutionDag::new();
        let n0 = dag.add_input(vec![1], Partition::A);
        let n1 = dag.add_input(vec![-1, 2], Partition::B);
        let n2 = dag.add_input(vec![-1, -2], Partition::B);
        let n3 = dag.add_resolve(n1, n2, 2);
        let _n4 = dag.add_resolve(n0, n3, 1);
        let interp = extract_mcmillan_interpolant(&dag);

        verify_shared_variable_property(&dag, &interp).expect("shared variable property");
        assert!(!interp.variables().contains(&2));
    }

    #[test]
    fn test_empty_dag_interpolant() {
        let dag = ResolutionDag::new();
        let interp = extract_mcmillan_interpolant(&dag);
        assert_eq!(interp, PropFormula::True);
    }

    #[test]
    fn test_shared_variable_violation_detected() {
        let mut dag = ResolutionDag::new();
        dag.add_input(vec![1], Partition::A);
        dag.add_input(vec![2], Partition::B);

        let bad_interp = PropFormula::Var(1);
        let result = verify_shared_variable_property(&dag, &bad_interp);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains(&1));
    }
}
