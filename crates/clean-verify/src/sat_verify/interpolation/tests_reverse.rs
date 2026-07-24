// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Pudlak (reverse) interpolation.

#[cfg(test)]
mod tests {
    use crate::sat_verify::interpolation::mcmillan::{
        extract_mcmillan_interpolant, verify_shared_variable_property, Partition, ResolutionDag,
    };
    use crate::sat_verify::interpolation::reverse::{
        compare_interpolant_size, formula_size, pudlak_interpolation, ReverseInterpolationError,
        I04_PUDLAK_IMPL,
    };
    use crate::sat_verify::interpolation::PropFormula;
    use crate::spec::ProofStatus;
    use std::collections::{HashMap, HashSet};

    // ---- Helper builders ----

    fn var(v: u32) -> PropFormula {
        PropFormula::Var(v)
    }

    fn not(f: PropFormula) -> PropFormula {
        PropFormula::Not(Box::new(f))
    }

    fn and(l: PropFormula, r: PropFormula) -> PropFormula {
        PropFormula::AndType(Box::new(l), Box::new(r))
    }

    fn or(l: PropFormula, r: PropFormula) -> PropFormula {
        PropFormula::Or(Box::new(l), Box::new(r))
    }

    // ---- Basic Pudlak tests ----

    #[test]
    fn test_pudlak_simple_shared_pivot() {
        // A = {(1)}, B = {(-1)}. Shared pivot: var 1.
        let mut dag = ResolutionDag::new();
        let a = dag.add_input(vec![1], Partition::A);
        let b = dag.add_input(vec![-1], Partition::B);
        dag.add_resolve(a, b, 1);

        let shared: HashSet<u32> = [1].into_iter().collect();
        let interp = pudlak_interpolation(&dag, &Partition::A, &shared).expect("should succeed");

        // Interpolant should only use shared variables
        let interp_vars = interp.variables();
        assert!(interp_vars.is_subset(&shared), "vars: {interp_vars:?}");

        // A implies I: when var 1 = true, I should be true
        let mut asgn = HashMap::new();
        asgn.insert(1, true);
        assert!(interp.evaluate(&asgn), "A-sat should satisfy I: {interp}");

        // I AND B unsat: when var 1 = false, I should be false
        asgn.insert(1, false);
        assert!(!interp.evaluate(&asgn), "B-sat should falsify I: {interp}");
    }

    #[test]
    fn test_pudlak_three_clause_proof() {
        // A = {(1, 2)}, B = {(-1, 3), (-2, -3)}
        // Resolution: (1,2) resolve with (-1,3) on var 1 => (2,3)
        //             (2,3) resolve with (-2,-3) on var 2 => (3)
        //             ... but var 3 is B-only, so we need a further step.
        // Actually let's use: A = {(1,2)}, B = {(-1), (-2)}
        let mut dag = ResolutionDag::new();
        let n0 = dag.add_input(vec![1, 2], Partition::A);
        let n1 = dag.add_input(vec![-1], Partition::B);
        let n2 = dag.add_input(vec![-2], Partition::B);
        let n3 = dag.add_resolve(n0, n1, 1);
        dag.add_resolve(n3, n2, 2);

        let shared: HashSet<u32> = [1, 2].into_iter().collect();
        let interp = pudlak_interpolation(&dag, &Partition::A, &shared).expect("should succeed");

        verify_shared_variable_property(&dag, &interp).expect("shared variable property");
    }

    #[test]
    fn test_pudlak_empty_dag() {
        let dag = ResolutionDag::new();
        let shared: HashSet<u32> = HashSet::new();
        let result = pudlak_interpolation(&dag, &Partition::A, &shared);
        assert_eq!(result.unwrap_err(), ReverseInterpolationError::EmptyDag);
    }

    #[test]
    fn test_pudlak_a_only_pivot() {
        // A = {(1, 2), (-1, 2)}, B = {(-2)}
        // Var 1 is A-only, var 2 is shared.
        // Resolution on A-only pivot => disjunction of child interpolants.
        let mut dag = ResolutionDag::new();
        let n0 = dag.add_input(vec![1, 2], Partition::A);
        let n1 = dag.add_input(vec![-1, 2], Partition::A);
        let n2 = dag.add_input(vec![-2], Partition::B);
        let n3 = dag.add_resolve(n0, n1, 1); // A-only pivot
        dag.add_resolve(n3, n2, 2);

        let shared: HashSet<u32> = [2].into_iter().collect();
        let interp = pudlak_interpolation(&dag, &Partition::A, &shared).expect("should succeed");

        // Interpolant should not mention A-only var 1
        assert!(!interp.variables().contains(&1));
    }

    #[test]
    fn test_pudlak_b_only_pivot() {
        // A = {(1)}, B = {(-1, 2), (-1, -2)}
        // Var 1 is shared, var 2 is B-only.
        // Resolution on B-only pivot => conjunction of child interpolants.
        let mut dag = ResolutionDag::new();
        let n0 = dag.add_input(vec![1], Partition::A);
        let n1 = dag.add_input(vec![-1, 2], Partition::B);
        let n2 = dag.add_input(vec![-1, -2], Partition::B);
        let n3 = dag.add_resolve(n1, n2, 2); // B-only pivot
        dag.add_resolve(n0, n3, 1);

        let shared: HashSet<u32> = [1].into_iter().collect();
        let interp = pudlak_interpolation(&dag, &Partition::A, &shared).expect("should succeed");

        // Interpolant should not mention B-only var 2
        assert!(!interp.variables().contains(&2));
    }

    #[test]
    fn test_pudlak_b_leaf_negates_shared() {
        // B = {(-1, 2)} with vars 1,2 shared.
        // Pudlak B-leaf: conjunction of negated shared literals => (1 AND NOT 2)
        // (negation of -1 is 1, negation of 2 is NOT 2)
        let mut dag = ResolutionDag::new();
        dag.add_input(vec![-1, 2], Partition::B);

        let shared: HashSet<u32> = [1, 2].into_iter().collect();
        let interp = pudlak_interpolation(&dag, &Partition::A, &shared).expect("should succeed");

        // Under assignment {1: true, 2: false}, B-leaf has -1=false, 2=false => clause false
        // The interpolant (negated shared) should be: 1 AND NOT 2
        let mut asgn = HashMap::new();
        asgn.insert(1, true);
        asgn.insert(2, false);
        assert!(
            interp.evaluate(&asgn),
            "B-leaf interpolant should be true when B-clause is false: {interp}"
        );
    }

    // ---- McMillan vs Pudlak comparison ----

    #[test]
    fn test_compare_mcmillan_vs_pudlak_same_dag() {
        let mut dag = ResolutionDag::new();
        let n0 = dag.add_input(vec![1, 2], Partition::A);
        let n1 = dag.add_input(vec![-1], Partition::B);
        let n2 = dag.add_input(vec![-2], Partition::B);
        let n3 = dag.add_resolve(n0, n1, 1);
        dag.add_resolve(n3, n2, 2);

        let mcmillan = extract_mcmillan_interpolant(&dag);
        let shared: HashSet<u32> = [1, 2].into_iter().collect();
        let pudlak = pudlak_interpolation(&dag, &Partition::A, &shared).expect("should succeed");

        // Both should satisfy shared variable property
        verify_shared_variable_property(&dag, &mcmillan).expect("McMillan shared vars");
        verify_shared_variable_property(&dag, &pudlak).expect("Pudlak shared vars");

        // Both should satisfy Craig properties on all assignments
        for x1 in [false, true] {
            for x2 in [false, true] {
                let mut asgn = HashMap::new();
                asgn.insert(1, x1);
                asgn.insert(2, x2);

                // A = {(1, 2)}: satisfied when x1=true OR x2=true
                let a_sat = x1 || x2;
                if a_sat {
                    assert!(
                        mcmillan.evaluate(&asgn),
                        "McMillan: A-sat should imply I for x1={x1}, x2={x2}"
                    );
                    assert!(
                        pudlak.evaluate(&asgn),
                        "Pudlak: A-sat should imply I for x1={x1}, x2={x2}"
                    );
                }
            }
        }
    }

    #[test]
    fn test_compare_interpolant_sizes() {
        let (m_size, p_size) = compare_interpolant_size(&var(1), &and(var(1), var(2)));
        assert_eq!(m_size, 0); // single variable
        assert_eq!(p_size, 1); // one AndType connective
    }

    // ---- formula_size tests ----

    #[test]
    fn test_formula_size_variable() {
        assert_eq!(formula_size(&var(1)), 0);
    }

    #[test]
    fn test_formula_size_constants() {
        assert_eq!(formula_size(&PropFormula::True), 0);
        assert_eq!(formula_size(&PropFormula::False), 0);
    }

    #[test]
    fn test_formula_size_not() {
        assert_eq!(formula_size(&not(var(1))), 1);
    }

    #[test]
    fn test_formula_size_binary() {
        assert_eq!(formula_size(&and(var(1), var(2))), 1);
        assert_eq!(formula_size(&or(var(1), var(2))), 1);
    }

    #[test]
    fn test_formula_size_nested() {
        // (x1 AND (NOT x2 OR x3)) => 1 (AndType) + 1 (Or) + 1 (Not) = 3
        let f = and(var(1), or(not(var(2)), var(3)));
        assert_eq!(formula_size(&f), 3);
    }

    #[test]
    fn test_formula_size_implies() {
        let f = PropFormula::Implies(Box::new(var(1)), Box::new(var(2)));
        assert_eq!(formula_size(&f), 1);
    }

    // ---- Pudlak simplification ----

    #[test]
    fn test_pudlak_output_simplifies() {
        // Single A-input with no shared vars => interpolant simplifies to False
        let mut dag = ResolutionDag::new();
        dag.add_input(vec![1], Partition::A);

        let shared: HashSet<u32> = HashSet::new();
        let interp = pudlak_interpolation(&dag, &Partition::A, &shared).expect("should succeed");

        // No shared vars in an A-only clause => disjunction of nothing => False
        assert_eq!(interp, PropFormula::False);
    }

    #[test]
    fn test_pudlak_b_only_no_shared_simplifies_to_true() {
        // Single B-input with no shared vars => interpolant simplifies to True
        let mut dag = ResolutionDag::new();
        dag.add_input(vec![1], Partition::B);

        let shared: HashSet<u32> = HashSet::new();
        let interp = pudlak_interpolation(&dag, &Partition::A, &shared).expect("should succeed");

        assert_eq!(interp, PropFormula::True);
    }

    // ---- Proof constant test ----

    #[test]
    fn test_pudlak_proof_constant() {
        assert_eq!(I04_PUDLAK_IMPL, ProofStatus::DerivedPending);
    }
}
