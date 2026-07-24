// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended tests (part 2): CP derivation verification, PHP CP proof
//! construction, and Haken lower-bound witnesses.

#[cfg(test)]
mod tests {
    use crate::sat_verify::proof_complexity::cutting_planes::CpInequality;
    use crate::sat_verify::proof_complexity::separations::haken_lower_bound_witness;
    use crate::sat_verify::proof_complexity::separations_cp::{
        cp_proof_of_php, php_cp_axioms, verify_cp_derivation, SepCpStep,
    };

    // -----------------------------------------------------------------------
    // 15-18: CP derivation verification
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_cp_simple_contradiction() {
        // x >= 1 and -x >= 0 => add => 0 >= 1
        let axioms = vec![
            CpInequality::new(vec![1], 1),  // x >= 1
            CpInequality::new(vec![-1], 0), // -x >= 0
        ];
        let steps = vec![SepCpStep::Addition(0, 1)];
        assert!(verify_cp_derivation(&axioms, &steps));
    }

    #[test]
    fn test_verify_cp_multiplication_and_addition() {
        // x >= 1, multiply by 2 => 2x >= 2, add -2x >= 0 => 0 >= 2
        let axioms = vec![
            CpInequality::new(vec![1], 1),  // x >= 1
            CpInequality::new(vec![-2], 0), // -2x >= 0
        ];
        let steps = vec![
            SepCpStep::Multiplication(0, 2), // 2x >= 2 (index 2)
            SepCpStep::Addition(2, 1),       // 0 >= 2 (index 3)
        ];
        assert!(verify_cp_derivation(&axioms, &steps));
    }

    #[test]
    fn test_verify_cp_division() {
        // 2x >= 3 => divide by 2 => x >= 2 (ceil(3/2)=2)
        // -x >= 0 => add => 0 >= 2
        let axioms = vec![
            CpInequality::new(vec![2], 3),
            CpInequality::new(vec![-1], 0),
        ];
        let steps = vec![
            SepCpStep::Division(0, 2), // x >= 2
            SepCpStep::Addition(2, 1), // 0 >= 2
        ];
        assert!(verify_cp_derivation(&axioms, &steps));
    }

    #[test]
    fn test_verify_cp_invalid_scalar() {
        let axioms = vec![CpInequality::new(vec![1], 1)];
        let steps = vec![SepCpStep::Multiplication(0, 0)]; // scalar must be positive
        assert!(!verify_cp_derivation(&axioms, &steps));
    }

    // -----------------------------------------------------------------------
    // 19-22: PHP CP proof construction and verification
    // -----------------------------------------------------------------------

    #[test]
    fn test_cp_proof_php_n0() {
        // PHP(1,0): pigeon must go somewhere, no holes.
        let steps = cp_proof_of_php(0);
        assert!(steps.is_empty()); // Input alone is 0 >= 1.
        let axioms = php_cp_axioms(0);
        assert!(verify_cp_derivation(&axioms, &steps));
    }

    #[test]
    fn test_cp_proof_php_n1() {
        // PHP(2,1): 2 pigeons, 1 hole.
        let axioms = php_cp_axioms(1);
        let steps = cp_proof_of_php(1);
        assert!(verify_cp_derivation(&axioms, &steps));
    }

    #[test]
    fn test_cp_proof_php_n2() {
        // PHP(3,2): 3 pigeons, 2 holes.
        let axioms = php_cp_axioms(2);
        let steps = cp_proof_of_php(2);
        assert!(
            verify_cp_derivation(&axioms, &steps),
            "CP proof of PHP(3,2) should verify"
        );
    }

    #[test]
    fn test_cp_proof_php_n3() {
        // PHP(4,3): 4 pigeons, 3 holes.
        let axioms = php_cp_axioms(3);
        let steps = cp_proof_of_php(3);
        assert!(
            verify_cp_derivation(&axioms, &steps),
            "CP proof of PHP(4,3) should verify"
        );
    }

    // -----------------------------------------------------------------------
    // 23: PHP CP proof is polynomial size
    // -----------------------------------------------------------------------

    #[test]
    fn test_cp_proof_php_polynomial_size() {
        for n in 1..=5 {
            let steps = cp_proof_of_php(n);
            // Proof has exactly (pigeons-1) + n = n + n = 2n steps.
            assert_eq!(
                steps.len(),
                2 * n,
                "PHP({},{}) should have 2n steps",
                n + 1,
                n
            );
        }
    }

    // -----------------------------------------------------------------------
    // 24-27: Haken lower bound witness
    // -----------------------------------------------------------------------

    #[test]
    fn test_haken_witness_n2() {
        let w = haken_lower_bound_witness(2);
        assert_eq!(w.n, 2);
        // 2^{2/20} = 2^0.1 ~ 1.07 => truncates to 1
        assert_eq!(w.tree_size_lower_bound, 1);
        assert!(w.description.contains("Haken"));
        assert!(w.description.contains("PHP(3,2)"));
    }

    #[test]
    fn test_haken_witness_n20() {
        let w = haken_lower_bound_witness(20);
        // 2^{20/20} = 2
        assert_eq!(w.tree_size_lower_bound, 2);
        assert!(w.description.contains("PHP(21,20)"));
    }

    #[test]
    fn test_haken_witness_n100() {
        let w = haken_lower_bound_witness(100);
        // 2^{100/20} = 2^5 = 32
        assert_eq!(w.tree_size_lower_bound, 32);
    }

    #[test]
    fn test_haken_witness_large_n() {
        let w = haken_lower_bound_witness(2000);
        // 2^{2000/20} = 2^100 ~ 1.27e30, which fits in u64 (max ~1.84e19)
        // Actually 2^100 > u64::MAX, so should be u64::MAX.
        assert_eq!(w.tree_size_lower_bound, u64::MAX);
    }

    // -----------------------------------------------------------------------
    // 28: CP weakening step
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_cp_weakening() {
        // x + y >= 2, weaken y => x + 0 >= 2 (i.e. x >= 2), then
        // -x >= 0 => add => 0 >= 2
        let axioms = vec![
            CpInequality::new(vec![1, 1], 2),
            CpInequality::new(vec![-1, 0], 0),
        ];
        let steps = vec![
            SepCpStep::Weakening(0, 1), // drop var 1 => [1, 0] >= 2
            SepCpStep::Addition(2, 1),  // [0, 0] >= 2
        ];
        assert!(verify_cp_derivation(&axioms, &steps));
    }

    // -----------------------------------------------------------------------
    // 29: CP boolean axiom step
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_cp_boolean_axiom() {
        // Use boolean axiom x_0 >= 0, then multiply by -1 is invalid (scalar must be positive).
        // Instead: -x >= 1 (impossible for x in {0,1}), add boolean axiom x >= 0 => 0 >= 1.
        let axioms = vec![
            CpInequality::new(vec![-1], 1), // -x >= 1
        ];
        let steps = vec![
            SepCpStep::BooleanAxiom(0), // x >= 0 (index 1)
            SepCpStep::Addition(0, 1),  // 0 >= 1
        ];
        assert!(verify_cp_derivation(&axioms, &steps));
    }

    // -----------------------------------------------------------------------
    // 30: CP invalid index returns false
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_cp_invalid_index() {
        let axioms = vec![CpInequality::new(vec![1], 1)];
        let steps = vec![SepCpStep::Addition(0, 5)]; // index 5 does not exist
        assert!(!verify_cp_derivation(&axioms, &steps));
    }
}
