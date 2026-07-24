// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for proof complexity: constructing actual refutations.

#[cfg(test)]
mod tests {
    use crate::sat_verify::proof_complexity::cutting_planes::{CpInequality, CuttingPlanesProof};
    use crate::sat_verify::proof_complexity::encodings::{encode_php, encode_php_cp};
    use crate::sat_verify::proof_complexity::resolution::{resolve_clauses, ResolutionProof};

    // ---------- Resolution ----------

    #[test]
    fn test_resolution_refutation_php_1_0() {
        // PHP(1,0): 1 pigeon, 0 holes.
        // Only clause: pigeon 1 must go somewhere -> empty clause.
        // Actually with 0 holes the pigeon clause is empty.
        let (_, clauses) = encode_php(0);
        let mut proof = ResolutionProof::new();
        for c in clauses {
            proof.add_input(c);
        }
        // PHP(1,0) generates a single empty pigeon clause -> proof verifies.
        assert!(proof.verify());
    }

    #[test]
    fn test_resolution_three_clause_chain() {
        // (a v b) AND (-a v c) AND (-b v -c) => resolve on a => (b v c) => ...
        let mut proof = ResolutionProof::new();
        let s0 = proof.add_input(vec![1, 2]); // a v b
        let s1 = proof.add_input(vec![-1, 3]); // -a v c
        let s2 = proof.add_input(vec![-2, -3]); // -b v -c
                                                // Resolve s0 and s1 on a => (b v c)
        let s3 = proof.add_resolve(s0, s1, 1).expect("resolve");
        // Resolve s3 (b v c) and s2 (-b v -c) on b => (c v -c)
        let s4 = proof.add_resolve(s3, s2, 2).expect("resolve");
        assert_eq!(proof.clause_at(s4), Some(&vec![3, -3]));
        // We can't easily get to empty from here without more clauses.
        // But we can test that chain resolution works.
        assert!(!proof.verify()); // not a complete refutation
    }

    #[test]
    fn test_resolution_refutation_unit_propagation() {
        // (a) AND (-a v b) AND (-b)
        let mut proof = ResolutionProof::new();
        let s0 = proof.add_input(vec![1]); // a
        let s1 = proof.add_input(vec![-1, 2]); // -a v b
        let s2 = proof.add_input(vec![-2]); // -b
        let s3 = proof.add_resolve(s0, s1, 1).expect("resolve"); // b
        let _s4 = proof.add_resolve(s3, s2, 2).expect("resolve"); // empty
        assert!(proof.verify());
    }

    #[test]
    fn test_resolve_clauses_symmetric_pivot() {
        // resolve_clauses should handle pivot in either polarity
        let r1 = resolve_clauses(&[-1, 2], &[1, 3], 1).expect("resolve");
        assert!(r1.contains(&2) && r1.contains(&3));
    }

    // ---------- Cutting Planes ----------

    #[test]
    fn test_cp_refutation_php_2_1() {
        // PHP(2,1): 2 pigeons, 1 hole.
        // Pigeon 1: x1 >= 1
        // Pigeon 2: x2 >= 1
        // Hole 1: x1 + x2 <= 1 => -x1 - x2 >= -1
        // Add all three: 0 >= 1 (contradiction)
        let ineqs = encode_php_cp(1);
        assert_eq!(ineqs.len(), 3);

        let mut proof = CuttingPlanesProof::new();
        let s0 = proof.add_input(ineqs[0].clone()); // x1 >= 1
        let s1 = proof.add_input(ineqs[1].clone()); // x2 >= 1
        let s2 = proof.add_input(ineqs[2].clone()); // -x1 - x2 >= -1

        let s3 = proof.add(s0, s1).expect("add"); // x1 + x2 >= 2
        let _s4 = proof.add(s3, s2).expect("add"); // 0 >= 1

        assert!(proof.verify());
    }

    #[test]
    fn test_cp_refutation_simple() {
        // x >= 1 AND (1-x) >= 1 => x >= 1 AND -x >= 0 => 0 >= 1
        // (1-x) >= 1 means -x >= 0
        let mut proof = CuttingPlanesProof::new();
        let s0 = proof.add_input(CpInequality::new(vec![1], 1)); // x >= 1
        let s1 = proof.add_input(CpInequality::new(vec![-1], 0)); // -x >= 0
        let _s2 = proof.add(s0, s1).expect("add"); // 0 >= 1
        assert!(proof.verify());
    }

    #[test]
    fn test_cp_division_produces_contradiction() {
        // 2x >= 3. For x in {0,1}, max is 2 < 3. Divide by 2: ceil(2/2)*x >= ceil(3/2) => x >= 2.
        // Then -x >= 0 and x >= 2 => add => 0 >= 2.
        let mut proof = CuttingPlanesProof::new();
        let s0 = proof.add_input(CpInequality::new(vec![2], 3));
        let s1 = proof.divide(s0, 2).expect("divide"); // x >= 2
        let s2 = proof.add_input(CpInequality::new(vec![-1], 0)); // -x >= 0
        let _s3 = proof.add(s1, s2).expect("add"); // 0 >= 2
        assert!(proof.verify());
    }

    #[test]
    fn test_cp_saturation_step() {
        // 5x1 + 3x2 >= 3 => saturate => 3x1 + 3x2 >= 3
        let mut proof = CuttingPlanesProof::new();
        let s0 = proof.add_input(CpInequality::new(vec![5, 3], 3));
        let s1 = proof.saturate(s0).expect("saturate");
        let ineq = proof.inequality_at(s1).expect("get");
        assert_eq!(ineq.coeffs, vec![3, 3]);
        assert_eq!(ineq.rhs, 3);
    }

    // ---------- Encoding Properties ----------

    #[test]
    fn test_php_encoding_pigeon_clause_coverage() {
        // Every pigeon has a clause covering all holes.
        let n = 3;
        let (_, clauses) = encode_php(n);
        let pigeons = n + 1;
        // First `pigeons` clauses are pigeon clauses.
        for (i, clause) in clauses.iter().enumerate().take(pigeons) {
            assert_eq!(
                clause.len(),
                n,
                "pigeon clause {i} should have {n} literals"
            );
        }
    }

    #[test]
    fn test_php_unsatisfiable_small() {
        // PHP(2,1): 2 pigeons, 1 hole. Trivially unsatisfiable.
        let (num_vars, clauses) = encode_php(1);
        assert_eq!(num_vars, 2);
        // Pigeon clauses: (x1) and (x2)
        // Hole clause: (-x1 v -x2)
        // x1=true, x2=true violates hole. x1=true, x2=false violates pigeon 2.
        // Verify by brute force: no assignment satisfies all clauses.
        let n = num_vars as usize;
        for mask in 0..(1u32 << n) {
            let assignment: Vec<bool> = (0..n).map(|i| (mask >> i) & 1 == 1).collect();
            let all_satisfied = clauses.iter().all(|clause| {
                clause.iter().any(|&lit| {
                    let var = (lit.unsigned_abs() - 1) as usize;
                    let val = assignment.get(var).copied().unwrap_or(false);
                    if lit > 0 {
                        val
                    } else {
                        !val
                    }
                })
            });
            assert!(
                !all_satisfied,
                "PHP(2,1) should be unsatisfiable, but mask={mask} satisfies"
            );
        }
    }

    #[test]
    fn test_cp_inequality_boundary_evaluation() {
        // 0 >= 1 is never satisfiable.
        let ineq = CpInequality::new(vec![0, 0], 1);
        for mask in 0..4u32 {
            let assignment = vec![(mask & 1) == 1, (mask & 2) == 2];
            assert!(
                !ineq.evaluate(&assignment),
                "0 >= 1 should never be satisfied"
            );
        }
    }

    #[test]
    fn test_resolution_proof_default() {
        let proof = ResolutionProof::default();
        assert!(proof.is_empty());
        assert_eq!(proof.len(), 0);
        assert!(!proof.verify());
    }
}
