// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for proof complexity separations.

#[cfg(test)]
mod tests {
    use crate::sat_verify::proof_complexity::cutting_planes::CuttingPlanesProof;
    use crate::sat_verify::proof_complexity::encodings::{
        encode_php, encode_php_cp, encode_tseitin,
    };
    use crate::sat_verify::proof_complexity::resolution::ResolutionProof;
    use crate::sat_verify::proof_complexity::separations::{
        cp_proof_size, php_cp_size_upper_bound, php_resolution_size_lower_bound,
        php_separation_witness, resolution_proof_size, tree_resolution_proof_size,
        tseitin_separation_witness, verify_separation_witness, ProofSizeBound, ProofSystem,
    };
    use crate::sat_verify::proof_complexity::tree_resolution::{
        is_tree_like, verify_tree_resolution, TreeNode, TreeResolutionProof,
    };

    // -----------------------------------------------------------------------
    // 1-3: PHP(2,1) — small enough for explicit proofs in both systems
    // -----------------------------------------------------------------------

    #[test]
    fn test_separations_php_2_1_resolution_proof() {
        // PHP(2,1): 2 pigeons, 1 hole.
        let (_, clauses) = encode_php(1);
        assert_eq!(clauses.len(), 3);

        let mut proof = ResolutionProof::new();
        for c in &clauses {
            proof.add_input(c.clone());
        }
        // resolve {1} and {-1, -2} on 1 => {-2}
        proof.add_resolve(0, 2, 1).expect("resolve step 1");
        // resolve {2} and {-2} on 2 => {}
        proof.add_resolve(1, 3, 2).expect("resolve step 2");
        assert!(proof.verify(), "PHP(2,1) resolution should refute");
        assert_eq!(resolution_proof_size(&proof), 5); // 3 inputs + 2 resolves
    }

    #[test]
    fn test_separations_php_2_1_cp_proof() {
        // PHP(2,1) as CP.
        let ineqs = encode_php_cp(1);
        assert_eq!(ineqs.len(), 3);

        let mut proof = CuttingPlanesProof::new();
        let s0 = proof.add_input(ineqs[0].clone());
        let s1 = proof.add_input(ineqs[1].clone());
        let s2 = proof.add_input(ineqs[2].clone());
        let s3 = proof.add(s0, s1).expect("add");
        let _s4 = proof.add(s3, s2).expect("add");
        assert!(proof.verify(), "PHP(2,1) CP should refute");
        assert_eq!(cp_proof_size(&proof), 5); // 3 inputs + 2 adds
    }

    #[test]
    fn test_separations_php_2_1_compare_sizes() {
        // Both use 5 total steps for PHP(2,1). No separation at this size.
        let (_, clauses) = encode_php(1);
        let mut res_proof = ResolutionProof::new();
        for c in &clauses {
            res_proof.add_input(c.clone());
        }
        res_proof.add_resolve(0, 2, 1).expect("res");
        res_proof.add_resolve(1, 3, 2).expect("res");

        let ineqs = encode_php_cp(1);
        let mut cp_proof = CuttingPlanesProof::new();
        let s0 = cp_proof.add_input(ineqs[0].clone());
        let s1 = cp_proof.add_input(ineqs[1].clone());
        let s2 = cp_proof.add_input(ineqs[2].clone());
        let s3 = cp_proof.add(s0, s1).expect("add");
        cp_proof.add(s3, s2).expect("add");

        let ratio = resolution_proof_size(&res_proof) as f64 / cp_proof_size(&cp_proof) as f64;
        assert!((ratio - 1.0).abs() < 0.01, "equal size at PHP(2,1)");
    }

    // -----------------------------------------------------------------------
    // 4-5: PHP(3,2) — resolution proof grows, CP stays small
    // -----------------------------------------------------------------------

    #[test]
    fn test_separations_php_3_2_resolution_proof() {
        // PHP(3,2): 3 pigeons, 2 holes. 6 variables, 9 clauses.
        let (_, clauses) = encode_php(2);
        assert_eq!(clauses.len(), 9);

        // Build explicit resolution refutation.
        // Vars: p11=1, p12=2, p21=3, p22=4, p31=5, p32=6
        // Clauses: {1,2}, {3,4}, {5,6}, {-1,-3}, {-1,-5}, {-3,-5}, {-2,-4}, {-2,-6}, {-4,-6}
        let mut proof = ResolutionProof::new();
        for c in &clauses {
            proof.add_input(c.clone());
        }

        // 9: {1,2}+{-1,-3} on 1 => {2,-3}
        proof.add_resolve(0, 3, 1).expect("s9");
        // 10: {2,-3}+{3,4} on 3 => {2,4}
        proof.add_resolve(9, 1, 3).expect("s10");
        // 11: {1,2}+{-1,-5} on 1 => {2,-5}
        proof.add_resolve(0, 4, 1).expect("s11");
        // 12: {2,-5}+{5,6} on 5 => {2,6}
        proof.add_resolve(11, 2, 5).expect("s12");
        // 13: {2,4}+{-2,-6} on 2 => {4,-6}
        proof.add_resolve(10, 7, 2).expect("s13");
        // 14: {2,6}+{4,-6} on 6 => {2,4}
        proof.add_resolve(12, 13, 6).expect("s14");
        // 15: {2,4}+{-4,-6} on 4 => {2,-6}
        proof.add_resolve(14, 8, 4).expect("s15");
        // 16: {2,-6}+{-2,-6} on 2 => {-6}
        proof.add_resolve(15, 7, 2).expect("s16");
        // 17: {5,6}+{-3,-5} on 5 => {-3,6}
        proof.add_resolve(2, 5, 5).expect("s17");
        // 18: {3,4}+{-3,6} on 3 => {4,6}
        proof.add_resolve(1, 17, 3).expect("s18");
        // 19: {4,6}+{-2,-4} on 4 => {-2,6}
        proof.add_resolve(18, 6, 4).expect("s19");
        // 20: {1,2}+{-2,6} on 2 => {1,6}
        proof.add_resolve(0, 19, 2).expect("s20");
        // 21: {1,6}+{-1,-5} on 1 => {-5,6}
        proof.add_resolve(20, 4, 1).expect("s21");
        // 22: {5,6}+{-5,6} on 5 => {6}
        proof.add_resolve(2, 21, 5).expect("s22");
        // 23: {6}+{-6} on 6 => {}
        proof.add_resolve(22, 16, 6).expect("s23");

        assert!(proof.verify(), "PHP(3,2) resolution should refute");
        let size = resolution_proof_size(&proof);
        assert!(size >= 20, "PHP(3,2) res proof needs many steps: {size}");
    }

    #[test]
    fn test_separations_php_3_2_cp_upper_bound() {
        let bound = php_cp_size_upper_bound(2);
        assert_eq!(bound, 16);
    }

    // -----------------------------------------------------------------------
    // 6-7: PHP(4,3) — CP advantage grows
    // -----------------------------------------------------------------------

    #[test]
    fn test_separations_php_4_3_formula_size() {
        let (num_vars, clauses) = encode_php(3);
        assert_eq!(num_vars, 12); // 4 pigeons * 3 holes
        assert_eq!(clauses.len(), 22); // 4 pigeon + C(4,2)*3 = 4+18 = 22
    }

    #[test]
    fn test_separations_php_4_3_bounds_comparison() {
        let n = 3;
        let haken = php_resolution_size_lower_bound(n);
        let cp_bound = php_cp_size_upper_bound(n);
        assert!(haken > 1.0, "Haken bound at n=3: {haken}");
        assert_eq!(cp_bound, 54); // 2*27
    }

    // -----------------------------------------------------------------------
    // 8-10: Haken bound computation for n=2..10
    // -----------------------------------------------------------------------

    #[test]
    fn test_separations_haken_bound_monotone() {
        let mut prev = 0.0;
        for n in 2..=10 {
            let bound = php_resolution_size_lower_bound(n);
            assert!(bound > prev, "Haken bound should increase with n");
            prev = bound;
        }
    }

    #[test]
    fn test_separations_haken_bound_values() {
        // 2^{2/20} = 2^{0.1} ~ 1.0718
        let b2 = php_resolution_size_lower_bound(2);
        assert!((b2 - 1.0718).abs() < 0.01, "n=2: {b2}");

        // 2^{10/20} = sqrt(2) ~ 1.4142
        let b10 = php_resolution_size_lower_bound(10);
        assert!((b10 - std::f64::consts::SQRT_2).abs() < 0.01, "n=10: {b10}");
    }

    #[test]
    fn test_separations_haken_bound_large_n() {
        // 2^{100/20} = 2^5 = 32
        let b100 = php_resolution_size_lower_bound(100);
        assert!((b100 - 32.0).abs() < 0.01);

        // 2^{200/20} = 2^10 = 1024
        let b200 = php_resolution_size_lower_bound(200);
        assert!((b200 - 1024.0).abs() < 0.01);
    }

    // -----------------------------------------------------------------------
    // 11-12: CP upper bound computation for n=2..10
    // -----------------------------------------------------------------------

    #[test]
    fn test_separations_cp_bound_monotone() {
        let mut prev = 0;
        for n in 2..=10 {
            let bound = php_cp_size_upper_bound(n);
            assert!(bound > prev, "CP bound should increase with n");
            prev = bound;
        }
    }

    #[test]
    fn test_separations_cp_bound_values() {
        assert_eq!(php_cp_size_upper_bound(2), 16);
        assert_eq!(php_cp_size_upper_bound(3), 54);
        assert_eq!(php_cp_size_upper_bound(5), 250);
        assert_eq!(php_cp_size_upper_bound(10), 2000);
    }

    // -----------------------------------------------------------------------
    // 13-15: Exponential separation at large n + witnesses
    // -----------------------------------------------------------------------

    #[test]
    fn test_separations_exponential_crossover() {
        // At n=1000: 2^{50} ~ 1.13e15 vs 2*10^9 = 2e9.
        let haken = php_resolution_size_lower_bound(1000);
        let cp = php_cp_size_upper_bound(1000) as f64;
        assert!(
            haken > cp,
            "At n=1000, Haken {haken:.2e} should exceed CP {cp:.0}"
        );
    }

    #[test]
    fn test_separations_witness_small_n() {
        let witness = php_separation_witness(3);
        assert_eq!(witness.formula_family, "PHP(4,3)");
        assert_eq!(witness.weaker_system, ProofSystem::Resolution);
        assert_eq!(witness.stronger_system, ProofSystem::CuttingPlanes);
    }

    #[test]
    fn test_separations_witness_large_n() {
        let witness = php_separation_witness(1000);
        match &witness.weaker_size {
            ProofSizeBound::LowerBound(lb) => assert!(*lb > 1e10),
            _ => panic!("expected LowerBound"),
        }
        match &witness.stronger_size {
            ProofSizeBound::UpperBound(ub) => assert!(*ub > 0),
            _ => panic!("expected UpperBound"),
        }
    }

    // -----------------------------------------------------------------------
    // 16-17: Tree-like check
    // -----------------------------------------------------------------------

    #[test]
    fn test_separations_tree_like_simple() {
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![1]);
        proof.add_input(vec![-1]);
        proof.add_resolve(0, 1, 1).expect("resolve");
        assert!(is_tree_like(&proof));
    }

    #[test]
    fn test_separations_tree_like_chain() {
        // Chain: (a) AND (-a v b) AND (-b) => unit propagation.
        let mut proof = ResolutionProof::new();
        proof.add_input(vec![1]);
        proof.add_input(vec![-1, 2]);
        proof.add_input(vec![-2]);
        proof.add_resolve(0, 1, 1).expect("res");
        proof.add_resolve(3, 2, 2).expect("res");
        assert!(proof.verify());
        assert!(is_tree_like(&proof));
    }

    // -----------------------------------------------------------------------
    // 18-19: Tree resolution proof size and verification
    // -----------------------------------------------------------------------

    #[test]
    fn test_separations_tree_resolution_size() {
        let proof = TreeResolutionProof {
            root: TreeNode::Resolve {
                left: Box::new(TreeNode::Resolve {
                    left: Box::new(TreeNode::Axiom(vec![1, 2])),
                    right: Box::new(TreeNode::Axiom(vec![-1, 2])),
                    pivot: 1,
                    result: vec![2],
                }),
                right: Box::new(TreeNode::Axiom(vec![-2])),
                pivot: 2,
                result: vec![],
            },
        };
        assert_eq!(tree_resolution_proof_size(&proof), 5);
    }

    #[test]
    fn test_separations_tree_resolution_verify() {
        let axioms = vec![vec![1, 2], vec![-1, 2], vec![-2]];
        let proof = TreeResolutionProof {
            root: TreeNode::Resolve {
                left: Box::new(TreeNode::Resolve {
                    left: Box::new(TreeNode::Axiom(vec![1, 2])),
                    right: Box::new(TreeNode::Axiom(vec![-1, 2])),
                    pivot: 1,
                    result: vec![2],
                }),
                right: Box::new(TreeNode::Axiom(vec![-2])),
                pivot: 2,
                result: vec![],
            },
        };
        verify_tree_resolution(&proof, &axioms).expect("should verify");
    }

    // -----------------------------------------------------------------------
    // 20-21: Tseitin formulas — resolution vs tree-resolution separation
    // -----------------------------------------------------------------------

    #[test]
    fn test_separations_tseitin_formula_generation() {
        let (num_vars, clauses) = encode_tseitin(5);
        assert_eq!(num_vars, 5);
        // 4 XOR constraints * 2 clauses + 2 boundary = 10
        assert_eq!(clauses.len(), 10);
    }

    #[test]
    fn test_separations_tseitin_witness() {
        let witness = tseitin_separation_witness(20);
        assert_eq!(witness.formula_family, "Tseitin(expander, 20)");
        assert_eq!(witness.weaker_system, ProofSystem::TreeResolution);
        assert_eq!(witness.stronger_system, ProofSystem::Resolution);
        match &witness.weaker_size {
            ProofSizeBound::LowerBound(lb) => {
                assert!(*lb > 1.0, "lower bound should be > 1");
            }
            _ => panic!("expected LowerBound for tree-res"),
        }
        match &witness.stronger_size {
            ProofSizeBound::UpperBound(ub) => {
                assert_eq!(*ub, 400); // 20^2
            }
            _ => panic!("expected UpperBound for general-res"),
        }
    }

    // -----------------------------------------------------------------------
    // 22-23: ProofSystem ordering
    // -----------------------------------------------------------------------

    #[test]
    fn test_separations_proof_system_total_order() {
        let systems = [
            ProofSystem::TreeResolution,
            ProofSystem::Resolution,
            ProofSystem::CuttingPlanes,
            ProofSystem::ExtendedResolution,
            ProofSystem::Frege,
        ];
        for i in 0..systems.len() {
            for j in (i + 1)..systems.len() {
                assert!(
                    systems[i] < systems[j],
                    "{:?} should be < {:?}",
                    systems[i],
                    systems[j]
                );
            }
        }
    }

    #[test]
    fn test_separations_proof_system_equality() {
        assert_eq!(ProofSystem::Resolution, ProofSystem::Resolution);
        assert_ne!(ProofSystem::Resolution, ProofSystem::CuttingPlanes);
    }

    // -----------------------------------------------------------------------
    // 24-26: verify_separation_witness integration
    // -----------------------------------------------------------------------

    #[test]
    fn test_separations_verify_witness_php_2_1() {
        let (_, clauses) = encode_php(1);
        let result = verify_separation_witness(&clauses, None, 2);
        assert_eq!(result.weaker, ProofSystem::Resolution);
        assert_eq!(result.stronger, ProofSystem::CuttingPlanes);
        assert!(result.size_ratio > 0.0);
    }

    #[test]
    fn test_separations_verify_witness_with_explicit_proof() {
        let (_, clauses) = encode_php(1);
        let res_steps: Vec<Vec<i32>> = vec![vec![-2], vec![]];
        let result = verify_separation_witness(&clauses, Some(&res_steps), 2);
        assert_eq!(result.size_ratio, 1.0);
    }

    #[test]
    fn test_separations_verify_witness_large_parameter() {
        let (_, clauses) = encode_php(100);
        let result = verify_separation_witness(&clauses, None, 200);
        assert!(
            result.explanation.contains("PHP"),
            "explanation: {}",
            result.explanation
        );
    }

    // -----------------------------------------------------------------------
    // 27-28: strict weakness + names
    // -----------------------------------------------------------------------

    #[test]
    fn test_separations_strict_weakness_all_pairs() {
        assert!(ProofSystem::TreeResolution.is_strictly_weaker_than(ProofSystem::Resolution));
        assert!(ProofSystem::Resolution.is_strictly_weaker_than(ProofSystem::CuttingPlanes));
        assert!(ProofSystem::TreeResolution.is_strictly_weaker_than(ProofSystem::Frege));
        assert!(
            !ProofSystem::CuttingPlanes.is_strictly_weaker_than(ProofSystem::ExtendedResolution)
        );
        assert!(!ProofSystem::Frege.is_strictly_weaker_than(ProofSystem::TreeResolution));
    }

    #[test]
    fn test_separations_proof_system_display_names() {
        assert_eq!(ProofSystem::TreeResolution.name(), "Tree Resolution");
        assert_eq!(ProofSystem::Resolution.name(), "Resolution");
        assert_eq!(ProofSystem::CuttingPlanes.name(), "Cutting Planes");
        assert_eq!(
            ProofSystem::ExtendedResolution.name(),
            "Extended Resolution"
        );
        assert_eq!(ProofSystem::Frege.name(), "Frege");
    }
}
