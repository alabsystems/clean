// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for symmetric (Krajicek) and path interpolation.

#[cfg(test)]
mod tests {
    use crate::sat_verify::interpolation::symmetric::{
        interpolant_strength_compare, path_interpolants, symmetric_interpolant,
        verify_path_interpolant_chain, verify_shared_variable_property, Derivation,
        PathVerifyResult, ProofNode, ResolutionProof, I07_SYMMETRIC_INTERPOLANT,
        I08_PATH_INTERPOLATION_CHAIN,
    };
    use crate::spec::ProofStatus;
    use std::cmp::Ordering;

    // ---- Proof construction helpers ----

    /// Build a simple proof: A={clause_a}, B={clause_b}, resolve on pivot.
    fn simple_two_clause_proof(
        clause_a: Vec<i32>,
        clause_b: Vec<i32>,
        pivot: i32,
    ) -> (Vec<Vec<i32>>, Vec<Vec<i32>>, ResolutionProof) {
        // Compute resolvent
        let pvar = pivot.unsigned_abs();
        let mut resolvent: Vec<i32> = Vec::new();
        for &lit in clause_a.iter().chain(clause_b.iter()) {
            if lit.unsigned_abs() == pvar {
                continue;
            }
            if !resolvent.contains(&lit) {
                resolvent.push(lit);
            }
        }
        resolvent.sort();

        let proof = ResolutionProof {
            nodes: vec![
                ProofNode {
                    clause: clause_a.clone(),
                    derivation: Derivation::Input(0),
                },
                ProofNode {
                    clause: clause_b.clone(),
                    derivation: Derivation::Input(1),
                },
                ProofNode {
                    clause: resolvent,
                    derivation: Derivation::Resolve {
                        left: 0,
                        right: 1,
                        pivot,
                    },
                },
            ],
        };
        (vec![clause_a], vec![clause_b], proof)
    }

    /// Build a proof: A={(1,2)}, B={(-1), (-2)}.
    /// Proof: resolve (1,2) with (-1) on 1 => (2), then (2) with (-2) on 2 => ()
    fn three_clause_proof() -> (Vec<Vec<i32>>, Vec<Vec<i32>>, ResolutionProof) {
        let proof = ResolutionProof {
            nodes: vec![
                ProofNode {
                    clause: vec![1, 2],
                    derivation: Derivation::Input(0),
                },
                ProofNode {
                    clause: vec![-1],
                    derivation: Derivation::Input(1),
                },
                ProofNode {
                    clause: vec![-2],
                    derivation: Derivation::Input(2),
                },
                ProofNode {
                    clause: vec![2],
                    derivation: Derivation::Resolve {
                        left: 0,
                        right: 1,
                        pivot: 1,
                    },
                },
                ProofNode {
                    clause: vec![],
                    derivation: Derivation::Resolve {
                        left: 3,
                        right: 2,
                        pivot: 2,
                    },
                },
            ],
        };
        (vec![vec![1, 2]], vec![vec![-1], vec![-2]], proof)
    }

    // ---- symmetric_interpolant tests ----

    #[test]
    fn test_symmetric_simple_single_shared_var() {
        // A = {(1)}, B = {(-1)}, shared = {1}
        let (a, b, proof) = simple_two_clause_proof(vec![1], vec![-1], 1);
        let result = symmetric_interpolant(&a, &b, &proof, &[1]);
        // The symmetric interpolant should only use var 1
        assert!(
            verify_shared_variable_property(&result, &[1], &[1]),
            "shared var property failed for: {result:?}"
        );
    }

    #[test]
    fn test_symmetric_three_clause_shared_vars() {
        let (a, b, proof) = three_clause_proof();
        let shared = vec![1, 2];
        let result = symmetric_interpolant(&a, &b, &proof, &shared);
        assert!(
            verify_shared_variable_property(&result, &[1, 2], &[1, 2]),
            "shared var property: {result:?}"
        );
    }

    #[test]
    fn test_symmetric_a_only_vars_excluded() {
        // A = {(1,2), (-1,2)}, B = {(-2)}
        // Var 1 is A-only, var 2 is shared.
        let proof = ResolutionProof {
            nodes: vec![
                ProofNode {
                    clause: vec![1, 2],
                    derivation: Derivation::Input(0),
                },
                ProofNode {
                    clause: vec![-1, 2],
                    derivation: Derivation::Input(1),
                },
                ProofNode {
                    clause: vec![-2],
                    derivation: Derivation::Input(2),
                },
                ProofNode {
                    clause: vec![2],
                    derivation: Derivation::Resolve {
                        left: 0,
                        right: 1,
                        pivot: 1,
                    },
                },
                ProofNode {
                    clause: vec![],
                    derivation: Derivation::Resolve {
                        left: 3,
                        right: 2,
                        pivot: 2,
                    },
                },
            ],
        };
        let a = vec![vec![1, 2], vec![-1, 2]];
        let b = vec![vec![-2]];
        let result = symmetric_interpolant(&a, &b, &proof, &[2]);
        // Var 1 should not appear (A-only)
        for clause in &result {
            for &lit in clause {
                assert_ne!(
                    lit.unsigned_abs(),
                    1,
                    "A-only var 1 should not appear in interpolant"
                );
            }
        }
    }

    #[test]
    fn test_symmetric_returns_nonempty_for_nontrivial_proof() {
        let (a, b, proof) = three_clause_proof();
        let result = symmetric_interpolant(&a, &b, &proof, &[1, 2]);
        assert!(
            !result.is_empty(),
            "symmetric interpolant should be nonempty"
        );
    }

    // ---- path_interpolants tests ----

    #[test]
    fn test_path_interpolants_two_partitions() {
        // P1 = {(1)}, P2 = {(-1)}
        let proof = ResolutionProof {
            nodes: vec![
                ProofNode {
                    clause: vec![1],
                    derivation: Derivation::Input(0),
                },
                ProofNode {
                    clause: vec![-1],
                    derivation: Derivation::Input(1),
                },
                ProofNode {
                    clause: vec![],
                    derivation: Derivation::Resolve {
                        left: 0,
                        right: 1,
                        pivot: 1,
                    },
                },
            ],
        };
        let partitions = vec![vec![vec![1]], vec![vec![-1]]];
        let result = path_interpolants(&partitions, &proof);
        assert_eq!(result.len(), 1, "2 partitions => 1 interpolant");
    }

    #[test]
    fn test_path_interpolants_three_partitions() {
        // P1 = {(1,2)}, P2 = {(-1)}, P3 = {(-2)}
        let proof = ResolutionProof {
            nodes: vec![
                ProofNode {
                    clause: vec![1, 2],
                    derivation: Derivation::Input(0),
                },
                ProofNode {
                    clause: vec![-1],
                    derivation: Derivation::Input(1),
                },
                ProofNode {
                    clause: vec![-2],
                    derivation: Derivation::Input(2),
                },
                ProofNode {
                    clause: vec![2],
                    derivation: Derivation::Resolve {
                        left: 0,
                        right: 1,
                        pivot: 1,
                    },
                },
                ProofNode {
                    clause: vec![],
                    derivation: Derivation::Resolve {
                        left: 3,
                        right: 2,
                        pivot: 2,
                    },
                },
            ],
        };
        let partitions = vec![vec![vec![1, 2]], vec![vec![-1]], vec![vec![-2]]];
        let result = path_interpolants(&partitions, &proof);
        assert_eq!(result.len(), 2, "3 partitions => 2 interpolants");
    }

    #[test]
    fn test_path_interpolants_degenerate_cases() {
        let proof = ResolutionProof {
            nodes: vec![ProofNode {
                clause: vec![1],
                derivation: Derivation::Input(0),
            }],
        };
        assert!(path_interpolants(&[vec![vec![1]]], &proof).is_empty());
        assert!(path_interpolants(&[], &ResolutionProof { nodes: vec![] }).is_empty());
    }

    // ---- verify_path_interpolant_chain tests ----

    #[test]
    fn test_verify_chain_valid_simple() {
        // P1 = {(1)}, P2 = {(-1)}
        // I_0 = {(1)} which is implied by P1 and contradicts P2
        let partitions = vec![vec![vec![1]], vec![vec![-1]]];
        let interpolants = vec![vec![vec![1]]];
        let result = verify_path_interpolant_chain(&partitions, &interpolants);
        assert!(result.valid, "failures: {:?}", result.failures);
    }

    #[test]
    fn test_verify_chain_invalid_wrong_interpolant() {
        // P1 = {(1)}, P2 = {(-1)}
        // I_0 = {(-1)} -- this is NOT implied by P1
        let partitions = vec![vec![vec![1]], vec![vec![-1]]];
        let interpolants = vec![vec![vec![-1]]];
        let result = verify_path_interpolant_chain(&partitions, &interpolants);
        assert!(!result.valid, "should detect prefix-implication failure");
        assert!(!result.failures.is_empty());
    }

    #[test]
    fn test_verify_chain_invalid_wrong_count() {
        let partitions = vec![vec![vec![1]], vec![vec![-1]]];
        let interpolants: Vec<Vec<Vec<i32>>> = vec![];
        let result = verify_path_interpolant_chain(&partitions, &interpolants);
        assert!(!result.valid);
    }

    #[test]
    fn test_verify_chain_three_partition_valid() {
        // P1 = {(1)}, P2 = {(2)}, P3 = {(-1,-2)}
        // Conjunction is unsat: 1 AND 2 AND (-1 OR -2) = false
        // I_0 separates P1 from P2,P3: I_0 = {(1)}
        // I_1 separates P1,P2 from P3: I_1 = {(1),(2)} => (1 AND 2)
        let partitions = vec![vec![vec![1]], vec![vec![2]], vec![vec![-1, -2]]];
        let interpolants = vec![vec![vec![1]], vec![vec![1], vec![2]]];
        let result = verify_path_interpolant_chain(&partitions, &interpolants);
        assert!(result.valid, "failures: {:?}", result.failures);
    }

    #[test]
    fn test_verify_chain_single_partition_no_interpolants() {
        let partitions = vec![vec![vec![1]]];
        let interpolants: Vec<Vec<Vec<i32>>> = vec![];
        let result = verify_path_interpolant_chain(&partitions, &interpolants);
        assert!(result.valid);
    }

    #[test]
    fn test_verify_chain_too_many_interpolants() {
        let partitions = vec![vec![vec![1]], vec![vec![-1]]];
        let interpolants = vec![vec![vec![1]], vec![vec![-1]]];
        let result = verify_path_interpolant_chain(&partitions, &interpolants);
        assert!(!result.valid);
    }

    // ---- verify_shared_variable_property tests ----

    #[test]
    fn test_shared_var_property_all_shared() {
        let interpolant = vec![vec![1, -2], vec![2]];
        assert!(verify_shared_variable_property(
            &interpolant,
            &[1, 2, 3],
            &[1, 2, 4]
        ));
    }

    #[test]
    fn test_shared_var_property_violation() {
        // Var 3 is only in A, not in B
        let interpolant = vec![vec![1, 3]];
        assert!(!verify_shared_variable_property(
            &interpolant,
            &[1, 2, 3],
            &[1, 2]
        ));
    }

    #[test]
    fn test_shared_var_property_empty_cases() {
        // Empty interpolant: trivially satisfied
        assert!(verify_shared_variable_property(&[], &[1, 2], &[2, 3]));
        // Empty clause (false) has no variables: trivially satisfied
        assert!(verify_shared_variable_property(&[vec![]], &[1], &[2]));
    }

    #[test]
    fn test_shared_var_property_negated_literals() {
        // -3 has variable 3, which must be shared.
        let interpolant = vec![vec![-3]];
        assert!(verify_shared_variable_property(
            &interpolant,
            &[1, 3],
            &[2, 3]
        ));
        // But var 1 is not in B
        let interpolant2 = vec![vec![-1]];
        assert!(!verify_shared_variable_property(
            &interpolant2,
            &[1, 3],
            &[2, 3]
        ));
    }

    // ---- interpolant_strength_compare tests ----

    #[test]
    fn test_strength_compare_equal() {
        let a = vec![vec![1]]; // models: {1=T} => 1 model out of 2
        let b = vec![vec![1]];
        assert_eq!(interpolant_strength_compare(&a, &b, 1), Ordering::Equal);
    }

    #[test]
    fn test_strength_compare_stronger() {
        // a = {(1),(2)}: only satisfied when 1=T AND 2=T => 1 model
        // b = {(1)}: satisfied when 1=T => 2 models (2 can be T or F)
        let a = vec![vec![1], vec![2]];
        let b = vec![vec![1]];
        assert_eq!(
            interpolant_strength_compare(&a, &b, 2),
            Ordering::Less,
            "a has fewer models => stronger"
        );
    }

    #[test]
    fn test_strength_compare_weaker() {
        let a = vec![vec![1]]; // 2 models (with 2 vars)
        let b = vec![vec![1], vec![2]]; // 1 model
        assert_eq!(
            interpolant_strength_compare(&a, &b, 2),
            Ordering::Greater,
            "a has more models => weaker"
        );
    }

    #[test]
    fn test_strength_compare_tautology_vs_single() {
        // Empty clause set = tautology = all models
        let taut: Vec<Vec<i32>> = vec![];
        let single = vec![vec![1]];
        assert_eq!(
            interpolant_strength_compare(&taut, &single, 2),
            Ordering::Greater,
            "tautology is weakest"
        );
    }

    #[test]
    fn test_strength_compare_contradiction() {
        // Empty clause = contradiction = 0 models
        let contra = vec![vec![]];
        let single = vec![vec![1]];
        assert_eq!(
            interpolant_strength_compare(&contra, &single, 2),
            Ordering::Less,
            "contradiction is strongest (0 models)"
        );
    }

    // ---- Proof status and type tests ----

    #[test]
    fn test_proof_status_constants() {
        assert_eq!(I07_SYMMETRIC_INTERPOLANT, ProofStatus::DerivedPending);
        assert_eq!(I08_PATH_INTERPOLATION_CHAIN, ProofStatus::DerivedPending);
    }

    #[test]
    fn test_derivation_equality() {
        assert_eq!(Derivation::Input(0), Derivation::Input(0));
        assert_ne!(Derivation::Input(0), Derivation::Input(1));
        let r = Derivation::Resolve {
            left: 0,
            right: 1,
            pivot: 3,
        };
        assert_eq!(
            r,
            Derivation::Resolve {
                left: 0,
                right: 1,
                pivot: 3
            }
        );
        assert_ne!(Derivation::Input(0), r);
    }

    #[test]
    fn test_path_verify_result_construction() {
        let valid = PathVerifyResult {
            valid: true,
            failures: vec![],
        };
        assert!(valid.valid && valid.failures.is_empty());
        let invalid = PathVerifyResult {
            valid: false,
            failures: vec![(0, "test failure".into())],
        };
        assert!(!invalid.valid);
        assert_eq!(invalid.failures.len(), 1);
    }

    // ---- Edge cases ----

    #[test]
    fn test_symmetric_empty_shared_vars() {
        // A = {(1)}, B = {(-2)}, shared = {} (no overlap)
        // The proof doesn't actually refute, but we test the function behavior.
        let proof = ResolutionProof {
            nodes: vec![
                ProofNode {
                    clause: vec![1],
                    derivation: Derivation::Input(0),
                },
                ProofNode {
                    clause: vec![-2],
                    derivation: Derivation::Input(1),
                },
            ],
        };
        let result = symmetric_interpolant(&[vec![1]], &[vec![-2]], &proof, &[]);
        // With no shared vars, the interpolant should be trivial
        for clause in &result {
            assert!(clause.is_empty(), "no shared vars => trivial clauses");
        }
    }

    #[test]
    fn test_verify_chain_with_disjoint_partitions() {
        // P1={(1)}, P2={(-1)}: vars are disjoint per-partition but overlapping
        // I_0={(1)}: implied by P1, contradicts P2
        let partitions = vec![vec![vec![1]], vec![vec![-1]]];
        let interpolants = vec![vec![vec![1]]];
        let result = verify_path_interpolant_chain(&partitions, &interpolants);
        assert!(result.valid, "failures: {:?}", result.failures);
    }

    #[test]
    fn test_strength_compare_single_var() {
        // With 1 var: {(1)} has 1 model, {(-1)} has 1 model => equal
        let a = vec![vec![1]];
        let b = vec![vec![-1]];
        assert_eq!(interpolant_strength_compare(&a, &b, 1), Ordering::Equal);
    }
}
