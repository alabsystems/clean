// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended tests for resolution verification and tree-to-DAG conversion.
//! CP/PHP/Haken tests live in `tests_proofs_ext2`.

#[cfg(test)]
mod tests {
    use crate::sat_verify::proof_complexity::separations::{
        sep_resolution_proof_size, tree_resolution_to_dag, verify_resolution_proof,
        SepResolutionStep, SepTreeNode, SepTreeResStep,
    };

    // -----------------------------------------------------------------------
    // 1-5: Resolution proof verification — valid proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_res_simple_refutation() {
        // (1) AND (-1) => resolve on 1 => empty
        let clauses = vec![vec![1], vec![-1]];
        let steps = vec![SepResolutionStep {
            left: 0,
            right: 1,
            pivot: 1,
            result: vec![],
        }];
        let r = verify_resolution_proof(&clauses, &steps);
        assert!(r.valid);
        assert!(r.derived_empty);
        assert_eq!(r.steps_verified, 1);
        assert!(r.errors.is_empty());
    }

    #[test]
    fn test_verify_res_unit_propagation() {
        // (a) AND (-a v b) AND (-b)
        let clauses = vec![vec![1], vec![-1, 2], vec![-2]];
        let steps = vec![
            SepResolutionStep {
                left: 0,
                right: 1,
                pivot: 1,
                result: vec![2],
            },
            SepResolutionStep {
                left: 3,
                right: 2,
                pivot: 2,
                result: vec![],
            },
        ];
        let r = verify_resolution_proof(&clauses, &steps);
        assert!(r.valid);
        assert!(r.derived_empty);
        assert_eq!(r.steps_verified, 2);
    }

    #[test]
    fn test_verify_res_three_step_chain() {
        // (a) AND (-a v b) AND (-b v c) AND (-c)
        // Step 0: resolve 0,1 on a => (b) at idx 4
        // Step 1: resolve 4,2 on b => (c) at idx 5
        // Step 2: resolve 5,3 on c => () at idx 6
        let clauses = vec![
            vec![1],     // 0: a
            vec![-1, 2], // 1: -a v b
            vec![-2, 3], // 2: -b v c
            vec![-3],    // 3: -c
        ];
        let steps = vec![
            SepResolutionStep {
                left: 0,
                right: 1,
                pivot: 1,
                result: vec![2],
            },
            SepResolutionStep {
                left: 4,
                right: 2,
                pivot: 2,
                result: vec![3],
            },
            SepResolutionStep {
                left: 5,
                right: 3,
                pivot: 3,
                result: vec![],
            },
        ];
        let r = verify_resolution_proof(&clauses, &steps);
        assert!(r.valid);
        assert!(r.derived_empty);
        assert_eq!(r.steps_verified, 3);
    }

    #[test]
    fn test_verify_res_no_steps() {
        let clauses = vec![vec![1], vec![-1]];
        let r = verify_resolution_proof(&clauses, &[]);
        assert!(r.valid);
        assert!(!r.derived_empty);
        assert_eq!(r.steps_verified, 0);
    }

    #[test]
    fn test_verify_res_dedup_in_result() {
        // (a v b) AND (-a v b) => resolve on a => (b) [dedup]
        let clauses = vec![vec![1, 2], vec![-1, 2]];
        let steps = vec![SepResolutionStep {
            left: 0,
            right: 1,
            pivot: 1,
            result: vec![2],
        }];
        let r = verify_resolution_proof(&clauses, &steps);
        assert!(r.valid);
        assert!(!r.derived_empty);
    }

    // -----------------------------------------------------------------------
    // 6-9: Resolution proof verification — invalid proofs
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_res_invalid_pivot() {
        let clauses = vec![vec![1, 2], vec![3, 4]];
        let steps = vec![SepResolutionStep {
            left: 0,
            right: 1,
            pivot: 1,
            result: vec![2, 3, 4],
        }];
        let r = verify_resolution_proof(&clauses, &steps);
        assert!(!r.valid);
        assert!(!r.errors.is_empty());
    }

    #[test]
    fn test_verify_res_index_out_of_range() {
        let clauses = vec![vec![1]];
        let steps = vec![SepResolutionStep {
            left: 0,
            right: 5,
            pivot: 1,
            result: vec![],
        }];
        let r = verify_resolution_proof(&clauses, &steps);
        assert!(!r.valid);
    }

    #[test]
    fn test_verify_res_wrong_result() {
        let clauses = vec![vec![1, 2], vec![-1, 3]];
        let steps = vec![SepResolutionStep {
            left: 0,
            right: 1,
            pivot: 1,
            result: vec![2, 4], // wrong: should be [2,3]
        }];
        let r = verify_resolution_proof(&clauses, &steps);
        assert!(!r.valid);
    }

    #[test]
    fn test_verify_res_missing_step_in_chain() {
        // Step 1 references derived clause at index 2, but only 2 input clauses.
        let clauses = vec![vec![1], vec![-1]];
        let steps = vec![
            SepResolutionStep {
                left: 0,
                right: 1,
                pivot: 1,
                result: vec![],
            },
            SepResolutionStep {
                left: 2,
                right: 99,
                pivot: 1,
                result: vec![],
            },
        ];
        let r = verify_resolution_proof(&clauses, &steps);
        // First step valid, second has out-of-range index.
        assert!(!r.valid);
        assert_eq!(r.steps_verified, 1);
    }

    // -----------------------------------------------------------------------
    // 10-11: Resolution proof size
    // -----------------------------------------------------------------------

    #[test]
    fn test_sep_resolution_proof_size_empty() {
        assert_eq!(sep_resolution_proof_size(&[]), 0);
    }

    #[test]
    fn test_sep_resolution_proof_size_three() {
        let steps = vec![
            SepResolutionStep {
                left: 0,
                right: 1,
                pivot: 1,
                result: vec![2],
            },
            SepResolutionStep {
                left: 2,
                right: 3,
                pivot: 2,
                result: vec![3],
            },
            SepResolutionStep {
                left: 4,
                right: 5,
                pivot: 3,
                result: vec![],
            },
        ];
        assert_eq!(sep_resolution_proof_size(&steps), 3);
    }

    // -----------------------------------------------------------------------
    // 12-14: Tree-to-DAG conversion
    // -----------------------------------------------------------------------

    #[test]
    fn test_tree_to_dag_single_step() {
        // Tree: Leaf(0) resolve Leaf(1) on pivot 1
        let tree = vec![SepTreeResStep {
            left: SepTreeNode::Leaf(0),
            right: SepTreeNode::Leaf(1),
            pivot: 1,
        }];
        let dag = tree_resolution_to_dag(&tree, 2);
        assert_eq!(dag.len(), 1);
        assert_eq!(dag[0].left, 0);
        assert_eq!(dag[0].right, 1);
        assert_eq!(dag[0].pivot, 1);
    }

    #[test]
    fn test_tree_to_dag_two_steps() {
        // Step 0: Leaf(0) resolve Leaf(1) on 1
        // Step 1: Leaf(2) resolve Leaf(0) on 2  (reuse of Leaf(0))
        let tree = vec![
            SepTreeResStep {
                left: SepTreeNode::Leaf(0),
                right: SepTreeNode::Leaf(1),
                pivot: 1,
            },
            SepTreeResStep {
                left: SepTreeNode::Leaf(2),
                right: SepTreeNode::Leaf(0),
                pivot: 2,
            },
        ];
        let dag = tree_resolution_to_dag(&tree, 3);
        assert_eq!(dag.len(), 2);
        // First step references inputs 0,1; second references input 2 and 0.
        assert_eq!(dag[1].left, 2);
        assert_eq!(dag[1].right, 0);
    }

    #[test]
    fn test_tree_to_dag_empty() {
        let dag = tree_resolution_to_dag(&[], 0);
        assert!(dag.is_empty());
    }

    // -----------------------------------------------------------------------
    // 31: ProofVerifyResult fields
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_verify_result_errors_collected() {
        let clauses = vec![vec![1], vec![-1]];
        let steps = vec![
            SepResolutionStep {
                left: 0,
                right: 1,
                pivot: 1,
                result: vec![99],
            }, // wrong result
            SepResolutionStep {
                left: 0,
                right: 1,
                pivot: 1,
                result: vec![],
            }, // correct
        ];
        let r = verify_resolution_proof(&clauses, &steps);
        assert!(!r.valid);
        assert_eq!(r.errors.len(), 1);
        // First step failed, second succeeded.
        assert_eq!(r.steps_verified, 1);
        assert!(r.derived_empty);
    }
}
