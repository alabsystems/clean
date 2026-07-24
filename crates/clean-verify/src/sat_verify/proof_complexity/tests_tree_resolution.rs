// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dedicated tests for tree_resolution.rs — TreeNode, TreeResolutionProof,
//! verify_tree_resolution, tree_resolution_size, and is_tree_like.

use super::resolution::ResolutionProof;
use super::tree_resolution::*;

// -----------------------------------------------------------------------
// Helper builders
// -----------------------------------------------------------------------

fn leaf(lits: Vec<i32>) -> TreeNode {
    TreeNode::Axiom(lits)
}

fn resolve(left: TreeNode, right: TreeNode, pivot: i32, result: Vec<i32>) -> TreeNode {
    TreeNode::Resolve {
        left: Box::new(left),
        right: Box::new(right),
        pivot,
        result,
    }
}

fn proof_of(root: TreeNode) -> TreeResolutionProof {
    TreeResolutionProof { root }
}

// =======================================================================
// TreeNode::clause
// =======================================================================

#[test]
fn test_clause_axiom_single_literal() {
    let n = leaf(vec![5]);
    assert_eq!(n.clause(), &vec![5]);
}

#[test]
fn test_clause_axiom_multiple_literals() {
    let n = leaf(vec![1, -2, 3]);
    assert_eq!(n.clause(), &vec![1, -2, 3]);
}

#[test]
fn test_clause_axiom_empty() {
    let n = leaf(vec![]);
    assert!(n.clause().is_empty());
}

#[test]
fn test_clause_resolve_returns_result() {
    let n = resolve(leaf(vec![1, 2]), leaf(vec![-1, 3]), 1, vec![2, 3]);
    assert_eq!(n.clause(), &vec![2, 3]);
}

#[test]
fn test_clause_resolve_empty_result() {
    let n = resolve(leaf(vec![1]), leaf(vec![-1]), 1, vec![]);
    assert!(n.clause().is_empty());
}

// =======================================================================
// TreeNode::size
// =======================================================================

#[test]
fn test_size_single_leaf() {
    assert_eq!(leaf(vec![1]).size(), 1);
}

#[test]
fn test_size_simple_resolve() {
    let t = resolve(leaf(vec![1]), leaf(vec![-1]), 1, vec![]);
    assert_eq!(t.size(), 3);
}

#[test]
fn test_size_left_heavy_tree() {
    // Left subtree has depth 2, right is a leaf.
    let inner = resolve(leaf(vec![1, 2]), leaf(vec![-1, 3]), 1, vec![2, 3]);
    let root = resolve(inner, leaf(vec![-2, -3]), 2, vec![3, -3]);
    // 5 nodes: 3 leaves + 2 internal
    assert_eq!(root.size(), 5);
}

#[test]
fn test_size_right_heavy_tree() {
    let inner = resolve(leaf(vec![-1, 3]), leaf(vec![1, 2]), 1, vec![2, 3]);
    let root = resolve(leaf(vec![-2, -3]), inner, 2, vec![3, -3]);
    assert_eq!(root.size(), 5);
}

#[test]
fn test_size_balanced_depth_two() {
    let l = resolve(leaf(vec![1, 2]), leaf(vec![-1, 2]), 1, vec![2]);
    let r = resolve(leaf(vec![3, 4]), leaf(vec![-3, 4]), 3, vec![4]);
    let root = resolve(l, r, 2, vec![4]);
    // 7 nodes: 4 leaves + 3 internal
    assert_eq!(root.size(), 7);
}

// =======================================================================
// TreeNode::depth
// =======================================================================

#[test]
fn test_depth_leaf_is_zero() {
    assert_eq!(leaf(vec![1]).depth(), 0);
}

#[test]
fn test_depth_one_resolve() {
    let t = resolve(leaf(vec![1]), leaf(vec![-1]), 1, vec![]);
    assert_eq!(t.depth(), 1);
}

#[test]
fn test_depth_left_heavy() {
    let inner = resolve(leaf(vec![1, 2]), leaf(vec![-1, 3]), 1, vec![2, 3]);
    let root = resolve(inner, leaf(vec![-2]), 2, vec![3]);
    assert_eq!(root.depth(), 2);
}

#[test]
fn test_depth_right_heavy() {
    let inner = resolve(leaf(vec![-1, 3]), leaf(vec![1, 2]), 1, vec![2, 3]);
    let root = resolve(leaf(vec![-2]), inner, 2, vec![3]);
    assert_eq!(root.depth(), 2);
}

#[test]
fn test_depth_balanced_depth_two() {
    let l = resolve(leaf(vec![1, 2]), leaf(vec![-1, 2]), 1, vec![2]);
    let r = resolve(leaf(vec![3, -2]), leaf(vec![-3, -2]), 3, vec![-2]);
    let root = resolve(l, r, 2, vec![]);
    assert_eq!(root.depth(), 2);
}

#[test]
fn test_depth_chain_three() {
    // Linear chain: depth 3
    let n1 = resolve(leaf(vec![1, 2]), leaf(vec![-1, 3]), 1, vec![2, 3]);
    let n2 = resolve(n1, leaf(vec![-2, 4]), 2, vec![3, 4]);
    let n3 = resolve(n2, leaf(vec![-3, -4]), 3, vec![4, -4]);
    assert_eq!(n3.depth(), 3);
}

// =======================================================================
// tree_resolution_size
// =======================================================================

#[test]
fn test_tree_resolution_size_leaf_proof() {
    let p = proof_of(leaf(vec![]));
    assert_eq!(tree_resolution_size(&p), 1);
}

#[test]
fn test_tree_resolution_size_matches_root_size() {
    let root = resolve(leaf(vec![1]), leaf(vec![-1]), 1, vec![]);
    let p = proof_of(root.clone());
    assert_eq!(tree_resolution_size(&p), root.size());
}

#[test]
fn test_tree_resolution_size_five_node_tree() {
    let inner = resolve(leaf(vec![1, 2]), leaf(vec![-1, 2]), 1, vec![2]);
    let root = resolve(inner, leaf(vec![-2]), 2, vec![]);
    let p = proof_of(root);
    assert_eq!(tree_resolution_size(&p), 5);
}

// =======================================================================
// verify_tree_resolution — valid proofs
// =======================================================================

#[test]
fn test_verify_simple_refutation() {
    let axioms = vec![vec![1], vec![-1]];
    let p = proof_of(resolve(leaf(vec![1]), leaf(vec![-1]), 1, vec![]));
    verify_tree_resolution(&p, &axioms).expect("valid refutation");
}

#[test]
fn test_verify_two_level_refutation() {
    let axioms = vec![vec![1, 2], vec![-1, 2], vec![-2]];
    let inner = resolve(leaf(vec![1, 2]), leaf(vec![-1, 2]), 1, vec![2]);
    let root = resolve(inner, leaf(vec![-2]), 2, vec![]);
    let p = proof_of(root);
    verify_tree_resolution(&p, &axioms).expect("valid two-level refutation");
}

#[test]
fn test_verify_three_level_refutation() {
    // (a v b) (-a v b) (-b v c) (-c)
    let axioms = vec![vec![1, 2], vec![-1, 2], vec![-2, 3], vec![-3]];
    let n1 = resolve(leaf(vec![1, 2]), leaf(vec![-1, 2]), 1, vec![2]);
    let n2 = resolve(n1, leaf(vec![-2, 3]), 2, vec![3]);
    let root = resolve(n2, leaf(vec![-3]), 3, vec![]);
    let p = proof_of(root);
    verify_tree_resolution(&p, &axioms).expect("valid three-level refutation");
}

#[test]
fn test_verify_pivot_negative_in_left() {
    // Left has -1, right has 1. Pivot = 1. verify_node allows either polarity.
    let axioms = vec![vec![-1, 2], vec![1]];
    let root = resolve(leaf(vec![-1, 2]), leaf(vec![1]), 1, vec![2]);
    // Not a refutation (result is [2]), but individual nodes should verify.
    // We test that the node verification works, even though full proof fails.
    let p = proof_of(root);
    let err = verify_tree_resolution(&p, &axioms).unwrap_err();
    assert!(err.contains("not the empty clause"));
}

#[test]
fn test_verify_axiom_with_duplicate_literals() {
    // Axiom [1, 1] should match against [1, 1] after sort+dedup = [1].
    let axioms = vec![vec![1, 1], vec![-1]];
    let root = resolve(leaf(vec![1, 1]), leaf(vec![-1]), 1, vec![]);
    let p = proof_of(root);
    verify_tree_resolution(&p, &axioms).expect("duplicates normalized");
}

#[test]
fn test_verify_axiom_out_of_order_matches() {
    // Axiom in proof is [2, 1], formula has [1, 2]. Should match after sort.
    let axioms = vec![vec![1, 2], vec![-1, -2]];
    let root = resolve(leaf(vec![2, 1]), leaf(vec![-1, -2]), 1, vec![2, -2]);
    // Not a refutation, but axiom matching should succeed.
    let p = proof_of(root);
    let err = verify_tree_resolution(&p, &axioms).unwrap_err();
    assert!(err.contains("not the empty clause"));
}

// =======================================================================
// verify_tree_resolution — invalid proofs (error paths)
// =======================================================================

#[test]
fn test_verify_rejects_bad_axiom() {
    let axioms = vec![vec![1], vec![-1]];
    let p = proof_of(leaf(vec![99]));
    let err = verify_tree_resolution(&p, &axioms).unwrap_err();
    assert!(err.contains("not in the input formula"));
}

#[test]
fn test_verify_rejects_non_refutation_leaf() {
    let axioms = vec![vec![1]];
    let p = proof_of(leaf(vec![1]));
    let err = verify_tree_resolution(&p, &axioms).unwrap_err();
    assert!(err.contains("not the empty clause"));
}

#[test]
fn test_verify_rejects_non_refutation_resolve() {
    let axioms = vec![vec![1, 2], vec![-1, 3]];
    let root = resolve(leaf(vec![1, 2]), leaf(vec![-1, 3]), 1, vec![2, 3]);
    let p = proof_of(root);
    let err = verify_tree_resolution(&p, &axioms).unwrap_err();
    assert!(err.contains("not the empty clause"));
}

#[test]
fn test_verify_rejects_wrong_pivot() {
    // Pivot 2 is not present in complementary form.
    let axioms = vec![vec![1], vec![-1]];
    let root = resolve(leaf(vec![1]), leaf(vec![-1]), 2, vec![]);
    let p = proof_of(root);
    let err = verify_tree_resolution(&p, &axioms).unwrap_err();
    assert!(err.contains("pivot"));
}

#[test]
fn test_verify_rejects_wrong_result_clause() {
    // Correct resolvent of [1, 2] and [-1, 3] on 1 is [2, 3], not [2].
    let axioms = vec![vec![1, 2], vec![-1, 3]];
    let root = resolve(leaf(vec![1, 2]), leaf(vec![-1, 3]), 1, vec![2]);
    let p = proof_of(root);
    let err = verify_tree_resolution(&p, &axioms).unwrap_err();
    assert!(err.contains("result clause mismatch"));
}

#[test]
fn test_verify_rejects_extra_literal_in_result() {
    // Result has an extra literal not in either parent.
    let axioms = vec![vec![1], vec![-1]];
    let root = resolve(leaf(vec![1]), leaf(vec![-1]), 1, vec![5]);
    let p = proof_of(root);
    let err = verify_tree_resolution(&p, &axioms).unwrap_err();
    assert!(err.contains("result clause mismatch"));
}

#[test]
fn test_verify_rejects_bad_axiom_in_subtree() {
    // Left subtree has a bad axiom.
    let axioms = vec![vec![1], vec![-1]];
    let inner = resolve(leaf(vec![99]), leaf(vec![-1]), 1, vec![]);
    let root = resolve(inner, leaf(vec![1]), 1, vec![]);
    let p = proof_of(root);
    let err = verify_tree_resolution(&p, &axioms).unwrap_err();
    assert!(err.contains("not in the input formula"));
}

#[test]
fn test_verify_rejects_non_empty_root_after_valid_subtrees() {
    // All subtree nodes are valid, but root resolvent is non-empty.
    let axioms = vec![vec![1, 2], vec![-1, 3]];
    let root = resolve(leaf(vec![1, 2]), leaf(vec![-1, 3]), 1, vec![2, 3]);
    let p = proof_of(root);
    assert!(verify_tree_resolution(&p, &axioms).is_err());
}

// =======================================================================
// verify_tree_resolution — edge cases
// =======================================================================

#[test]
fn test_verify_empty_axiom_set_rejects() {
    let axioms: Vec<Vec<i32>> = vec![];
    let p = proof_of(leaf(vec![1]));
    assert!(verify_tree_resolution(&p, &axioms).is_err());
}

#[test]
fn test_verify_axiom_is_empty_clause() {
    // If the formula contains the empty clause, a trivial refutation exists.
    let axioms = vec![vec![]];
    let p = proof_of(leaf(vec![]));
    verify_tree_resolution(&p, &axioms).expect("empty axiom is trivial refutation");
}

#[test]
fn test_verify_large_literals() {
    let axioms = vec![vec![1000], vec![-1000]];
    let root = resolve(leaf(vec![1000]), leaf(vec![-1000]), 1000, vec![]);
    let p = proof_of(root);
    verify_tree_resolution(&p, &axioms).expect("large literal values work");
}

#[test]
fn test_verify_reused_axiom_in_tree() {
    // Same axiom used twice (as separate leaves). Tree resolution allows this.
    let axioms = vec![vec![1, 2], vec![-1, 2], vec![-2]];
    // Resolve [1,2] and [-1,2] on 1 => [2], then resolve [2] and [-2] on 2 => [].
    // A second subtree also using [1,2] is fine in tree resolution.
    let inner = resolve(leaf(vec![1, 2]), leaf(vec![-1, 2]), 1, vec![2]);
    let root = resolve(inner, leaf(vec![-2]), 2, vec![]);
    let p = proof_of(root);
    verify_tree_resolution(&p, &axioms).expect("reused axioms are fine");
}

// =======================================================================
// TreeNode / TreeResolutionProof — Clone and PartialEq
// =======================================================================

#[test]
fn test_tree_node_clone() {
    let n = resolve(leaf(vec![1, 2]), leaf(vec![-1, 3]), 1, vec![2, 3]);
    let n2 = n.clone();
    assert_eq!(n, n2);
}

#[test]
fn test_tree_node_eq_axioms() {
    assert_eq!(leaf(vec![1, 2]), leaf(vec![1, 2]));
    assert_ne!(leaf(vec![1, 2]), leaf(vec![2, 1]));
}

#[test]
fn test_tree_node_eq_resolve_different_pivot() {
    let a = resolve(leaf(vec![1]), leaf(vec![-1]), 1, vec![]);
    let b = resolve(leaf(vec![1]), leaf(vec![-1]), 2, vec![]);
    assert_ne!(a, b);
}

#[test]
fn test_tree_resolution_proof_clone() {
    let p = proof_of(resolve(leaf(vec![1]), leaf(vec![-1]), 1, vec![]));
    let p2 = p.clone();
    assert_eq!(p.root, p2.root);
}

// =======================================================================
// is_tree_like — positive cases
// =======================================================================

#[test]
fn test_is_tree_like_empty_proof() {
    let proof = ResolutionProof::new();
    assert!(is_tree_like(&proof));
}

#[test]
fn test_is_tree_like_single_input() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1]);
    assert!(is_tree_like(&proof));
}

#[test]
fn test_is_tree_like_two_inputs_no_resolve() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1]);
    proof.add_input(vec![-1]);
    assert!(is_tree_like(&proof));
}

#[test]
fn test_is_tree_like_simple_refutation() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1]);
    proof.add_input(vec![-1]);
    proof.add_resolve(0, 1, 1).expect("resolve");
    assert!(is_tree_like(&proof));
}

#[test]
fn test_is_tree_like_chain_refutation() {
    // (a) (-a v b) (-b) => resolve 0,1 on a => (b) => resolve 3,2 on b => ()
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1]); // 0
    proof.add_input(vec![-1, 2]); // 1
    proof.add_input(vec![-2]); // 2
    proof.add_resolve(0, 1, 1).expect("step 3"); // (b) = [2]
    proof.add_resolve(3, 2, 2).expect("step 4"); // () = []
    assert!(is_tree_like(&proof));
}

#[test]
fn test_is_tree_like_default_proof() {
    let proof = ResolutionProof::default();
    assert!(is_tree_like(&proof));
}

// =======================================================================
// is_tree_like — negative / boundary cases
// =======================================================================

#[test]
fn test_is_tree_like_inputs_only() {
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1, 2]);
    proof.add_input(vec![-1, 3]);
    proof.add_input(vec![-2, -3]);
    // No resolves: still tree-like (vacuously)
    assert!(is_tree_like(&proof));
}

#[test]
fn test_is_tree_like_single_step_refutation() {
    // Minimal possible refutation
    let mut proof = ResolutionProof::new();
    proof.add_input(vec![1]);
    proof.add_input(vec![-1]);
    proof.add_resolve(0, 1, 1).expect("resolve");
    assert!(is_tree_like(&proof));
    assert!(proof.verify());
}

// =======================================================================
// TreeNode::Debug formatting
// =======================================================================

#[test]
fn test_tree_node_debug_axiom() {
    let n = leaf(vec![1, -2]);
    let dbg = format!("{n:?}");
    assert!(dbg.contains("Axiom"));
    assert!(dbg.contains("1"));
    assert!(dbg.contains("-2"));
}

#[test]
fn test_tree_node_debug_resolve() {
    let n = resolve(leaf(vec![1]), leaf(vec![-1]), 1, vec![]);
    let dbg = format!("{n:?}");
    assert!(dbg.contains("Resolve"));
    assert!(dbg.contains("pivot: 1"));
}

// =======================================================================
// Larger integration scenarios
// =======================================================================

#[test]
fn test_verify_balanced_four_axiom_refutation() {
    // (a v b) (-a v b) (a v -b) (-a v -b) => unsat
    // Resolve on a: (b) and (-b)
    // Resolve on b: ()
    let axioms = vec![vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]];
    let l = resolve(leaf(vec![1, 2]), leaf(vec![-1, 2]), 1, vec![2]);
    let r = resolve(leaf(vec![1, -2]), leaf(vec![-1, -2]), 1, vec![-2]);
    let root = resolve(l, r, 2, vec![]);
    let p = proof_of(root);
    verify_tree_resolution(&p, &axioms).expect("balanced refutation");
    assert_eq!(tree_resolution_size(&p), 7);
    assert_eq!(p.root.depth(), 2);
}

#[test]
fn test_verify_chain_four_axiom_refutation() {
    // (a) (-a v b) (-b v c) (-c)
    let axioms = vec![vec![1], vec![-1, 2], vec![-2, 3], vec![-3]];
    let n1 = resolve(leaf(vec![1]), leaf(vec![-1, 2]), 1, vec![2]);
    let n2 = resolve(n1, leaf(vec![-2, 3]), 2, vec![3]);
    let root = resolve(n2, leaf(vec![-3]), 3, vec![]);
    let p = proof_of(root);
    verify_tree_resolution(&p, &axioms).expect("chain refutation");
    assert_eq!(tree_resolution_size(&p), 7);
    assert_eq!(p.root.depth(), 3);
}

#[test]
fn test_size_and_depth_differ_for_chain_vs_balanced() {
    // Chain of depth 3, size 7
    let chain = resolve(
        resolve(
            resolve(leaf(vec![1]), leaf(vec![-1, 2]), 1, vec![2]),
            leaf(vec![-2, 3]),
            2,
            vec![3],
        ),
        leaf(vec![-3]),
        3,
        vec![],
    );
    // Balanced of depth 2, size 7
    let balanced = resolve(
        resolve(leaf(vec![1, 2]), leaf(vec![-1, 2]), 1, vec![2]),
        resolve(leaf(vec![1, -2]), leaf(vec![-1, -2]), 1, vec![-2]),
        2,
        vec![],
    );
    assert_eq!(chain.size(), balanced.size());
    assert!(chain.depth() > balanced.depth());
}

#[test]
fn test_verify_with_multi_literal_resolve() {
    // (a v b v c) (-a v d) => resolvent (b v c v d)
    // (b v c v d) (-b v -c v -d) => cannot resolve to empty in one step
    // but we test multi-literal clause handling.
    let axioms = vec![vec![1, 2, 3], vec![-1, 4], vec![-2, -3, -4]];
    let n1 = resolve(leaf(vec![1, 2, 3]), leaf(vec![-1, 4]), 1, vec![2, 3, 4]);
    // Resolve on 2: (3 v 4 v -3 v -4) - no, need pivot in both clauses.
    // n1 = [2, 3, 4], axiom3 = [-2, -3, -4], resolve on 2 => [3, 4, -3, -4]
    let root = resolve(n1, leaf(vec![-2, -3, -4]), 2, vec![-4, -3, 3, 4]);
    let p = proof_of(root);
    // Not a refutation, but node verification should succeed.
    let err = verify_tree_resolution(&p, &axioms).unwrap_err();
    assert!(err.contains("not the empty clause"));
}

#[test]
fn test_verify_pivot_complementary_check_both_directions() {
    // verify_node checks has_pos (left has +pivot, right has -pivot)
    // OR has_neg (left has -pivot, right has +pivot).
    // Test the second direction: left has -1, right has 1.
    let axioms = vec![vec![-1, 2], vec![1, 3]];
    let root = resolve(leaf(vec![-1, 2]), leaf(vec![1, 3]), 1, vec![2, 3]);
    let p = proof_of(root);
    let err = verify_tree_resolution(&p, &axioms).unwrap_err();
    // Node verification passes (pivot found), but root is non-empty.
    assert!(err.contains("not the empty clause"));
}
