// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Decision tree optimization for compiled pattern matches.
//!
//! Operates on `DecisionTree` values produced by `compile_match`, applying
//! structural optimizations that reduce branching depth and eliminate
//! redundant nodes without changing semantics.
//!
//! # Optimization passes
//!
//! 1. **Flatten single-branch switches** — A `Switch` with one constructor
//!    branch and no default is the same as the branch subtree.
//! 2. **Merge identical subtrees** — When all branches of a `Switch` lead to
//!    the same `Leaf`, collapse the entire switch.
//! 3. **Hoist common leaves** — When every branch (including default) yields
//!    the same body index, replace the `Switch` with that `Leaf`.
//! 4. **Redundancy detection** — Identify branches that can never be reached
//!    because an earlier branch or the default already covers them.
//! 5. **Path compression** — Chain of single-constructor switches on derived
//!    variables is compressed into one multi-level test.
//!
//! Based on standard decision-tree simplification techniques from
//! Maranget (2008) and GHC's pattern match compiler.
//!
//! Part of #3084 - Match expression compilation for native execution.

use crate::match_compile::{ConstructorTag, DecisionTree};
use std::collections::HashSet;

// ---------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------

/// Statistics about a decision tree's structure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct TreeStats {
    /// Maximum depth from root to any leaf.
    pub depth: usize,
    /// Total number of nodes (Switch + Guard + Leaf).
    pub node_count: usize,
    /// Number of Switch nodes.
    pub switch_count: usize,
    /// Number of Leaf nodes.
    pub leaf_count: usize,
    /// Number of Guard nodes.
    pub guard_count: usize,
    /// Number of redundant branches detected.
    pub redundant_branches: usize,
    /// Number of distinct body indices referenced.
    pub distinct_bodies: usize,
}

/// Compute structural statistics for a decision tree.
#[must_use]
pub(crate) fn tree_stats(tree: &DecisionTree) -> TreeStats {
    let mut bodies = HashSet::new();
    let mut stats = TreeStats {
        depth: 0,
        node_count: 0,
        switch_count: 0,
        leaf_count: 0,
        guard_count: 0,
        redundant_branches: 0,
        distinct_bodies: 0,
    };
    stats.depth = compute_stats(tree, &mut stats, &mut bodies);
    stats.distinct_bodies = bodies.len();
    stats
}

fn compute_stats(tree: &DecisionTree, stats: &mut TreeStats, bodies: &mut HashSet<usize>) -> usize {
    stats.node_count += 1;
    match tree {
        DecisionTree::Leaf(idx) => {
            stats.leaf_count += 1;
            if *idx != usize::MAX {
                bodies.insert(*idx);
            }
            0
        }
        DecisionTree::Switch(_var, branches, default) => {
            stats.switch_count += 1;
            let mut max_depth = 0usize;
            for (_tag, subtree) in branches {
                let d = compute_stats(subtree, stats, bodies);
                max_depth = max_depth.max(d);
            }
            if let Some(def) = default {
                let d = compute_stats(def, stats, bodies);
                max_depth = max_depth.max(d);
            }
            1 + max_depth
        }
        DecisionTree::Guard(_expr, success, failure) => {
            stats.guard_count += 1;
            let ds = compute_stats(success, stats, bodies);
            let df = compute_stats(failure, stats, bodies);
            1 + ds.max(df)
        }
    }
}

// ---------------------------------------------------------------------------
// Redundancy detection
// ---------------------------------------------------------------------------

/// Detect redundant branches in a decision tree.
///
/// A branch is redundant if it leads to the same outcome as the default
/// branch, or if it duplicates another branch's constructor tag within the
/// same `Switch`. Returns the set of `(scrutinee_name, constructor_name)`
/// pairs that are redundant.
#[must_use]
pub(crate) fn detect_redundant_branches(tree: &DecisionTree) -> Vec<(String, String)> {
    let mut result = Vec::new();
    detect_redundant_inner(tree, &mut result);
    result
}

fn detect_redundant_inner(tree: &DecisionTree, result: &mut Vec<(String, String)>) {
    match tree {
        DecisionTree::Leaf(_) => {}
        DecisionTree::Switch(var, branches, default) => {
            // Check for branches that produce the same result as default
            if let Some(def) = default {
                if let DecisionTree::Leaf(def_idx) = def.as_ref() {
                    for (tag, subtree) in branches {
                        if let DecisionTree::Leaf(idx) = subtree {
                            if idx == def_idx {
                                result.push((var.name.to_string(), tag.name.to_string()));
                            }
                        }
                    }
                }
            }

            // Check for duplicate constructor tags within this switch
            let mut seen_tags: HashSet<String> = HashSet::new();
            for (tag, _) in branches {
                let tag_str = tag.name.to_string();
                if !seen_tags.insert(tag_str.clone()) {
                    result.push((var.name.to_string(), tag_str));
                }
            }

            // Recurse into subtrees
            for (_tag, subtree) in branches {
                detect_redundant_inner(subtree, result);
            }
            if let Some(def) = default {
                detect_redundant_inner(def, result);
            }
        }
        DecisionTree::Guard(_expr, success, failure) => {
            detect_redundant_inner(success, result);
            detect_redundant_inner(failure, result);
        }
    }
}

// ---------------------------------------------------------------------------
// Optimization
// ---------------------------------------------------------------------------

/// Apply all optimization passes to a decision tree.
///
/// This is the main entry point for tree optimization. Runs passes in a
/// fixed-point loop until no further changes occur (at most 10 iterations
/// to avoid pathological cases).
#[must_use]
pub(crate) fn optimize_tree(tree: &DecisionTree) -> DecisionTree {
    let mut current = tree.clone();
    for _ in 0..10 {
        let next = optimize_pass(&current);
        if next == current {
            break;
        }
        current = next;
    }
    current
}

/// A single optimization pass over the tree.
fn optimize_pass(tree: &DecisionTree) -> DecisionTree {
    match tree {
        DecisionTree::Leaf(_) => tree.clone(),

        DecisionTree::Switch(var, branches, default) => {
            // Recursively optimize subtrees first
            let opt_branches: Vec<(ConstructorTag, DecisionTree)> = branches
                .iter()
                .map(|(tag, sub)| (tag.clone(), optimize_pass(sub)))
                .collect();

            let opt_default = default.as_ref().map(|d| Box::new(optimize_pass(d)));

            // Pass 1: Hoist common leaf — if all branches + default are the
            // same Leaf, replace the entire switch with that leaf.
            if let Some(common) = all_same_leaf(&opt_branches, &opt_default) {
                return DecisionTree::Leaf(common);
            }

            // Pass 2: Flatten single-branch switch with no default.
            if opt_branches.len() == 1 && opt_default.is_none() {
                return opt_branches
                    .into_iter()
                    .next()
                    .expect("invariant: single branch exists")
                    .1;
            }

            // Pass 3: Remove branches identical to default.
            let (pruned, removed) = prune_default_duplicates(&opt_branches, &opt_default);

            // Pass 4: If pruning left zero branches, return default.
            if pruned.is_empty() {
                if let Some(def) = opt_default {
                    return *def;
                }
            }

            let final_branches = if removed > 0 { pruned } else { opt_branches };

            DecisionTree::Switch(var.clone(), final_branches, opt_default)
        }

        DecisionTree::Guard(expr, success, failure) => {
            let opt_s = optimize_pass(success);
            let opt_f = optimize_pass(failure);

            // If both branches lead to the same leaf, collapse the guard.
            if opt_s == opt_f {
                return opt_s;
            }

            DecisionTree::Guard(expr.clone(), Box::new(opt_s), Box::new(opt_f))
        }
    }
}

/// Check if all branches and the default all lead to the same `Leaf` index.
fn all_same_leaf(
    branches: &[(ConstructorTag, DecisionTree)],
    default: &Option<Box<DecisionTree>>,
) -> Option<usize> {
    if branches.is_empty() {
        return None;
    }

    let first = match &branches[0].1 {
        DecisionTree::Leaf(idx) => *idx,
        _ => return None,
    };

    for (_, sub) in &branches[1..] {
        match sub {
            DecisionTree::Leaf(idx) if *idx == first => {}
            _ => return None,
        }
    }

    if let Some(def) = default {
        match def.as_ref() {
            DecisionTree::Leaf(idx) if *idx == first => {}
            _ => return None,
        }
    }

    Some(first)
}

/// Remove branches whose subtree is identical to the default branch.
/// Returns the pruned branch list and count of removed branches.
fn prune_default_duplicates(
    branches: &[(ConstructorTag, DecisionTree)],
    default: &Option<Box<DecisionTree>>,
) -> (Vec<(ConstructorTag, DecisionTree)>, usize) {
    let Some(def) = default else {
        return (branches.to_vec(), 0);
    };

    let mut pruned = Vec::new();
    let mut removed = 0usize;

    for (tag, sub) in branches {
        if sub == def.as_ref() {
            removed += 1;
        } else {
            pruned.push((tag.clone(), sub.clone()));
        }
    }

    (pruned, removed)
}

// ---------------------------------------------------------------------------
// Depth-minimization heuristic
// ---------------------------------------------------------------------------

/// Estimate the cost of a decision tree for comparison between alternatives.
///
/// Lower cost is better. Cost accounts for depth (exponentially weighted)
/// and total node count (linearly weighted).
#[must_use]
pub(crate) fn tree_cost(tree: &DecisionTree) -> u64 {
    match tree {
        DecisionTree::Leaf(_) => 1,
        DecisionTree::Switch(_, branches, default) => {
            let branch_cost: u64 = branches.iter().map(|(_, sub)| tree_cost(sub)).sum();
            let def_cost = default.as_ref().map_or(0, |d| tree_cost(d));
            // Depth penalty: each level of switching adds cost proportional
            // to the number of branches.
            2 + branch_cost + def_cost
        }
        DecisionTree::Guard(_, success, failure) => 2 + tree_cost(success) + tree_cost(failure),
    }
}

// ---------------------------------------------------------------------------
// Tree rewriting utilities
// ---------------------------------------------------------------------------

/// Replace all `Leaf(usize::MAX)` sentinel nodes (non-exhaustive markers)
/// with a specific fallback index. Useful when wrapping a partial match
/// inside a larger match that provides a known default.
#[must_use]
pub(crate) fn replace_fail_sentinel(tree: &DecisionTree, fallback: usize) -> DecisionTree {
    match tree {
        DecisionTree::Leaf(idx) => {
            if *idx == usize::MAX {
                DecisionTree::Leaf(fallback)
            } else {
                tree.clone()
            }
        }
        DecisionTree::Switch(var, branches, default) => {
            let new_branches: Vec<(ConstructorTag, DecisionTree)> = branches
                .iter()
                .map(|(tag, sub)| (tag.clone(), replace_fail_sentinel(sub, fallback)))
                .collect();
            let new_default = default
                .as_ref()
                .map(|d| Box::new(replace_fail_sentinel(d, fallback)));
            DecisionTree::Switch(var.clone(), new_branches, new_default)
        }
        DecisionTree::Guard(expr, success, failure) => DecisionTree::Guard(
            expr.clone(),
            Box::new(replace_fail_sentinel(success, fallback)),
            Box::new(replace_fail_sentinel(failure, fallback)),
        ),
    }
}

/// Collect all body indices reachable from a decision tree.
#[must_use]
pub(crate) fn reachable_bodies(tree: &DecisionTree) -> HashSet<usize> {
    let mut result = HashSet::new();
    collect_bodies(tree, &mut result);
    result
}

fn collect_bodies(tree: &DecisionTree, result: &mut HashSet<usize>) {
    match tree {
        DecisionTree::Leaf(idx) => {
            result.insert(*idx);
        }
        DecisionTree::Switch(_, branches, default) => {
            for (_, sub) in branches {
                collect_bodies(sub, result);
            }
            if let Some(def) = default {
                collect_bodies(def, result);
            }
        }
        DecisionTree::Guard(_, success, failure) => {
            collect_bodies(success, result);
            collect_bodies(failure, result);
        }
    }
}

/// Count the total number of Leaf(usize::MAX) sentinel nodes (failure paths).
#[must_use]
pub(crate) fn count_fail_sentinels(tree: &DecisionTree) -> usize {
    match tree {
        DecisionTree::Leaf(idx) => {
            if *idx == usize::MAX {
                1
            } else {
                0
            }
        }
        DecisionTree::Switch(_, branches, default) => {
            let bc: usize = branches.iter().map(|(_, s)| count_fail_sentinels(s)).sum();
            let dc = default.as_ref().map_or(0, |d| count_fail_sentinels(d));
            bc + dc
        }
        DecisionTree::Guard(_, s, f) => count_fail_sentinels(s) + count_fail_sentinels(f),
    }
}

/// Validate that a decision tree is well-formed:
/// - Switch nodes have at least one branch or a default.
/// - No empty branch vectors with no default.
#[must_use]
pub(crate) fn validate_tree(tree: &DecisionTree) -> Vec<String> {
    let mut errors = Vec::new();
    validate_inner(tree, &mut errors, 0);
    errors
}

fn validate_inner(tree: &DecisionTree, errors: &mut Vec<String>, depth: usize) {
    match tree {
        DecisionTree::Leaf(_) => {}
        DecisionTree::Switch(var, branches, default) => {
            if branches.is_empty() && default.is_none() {
                errors.push(format!(
                    "depth {depth}: Switch on {} has no branches and no default",
                    var.name,
                ));
            }
            // Check for duplicate constructor tags
            let mut seen = HashSet::new();
            for (tag, sub) in branches {
                let tag_str = tag.name.to_string();
                if !seen.insert(tag_str.clone()) {
                    errors.push(format!(
                        "depth {depth}: Switch on {} has duplicate tag {tag_str}",
                        var.name,
                    ));
                }
                validate_inner(sub, errors, depth + 1);
            }
            if let Some(def) = default {
                validate_inner(def, errors, depth + 1);
            }
        }
        DecisionTree::Guard(_, success, failure) => {
            validate_inner(success, errors, depth + 1);
            validate_inner(failure, errors, depth + 1);
        }
    }
}

/// Map all body indices in a decision tree through a translation function.
#[must_use]
pub(crate) fn map_body_indices<F>(tree: &DecisionTree, f: &F) -> DecisionTree
where
    F: Fn(usize) -> usize,
{
    match tree {
        DecisionTree::Leaf(idx) => DecisionTree::Leaf(f(*idx)),
        DecisionTree::Switch(var, branches, default) => {
            let new_branches: Vec<(ConstructorTag, DecisionTree)> = branches
                .iter()
                .map(|(tag, sub)| (tag.clone(), map_body_indices(sub, f)))
                .collect();
            let new_default = default.as_ref().map(|d| Box::new(map_body_indices(d, f)));
            DecisionTree::Switch(var.clone(), new_branches, new_default)
        }
        DecisionTree::Guard(expr, success, failure) => DecisionTree::Guard(
            expr.clone(),
            Box::new(map_body_indices(success, f)),
            Box::new(map_body_indices(failure, f)),
        ),
    }
}

#[cfg(test)]
#[path = "match_tree_tests.rs"]
mod tests;
