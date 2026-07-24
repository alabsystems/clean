// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Additional decision tree analysis and transformation utilities.
//!
//! Extends `match_tree` with subtree sharing analysis, branch-factor
//! statistics, path enumeration, DOT rendering, structural comparison,
//! depth-bounded extraction, and scrutinee collection.
//!
//! Part of #3084 - Match expression compilation for native execution.

use std::collections::{hash_map::DefaultHasher, HashMap, HashSet};
use std::fmt::Write;
use std::hash::{Hash, Hasher};

use clean_kernel::Name;

use crate::match_compile::{ConstructorTag, DecisionTree, Var};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct SubtreeHash(pub(crate) u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum SubtreePathStep {
    SwitchBranch(usize),
    SwitchDefault,
    GuardTrue,
    GuardFalse,
}

pub(crate) type SubtreePath = Vec<SubtreePathStep>;

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct SharingStats {
    pub(crate) total_nodes: usize,
    pub(crate) unique_nodes: usize,
    pub(crate) shared_nodes: usize,
    pub(crate) sharing_ratio: f64,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct BranchStats {
    pub(crate) min_factor: usize,
    pub(crate) max_factor: usize,
    pub(crate) avg_factor: f64,
    pub(crate) total_switches: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum PathStep {
    SwitchOn { var: Var, tag: ConstructorTag },
    GuardTrue,
    GuardFalse,
}

pub(crate) type TreePath = Vec<PathStep>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum TreeDiff {
    Same,
    DifferentLeaf,
    DifferentStructure,
    SubtreeDiff,
}

#[must_use]
pub(crate) fn hash_subtree(tree: &DecisionTree) -> HashMap<SubtreeHash, Vec<SubtreePath>> {
    let mut hashes = HashMap::new();
    let mut path = Vec::new();
    let _ = collect_subtree_hashes(tree, &mut path, &mut hashes);
    hashes
}

#[must_use]
pub(crate) fn sharing_stats(tree: &DecisionTree) -> SharingStats {
    let hashes = hash_subtree(tree);
    let total_nodes: usize = hashes.values().map(Vec::len).sum();
    let unique_nodes = hashes.len();
    let shared_nodes = total_nodes.saturating_sub(unique_nodes);
    let sharing_ratio = if total_nodes == 0 {
        0.0
    } else {
        shared_nodes as f64 / total_nodes as f64
    };
    SharingStats {
        total_nodes,
        unique_nodes,
        shared_nodes,
        sharing_ratio,
    }
}

#[must_use]
pub(crate) fn branch_stats(tree: &DecisionTree) -> BranchStats {
    let mut total_switches = 0usize;
    let mut total_factor = 0usize;
    let mut min_factor = usize::MAX;
    let mut max_factor = 0usize;
    collect_branch_stats(
        tree,
        &mut total_switches,
        &mut total_factor,
        &mut min_factor,
        &mut max_factor,
    );
    if total_switches == 0 {
        return BranchStats {
            min_factor: 0,
            max_factor: 0,
            avg_factor: 0.0,
            total_switches: 0,
        };
    }
    BranchStats {
        min_factor,
        max_factor,
        avg_factor: total_factor as f64 / total_switches as f64,
        total_switches,
    }
}

#[must_use]
pub(crate) fn enumerate_paths(tree: &DecisionTree) -> Vec<(TreePath, usize)> {
    let mut paths = Vec::new();
    let mut path = Vec::new();
    enumerate_paths_inner(tree, &mut path, &mut paths);
    paths
}

#[must_use]
pub(crate) fn tree_to_dot(tree: &DecisionTree) -> String {
    let mut out = String::new();
    let mut next_id = 0usize;
    let _ = writeln!(out, "digraph DecisionTree {{");
    let _ = writeln!(out, "  rankdir=TB;");
    let _ = emit_dot(tree, &mut out, &mut next_id);
    let _ = writeln!(out, "}}");
    out
}

#[must_use]
pub(crate) fn diff_trees(a: &DecisionTree, b: &DecisionTree) -> TreeDiff {
    match (a, b) {
        (DecisionTree::Leaf(x), DecisionTree::Leaf(y)) => {
            if x == y {
                TreeDiff::Same
            } else {
                TreeDiff::DifferentLeaf
            }
        }
        (
            DecisionTree::Switch(var_a, branches_a, default_a),
            DecisionTree::Switch(var_b, branches_b, default_b),
        ) => {
            if var_a != var_b
                || branches_a.len() != branches_b.len()
                || default_a.is_some() != default_b.is_some()
            {
                return TreeDiff::DifferentStructure;
            }
            for ((tag_a, sub_a), (tag_b, sub_b)) in branches_a.iter().zip(branches_b) {
                if tag_a != tag_b {
                    return TreeDiff::DifferentStructure;
                }
                if diff_trees(sub_a, sub_b) != TreeDiff::Same {
                    return TreeDiff::SubtreeDiff;
                }
            }
            match (default_a, default_b) {
                (Some(sub_a), Some(sub_b)) => {
                    if diff_trees(sub_a, sub_b) == TreeDiff::Same {
                        TreeDiff::Same
                    } else {
                        TreeDiff::SubtreeDiff
                    }
                }
                (None, None) => TreeDiff::Same,
                _ => TreeDiff::DifferentStructure,
            }
        }
        (DecisionTree::Guard(expr_a, yes_a, no_a), DecisionTree::Guard(expr_b, yes_b, no_b)) => {
            if expr_a != expr_b {
                return TreeDiff::DifferentStructure;
            }
            if diff_trees(yes_a, yes_b) == TreeDiff::Same
                && diff_trees(no_a, no_b) == TreeDiff::Same
            {
                TreeDiff::Same
            } else {
                TreeDiff::SubtreeDiff
            }
        }
        _ => TreeDiff::DifferentStructure,
    }
}

#[must_use]
pub(crate) fn extract_subtree(tree: &DecisionTree, max_depth: usize) -> DecisionTree {
    match tree {
        DecisionTree::Leaf(_) => tree.clone(),
        DecisionTree::Switch(var, branches, default) => {
            let new_branches = branches
                .iter()
                .map(|(tag, subtree)| {
                    let next = if max_depth == 0 {
                        DecisionTree::Leaf(usize::MAX)
                    } else {
                        extract_subtree(subtree, max_depth - 1)
                    };
                    (tag.clone(), next)
                })
                .collect();
            let new_default = default.as_ref().map(|subtree| {
                Box::new(if max_depth == 0 {
                    DecisionTree::Leaf(usize::MAX)
                } else {
                    extract_subtree(subtree, max_depth - 1)
                })
            });
            DecisionTree::Switch(var.clone(), new_branches, new_default)
        }
        DecisionTree::Guard(expr, yes, no) => {
            let yes = if max_depth == 0 {
                DecisionTree::Leaf(usize::MAX)
            } else {
                extract_subtree(yes, max_depth - 1)
            };
            let no = if max_depth == 0 {
                DecisionTree::Leaf(usize::MAX)
            } else {
                extract_subtree(no, max_depth - 1)
            };
            DecisionTree::Guard(expr.clone(), Box::new(yes), Box::new(no))
        }
    }
}

#[must_use]
pub(crate) fn collect_scrutinees(tree: &DecisionTree) -> Vec<Var> {
    let mut vars = Vec::new();
    let mut seen = HashSet::new();
    collect_scrutinees_inner(tree, &mut seen, &mut vars);
    vars
}

fn collect_subtree_hashes(
    tree: &DecisionTree,
    path: &mut SubtreePath,
    hashes: &mut HashMap<SubtreeHash, Vec<SubtreePath>>,
) -> SubtreeHash {
    let hash = match tree {
        DecisionTree::Leaf(idx) => hash_with(|state| {
            0u8.hash(state);
            idx.hash(state);
        }),
        DecisionTree::Switch(var, branches, default) => {
            let mut branch_hashes = Vec::with_capacity(branches.len());
            for (index, (tag, subtree)) in branches.iter().enumerate() {
                path.push(SubtreePathStep::SwitchBranch(index));
                let subtree_hash = collect_subtree_hashes(subtree, path, hashes);
                let _ = path.pop();
                branch_hashes.push((tag, subtree_hash));
            }
            let default_hash = if let Some(subtree) = default {
                path.push(SubtreePathStep::SwitchDefault);
                let subtree_hash = collect_subtree_hashes(subtree, path, hashes);
                let _ = path.pop();
                Some(subtree_hash)
            } else {
                None
            };
            hash_with(|state| {
                1u8.hash(state);
                var.hash(state);
                branches.len().hash(state);
                for (tag, subtree_hash) in &branch_hashes {
                    tag.hash(state);
                    subtree_hash.hash(state);
                }
                default_hash.hash(state);
            })
        }
        DecisionTree::Guard(expr, yes, no) => {
            path.push(SubtreePathStep::GuardTrue);
            let yes_hash = collect_subtree_hashes(yes, path, hashes);
            let _ = path.pop();
            path.push(SubtreePathStep::GuardFalse);
            let no_hash = collect_subtree_hashes(no, path, hashes);
            let _ = path.pop();
            hash_with(|state| {
                2u8.hash(state);
                expr.hash(state);
                yes_hash.hash(state);
                no_hash.hash(state);
            })
        }
    };
    hashes.entry(hash).or_default().push(path.clone());
    hash
}

fn hash_with(f: impl FnOnce(&mut DefaultHasher)) -> SubtreeHash {
    let mut hasher = DefaultHasher::new();
    f(&mut hasher);
    SubtreeHash(hasher.finish())
}

fn collect_branch_stats(
    tree: &DecisionTree,
    total_switches: &mut usize,
    total_factor: &mut usize,
    min_factor: &mut usize,
    max_factor: &mut usize,
) {
    match tree {
        DecisionTree::Leaf(_) => {}
        DecisionTree::Switch(_, branches, default) => {
            let factor = branches.len() + usize::from(default.is_some());
            *total_switches += 1;
            *total_factor += factor;
            *min_factor = (*min_factor).min(factor);
            *max_factor = (*max_factor).max(factor);
            for (_, subtree) in branches {
                collect_branch_stats(
                    subtree,
                    total_switches,
                    total_factor,
                    min_factor,
                    max_factor,
                );
            }
            if let Some(subtree) = default {
                collect_branch_stats(
                    subtree,
                    total_switches,
                    total_factor,
                    min_factor,
                    max_factor,
                );
            }
        }
        DecisionTree::Guard(_, yes, no) => {
            collect_branch_stats(yes, total_switches, total_factor, min_factor, max_factor);
            collect_branch_stats(no, total_switches, total_factor, min_factor, max_factor);
        }
    }
}

fn enumerate_paths_inner(
    tree: &DecisionTree,
    path: &mut TreePath,
    paths: &mut Vec<(TreePath, usize)>,
) {
    match tree {
        DecisionTree::Leaf(idx) => paths.push((path.clone(), *idx)),
        DecisionTree::Switch(var, branches, default) => {
            for (tag, subtree) in branches {
                path.push(PathStep::SwitchOn {
                    var: var.clone(),
                    tag: tag.clone(),
                });
                enumerate_paths_inner(subtree, path, paths);
                let _ = path.pop();
            }
            if let Some(subtree) = default {
                path.push(PathStep::SwitchOn {
                    var: var.clone(),
                    tag: default_path_tag(),
                });
                enumerate_paths_inner(subtree, path, paths);
                let _ = path.pop();
            }
        }
        DecisionTree::Guard(_, yes, no) => {
            path.push(PathStep::GuardTrue);
            enumerate_paths_inner(yes, path, paths);
            let _ = path.pop();
            path.push(PathStep::GuardFalse);
            enumerate_paths_inner(no, path, paths);
            let _ = path.pop();
        }
    }
}

fn emit_dot(tree: &DecisionTree, out: &mut String, next_id: &mut usize) -> usize {
    let node_id = *next_id;
    *next_id += 1;
    match tree {
        DecisionTree::Leaf(idx) => {
            let label = if *idx == usize::MAX {
                "Leaf fail".to_string()
            } else {
                format!("Leaf {idx}")
            };
            let _ = writeln!(
                out,
                "  n{node_id} [label=\"{}\", shape=box];",
                escape_dot(&label)
            );
        }
        DecisionTree::Switch(var, branches, default) => {
            let label = format!("Switch {}", var.name);
            let _ = writeln!(
                out,
                "  n{node_id} [label=\"{}\", shape=ellipse];",
                escape_dot(&label)
            );
            for (tag, subtree) in branches {
                let child_id = emit_dot(subtree, out, next_id);
                let _ = writeln!(
                    out,
                    "  n{node_id} -> n{child_id} [label=\"{}\"];",
                    escape_dot(&tag.name.to_string()),
                );
            }
            if let Some(subtree) = default {
                let child_id = emit_dot(subtree, out, next_id);
                let _ = writeln!(out, "  n{node_id} -> n{child_id} [label=\"default\"];");
            }
        }
        DecisionTree::Guard(expr, yes, no) => {
            let label = format!("Guard {}", expr);
            let _ = writeln!(
                out,
                "  n{node_id} [label=\"{}\", shape=diamond];",
                escape_dot(&label)
            );
            let yes_id = emit_dot(yes, out, next_id);
            let no_id = emit_dot(no, out, next_id);
            let _ = writeln!(out, "  n{node_id} -> n{yes_id} [label=\"true\"];");
            let _ = writeln!(out, "  n{node_id} -> n{no_id} [label=\"false\"];");
        }
    }
    node_id
}

fn escape_dot(text: &str) -> String {
    let mut escaped = String::with_capacity(text.len());
    for ch in text.chars() {
        match ch {
            '\\' => escaped.push_str("\\\\"),
            '"' => escaped.push_str("\\\""),
            '\n' => escaped.push_str("\\n"),
            _ => escaped.push(ch),
        }
    }
    escaped
}

fn default_path_tag() -> ConstructorTag {
    ConstructorTag {
        name: Name::from_string("__default__"),
        arity: 0,
    }
}

fn collect_scrutinees_inner(tree: &DecisionTree, seen: &mut HashSet<Var>, vars: &mut Vec<Var>) {
    match tree {
        DecisionTree::Leaf(_) => {}
        DecisionTree::Switch(var, branches, default) => {
            if seen.insert(var.clone()) {
                vars.push(var.clone());
            }
            for (_, subtree) in branches {
                collect_scrutinees_inner(subtree, seen, vars);
            }
            if let Some(subtree) = default {
                collect_scrutinees_inner(subtree, seen, vars);
            }
        }
        DecisionTree::Guard(_, yes, no) => {
            collect_scrutinees_inner(yes, seen, vars);
            collect_scrutinees_inner(no, seen, vars);
        }
    }
}
