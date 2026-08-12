// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended match compilation analysis and optimization.
//!
//! Extends `match_compile` with heuristic scoring, overlap detection,
//! exhaustiveness gap reporting, match statistics, decision tree metrics,
//! and multiple column selection strategies.
//!
//! Part of #3084 - Match expression compilation for native execution.

use std::collections::{HashMap, HashSet};

use clean_kernel::Name;

use crate::match_compile::{DecisionTree, MatchArm, Pattern, Var};

/// Errors from extended match compilation analysis.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum MatchCompileExtError {
    #[error("empty match matrix has no columns to analyze")]
    EmptyMatrix,
    // Staged diagnostic for the column-selection API. Nothing can raise it
    // yet: `pick_column_with_strategy` chooses the index itself, and the one
    // API that takes a column (`score_column_with_strategy`) is infallible.
    // Kept so the bounds contract stays expressible once a caller supplies a
    // column — 2026-07-31.
    #[allow(dead_code)]
    #[error("column index {col} out of bounds (max {max})")]
    ColumnOutOfBounds { col: usize, max: usize },
}

/// Strategy for selecting which column to split on during compilation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum ColumnStrategy {
    /// Always pick the first column (left-to-right).
    FirstColumn,
    /// Pick the column with the most distinct constructors.
    MostConstructors,
    /// Pick the column with the fewest wildcards/variables.
    FewestWildcards,
    /// Smallest branching factor, breaking ties by fewest wildcards.
    SmallestBranchingFactor,
}

/// Score for a single match arm based on pattern specificity.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct ArmScore {
    pub(crate) arm_idx: usize,
    pub(crate) specificity: usize,
    pub(crate) total_arity: usize,
    pub(crate) wildcard_count: usize,
    pub(crate) max_depth: usize,
}

/// Compute the heuristic score for a single arm.
#[must_use]
pub(crate) fn score_arm(arm: &MatchArm) -> ArmScore {
    let mut specificity = 0;
    let mut total_arity = 0;
    let mut wildcard_count = 0;
    let mut max_depth: usize = 0;
    for pat in &arm.patterns {
        let (spec, arity, wilds, depth) = score_pattern(pat);
        specificity += spec;
        total_arity += arity;
        wildcard_count += wilds;
        max_depth = max_depth.max(depth);
    }
    ArmScore {
        arm_idx: arm.body_idx,
        specificity,
        total_arity,
        wildcard_count,
        max_depth,
    }
}

/// Returns (specificity, arity, wildcards, depth).
fn score_pattern(pat: &Pattern) -> (usize, usize, usize, usize) {
    match pat {
        Pattern::Constructor(_, sub_pats) => {
            let (mut spec, mut arity, mut wilds, mut md) = (1, sub_pats.len(), 0, 1);
            for sp in sub_pats {
                let (s, a, w, d) = score_pattern(sp);
                spec += s;
                arity += a;
                wilds += w;
                md = md.max(1 + d);
            }
            (spec, arity, wilds, md)
        }
        Pattern::Literal(_) => (1, 0, 0, 1),
        Pattern::Variable(_) | Pattern::Wildcard => (0, 0, 1, 1),
        Pattern::Or(alts) => {
            let mut best = (0, 0, 1, 1);
            for alt in alts {
                let s = score_pattern(alt);
                if s.0 > best.0 {
                    best = s;
                }
            }
            best
        }
    }
}

/// Score all arms, returned in original order.
#[must_use]
pub(crate) fn score_arms(arms: &[MatchArm]) -> Vec<ArmScore> {
    arms.iter().map(score_arm).collect()
}

/// Arm indices sorted by decreasing specificity (most specific first).
#[must_use]
pub(crate) fn rank_arms_by_specificity(arms: &[MatchArm]) -> Vec<usize> {
    let mut scores: Vec<(usize, ArmScore)> = arms
        .iter()
        .enumerate()
        .map(|(i, arm)| (i, score_arm(arm)))
        .collect();
    scores.sort_by(|a, b| {
        b.1.specificity
            .cmp(&a.1.specificity)
            .then(a.1.wildcard_count.cmp(&b.1.wildcard_count))
            .then(a.0.cmp(&b.0))
    });
    scores.into_iter().map(|(i, _)| i).collect()
}

/// Score a column using the given strategy. Higher is better.
#[must_use]
pub(crate) fn score_column_with_strategy(
    arms: &[MatchArm],
    col: usize,
    strategy: ColumnStrategy,
) -> i64 {
    match strategy {
        ColumnStrategy::FirstColumn => -(col as i64),
        ColumnStrategy::MostConstructors => {
            let mut names: HashSet<&Name> = HashSet::new();
            for arm in arms {
                if col < arm.patterns.len() {
                    collect_ctor_names(&arm.patterns[col], &mut names);
                }
            }
            names.len() as i64
        }
        ColumnStrategy::FewestWildcards => {
            let mut wilds: i64 = 0;
            for arm in arms {
                if col >= arm.patterns.len() || is_wildcard_like(&arm.patterns[col]) {
                    wilds += 1;
                }
            }
            -wilds
        }
        ColumnStrategy::SmallestBranchingFactor => {
            let mut names: HashSet<&Name> = HashSet::new();
            let mut wilds: i64 = 0;
            for arm in arms {
                if col >= arm.patterns.len() || is_wildcard_like(&arm.patterns[col]) {
                    wilds += 1;
                } else {
                    collect_ctor_names(&arm.patterns[col], &mut names);
                }
            }
            let branching = names.len() as i64;
            if branching == 0 {
                return -1000 - wilds;
            }
            -(branching * 100 + wilds)
        }
    }
}

fn collect_ctor_names<'a>(pat: &'a Pattern, names: &mut HashSet<&'a Name>) {
    match pat {
        Pattern::Constructor(name, _) => {
            names.insert(name);
        }
        Pattern::Or(alts) => {
            for alt in alts {
                collect_ctor_names(alt, names);
            }
        }
        _ => {}
    }
}

fn is_wildcard_like(pat: &Pattern) -> bool {
    matches!(pat, Pattern::Wildcard | Pattern::Variable(_))
}

/// Pick the best column using a given strategy.
pub(crate) fn pick_column_with_strategy(
    scrutinees: &[Var],
    arms: &[MatchArm],
    strategy: ColumnStrategy,
) -> Result<usize, MatchCompileExtError> {
    if scrutinees.is_empty() {
        return Err(MatchCompileExtError::EmptyMatrix);
    }
    let mut best_col = 0;
    let mut best_score = i64::MIN;
    for col in 0..scrutinees.len() {
        let s = score_column_with_strategy(arms, col, strategy);
        if s > best_score {
            best_score = s;
            best_col = col;
        }
    }
    Ok(best_col)
}

/// Description of an overlap between two match arms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ArmOverlap {
    pub(crate) arm_a: usize,
    pub(crate) arm_b: usize,
    pub(crate) overlapping_columns: Vec<usize>,
}

/// Check if two patterns can match the same input.
#[must_use]
pub(crate) fn patterns_overlap(a: &Pattern, b: &Pattern) -> bool {
    match (a, b) {
        (Pattern::Wildcard, _) | (_, Pattern::Wildcard) => true,
        (Pattern::Variable(_), _) | (_, Pattern::Variable(_)) => true,
        (Pattern::Constructor(na, sa), Pattern::Constructor(nb, sb)) => {
            na == nb
                && sa.len() == sb.len()
                && sa
                    .iter()
                    .zip(sb.iter())
                    .all(|(x, y)| patterns_overlap(x, y))
        }
        (Pattern::Literal(la), Pattern::Literal(lb)) => la == lb,
        (Pattern::Or(alts), other) | (other, Pattern::Or(alts)) => {
            alts.iter().any(|alt| patterns_overlap(alt, other))
        }
        _ => false,
    }
}

/// Detect overlapping arms. Two arms overlap when every column has compatible patterns.
#[must_use]
pub(crate) fn detect_overlaps(arms: &[MatchArm]) -> Vec<ArmOverlap> {
    let mut overlaps = Vec::new();
    for i in 0..arms.len() {
        for j in (i + 1)..arms.len() {
            let width = arms[i].patterns.len().min(arms[j].patterns.len());
            let mut cols = Vec::new();
            let mut all = true;
            for col in 0..width {
                if patterns_overlap(&arms[i].patterns[col], &arms[j].patterns[col]) {
                    cols.push(col);
                } else {
                    all = false;
                }
            }
            if all && width > 0 {
                overlaps.push(ArmOverlap {
                    arm_a: i,
                    arm_b: j,
                    overlapping_columns: cols,
                });
            }
        }
    }
    overlaps
}

/// Check if a specific arm is fully shadowed by earlier arms.
#[must_use]
pub(crate) fn is_arm_shadowed(arms: &[MatchArm], arm_idx: usize) -> bool {
    if arm_idx == 0 || arm_idx >= arms.len() {
        return false;
    }
    (0..arm_idx).any(|earlier| arm_fully_covered_by(&arms[arm_idx], &arms[earlier]))
}

fn arm_fully_covered_by(covered: &MatchArm, covering: &MatchArm) -> bool {
    let width = covered.patterns.len().min(covering.patterns.len());
    if width == 0 {
        return false;
    }
    (0..width).all(|col| pattern_covers(&covering.patterns[col], &covered.patterns[col]))
        && covering.guard.is_none()
}

/// Check if pattern `a` covers pattern `b` (every input matching `b` also matches `a`).
fn pattern_covers(a: &Pattern, b: &Pattern) -> bool {
    match a {
        Pattern::Wildcard | Pattern::Variable(_) => true,
        Pattern::Constructor(na, sa) => match b {
            Pattern::Constructor(nb, sb) if na == nb && sa.len() == sb.len() => {
                sa.iter().zip(sb.iter()).all(|(x, y)| pattern_covers(x, y))
            }
            _ => false,
        },
        Pattern::Literal(la) => matches!(b, Pattern::Literal(lb) if la == lb),
        Pattern::Or(alts) => alts.iter().any(|alt| pattern_covers(alt, b)),
    }
}

/// A human-readable description of an uncovered pattern combination.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExhaustivenessGap {
    pub(crate) description: String,
    pub(crate) column: usize,
}

/// Report exhaustiveness gaps. `known_ctors` maps column index to expected constructor names.
#[must_use]
pub(crate) fn report_exhaustiveness_gaps(
    arms: &[MatchArm],
    known_ctors: &HashMap<usize, Vec<String>>,
) -> Vec<ExhaustivenessGap> {
    let mut gaps = Vec::new();
    for (&col, expected) in known_ctors {
        let mut present: HashSet<String> = HashSet::new();
        let mut has_wildcard = false;
        for arm in arms {
            if col < arm.patterns.len() {
                collect_present_names(&arm.patterns[col], &mut present, &mut has_wildcard);
            } else {
                has_wildcard = true;
            }
        }
        if has_wildcard {
            continue;
        }
        for name in expected {
            if !present.contains(name) {
                gaps.push(ExhaustivenessGap {
                    description: format!("missing constructor `{name}`"),
                    column: col,
                });
            }
        }
    }
    gaps.sort_by_key(|g| (g.column, g.description.clone()));
    gaps
}

fn collect_present_names(pat: &Pattern, names: &mut HashSet<String>, has_wild: &mut bool) {
    match pat {
        Pattern::Constructor(name, _) => {
            names.insert(name.to_string());
        }
        Pattern::Wildcard | Pattern::Variable(_) => {
            *has_wild = true;
        }
        Pattern::Or(alts) => {
            for alt in alts {
                collect_present_names(alt, names, has_wild);
            }
        }
        Pattern::Literal(_) => {}
    }
}

/// Statistics about a match expression's pattern structure.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct MatchStats {
    pub(crate) arm_count: usize,
    pub(crate) column_count: usize,
    pub(crate) max_nesting_depth: usize,
    pub(crate) total_pattern_nodes: usize,
    pub(crate) wildcard_ratio: f64,
    pub(crate) or_pattern_count: usize,
    pub(crate) literal_count: usize,
    pub(crate) constructor_count: usize,
}

/// Compute statistics about a match expression.
#[must_use]
pub(crate) fn compute_match_stats(arms: &[MatchArm], column_count: usize) -> MatchStats {
    let (mut max_depth, mut total, mut wilds, mut ors, mut lits, mut ctors) = (0, 0, 0, 0, 0, 0);
    for arm in arms {
        for pat in &arm.patterns {
            let c = count_pattern_nodes(pat);
            total += c.0;
            wilds += c.1;
            ors += c.2;
            lits += c.3;
            ctors += c.4;
            max_depth = max_depth.max(c.5);
        }
    }
    let wildcard_ratio = if total == 0 {
        0.0
    } else {
        wilds as f64 / total as f64
    };
    MatchStats {
        arm_count: arms.len(),
        column_count,
        max_nesting_depth: max_depth,
        total_pattern_nodes: total,
        wildcard_ratio,
        or_pattern_count: ors,
        literal_count: lits,
        constructor_count: ctors,
    }
}

/// Returns (total, wildcards, or_patterns, literals, constructors, depth).
fn count_pattern_nodes(pat: &Pattern) -> (usize, usize, usize, usize, usize, usize) {
    match pat {
        Pattern::Wildcard | Pattern::Variable(_) => (1, 1, 0, 0, 0, 1),
        Pattern::Literal(_) => (1, 0, 0, 1, 0, 1),
        Pattern::Constructor(_, subs) => {
            let (mut t, mut w, mut o, mut l, mut c, mut d) = (1, 0, 0, 0, 1, 1);
            for sp in subs {
                let n = count_pattern_nodes(sp);
                t += n.0;
                w += n.1;
                o += n.2;
                l += n.3;
                c += n.4;
                d = d.max(1 + n.5);
            }
            (t, w, o, l, c, d)
        }
        Pattern::Or(alts) => {
            let (mut t, mut w, mut o, mut l, mut c, mut d) = (1, 0, 1, 0, 0, 1);
            for alt in alts {
                let n = count_pattern_nodes(alt);
                t += n.0;
                w += n.1;
                o += n.2;
                l += n.3;
                c += n.4;
                d = d.max(1 + n.5);
            }
            (t, w, o, l, c, d)
        }
    }
}

/// Quality metrics for a compiled decision tree.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct DecisionTreeMetrics {
    pub(crate) height: usize,
    pub(crate) avg_path_length: f64,
    pub(crate) total_nodes: usize,
    pub(crate) leaf_count: usize,
    pub(crate) switch_count: usize,
    pub(crate) guard_count: usize,
    pub(crate) unreachable_leaves: usize,
    pub(crate) duplicate_leaves: usize,
}

/// Compute quality metrics for a decision tree.
#[must_use]
pub(crate) fn compute_tree_metrics(tree: &DecisionTree) -> DecisionTreeMetrics {
    let mut leaves = Vec::new();
    let mut sc = 0;
    let mut gc = 0;
    let mut tn = 0;
    let mut ur = 0;
    walk_tree(tree, 0, &mut leaves, &mut sc, &mut gc, &mut tn, &mut ur);
    let leaf_count = leaves.len();
    let height = leaves.iter().copied().max().unwrap_or(0);
    let avg = if leaves.is_empty() {
        0.0
    } else {
        leaves.iter().sum::<usize>() as f64 / leaf_count as f64
    };
    let mut bodies = Vec::new();
    collect_leaf_bodies(tree, &mut bodies);
    let unique: HashSet<usize> = bodies.iter().copied().collect();
    DecisionTreeMetrics {
        height,
        avg_path_length: avg,
        total_nodes: tn,
        leaf_count,
        switch_count: sc,
        guard_count: gc,
        unreachable_leaves: ur,
        duplicate_leaves: bodies.len().saturating_sub(unique.len()),
    }
}

fn walk_tree(
    tree: &DecisionTree,
    depth: usize,
    ld: &mut Vec<usize>,
    sc: &mut usize,
    gc: &mut usize,
    tn: &mut usize,
    ur: &mut usize,
) {
    *tn += 1;
    match tree {
        DecisionTree::Leaf(idx) => {
            ld.push(depth);
            if *idx == usize::MAX {
                *ur += 1;
            }
        }
        DecisionTree::Switch(_, branches, def) => {
            *sc += 1;
            for (_, sub) in branches {
                walk_tree(sub, depth + 1, ld, sc, gc, tn, ur);
            }
            if let Some(d) = def {
                walk_tree(d, depth + 1, ld, sc, gc, tn, ur);
            }
        }
        DecisionTree::Guard(_, t, f) => {
            *gc += 1;
            walk_tree(t, depth + 1, ld, sc, gc, tn, ur);
            walk_tree(f, depth + 1, ld, sc, gc, tn, ur);
        }
    }
}

fn collect_leaf_bodies(tree: &DecisionTree, bodies: &mut Vec<usize>) {
    match tree {
        DecisionTree::Leaf(idx) => bodies.push(*idx),
        DecisionTree::Switch(_, branches, def) => {
            for (_, sub) in branches {
                collect_leaf_bodies(sub, bodies);
            }
            if let Some(d) = def {
                collect_leaf_bodies(d, bodies);
            }
        }
        DecisionTree::Guard(_, t, f) => {
            collect_leaf_bodies(t, bodies);
            collect_leaf_bodies(f, bodies);
        }
    }
}

/// Compute complexity of a pattern. Constructors=2, literals=1, wildcards=0.
#[must_use]
pub(crate) fn pattern_complexity(pat: &Pattern) -> usize {
    match pat {
        Pattern::Wildcard | Pattern::Variable(_) => 0,
        Pattern::Literal(_) => 1,
        Pattern::Constructor(_, subs) => 2 + subs.iter().map(pattern_complexity).sum::<usize>(),
        Pattern::Or(alts) => alts.iter().map(pattern_complexity).sum::<usize>(),
    }
}

/// Total complexity of a match expression (sum of all pattern complexities).
#[must_use]
pub(crate) fn match_complexity(arms: &[MatchArm]) -> usize {
    arms.iter()
        .flat_map(|arm| arm.patterns.iter())
        .map(pattern_complexity)
        .sum()
}

/// Count distinct constructors in each column across all arms.
#[must_use]
pub(crate) fn distinct_constructors_per_column(arms: &[MatchArm], num_cols: usize) -> Vec<usize> {
    (0..num_cols)
        .map(|col| {
            let mut names: HashSet<String> = HashSet::new();
            for arm in arms {
                if col < arm.patterns.len() {
                    collect_ctor_strings(&arm.patterns[col], &mut names);
                }
            }
            names.len()
        })
        .collect()
}

fn collect_ctor_strings(pat: &Pattern, names: &mut HashSet<String>) {
    match pat {
        Pattern::Constructor(name, _) => {
            names.insert(name.to_string());
        }
        Pattern::Or(alts) => {
            for alt in alts {
                collect_ctor_strings(alt, names);
            }
        }
        _ => {}
    }
}

/// Count wildcards per column across all arms.
#[must_use]
pub(crate) fn wildcards_per_column(arms: &[MatchArm], num_cols: usize) -> Vec<usize> {
    (0..num_cols)
        .map(|col| {
            arms.iter()
                .filter(|arm| col >= arm.patterns.len() || is_wildcard_like(&arm.patterns[col]))
                .count()
        })
        .collect()
}
