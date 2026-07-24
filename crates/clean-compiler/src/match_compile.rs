// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Match expression compilation to decision trees.
//!
//! Compiles pattern-match expressions into efficient `DecisionTree`
//! representations using column-based pattern compilation. The algorithm:
//!
//! 1. Pick the best column to split on (most constructors, fewest wildcards)
//! 2. Generate `Switch` nodes for constructor patterns
//! 3. Propagate variables/wildcards through non-matching columns
//! 4. Flatten nested patterns by introducing fresh scrutinee variables
//!
//! Based on the algorithm from Maranget (2008), "Compiling Pattern Matching
//! to Good Decision Trees" (ML Workshop).
//!
//! Part of #3084 - Match expression compilation for native execution.

use crate::native_types::NativeType;
use clean_kernel::expr::Literal;
use clean_kernel::Name;

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// A scrutinee variable in a match expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Var {
    pub name: Name,
    pub type_: NativeType,
}

/// A constructor tag identifying a specific constructor of an inductive type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstructorTag {
    pub name: Name,
    pub arity: usize,
}

/// A pattern in a match arm.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum Pattern {
    /// Match a specific constructor with sub-patterns for fields.
    Constructor(Name, Vec<Pattern>),
    /// Match a literal value.
    Literal(Literal),
    /// Bind the matched value to a variable name.
    Variable(Name),
    /// Match anything without binding.
    Wildcard,
    /// Match any of the given alternatives (or-pattern).
    Or(Vec<Pattern>),
}

/// A single arm in a match expression.
#[derive(Debug, Clone)]
pub struct MatchArm {
    /// One pattern per scrutinee.
    pub patterns: Vec<Pattern>,
    /// Optional guard expression (represented as a kernel `Expr`).
    pub guard: Option<clean_kernel::Expr>,
    /// Index of the body to execute when this arm matches.
    pub body_idx: usize,
}

/// A compiled decision tree for pattern matching.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum DecisionTree {
    /// A leaf node: we matched arm `body_idx`.
    Leaf(usize),
    /// Switch on a scrutinee variable by constructor tag.
    ///
    /// Each `(ConstructorTag, DecisionTree)` pair handles one constructor.
    /// The optional default handles any constructor not explicitly listed.
    Switch(
        Var,
        Vec<(ConstructorTag, DecisionTree)>,
        Option<Box<DecisionTree>>,
    ),
    /// Guard: evaluate a guard expression. If true, take the first subtree;
    /// if false (or error), take the second.
    Guard(clean_kernel::Expr, Box<DecisionTree>, Box<DecisionTree>),
}

// ---------------------------------------------------------------------------
// Column scoring
// ---------------------------------------------------------------------------

/// Score a column for splitting priority.
///
/// Higher scores are better. We prefer columns with more constructor patterns
/// and fewer wildcards/variables, since they produce more efficient switches.
fn score_column(arms: &[MatchArm], col: usize) -> i64 {
    let mut ctor_count: i64 = 0;
    let mut wild_count: i64 = 0;
    let mut lit_count: i64 = 0;

    for arm in arms {
        if col >= arm.patterns.len() {
            wild_count += 1;
            continue;
        }
        match &arm.patterns[col] {
            Pattern::Constructor(..) => ctor_count += 1,
            Pattern::Literal(_) => lit_count += 1,
            Pattern::Variable(_) | Pattern::Wildcard => wild_count += 1,
            Pattern::Or(alts) => {
                // Or-patterns contribute based on their first alternative
                if alts.iter().any(|p| matches!(p, Pattern::Constructor(..))) {
                    ctor_count += 1;
                } else if alts.iter().any(|p| matches!(p, Pattern::Literal(_))) {
                    lit_count += 1;
                } else {
                    wild_count += 1;
                }
            }
        }
    }

    // Prefer columns with more concrete patterns, penalize wildcards
    (ctor_count + lit_count) * 2 - wild_count
}

/// Pick the best column to split on. Returns the column index.
fn pick_column(scrutinees: &[Var], arms: &[MatchArm]) -> usize {
    if scrutinees.len() <= 1 {
        return 0;
    }

    let mut best_col = 0;
    let mut best_score = i64::MIN;

    for col in 0..scrutinees.len() {
        let s = score_column(arms, col);
        if s > best_score {
            best_score = s;
            best_col = col;
        }
    }

    best_col
}

// ---------------------------------------------------------------------------
// Pattern helpers
// ---------------------------------------------------------------------------

/// Check if a pattern is a wildcard or variable (matches anything).
fn is_wildcard_like(pat: &Pattern) -> bool {
    matches!(pat, Pattern::Wildcard | Pattern::Variable(_))
}

/// Collect all distinct constructor tags appearing in a specific column.
fn collect_ctors(arms: &[MatchArm], col: usize) -> Vec<ConstructorTag> {
    let mut tags: Vec<ConstructorTag> = Vec::new();
    let mut seen: Vec<Name> = Vec::new();

    for arm in arms {
        if col >= arm.patterns.len() {
            continue;
        }
        if let Pattern::Constructor(name, sub_pats) = &arm.patterns[col] {
            if !seen.iter().any(|n| n == name) {
                seen.push(name.clone());
                tags.push(ConstructorTag {
                    name: name.clone(),
                    arity: sub_pats.len(),
                });
            }
        }
        // Also handle or-patterns that contain constructors
        if let Pattern::Or(alts) = &arm.patterns[col] {
            for alt in alts {
                if let Pattern::Constructor(name, sub_pats) = alt {
                    if !seen.iter().any(|n| n == name) {
                        seen.push(name.clone());
                        tags.push(ConstructorTag {
                            name: name.clone(),
                            arity: sub_pats.len(),
                        });
                    }
                }
            }
        }
    }

    tags
}

/// Generate fresh scrutinee variables for constructor fields.
fn fresh_field_vars(tag: &ConstructorTag, parent: &Var) -> Vec<Var> {
    (0..tag.arity)
        .map(|i| Var {
            name: parent
                .name
                .clone()
                .str(format!("_{}", tag.name))
                .str(format!("f{i}")),
            type_: parent.type_,
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Specialization
// ---------------------------------------------------------------------------

/// Build a new pattern row by replacing column `col` with `replacements`.
fn replace_column(patterns: &[Pattern], col: usize, replacements: &[Pattern]) -> Vec<Pattern> {
    let mut new_pats = Vec::with_capacity(patterns.len() - 1 + replacements.len());
    new_pats.extend_from_slice(&patterns[..col]);
    new_pats.extend_from_slice(replacements);
    new_pats.extend_from_slice(&patterns[col + 1..]);
    new_pats
}

/// Build wildcard replacements for a constructor with the given arity.
fn wildcard_replacements(arity: usize) -> Vec<Pattern> {
    vec![Pattern::Wildcard; arity]
}

/// Try to specialize a single pattern against a constructor tag.
///
/// Returns `Some(replacement_patterns)` if the pattern matches, `None` to skip.
fn specialize_pattern(pat: &Pattern, tag: &ConstructorTag) -> Option<Vec<Pattern>> {
    match pat {
        Pattern::Constructor(name, sub_pats) if name == &tag.name => Some(sub_pats.clone()),
        Pattern::Wildcard | Pattern::Variable(_) => Some(wildcard_replacements(tag.arity)),
        _ => None,
    }
}

/// Specialize the match matrix for a specific constructor in the given column.
///
/// For each arm:
/// - If the arm has a matching constructor in `col`, expand its sub-patterns
///   in place of the scrutinee column.
/// - If the arm has a wildcard/variable in `col`, replicate it with wildcards
///   for each field of the constructor.
/// - If the arm has a different constructor, skip it.
fn specialize(arms: &[MatchArm], col: usize, tag: &ConstructorTag) -> Vec<MatchArm> {
    let mut result = Vec::new();

    for arm in arms {
        let pat = if col < arm.patterns.len() {
            &arm.patterns[col]
        } else {
            &Pattern::Wildcard
        };

        if let Pattern::Or(alts) = pat {
            for alt in alts {
                if let Some(replacements) = specialize_pattern(alt, tag) {
                    result.push(MatchArm {
                        patterns: replace_column(&arm.patterns, col, &replacements),
                        guard: arm.guard.clone(),
                        body_idx: arm.body_idx,
                    });
                }
            }
        } else if let Some(replacements) = specialize_pattern(pat, tag) {
            result.push(MatchArm {
                patterns: replace_column(&arm.patterns, col, &replacements),
                guard: arm.guard.clone(),
                body_idx: arm.body_idx,
            });
        }
    }

    result
}

/// Build the default matrix: arms that match when no listed constructor matches.
///
/// Keeps arms with wildcard/variable in `col`, removes the column.
fn default_matrix(arms: &[MatchArm], col: usize) -> Vec<MatchArm> {
    let mut result = Vec::new();

    for arm in arms {
        let pat = if col < arm.patterns.len() {
            &arm.patterns[col]
        } else {
            &Pattern::Wildcard
        };

        if is_wildcard_like(pat) {
            let mut new_pats = Vec::with_capacity(arm.patterns.len().saturating_sub(1));
            new_pats.extend_from_slice(&arm.patterns[..col]);
            if col + 1 < arm.patterns.len() {
                new_pats.extend_from_slice(&arm.patterns[col + 1..]);
            }
            result.push(MatchArm {
                patterns: new_pats,
                guard: arm.guard.clone(),
                body_idx: arm.body_idx,
            });
        }
    }

    result
}

// ---------------------------------------------------------------------------
// Main compilation
// ---------------------------------------------------------------------------

/// Remove column `col` from a scrutinee list.
fn remove_scrutinee_column(scrutinees: &[Var], col: usize) -> Vec<Var> {
    scrutinees
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != col)
        .map(|(_, v)| v.clone())
        .collect()
}

/// Replace column `col` with `field_vars` in the scrutinee list.
fn replace_scrutinee_column(scrutinees: &[Var], col: usize, field_vars: Vec<Var>) -> Vec<Var> {
    let mut new_scrutinees = Vec::with_capacity(scrutinees.len() - 1 + field_vars.len());
    new_scrutinees.extend_from_slice(&scrutinees[..col]);
    new_scrutinees.extend(field_vars);
    new_scrutinees.extend_from_slice(&scrutinees[col + 1..]);
    new_scrutinees
}

/// Build a Switch node for the given column. Called when constructors are present.
fn build_switch(scrutinees: &[Var], arms: &[MatchArm], col: usize) -> DecisionTree {
    let scrutinee = scrutinees[col].clone();
    let ctors = collect_ctors(arms, col);

    let branches: Vec<(ConstructorTag, DecisionTree)> = ctors
        .iter()
        .map(|tag| {
            let field_vars = fresh_field_vars(tag, &scrutinee);
            let specialized = specialize(arms, col, tag);
            let new_scrutinees = replace_scrutinee_column(scrutinees, col, field_vars);
            let subtree = compile_match(&new_scrutinees, &specialized);
            (tag.clone(), subtree)
        })
        .collect();

    let default_arms = default_matrix(arms, col);
    let default = if default_arms.is_empty() {
        None
    } else {
        let reduced = remove_scrutinee_column(scrutinees, col);
        Some(Box::new(compile_match(&reduced, &default_arms)))
    };

    DecisionTree::Switch(scrutinee, branches, default)
}

/// Compile a pattern match into a decision tree.
///
/// `scrutinees` is the list of variables being matched against.
/// `arms` is the list of match arms, each with one pattern per scrutinee.
///
/// Returns a `DecisionTree` that, when evaluated, yields the `body_idx`
/// of the first matching arm.
///
/// # Algorithm
///
/// Uses column-based compilation (Maranget 2008):
/// 1. If no arms remain, the match is non-exhaustive (returns a Leaf(usize::MAX)
///    as a sentinel).
/// 2. If the first arm is all wildcards/variables, it matches — emit a Leaf.
/// 3. Otherwise, pick the best column, collect constructor tags, and generate
///    a Switch node with specialized sub-trees per constructor plus a default.
#[must_use]
pub fn compile_match(scrutinees: &[Var], arms: &[MatchArm]) -> DecisionTree {
    if arms.is_empty() {
        return DecisionTree::Leaf(usize::MAX);
    }

    let first = &arms[0];
    let all_wild = first.patterns.iter().all(is_wildcard_like)
        && (first.patterns.len() >= scrutinees.len() || scrutinees.is_empty());

    if all_wild || scrutinees.is_empty() {
        if let Some(ref guard_expr) = first.guard {
            let success = DecisionTree::Leaf(first.body_idx);
            let failure = compile_match(scrutinees, &arms[1..]);
            return DecisionTree::Guard(guard_expr.clone(), Box::new(success), Box::new(failure));
        }
        return DecisionTree::Leaf(first.body_idx);
    }

    let col = pick_column(scrutinees, arms);

    if collect_ctors(arms, col).is_empty() {
        let reduced = remove_scrutinee_column(scrutinees, col);
        let reduced_arms = default_matrix(arms, col);
        return compile_match(&reduced, &reduced_arms);
    }

    build_switch(scrutinees, arms, col)
}

#[cfg(test)]
#[path = "match_compile_tests.rs"]
mod tests;
