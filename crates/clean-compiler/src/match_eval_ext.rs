// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended match evaluation with tracing, coverage, profiling, and budgets.
//!
//! Extends `match_eval` with:
//! - Step-by-step evaluation tracing with branch decisions
//! - Coverage analysis: which arms were exercised during evaluation
//! - Performance profiling: comparison count, branch depth, backtrack count
//! - Aggregate statistics across evaluations
//! - Configurable evaluation budget (comparison/depth limits)
//!
//! See `match_eval_ext2` for caching and symbolic evaluation.
//!
//! Part of #3084 - Match expression compilation for native execution.

use std::collections::HashMap;

use clean_kernel::Name;

use crate::match_compile::{ConstructorTag, DecisionTree, Var};
use crate::match_eval::{MatchEnv, MatchError, MatchValue};

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors specific to extended match evaluation.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum MatchEvalExtError {
    /// Evaluation exceeded the comparison budget.
    #[error("comparison budget exceeded: limit {limit}, used {used}")]
    ComparisonBudgetExceeded { limit: usize, used: usize },

    /// Evaluation exceeded the depth budget.
    #[error("depth budget exceeded: limit {limit}, reached {reached}")]
    DepthBudgetExceeded { limit: usize, reached: usize },

    /// Underlying match evaluation error.
    #[error("match evaluation error: {0}")]
    MatchError(#[from] MatchError),
}

// ---------------------------------------------------------------------------
// Evaluation tracing
// ---------------------------------------------------------------------------

/// A single step in the evaluation trace.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub(crate) enum TraceStep {
    /// Entered a Switch node, inspecting a scrutinee.
    EnterSwitch {
        scrutinee: Name,
        tag_found: Option<Name>,
    },
    /// Matched a specific constructor branch.
    BranchTaken {
        constructor: Name,
        field_count: usize,
    },
    /// Fell through to the default branch (no constructor matched).
    DefaultTaken,
    /// Entered a Guard node.
    EnterGuard,
    /// Guard evaluated to a boolean result.
    GuardResult { passed: bool },
    /// Reached a leaf node with the given arm index.
    ReachedLeaf { arm_idx: usize },
    /// Reached a non-exhaustive sentinel leaf.
    NonExhaustive,
}

/// A full evaluation trace recording each decision made.
#[derive(Debug, Clone, Default)]
pub(crate) struct EvalTrace {
    pub(crate) steps: Vec<TraceStep>,
}

impl EvalTrace {
    fn push(&mut self, step: TraceStep) {
        self.steps.push(step);
    }

    /// Number of steps in this trace.
    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.steps.len()
    }

    /// Whether the trace is empty.
    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// The arm index reached, if any.
    #[must_use]
    pub(crate) fn result_arm(&self) -> Option<usize> {
        self.steps.iter().rev().find_map(|s| match s {
            TraceStep::ReachedLeaf { arm_idx } => Some(*arm_idx),
            _ => None,
        })
    }
}

// ---------------------------------------------------------------------------
// Performance profiling
// ---------------------------------------------------------------------------

/// Performance profile for a single evaluation.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub(crate) struct EvalProfile {
    /// Number of constructor tag comparisons performed.
    pub(crate) comparison_count: usize,
    /// Maximum depth reached during evaluation.
    pub(crate) max_depth: usize,
    /// Number of times the default branch was taken (backtrack-like).
    pub(crate) backtrack_count: usize,
    /// Number of guard evaluations.
    pub(crate) guard_count: usize,
}

// ---------------------------------------------------------------------------
// Coverage analysis
// ---------------------------------------------------------------------------

/// Coverage information for match arms across evaluations.
#[derive(Debug, Clone)]
pub(crate) struct CoverageTracker {
    /// Maps arm index to the number of times it was reached.
    arm_hits: HashMap<usize, usize>,
    /// Total number of evaluations.
    total_evals: usize,
}

impl CoverageTracker {
    /// Create a new empty coverage tracker.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            arm_hits: HashMap::new(),
            total_evals: 0,
        }
    }

    /// Record that an arm was hit.
    pub(crate) fn record_hit(&mut self, arm_idx: usize) {
        *self.arm_hits.entry(arm_idx).or_insert(0) += 1;
        self.total_evals += 1;
    }

    /// Record a non-exhaustive (no arm matched).
    pub(crate) fn record_miss(&mut self) {
        self.total_evals += 1;
    }

    /// Number of times a specific arm was reached.
    #[must_use]
    pub(crate) fn arm_hit_count(&self, arm_idx: usize) -> usize {
        self.arm_hits.get(&arm_idx).copied().unwrap_or(0)
    }

    /// Total evaluations recorded.
    #[must_use]
    pub(crate) fn total_evaluations(&self) -> usize {
        self.total_evals
    }

    /// Hit rate for a specific arm (0.0 to 1.0).
    #[must_use]
    pub(crate) fn arm_hit_rate(&self, arm_idx: usize) -> f64 {
        if self.total_evals == 0 {
            return 0.0;
        }
        self.arm_hit_count(arm_idx) as f64 / self.total_evals as f64
    }

    /// All arm indices that were hit at least once.
    #[must_use]
    pub(crate) fn hit_arms(&self) -> Vec<usize> {
        let mut arms: Vec<usize> = self.arm_hits.keys().copied().collect();
        arms.sort_unstable();
        arms
    }

    /// Number of distinct arms hit.
    #[must_use]
    pub(crate) fn distinct_arms_hit(&self) -> usize {
        self.arm_hits.len()
    }
}

// ---------------------------------------------------------------------------
// Evaluation budget
// ---------------------------------------------------------------------------

/// Configurable budget for match evaluation.
#[derive(Debug, Clone, Copy)]
pub(crate) struct EvalBudget {
    /// Maximum number of constructor comparisons allowed.
    pub(crate) max_comparisons: usize,
    /// Maximum evaluation depth allowed.
    pub(crate) max_depth: usize,
}

impl EvalBudget {
    /// Create a new budget with specified limits.
    #[must_use]
    pub(crate) fn new(max_comparisons: usize, max_depth: usize) -> Self {
        Self {
            max_comparisons,
            max_depth,
        }
    }
}

impl Default for EvalBudget {
    fn default() -> Self {
        Self {
            max_comparisons: 10_000,
            max_depth: 100,
        }
    }
}

// ---------------------------------------------------------------------------
// Aggregate statistics
// ---------------------------------------------------------------------------

/// Aggregate statistics across multiple evaluations.
#[derive(Debug, Clone, Default)]
pub(crate) struct EvalStatistics {
    profiles: Vec<EvalProfile>,
}

impl EvalStatistics {
    /// Create new empty statistics.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            profiles: Vec::new(),
        }
    }

    /// Record a profile from one evaluation.
    pub(crate) fn record(&mut self, profile: EvalProfile) {
        self.profiles.push(profile);
    }

    /// Number of evaluations recorded.
    #[must_use]
    pub(crate) fn count(&self) -> usize {
        self.profiles.len()
    }

    /// Average comparison count across evaluations.
    #[must_use]
    pub(crate) fn avg_comparisons(&self) -> f64 {
        if self.profiles.is_empty() {
            return 0.0;
        }
        let total: usize = self.profiles.iter().map(|p| p.comparison_count).sum();
        total as f64 / self.profiles.len() as f64
    }

    /// Average depth across evaluations.
    #[must_use]
    pub(crate) fn avg_depth(&self) -> f64 {
        if self.profiles.is_empty() {
            return 0.0;
        }
        let total: usize = self.profiles.iter().map(|p| p.max_depth).sum();
        total as f64 / self.profiles.len() as f64
    }

    /// Maximum comparison count seen.
    #[must_use]
    pub(crate) fn max_comparisons(&self) -> usize {
        self.profiles
            .iter()
            .map(|p| p.comparison_count)
            .max()
            .unwrap_or(0)
    }

    /// Maximum depth seen.
    #[must_use]
    pub(crate) fn max_depth(&self) -> usize {
        self.profiles.iter().map(|p| p.max_depth).max().unwrap_or(0)
    }

    /// Total backtrack count across all evaluations.
    #[must_use]
    pub(crate) fn total_backtracks(&self) -> usize {
        self.profiles.iter().map(|p| p.backtrack_count).sum()
    }
}

// ---------------------------------------------------------------------------
// Traced evaluation
// ---------------------------------------------------------------------------

/// Generate fresh field variable names (mirrors match_eval::fresh_field_names).
fn fresh_field_names(tag: &ConstructorTag, parent: &Var) -> Vec<Name> {
    (0..tag.arity)
        .map(|i| {
            parent
                .name
                .clone()
                .str(format!("_{}", tag.name))
                .str(format!("f{i}"))
        })
        .collect()
}

/// Evaluate a decision tree with full tracing and profiling.
///
/// Returns the arm index, evaluation trace, and performance profile.
pub(crate) fn eval_traced(
    tree: &DecisionTree,
    env: &MatchEnv,
    budget: &EvalBudget,
) -> Result<(usize, EvalTrace, EvalProfile), MatchEvalExtError> {
    let mut trace = EvalTrace::default();
    let mut profile = EvalProfile::default();
    let result = eval_traced_inner(tree, env, budget, &mut trace, &mut profile, 0)?;
    Ok((result, trace, profile))
}

fn eval_traced_inner(
    tree: &DecisionTree,
    env: &MatchEnv,
    budget: &EvalBudget,
    trace: &mut EvalTrace,
    profile: &mut EvalProfile,
    depth: usize,
) -> Result<usize, MatchEvalExtError> {
    if depth > profile.max_depth {
        profile.max_depth = depth;
    }
    if depth > budget.max_depth {
        return Err(MatchEvalExtError::DepthBudgetExceeded {
            limit: budget.max_depth,
            reached: depth,
        });
    }

    match tree {
        DecisionTree::Leaf(idx) => {
            if *idx == usize::MAX {
                trace.push(TraceStep::NonExhaustive);
                Err(MatchEvalExtError::MatchError(MatchError::NonExhaustive))
            } else {
                trace.push(TraceStep::ReachedLeaf { arm_idx: *idx });
                Ok(*idx)
            }
        }
        DecisionTree::Switch(scrutinee, branches, default) => {
            let val = env
                .lookup(&scrutinee.name)
                .ok_or(MatchError::UnboundVariable(scrutinee.name.clone()))?;

            let tag_found = val.ctor_tag().map(|t| t.name.clone());
            trace.push(TraceStep::EnterSwitch {
                scrutinee: scrutinee.name.clone(),
                tag_found: tag_found.clone(),
            });

            if let Some(tag) = val.ctor_tag() {
                for (branch_tag, subtree) in branches {
                    profile.comparison_count += 1;
                    if profile.comparison_count > budget.max_comparisons {
                        return Err(MatchEvalExtError::ComparisonBudgetExceeded {
                            limit: budget.max_comparisons,
                            used: profile.comparison_count,
                        });
                    }

                    if branch_tag.name == tag.name {
                        trace.push(TraceStep::BranchTaken {
                            constructor: tag.name.clone(),
                            field_count: branch_tag.arity,
                        });

                        let field_vars = fresh_field_names(branch_tag, scrutinee);
                        let fields = val.fields().unwrap_or(&[]);
                        let new_bindings: Vec<(Name, MatchValue)> =
                            field_vars.into_iter().zip(fields.iter().cloned()).collect();
                        let new_env = env.extend(&new_bindings);
                        return eval_traced_inner(
                            subtree,
                            &new_env,
                            budget,
                            trace,
                            profile,
                            depth + 1,
                        );
                    }
                }
            }

            // Default branch
            profile.backtrack_count += 1;
            trace.push(TraceStep::DefaultTaken);
            match default {
                Some(default_tree) => {
                    eval_traced_inner(default_tree, env, budget, trace, profile, depth + 1)
                }
                None => {
                    trace.push(TraceStep::NonExhaustive);
                    Err(MatchEvalExtError::MatchError(MatchError::NonExhaustive))
                }
            }
        }
        DecisionTree::Guard(_guard_expr, _success, failure) => {
            profile.guard_count += 1;
            trace.push(TraceStep::EnterGuard);
            // Like base match_eval: guards fall through to failure
            trace.push(TraceStep::GuardResult { passed: false });
            eval_traced_inner(failure, env, budget, trace, profile, depth + 1)
        }
    }
}
