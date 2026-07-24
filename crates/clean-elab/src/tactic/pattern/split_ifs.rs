// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! split_ifs tactic: split on all if-then-else conditions in the goal.

use crate::stack_safe;
use clean_kernel::{Expr, ExprKind};

use super::super::{by_cases, ProofState, TacticError, TacticResult};
use super::util::{exprs_equal, generate_fresh_hyp_name};

/// Configuration for split_ifs tactic
#[derive(Debug, Clone, Default)]
pub struct SplitIfsConfig {
    /// Maximum depth of nested if-then-else to split
    pub max_depth: usize,
    /// Hypothesis names to use for conditions (auto-generated if empty)
    pub hyp_names: Vec<String>,
    /// Whether to also split hypotheses, not just the goal
    pub split_hyps: bool,
}

impl SplitIfsConfig {
    pub fn new() -> Self {
        Self {
            max_depth: 10,
            hyp_names: Vec::new(),
            split_hyps: false,
        }
    }

    #[must_use]
    pub fn with_max_depth(mut self, depth: usize) -> Self {
        self.max_depth = depth;
        self
    }

    #[must_use]
    pub fn with_hyp_names(mut self, names: Vec<String>) -> Self {
        self.hyp_names = names;
        self
    }

    #[must_use]
    pub fn split_hyps(mut self, split: bool) -> Self {
        self.split_hyps = split;
        self
    }
}

/// Find if-then-else expressions in an expression
fn find_ite_conditions(expr: &Expr, conditions: &mut Vec<Expr>, depth: usize, max_depth: usize) {
    stack_safe(|| {
        if depth > max_depth {
            return;
        }

        match expr.kind() {
            // ite c t e pattern - the standard if-then-else
            ExprKind::App(f, arg) => {
                // Check if this is an ite application
                if let Some((cond, _, _)) = try_extract_ite(expr) {
                    // Add the condition if not already present
                    if !conditions.iter().any(|c| exprs_equal(c, &cond)) {
                        conditions.push(cond);
                    }
                }

                // Recurse into subexpressions
                find_ite_conditions(f, conditions, depth + 1, max_depth);
                find_ite_conditions(arg, conditions, depth + 1, max_depth);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                find_ite_conditions(ty, conditions, depth + 1, max_depth);
                find_ite_conditions(body, conditions, depth + 1, max_depth);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                find_ite_conditions(ty, conditions, depth + 1, max_depth);
                find_ite_conditions(val, conditions, depth + 1, max_depth);
                find_ite_conditions(body, conditions, depth + 1, max_depth);
            }
            _ => {}
        }
    })
}

/// Try to extract ite condition from an expression
/// Returns (condition, then_branch, else_branch) if successful
fn try_extract_ite(expr: &Expr) -> Option<(Expr, Expr, Expr)> {
    // ite is applied as: ite alpha c dec t e
    // Lean 4: @ite.{u} {α : Sort u} (c : Prop) [h : Decidable c] (a b : α) : α
    // We need to match: App(App(App(App(App(ite, alpha), c), dec), t), e)
    if let ExprKind::App(f1, else_branch) = expr.kind() {
        if let ExprKind::App(f2, then_branch) = f1.kind() {
            if let ExprKind::App(f3, _decidable) = f2.kind() {
                if let ExprKind::App(f4, condition) = f3.kind() {
                    if let ExprKind::App(ite_const, _type_arg) = f4.kind() {
                        if is_ite_const(ite_const) {
                            return Some((
                                condition.as_ref().clone(),
                                then_branch.as_ref().clone(),
                                else_branch.as_ref().clone(),
                            ));
                        }
                    }
                }
            }
        }
    }

    // Also check for dite (dependent if-then-else)
    // dite is applied as: dite alpha c dec t e
    if let ExprKind::App(f1, else_branch) = expr.kind() {
        if let ExprKind::App(f2, then_branch) = f1.kind() {
            if let ExprKind::App(f3, _decidable) = f2.kind() {
                if let ExprKind::App(f4, condition) = f3.kind() {
                    if let ExprKind::App(dite_const, _type_arg) = f4.kind() {
                        if is_dite_const(dite_const) {
                            return Some((
                                condition.as_ref().clone(),
                                then_branch.as_ref().clone(),
                                else_branch.as_ref().clone(),
                            ));
                        }
                    }
                }
            }
        }
    }

    None
}

/// Check if expression is the ite constant
pub(crate) fn is_ite_const(expr: &Expr) -> bool {
    if let ExprKind::Const(name, _) = expr.kind() {
        let name_str = name.to_string();
        name_str == "ite" || name_str == "if" || name_str.ends_with(".ite")
    } else {
        false
    }
}

/// Check if expression is the dite constant
pub(crate) fn is_dite_const(expr: &Expr) -> bool {
    if let ExprKind::Const(name, _) = expr.kind() {
        let name_str = name.to_string();
        name_str == "dite" || name_str.ends_with(".dite")
    } else {
        false
    }
}

/// split_ifs tactic: split on all if-then-else conditions in the goal
///
/// This tactic finds all `if c then t else e` expressions in the goal
/// and creates cases for each condition.
///
/// # Example
/// ```text
/// -- Goal: if x > 0 then 1 else -1 > 0
/// split_ifs
/// -- Creates two goals:
/// -- Case h : x > 0: 1 > 0
/// -- Case h : not (x > 0): -1 > 0
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: Equivalent to `split_ifs_with_config(state, SplitIfsConfig::new())`
pub fn split_ifs(state: &mut ProofState) -> TacticResult {
    split_ifs_with_config(state, SplitIfsConfig::new())
}

/// split_ifs with configuration
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, `by_cases` is applied to the first discovered `ite`/`dite` condition
/// ENSURES: If `config.split_hyps`, candidate conditions are collected from both the target and local hypotheses
/// ENSURES: On Err(InvalidTarget), no `ite`/`dite` condition was found to split
pub fn split_ifs_with_config(state: &mut ProofState, config: SplitIfsConfig) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let target = goal.target.clone();

    // Find all if-then-else conditions in the goal
    let mut conditions = Vec::new();
    find_ite_conditions(&target, &mut conditions, 0, config.max_depth);

    // Also check hypotheses if configured
    if config.split_hyps {
        for decl in &goal.local_ctx {
            find_ite_conditions(&decl.ty, &mut conditions, 0, config.max_depth);
        }
    }

    if conditions.is_empty() {
        return Err(TacticError::InvalidTarget {
            tactic: "split_ifs".into(),
            detail: "no if-then-else found in goal".into(),
        });
    }

    // Split on the first condition
    let first_condition = conditions.remove(0);

    // Generate hypothesis name
    let hyp_name = if config.hyp_names.is_empty() {
        generate_fresh_hyp_name(&goal.local_ctx, "h")
    } else {
        config.hyp_names[0].clone()
    };

    // Use by_cases to split on the condition
    by_cases(state, &hyp_name, first_condition)
}

/// split_ifs with specific hypothesis names
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: Equivalent to `split_ifs_with_config(state, SplitIfsConfig::new().with_hyp_names(names))`
pub fn split_ifs_with_names(state: &mut ProofState, names: Vec<String>) -> TacticResult {
    split_ifs_with_config(state, SplitIfsConfig::new().with_hyp_names(names))
}
