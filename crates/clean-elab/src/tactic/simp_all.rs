// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lightweight `simp_all` state helpers used by unit tests.
//!
//! This module provides a deterministic, expression-only model of the enhanced
//! `simp_all` control flow: track hypotheses, remove trivial facts, rewrite the
//! goal from equality hypotheses, and iterate to a fixpoint with a bounded loop.

use super::simp::SimpConfig;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Level};

/// Configuration for the enhanced `simp_all` driver.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpAllConfig {
    /// Maximum number of passes to attempt when chasing a fixpoint.
    pub max_iterations: usize,
    /// Whether to run in `simp only` mode.
    pub only_mode: bool,
    /// Explicit lemma names to forward to the regular `simp` configuration.
    pub lemmas: Vec<Name>,
    /// Whether arithmetic simplification should be enabled.
    pub use_arith: bool,
    /// Whether trivial hypotheses should be removed automatically.
    pub remove_trivial: bool,
    /// Whether trace/debug instrumentation should be enabled.
    pub trace: bool,
}

impl Default for SimpAllConfig {
    fn default() -> Self {
        Self {
            max_iterations: 100,
            only_mode: false,
            lemmas: Vec::new(),
            use_arith: false,
            remove_trivial: true,
            trace: false,
        }
    }
}

impl SimpAllConfig {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn only(lemmas: Vec<Name>) -> Self {
        Self::new().with_only_mode(true).with_lemmas(lemmas)
    }

    #[must_use]
    pub fn with_arith() -> Self {
        Self::new().with_use_arith(true)
    }

    #[must_use]
    pub fn with_max_iterations(mut self, max_iterations: usize) -> Self {
        self.max_iterations = max_iterations;
        self
    }

    #[must_use]
    pub fn with_only_mode(mut self, only_mode: bool) -> Self {
        self.only_mode = only_mode;
        self
    }

    #[must_use]
    pub fn with_lemmas(mut self, lemmas: Vec<Name>) -> Self {
        self.lemmas = lemmas;
        self
    }

    #[must_use]
    pub fn with_use_arith(mut self, use_arith: bool) -> Self {
        self.use_arith = use_arith;
        self
    }

    #[must_use]
    pub fn with_remove_trivial(mut self, remove_trivial: bool) -> Self {
        self.remove_trivial = remove_trivial;
        self
    }

    #[must_use]
    pub fn with_trace(mut self, trace: bool) -> Self {
        self.trace = trace;
        self
    }

    #[must_use]
    pub fn to_simp_config(&self) -> SimpConfig {
        let mut config = SimpConfig::new();
        config.max_steps = self.max_iterations;
        config.extra_lemmas = self.lemmas.iter().map(ToString::to_string).collect();
        config.only = self.only_mode;
        config.only_simplify = self.only_mode;
        config.use_hypotheses = true;
        config
    }
}

/// Result of simplifying either a hypothesis or the goal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SimpStepResult {
    Unchanged,
    Simplified(Expr),
    Removed,
}

/// A local hypothesis tracked by the enhanced `simp_all` driver.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpHypothesis {
    pub name: Name,
    pub expr: Expr,
    pub changed: bool,
    pub removed: bool,
}

impl SimpHypothesis {
    #[must_use]
    pub fn new(name: Name, expr: Expr) -> Self {
        Self {
            name,
            expr,
            changed: false,
            removed: false,
        }
    }

    pub fn simplify(&mut self, config: &SimpAllConfig) -> SimpStepResult {
        if self.removed {
            return SimpStepResult::Unchanged;
        }

        if config.remove_trivial && (is_true_const(&self.expr) || is_trivial_equality(&self.expr)) {
            self.changed = true;
            self.removed = true;
            return SimpStepResult::Removed;
        }

        SimpStepResult::Unchanged
    }
}

/// Mutable state for a single `simp_all` run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpAllState {
    pub hypotheses: Vec<SimpHypothesis>,
    pub goal: Expr,
    pub goal_changed: bool,
    pub iterations: usize,
}

impl SimpAllState {
    #[must_use]
    pub fn new(hypotheses: Vec<SimpHypothesis>, goal: Expr) -> Self {
        Self {
            hypotheses,
            goal,
            goal_changed: false,
            iterations: 0,
        }
    }

    pub fn simplify_goal(&mut self, _config: &SimpAllConfig) -> SimpStepResult {
        let rewrite_rules = self.collect_rewrite_rules();
        let Some(new_goal) = rewrite_expr_once(&self.goal, &rewrite_rules) else {
            return SimpStepResult::Unchanged;
        };

        self.goal = new_goal.clone();
        self.goal_changed = true;
        SimpStepResult::Simplified(new_goal)
    }

    #[must_use]
    pub fn run_one_pass(&mut self, config: &SimpAllConfig) -> bool {
        self.iterations += 1;

        let mut made_progress = false;
        for hyp in &mut self.hypotheses {
            if hyp.simplify(config) != SimpStepResult::Unchanged {
                made_progress = true;
            }
        }

        if self.simplify_goal(config) != SimpStepResult::Unchanged {
            made_progress = true;
        }

        made_progress
    }

    #[must_use]
    pub fn run_fixpoint(&mut self, config: &SimpAllConfig) -> SimpAllResult {
        let start_iterations = self.iterations;
        let mut changed = false;
        let mut reached_fixpoint = false;

        for _ in 0..config.max_iterations {
            if self.run_one_pass(config) {
                changed = true;
            } else {
                reached_fixpoint = true;
                break;
            }
        }

        SimpAllResult {
            hypotheses: self.hypotheses.clone(),
            goal: self.goal.clone(),
            changed,
            goal_changed: self.goal_changed,
            iterations: self.iterations - start_iterations,
            reached_fixpoint,
            changed_hypotheses: self.hypotheses.iter().filter(|hyp| hyp.changed).count(),
            removed_hypotheses: self.hypotheses.iter().filter(|hyp| hyp.removed).count(),
        }
    }

    fn collect_rewrite_rules(&self) -> Vec<(Expr, Expr)> {
        self.hypotheses
            .iter()
            .filter(|hyp| !hyp.removed)
            .filter_map(|hyp| match_eq(&hyp.expr).map(|(_, lhs, rhs)| (lhs.clone(), rhs.clone())))
            .filter(|(lhs, rhs)| lhs != rhs)
            .collect()
    }
}

/// Final summary of a `simp_all` run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SimpAllResult {
    pub hypotheses: Vec<SimpHypothesis>,
    pub goal: Expr,
    pub changed: bool,
    pub goal_changed: bool,
    pub iterations: usize,
    pub reached_fixpoint: bool,
    pub changed_hypotheses: usize,
    pub removed_hypotheses: usize,
}

fn is_true_const(expr: &Expr) -> bool {
    matches!(expr.kind(), ExprKind::Const(name, _) if *name == Name::from_string("True"))
}

fn is_trivial_equality(expr: &Expr) -> bool {
    match_eq(expr)
        .map(|(_, lhs, rhs)| lhs == rhs)
        .unwrap_or(false)
}

fn match_eq(expr: &Expr) -> Option<(&Expr, &Expr, &Expr)> {
    let ExprKind::App(fn_lhs, rhs) = expr.kind() else {
        return None;
    };
    let ExprKind::App(fn_ty, lhs) = fn_lhs.kind() else {
        return None;
    };
    let ExprKind::App(head, ty) = fn_ty.kind() else {
        return None;
    };
    match head.kind() {
        ExprKind::Const(name, _) if *name == Name::from_string("Eq") => Some((ty, lhs, rhs)),
        _ => None,
    }
}

fn rewrite_expr_once(expr: &Expr, rewrite_rules: &[(Expr, Expr)]) -> Option<Expr> {
    for (lhs, rhs) in rewrite_rules {
        if expr == lhs {
            return Some(rhs.clone());
        }
    }

    if let Some((ty, lhs, rhs)) = match_eq(expr) {
        if let Some(new_lhs) = rewrite_expr_once(lhs, rewrite_rules) {
            return Some(mk_eq(ty, &new_lhs, rhs));
        }
        if let Some(new_rhs) = rewrite_expr_once(rhs, rewrite_rules) {
            return Some(mk_eq(ty, lhs, &new_rhs));
        }
    }

    match expr.kind() {
        ExprKind::App(fun, arg) => {
            if let Some(new_fun) = rewrite_expr_once(fun, rewrite_rules) {
                return Some(Expr::app(new_fun, (**arg).clone()));
            }
            if let Some(new_arg) = rewrite_expr_once(arg, rewrite_rules) {
                return Some(Expr::app((**fun).clone(), new_arg));
            }
            None
        }
        _ => None,
    }
}

fn mk_eq(ty: &Expr, lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty.clone(),
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}
