// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Debugging and utility tactics
//!
//! This module provides tactics for debugging and utility operations:
//! - `trace`: Output debug messages during proof
//! - `itauto`: Intuitionistic tautology prover
//! - `clean`: Beta-reduce let-expressions
//! - `bound`: Prove inequalities by combining bounds
//! - `substs`: Substitute all equality hypotheses

use std::sync::Arc;

use crate::stack_safe;
use crate::tactic::{
    assumption, constructor, exfalso, exprs_equal, intro, is_pi_expr, linarith, match_and,
    match_eq_simple, subst, ProofState, TacticError, TacticResult,
};
use clean_kernel::expr::ExprKind;
use clean_kernel::Expr;

// ============================================================================
// Trace Tactic (debugging)
// ============================================================================

/// Trace output level
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TraceLevel {
    /// Only critical messages
    Error,
    /// Warnings and errors
    Warn,
    /// Informational messages
    #[default]
    Info,
    /// Detailed debug output
    Debug,
    /// Very detailed trace output
    Trace,
}

/// Result of a trace call
#[derive(Debug, Clone)]
pub struct TraceOutput {
    /// The message that was traced
    pub message: String,
    /// The trace level
    pub level: TraceLevel,
    /// Current goal state summary
    pub goal_summary: String,
    /// Number of remaining goals
    pub num_goals: usize,
}

/// Tactic: trace
///
/// Outputs a debug message and current goal state without modifying
/// the proof. Useful for debugging complex tactic scripts.
///
/// # Example
/// ```text
/// -- Goal: P ∧ Q
/// trace "About to split the conjunction"
/// -- Output: "About to split the conjunction"
/// -- Goal: P ∧ Q (unchanged)
/// split
/// ```
///
/// # Arguments
/// * `message` - The message to output
///
/// # Returns
/// A `TraceOutput` containing the message and goal state summary
///
/// # Contract
///
/// ENSURES: `state` is observed but not mutated.
/// ENSURES: Equivalent to `trace_with_level(state, message, TraceLevel::Info)`.
pub fn trace(state: &ProofState, message: &str) -> Result<TraceOutput, TacticError> {
    trace_with_level(state, message, TraceLevel::Info)
}

/// trace with explicit level
///
/// # Contract
///
/// ENSURES: `state` is observed but not mutated.
/// ENSURES: Returned `TraceOutput.level == level`.
/// ENSURES: Returned goal summary and goal count reflect `state` at call time.
pub fn trace_with_level(
    state: &ProofState,
    message: &str,
    level: TraceLevel,
) -> Result<TraceOutput, TacticError> {
    let goal_summary = if let Some(goal) = state.current_goal() {
        format!(
            "⊢ {:?} (with {} hypotheses)",
            goal.target,
            goal.local_ctx.len()
        )
    } else {
        "no goals".to_string()
    };

    Ok(TraceOutput {
        message: message.to_string(),
        level,
        goal_summary,
        num_goals: state.goals.len(),
    })
}

/// trace_state - outputs detailed state information
///
/// # Contract
///
/// ENSURES: `state` is observed but not mutated.
/// ENSURES: Returned message enumerates each goal in order with its target and
/// local context entries.
/// ENSURES: Returned `num_goals == state.goals.len()`.
pub fn trace_state(state: &ProofState) -> Result<TraceOutput, TacticError> {
    let mut lines = Vec::new();
    lines.push(format!("Goals: {}", state.goals.len()));

    for (i, goal) in state.goals.iter().enumerate() {
        lines.push(format!("Goal {}:", i + 1));
        lines.push(format!("  Target: {:?}", goal.target));
        lines.push(format!("  Context ({} items):", goal.local_ctx.len()));
        for decl in &goal.local_ctx {
            lines.push(format!("    {} : {:?}", decl.name, decl.ty));
        }
    }

    let message = lines.join("\n");
    let goal_summary = if state.goals.is_empty() {
        "no goals".to_string()
    } else {
        format!("{} goal(s)", state.goals.len())
    };

    Ok(TraceOutput {
        message,
        level: TraceLevel::Debug,
        goal_summary,
        num_goals: state.goals.len(),
    })
}

/// trace_expr - trace an expression's structure
///
/// # Contract
///
/// REQUIRES: `expr` is a well-formed kernel expression.
/// ENSURES: `state` is observed but not mutated.
/// ENSURES: Returned message contains the debug rendering of `expr`.
pub fn trace_expr(state: &ProofState, expr: &Expr) -> Result<TraceOutput, TacticError> {
    let message = format!("Expression structure: {expr:?}");
    let goal_summary = if let Some(goal) = state.current_goal() {
        format!("⊢ {:?}", goal.target)
    } else {
        "no goals".to_string()
    };

    Ok(TraceOutput {
        message,
        level: TraceLevel::Debug,
        goal_summary,
        num_goals: state.goals.len(),
    })
}

// ============================================================================
// ITauto Tactic
// ============================================================================

#[derive(Debug, Clone)]
pub struct ITautoConfig {
    pub max_depth: usize,
    pub verbose: bool,
}

impl Default for ITautoConfig {
    /// ENSURES: Default config uses a depth bound of `20` and disables verbose
    /// output.
    fn default() -> Self {
        Self {
            max_depth: 20,
            verbose: false,
        }
    }
}

/// Tactic: itauto - Intuitionistic tautology prover.
/// ENSURES: Equivalent to `itauto_with_config(state, ITautoConfig::default())`.
pub fn itauto(state: &mut ProofState) -> TacticResult {
    let mut config = ITautoConfig::default();
    if let Some(max_depth) = state.options().max_depth_override() {
        config.max_depth = max_depth;
    }
    if let Some(verbose) = state.options().verbose_override() {
        config.verbose = verbose;
    }
    itauto_with_config(state, config)
}

/// REQUIRES: `config.max_depth > 0` if bounded search should explore any rule.
/// ENSURES: On `Ok(())`, the goal state is advanced only by supported
/// intuitionistic search steps discovered within `config.max_depth`.
/// ENSURES: On `Err(SearchExhausted)`, no supported proof was found within the
/// configured depth bound.
pub fn itauto_with_config(state: &mut ProofState, config: ITautoConfig) -> TacticResult {
    itauto_search(state, config.max_depth)
}

fn itauto_search(state: &mut ProofState, depth: usize) -> TacticResult {
    if depth == 0 {
        return Err(TacticError::SearchExhausted {
            tactic: "itauto".into(),
            detail: "search depth exhausted".into(),
        });
    }

    if state.is_complete() {
        return Ok(());
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let target = state.metas.instantiate(&goal.target);

    // Rule 1: Check if goal is in hypotheses
    for decl in &goal.local_ctx {
        let ty = state.metas.instantiate(&decl.ty);
        if exprs_equal(&ty, &target) {
            assumption(state)?;
            // Continue with remaining goals (e.g. after constructor split)
            return itauto_search(state, depth - 1);
        }
    }

    // Rule 2: If goal is True, apply True.intro via constructor
    if matches!(target.kind(), ExprKind::Const(name, _) if name.to_string() == "True") {
        constructor(state)?;
        return itauto_search(state, depth - 1);
    }

    // Rule 3: Check for False in hypotheses
    for decl in &goal.local_ctx {
        let ty = state.metas.instantiate(&decl.ty);
        if matches!(ty.kind(), ExprKind::Const(name, _) if name.to_string() == "False") {
            exfalso(state).and_then(|_| assumption(state))?;
            return itauto_search(state, depth - 1);
        }
    }

    // Rule 4: If goal is P -> Q, use intro
    if is_pi_expr(&target) {
        let mut new_state = state.clone();
        if intro(&mut new_state, "h").is_ok() && itauto_search(&mut new_state, depth - 1).is_ok() {
            *state = new_state;
            return Ok(());
        }
    }

    // Rule 5: If goal is P /\ Q, split
    if match_and(&target).is_some() {
        let mut new_state = state.clone();
        if constructor(&mut new_state).is_ok() && itauto_search(&mut new_state, depth - 1).is_ok() {
            *state = new_state;
            return Ok(());
        }
    }

    Err(TacticError::SearchExhausted {
        tactic: "itauto".into(),
        detail: "no intuitionistic proof found".into(),
    })
}

// ============================================================================
// clean Tactic
// ============================================================================

/// Tactic: clean - Simplifies by beta-reducing let-expressions.
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok(())`, the current goal target and each local declaration
/// type are replaced by `beta_reduce_all` of their previous values.
/// ENSURES: On `Ok(())`, goal count and local-context lengths are unchanged.
/// ENSURES: On `Err(NoGoals)`, `state` is unchanged.
pub fn clean(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let new_target = beta_reduce_all(&goal.target);

    if new_target != goal.target {
        // Part of #2477: use replace_target_def_eq instead of in-place mutation.
        // Beta reduction is definitionally equal by construction.
        state.replace_target_def_eq(new_target)?;
    }

    state.rewrite_local_decl_types_def_eq(beta_reduce_all)
}

/// REQUIRES: `expr` is a well-formed kernel expression.
/// ENSURES: Beta redexes and `let` redexes are recursively reduced throughout
/// the expression tree.
/// ENSURES: Non-reducible nodes are rebuilt with recursively reduced children
/// or cloned unchanged when atomic.
/// ENSURES: Recursive descent runs under `stack_safe`.
pub(crate) fn beta_reduce_all(expr: &Expr) -> Expr {
    stack_safe(|| match expr.kind() {
        ExprKind::App(f, a) => {
            let f_reduced = beta_reduce_all(f);
            let a_reduced = beta_reduce_all(a);
            if let ExprKind::Lam(_, _, body) = f_reduced.kind() {
                beta_reduce_all(&body.instantiate(&a_reduced))
            } else {
                Expr::app(f_reduced, a_reduced)
            }
        }
        ExprKind::Lam(bi, ty, body) => Expr::lam(*bi, beta_reduce_all(ty), beta_reduce_all(body)),
        ExprKind::Pi(bi, ty, body) => Expr::pi(*bi, beta_reduce_all(ty), beta_reduce_all(body)),
        ExprKind::Let(_, _ty, val, body, _) => {
            let val_reduced = beta_reduce_all(val);
            let body_reduced = beta_reduce_all(body);
            beta_reduce_all(&body_reduced.instantiate(&val_reduced))
        }
        ExprKind::Proj(name, idx, inner) => Expr::proj(name.clone(), *idx, beta_reduce_all(inner)),
        ExprKind::MData(md, inner) => Expr::mdata(md.clone(), beta_reduce_all(inner)),
        ExprKind::Squash(inner) => {
            Expr::from_kind(ExprKind::Squash(Arc::new(beta_reduce_all(inner))))
        }
        _ => expr.clone(),
    })
}

// ============================================================================
// Bound Tactic
// ============================================================================

/// Tactic: bound - Proves inequalities by combining bounds.
/// REQUIRES: `state.goals` is non-empty if `linarith` should run.
/// ENSURES: Equivalent to `linarith(state)`.
pub fn bound(state: &mut ProofState) -> TacticResult {
    let _goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    linarith(state)
}

// ============================================================================
// Substs Tactic
// ============================================================================

/// Tactic: substs - Substitutes all equality hypotheses where lhs is a variable.
/// REQUIRES: `state.goals` is non-empty at entry.
/// ENSURES: Each successful round chooses at most one equality hypothesis whose
/// lhs is a live local variable and invokes `subst` on that hypothesis name.
/// ENSURES: On `Ok(())`, the loop stopped because one full round made no
/// successful substitution or because `100` rounds were reached.
/// ENSURES: On `Err(NoGoals)`, a prior successful substitution round discharged
/// the remaining goals before the next scan began.
pub fn substs(state: &mut ProofState) -> TacticResult {
    let mut made_progress = true;
    let mut iterations = 0;
    let max_iterations = 100;

    while made_progress && iterations < max_iterations {
        made_progress = false;
        iterations += 1;

        let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
        let local_ctx = goal.local_ctx.clone();

        let mut subst_name = None;
        for decl in &local_ctx {
            let ty = state.metas.instantiate(&decl.ty);
            if let Some((lhs, _rhs)) = match_eq_simple(&ty) {
                let fvar_id = if let ExprKind::FVar(id) = lhs.kind() {
                    Some(*id)
                } else {
                    None
                };
                let Some(fvar_id) = fvar_id else { continue };
                let is_in_ctx = local_ctx
                    .iter()
                    .any(|d| d.fvar == fvar_id && d.name != decl.name);
                if is_in_ctx {
                    subst_name = Some(decl.name.clone());
                    break;
                }
            }
        }

        if let Some(name) = subst_name {
            if subst(state, &name).is_ok() {
                made_progress = true;
            }
        }
    }

    Ok(())
}
