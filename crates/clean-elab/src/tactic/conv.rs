// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Conv (conversion) tactics for targeted rewriting
//!
//! This module provides tactics for navigating to specific subexpressions
//! and performing targeted rewrites:
//! - `ConvPosition` - Position markers for expression navigation
//! - `ConvPath` - A path through an expression tree
//! - `ConvState` - State for conv-mode rewriting
//! - `conv_rw` - Targeted rewrite using conv-style navigation
//! - `conv_lhs` - Rewrite only the left-hand side of an equality
//! - `conv_rhs` - Rewrite only the right-hand side of an equality
//! - `conv_arg` - Navigate into an argument and apply a tactic
//! - `conv_ext` - Enter a binder body, introducing the bound variable
//! - `conv_congr` - Enter all arguments of an application simultaneously
//! - `conv_change` - Replace the focused expression with a definitionally equal one
//! - `eval_conv` - Entry point for conv tactic mode

use clean_kernel::expr::ExprKind;
use clean_kernel::{Expr, Name};

use super::conv_proof::{build_conv_rewrite_eq_proof, ConvRewriteProofInputs};
use super::{
    contains_expr, match_equality, replace_expr, rewrite_candidate_summaries, ProofState,
    TacticError, TacticResult,
};
use crate::stack_safe;

// ============================================================================
// Conv Position and Path Types
// ============================================================================

/// Position in an expression for targeted rewriting.
///
/// Used by conv tactics to navigate to specific subexpressions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConvPosition {
    /// The root expression
    Root,
    /// Function in application (f x) - go to f
    AppFn,
    /// Argument in application (f x) - go to x
    AppArg,
    /// Body of lambda/forall (λ x, body / ∀ x, body)
    BinderBody,
    /// Type of lambda/forall (λ x : T, body / ∀ x : T, body)
    BinderType,
    /// Value in let binding (let x := v in body)
    LetValue,
    /// Body in let binding (let x := v in body)
    LetBody,
    /// Type in let binding (let x : T := v in body)
    LetType,
    /// Left-hand side of equality (a = b) - go to a
    EqLhs,
    /// Right-hand side of equality (a = b) - go to b
    EqRhs,
}

/// A path through an expression tree for conv navigation.
pub type ConvPath = Vec<ConvPosition>;

// ============================================================================
// Conv State
// ============================================================================

/// State for conv-mode rewriting
pub struct ConvState {
    /// The original expression being rewritten
    pub original: Expr,
    /// Current position in the expression tree
    pub path: ConvPath,
    /// The focused subexpression at current position
    pub focus: Expr,
}

impl ConvState {
    /// Create a new conv state focused on the given expression.
    ///
    /// REQUIRES: `expr` is a well-formed kernel expression
    ///
    /// ENSURES: `self.original == expr`, `self.focus == expr`, `self.path` is empty
    pub fn new(expr: Expr) -> Self {
        ConvState {
            original: expr.clone(),
            path: vec![],
            focus: expr,
        }
    }

    /// Rebuild an n-ary application after replacing one of its arguments.
    fn replace_app_arg(
        expr: &Expr,
        arg_idx: usize,
        rest: &[ConvPosition],
        replacement: &Expr,
    ) -> Option<Expr> {
        let mut args: Vec<Expr> = expr.get_app_args().into_iter().cloned().collect();
        if args.len() <= arg_idx {
            return None;
        }

        args[arg_idx] = Self::replace_at_position(&args[arg_idx], rest, replacement)?;
        let mut rebuilt = expr.get_app_fn().clone();
        for arg in args {
            rebuilt = Expr::app(rebuilt, arg);
        }
        Some(rebuilt)
    }

    /// Replace the expression at a given position.
    ///
    /// Part of #2477: pub(crate) to allow eval_conv_goal to reconstruct the
    /// full expression after conv navigation + rewrite.
    pub(crate) fn replace_at_position(
        expr: &Expr,
        path: &[ConvPosition],
        replacement: &Expr,
    ) -> Option<Expr> {
        stack_safe(|| {
            if path.is_empty() {
                return Some(replacement.clone());
            }

            let (head, rest) = (&path[0], &path[1..]);
            match (head, expr.kind()) {
                (ConvPosition::Root, _) => Self::replace_at_position(expr, rest, replacement),
                (ConvPosition::AppFn, ExprKind::App(f, a)) => {
                    let new_f = Self::replace_at_position(f, rest, replacement)?;
                    Some(Expr::app(new_f, (**a).clone()))
                }
                (ConvPosition::AppArg, ExprKind::App(f, a)) => {
                    let new_a = Self::replace_at_position(a, rest, replacement)?;
                    Some(Expr::app((**f).clone(), new_a))
                }
                (ConvPosition::BinderBody, ExprKind::Lam(bi, ty, body)) => {
                    let new_body = Self::replace_at_position(body, rest, replacement)?;
                    Some(Expr::lam(*bi, (**ty).clone(), new_body))
                }
                (ConvPosition::BinderBody, ExprKind::Pi(bi, ty, body)) => {
                    let new_body = Self::replace_at_position(body, rest, replacement)?;
                    Some(Expr::pi(*bi, (**ty).clone(), new_body))
                }
                (ConvPosition::BinderType, ExprKind::Lam(bi, ty, body)) => {
                    let new_ty = Self::replace_at_position(ty, rest, replacement)?;
                    Some(Expr::lam(*bi, new_ty, (**body).clone()))
                }
                (ConvPosition::BinderType, ExprKind::Pi(bi, ty, body)) => {
                    let new_ty = Self::replace_at_position(ty, rest, replacement)?;
                    Some(Expr::pi(*bi, new_ty, (**body).clone()))
                }
                (ConvPosition::LetValue, ExprKind::Let(name, ty, val, body, non_dep)) => {
                    let new_val = Self::replace_at_position(val, rest, replacement)?;
                    Some(Expr::let_named(
                        name.clone(),
                        (**ty).clone(),
                        new_val,
                        (**body).clone(),
                        *non_dep,
                    ))
                }
                (ConvPosition::LetBody, ExprKind::Let(name, ty, val, body, non_dep)) => {
                    let new_body = Self::replace_at_position(body, rest, replacement)?;
                    Some(Expr::let_named(
                        name.clone(),
                        (**ty).clone(),
                        (**val).clone(),
                        new_body,
                        *non_dep,
                    ))
                }
                (ConvPosition::LetType, ExprKind::Let(name, ty, val, body, non_dep)) => {
                    let new_ty = Self::replace_at_position(ty, rest, replacement)?;
                    Some(Expr::let_named(
                        name.clone(),
                        new_ty,
                        (**val).clone(),
                        (**body).clone(),
                        *non_dep,
                    ))
                }
                (ConvPosition::EqLhs, _) => Self::replace_app_arg(expr, 1, rest, replacement),
                (ConvPosition::EqRhs, _) => Self::replace_app_arg(expr, 2, rest, replacement),
                _ => None,
            }
        })
    }

    /// Navigate to a subexpression.
    ///
    /// REQUIRES: `pos` is compatible with the current `self.focus` expression
    /// kind (e.g., AppFn requires focus to be an App)
    ///
    /// ENSURES: on Ok, `self.path` has `pos` appended and `self.focus` is
    /// the subexpression at that position; on Err, state is unchanged
    pub fn go(&mut self, pos: ConvPosition) -> Result<(), TacticError> {
        let new_focus = match (&pos, self.focus.kind()) {
            (ConvPosition::Root, _) => self.original.clone(),
            (ConvPosition::AppFn, ExprKind::App(f, _)) => (**f).clone(),
            (ConvPosition::AppArg, ExprKind::App(_, a)) => (**a).clone(),
            (ConvPosition::BinderBody, ExprKind::Lam(_, _, body))
            | (ConvPosition::BinderBody, ExprKind::Pi(_, _, body))
            | (ConvPosition::LetBody, ExprKind::Let(_, _, _, body, _)) => (**body).clone(),
            (ConvPosition::BinderType, ExprKind::Lam(_, ty, _))
            | (ConvPosition::BinderType, ExprKind::Pi(_, ty, _))
            | (ConvPosition::LetType, ExprKind::Let(_, ty, _, _, _)) => (**ty).clone(),
            (ConvPosition::LetValue, ExprKind::Let(_, _, val, _, _)) => (**val).clone(),
            (ConvPosition::EqLhs, _) => {
                let args = self.focus.get_app_args();
                if args.len() >= 2 {
                    args[1].clone()
                } else {
                    return Err(TacticError::GoalMismatch(
                        "cannot go to lhs - not an equality".into(),
                    ));
                }
            }
            (ConvPosition::EqRhs, _) => {
                let args = self.focus.get_app_args();
                if args.len() >= 3 {
                    args[2].clone()
                } else {
                    return Err(TacticError::GoalMismatch(
                        "cannot go to rhs - not an equality".into(),
                    ));
                }
            }
            _ => {
                return Err(TacticError::InvalidTarget {
                    tactic: "conv".into(),
                    detail: format!("cannot navigate {pos:?} at this position"),
                })
            }
        };

        self.path.push(pos);
        self.focus = new_focus;
        Ok(())
    }

    /// Apply a rewrite to the focused expression.
    ///
    /// REQUIRES: `from` and `to` are well-formed expressions
    ///
    /// ENSURES: returns true iff `from` appears in `self.focus`, in which
    /// case all occurrences of `from` are replaced by `to`; returns false
    /// with `self.focus` unchanged if `from` is not found
    pub fn rewrite_focus(&mut self, from: &Expr, to: &Expr) -> bool {
        if contains_expr(&self.focus, from) {
            self.focus = replace_expr(&self.focus, from, to);
            true
        } else {
            false
        }
    }

    /// Get the final expression after all modifications.
    ///
    /// REQUIRES: all `go()` navigations used valid positions
    ///
    /// ENSURES: returns `self.original` with the subexpression at `self.path`
    /// replaced by `self.focus`; if path is empty returns `self.focus` directly
    pub fn finish(&self) -> Expr {
        if self.path.is_empty() {
            self.focus.clone()
        } else {
            ConvState::replace_at_position(&self.original, &self.path, &self.focus)
                .unwrap_or_else(|| self.original.clone())
        }
    }
}

// ============================================================================
// Conv Tactics
// ============================================================================

/// Targeted rewrite using conv-style navigation.
///
/// Allows rewriting at specific positions in the goal using a path.
///
/// REQUIRES: `state.goals` is non-empty; `hyp_name` exists in the current
/// goal's local context and has equality type
///
/// ENSURES: on Ok, the goal target is rewritten at the position specified
/// by `path` using the hypothesis equality (reversed if `reverse` is true);
/// on Err(NoProgress), the hypothesis LHS was not found at the target position
///
/// # Example
/// ```text
/// -- Goal: f (a + b) = f (b + a)
/// conv_rw [AppArg, AppArg] h  -- rewrites inner (a + b) using h : a + b = b + a
/// ```
pub fn conv_rw(
    state: &mut ProofState,
    path: ConvPath,
    hyp_name: &str,
    reverse: bool,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    // Find the hypothesis
    let hyp_decl = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?
        .clone();

    // Check that the hypothesis is an equality
    let hyp_ty = state.whnf(&goal, &hyp_decl.ty);
    let (eq_type, lhs, rhs, eq_levels) = match_equality(&hyp_ty)?;

    let (from, to) = if reverse {
        (rhs.clone(), lhs.clone())
    } else {
        (lhs.clone(), rhs.clone())
    };

    // Create conv state and navigate to position
    let mut conv = ConvState::new(target.clone());
    for pos in &path {
        conv.go(pos.clone())?;
    }
    let focus_before = conv.focus.clone();

    // Apply the rewrite at the focused position
    if !conv.rewrite_focus(&from, &to) {
        return Err(TacticError::RewriteNoMatch {
            tactic: "conv_rw".to_owned(),
            rule: hyp_name.to_owned(),
            direction: if reverse { "backward" } else { "forward" }.to_owned(),
            searched_for: from.to_string(),
            focus: focus_before.to_string(),
            focus_path: path.iter().map(|pos| format!("{pos:?}")).collect(),
            candidates: rewrite_candidate_summaries(&focus_before, &from, 5),
        });
    }
    let focus_after = conv.focus.clone();

    // Get the new target
    let new_target = conv.finish();
    if new_target == target {
        return Err(TacticError::NoProgress {
            tactic: "conv_rw".into(),
        });
    }

    match state.replace_target_def_eq(new_target.clone()) {
        Ok(()) => Ok(()),
        Err(TacticError::GoalMismatch(_)) => {
            let leaf_eq_proof = if reverse {
                let symm = Expr::const_(Name::from_string("Eq.symm"), eq_levels.clone());
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(symm, eq_type.clone()), lhs.clone()),
                        rhs.clone(),
                    ),
                    Expr::fvar(hyp_decl.fvar),
                )
            } else {
                Expr::fvar(hyp_decl.fvar)
            };

            let Some(target_eq_proof) = build_conv_rewrite_eq_proof(
                state,
                &goal,
                ConvRewriteProofInputs {
                    target: &target,
                    path: &path,
                    focus_before: &focus_before,
                    focus_after: &focus_after,
                    from: &from,
                    to: &to,
                    from_ty: &eq_type,
                    leaf_eq_proof,
                },
            )?
            else {
                return Err(TacticError::RewriteProofLiftFailed {
                    tactic: "conv_rw".to_owned(),
                    rule: hyp_name.to_owned(),
                    direction: if reverse { "backward" } else { "forward" }.to_owned(),
                    searched_for: from.to_string(),
                    replacement: to.to_string(),
                    focus_before: focus_before.to_string(),
                    focus_after: focus_after.to_string(),
                    focus_path: path.iter().map(|pos| format!("{pos:?}")).collect(),
                });
            };
            state.replace_target_eq(new_target, target_eq_proof)
        }
        Err(err) => Err(err),
    }
}

/// Rewrite the left-hand side of an equality goal.
///
/// For goal `a = b`, applies a rewrite to just the `a` part.
///
/// REQUIRES: goal target is an equality; `hyp_name` has equality type in context
///
/// ENSURES: on Ok, only the LHS of the equality is rewritten
pub fn conv_lhs(state: &mut ProofState, hyp_name: &str, reverse: bool) -> TacticResult {
    conv_rw(state, vec![ConvPosition::EqLhs], hyp_name, reverse)
}

/// Rewrite the right-hand side of an equality goal.
///
/// For goal `a = b`, applies a rewrite to just the `b` part.
///
/// REQUIRES: goal target is an equality; `hyp_name` has equality type in context
///
/// ENSURES: on Ok, only the RHS of the equality is rewritten
pub fn conv_rhs(state: &mut ProofState, hyp_name: &str, reverse: bool) -> TacticResult {
    conv_rw(state, vec![ConvPosition::EqRhs], hyp_name, reverse)
}

/// Navigate into an argument of the goal and apply a tactic.
///
/// For goal `f x`, `conv_arg` applies a transformation to just `x`.
///
/// REQUIRES: current goal target is an application (ExprKind::App)
///
/// ENSURES: on Ok, the argument subexpression is transformed by the tactic
/// while the function head is preserved; on Err(GoalMismatch), goal is not App
/// or the rebuilt application is not definitionally equal to the original goal
pub fn conv_arg<F>(state: &mut ProofState, tactic: F) -> TacticResult
where
    F: FnOnce(&mut ProofState) -> TacticResult,
{
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Extract the argument if this is an application
    match goal.target.kind() {
        ExprKind::App(_, arg) => {
            // Create a temporary state focused on the argument
            let mut temp_state = state.clone_with_fresh_goal_target((**arg).clone());

            // Apply the tactic
            tactic(&mut temp_state)?;

            // Get the transformed argument
            if let Some(new_goal) = temp_state.current_goal() {
                // Reconstruct with new argument
                if let ExprKind::App(f, _) = goal.target.kind() {
                    let new_target = Expr::app((**f).clone(), new_goal.target.clone());
                    return match state.replace_target_def_eq(new_target) {
                        Ok(()) => Ok(()),
                        Err(TacticError::GoalMismatch(_)) => Err(TacticError::GoalMismatch(
                            "conv_arg: direct helper only supports definitionally equal argument rewrites"
                                .to_string(),
                        )),
                        Err(err) => Err(err),
                    };
                }
            }

            Ok(())
        }
        _ => Err(TacticError::GoalMismatch(
            "conv_arg: goal is not an application".to_string(),
        )),
    }
}
