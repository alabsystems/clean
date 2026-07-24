// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! dsimp tactic: Definitional simplification.

use std::sync::Arc;

use crate::stack_safe;
use clean_kernel::{Environment, Expr, ExprKind};

use super::super::{ProofState, TacticError, TacticResult};

/// Configuration for dsimp tactic.
#[derive(Debug, Clone)]
pub struct DsimpConfig {
    /// Whether to simplify in hypotheses too
    pub at_hyps: bool,
    /// Maximum simplification depth
    pub max_depth: usize,
    /// Whether to use beta reduction
    pub beta: bool,
    /// Whether to use eta reduction
    pub eta: bool,
    /// Whether to use zeta reduction (let expansion)
    pub zeta: bool,
    /// Whether to use iota reduction (recursor computation)
    pub iota: bool,
}

impl Default for DsimpConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl DsimpConfig {
    /// Create default configuration
    pub fn new() -> Self {
        Self {
            at_hyps: false,
            max_depth: 100,
            beta: true,
            eta: true,
            zeta: true,
            iota: true,
        }
    }

    /// Simplify at hypotheses too
    #[must_use]
    pub fn at_all(mut self) -> Self {
        self.at_hyps = true;
        self
    }

    /// Set beta reduction
    #[must_use]
    pub fn with_beta(mut self, beta: bool) -> Self {
        self.beta = beta;
        self
    }

    /// Set eta reduction
    #[must_use]
    pub fn with_eta(mut self, eta: bool) -> Self {
        self.eta = eta;
        self
    }

    /// Set zeta reduction
    #[must_use]
    pub fn with_zeta(mut self, zeta: bool) -> Self {
        self.zeta = zeta;
        self
    }

    /// Set iota reduction
    #[must_use]
    pub fn with_iota(mut self, iota: bool) -> Self {
        self.iota = iota;
        self
    }
}

/// Apply definitional simplification to the goal.
///
/// `dsimp` simplifies expressions using only definitional equality rules
/// (beta, eta, zeta, iota reductions). Unlike `simp`, it does not use
/// rewrite lemmas and produces definitionally equal terms.
///
/// # Reductions
/// - **Beta**: `(lambda x, e) a` -> `e[x := a]`
/// - **Eta**: `lambda x, f x` -> `f` (when `x` not free in `f`)
/// - **Zeta**: `let x := v in e` -> `e[x := v]`
/// - **Iota**: Recursor computation rules
///
/// # Example
/// ```text
/// -- Goal: (lambda x, x + 1) 5 = 6
/// dsimp
/// -- Goal: 5 + 1 = 6
/// ```
///
/// # Errors
/// - `NoGoals` if there are no goals
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: Equivalent to `dsimp_with_config(state, DsimpConfig::new())`
pub fn dsimp(state: &mut ProofState) -> TacticResult {
    dsimp_with_config(state, DsimpConfig::new())
}

/// dsimp with custom configuration
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the goal target is replaced by a definitionally equal expression reduced according to `config`
/// ENSURES: If `config.at_hyps`, every local hypothesis type is likewise simplified with the same reduction settings
/// ENSURES: On Ok, no new goals are created or removed
pub fn dsimp_with_config(state: &mut ProofState, config: DsimpConfig) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);
    let env = state.env().clone();

    // Apply definitional simplification
    let new_target = dsimp_expr(&target, &env, &config, 0);

    let target_changed = new_target != target;
    if target_changed {
        // Part of #2477: use replace_target_def_eq instead of in-place mutation.
        // dsimp reductions (beta, eta, zeta, iota) are definitionally equal.
        state.replace_target_def_eq(new_target)?;
    }

    // Simplify hypotheses when at_hyps is set (e.g., `dsimp at *`).
    // This must run even when the goal target didn't change.
    if config.at_hyps {
        state.rewrite_local_decl_types_def_eq(|ty| dsimp_expr(ty, &env, &config, 0))?;
    }

    Ok(())
}

/// Recursively apply dsimp to all sub-expressions (structural traversal only).
fn dsimp_recurse(expr: &Expr, env: &Environment, config: &DsimpConfig, depth: usize) -> Expr {
    let d = depth + 1;
    match expr.kind() {
        ExprKind::App(f, a) => {
            Expr::app(dsimp_expr(f, env, config, d), dsimp_expr(a, env, config, d))
        }
        ExprKind::Lam(bi, ty, body) => Expr::lam(
            *bi,
            dsimp_expr(ty, env, config, d),
            dsimp_expr(body, env, config, d),
        ),
        ExprKind::Pi(bi, ty, body) => Expr::pi(
            *bi,
            dsimp_expr(ty, env, config, d),
            dsimp_expr(body, env, config, d),
        ),
        ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
            name.clone(),
            dsimp_expr(ty, env, config, d),
            dsimp_expr(val, env, config, d),
            dsimp_expr(body, env, config, d),
            *non_dep,
        ),
        ExprKind::Proj(name, idx, e) => {
            Expr::proj(name.clone(), *idx, dsimp_expr(e, env, config, d))
        }
        ExprKind::MData(mdata, e) => Expr::mdata(mdata.clone(), dsimp_expr(e, env, config, d)),
        ExprKind::Squash(e) => {
            Expr::from_kind(ExprKind::Squash(Arc::new(dsimp_expr(e, env, config, d))))
        }
        // Leaf nodes (FVar, Sort, Const, Lit, SProp, BVar) and cubical extensions
        _ => expr.clone(),
    }
}

/// Apply definitional simplification to an expression
fn dsimp_expr(expr: &Expr, env: &Environment, config: &DsimpConfig, depth: usize) -> Expr {
    stack_safe(|| {
        if depth > config.max_depth {
            return expr.clone();
        }

        match expr.kind() {
            // Beta reduction: (lambda x, e) a -> e[x := a]
            ExprKind::App(func, arg) if config.beta => {
                let func_reduced = dsimp_expr(func, env, config, depth + 1);
                let arg_reduced = dsimp_expr(arg, env, config, depth + 1);

                if let ExprKind::Lam(_bi, _ty, body) = func_reduced.kind() {
                    // Delegate to kernel's ExprFolderOpt-based instantiate (#2141)
                    let result = body.instantiate(&arg_reduced);
                    return dsimp_expr(&result, env, config, depth + 1);
                }

                Expr::app(func_reduced, arg_reduced)
            }

            // Zeta reduction: let x := v in e -> e[x := v]
            ExprKind::Let(_, _ty, value, body, _) if config.zeta => {
                let value_reduced = dsimp_expr(value, env, config, depth + 1);
                // Delegate to kernel's ExprFolderOpt-based instantiate (#2141)
                let result = body.instantiate(&value_reduced);
                dsimp_expr(&result, env, config, depth + 1)
            }

            // Eta reduction: lambda x, f x -> f (when x not free in f)
            ExprKind::Lam(bi, binder_type, body) if config.eta => {
                let body_reduced = dsimp_expr(body, env, config, depth + 1);

                if let ExprKind::App(func, arg) = body_reduced.kind() {
                    if matches!(arg.kind(), ExprKind::BVar(idx) if *idx == 0)
                        // Delegate to kernel's has_loose_bvar (#2141)
                        && !func.has_loose_bvar(0)
                    {
                        // BVar(0) doesn't occur in func; instantiate just
                        // decrements all BVar(i>0) to BVar(i-1). (#2141)
                        return func.instantiate(&Expr::bvar(0));
                    }
                }

                Expr::lam(
                    *bi,
                    dsimp_expr(binder_type, env, config, depth + 1),
                    body_reduced,
                )
            }

            // Structural recursion for all other expression forms
            _ => dsimp_recurse(expr, env, config, depth),
        }
    })
}

/// Check if a bound variable occurs in an expression (for dsimp).
///
/// Delegates to the kernel's `Expr::has_loose_bvar` which correctly handles
/// all ExprKind variants via metadata and recursive traversal. (#2141)
///
/// # Contract
///
/// REQUIRES: `expr` is a well-formed expression
/// ENSURES: Returns `true` iff `bvar(idx)` occurs free (at depth 0) in `expr`
pub(crate) fn occurs_bvar_dsimp(expr: &Expr, idx: u32) -> bool {
    expr.has_loose_bvar(idx)
}

/// Shift bound variable indices by delta for variables >= cutoff (for dsimp).
///
/// For positive delta, delegates to the kernel's `Expr::lift_from` (aka `lift_at`)
/// which uses `ExprFolderOpt` to correctly handle all ExprKind variants. (#2141)
///
/// For negative delta with cutoff=0 and delta=-1, uses `Expr::instantiate` to
/// decrement all BVar indices by 1 (safe only when BVar(0) is not free in expr).
///
/// # Contract
///
/// REQUIRES: For negative `delta`, every affected `bvar(i)` satisfies `i >= cutoff + |delta|`
/// ENSURES: Every `bvar(i)` with `i >= cutoff` is replaced by `bvar(i + delta)`
/// ENSURES: Binder bodies recurse with `cutoff + 1`, preserving de Bruijn scoping
pub(crate) fn shift_bvars_dsimp(expr: &Expr, delta: i32, cutoff: u32) -> Expr {
    if delta == 0 {
        return expr.clone();
    }
    if delta > 0 {
        expr.lift_from(cutoff, delta as u32)
    } else {
        // Negative shift: only delta=-1, cutoff=0 is used (eta reduction).
        debug_assert_eq!(
            delta, -1,
            "shift_bvars_dsimp only supports delta=-1 for negative shifts"
        );
        debug_assert_eq!(
            cutoff, 0,
            "shift_bvars_dsimp only supports cutoff=0 for negative shifts"
        );
        // instantiate replaces BVar(0) (which must not exist per precondition)
        // and decrements all BVar(i>0) to BVar(i-1).
        expr.instantiate(&Expr::bvar(0))
    }
}

/// Apply dsimp to a specific hypothesis
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` names a local hypothesis in the current goal
/// ENSURES: On Ok, only the named hypothesis type is replaced by its `dsimp` normal form
/// ENSURES: On Ok, the goal target is unchanged
pub fn dsimp_at(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let env = state.env().clone();
    let config = DsimpConfig::new();
    state.rewrite_named_local_decl_type_def_eq(hyp_name, |ty| dsimp_expr(ty, &env, &config, 0))
}

/// Apply dsimp to all hypotheses and the goal
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: Equivalent to `dsimp_with_config(state, DsimpConfig::new().at_all())`
pub fn dsimp_all(state: &mut ProofState) -> TacticResult {
    dsimp_with_config(state, DsimpConfig::new().at_all())
}
