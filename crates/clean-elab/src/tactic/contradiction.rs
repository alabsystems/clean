// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Enhanced contradiction, exfalso, and absurd tactics.
//!
//! Extends the base tactics in `connective.rs` with additional contradiction
//! patterns:
//!
//! - `h : True = False` (propositional absurdity)
//! - `h : Nat.zero = Nat.succ n` or `h : Nat.succ n = Nat.zero` (constructor discrimination)
//! - `eval_absurd` closes any goal given `proof : P` and `neg_proof : ¬P`
//!
//! The `eval_*` functions use the [`TacticCtx`] combinator API and are suitable
//! for registry dispatch.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Level};

use super::combinators::TacticCtx;
use super::core::{Goal, LocalDecl, ProofState, TacticError, TacticResult};
use super::equality::match_equality;

/// Check whether an expression is the constant `True`.
fn is_true_const(expr: &Expr) -> bool {
    matches!(expr.kind(), ExprKind::Const(n, _) if n.to_string() == "True")
}

/// Check whether an expression is the constant `False`.
fn is_false_const(expr: &Expr) -> bool {
    matches!(expr.kind(), ExprKind::Const(n, _) if n.to_string() == "False")
}

/// Try to close the goal from a hypothesis whose type is an equality between
/// distinct constructors of the same inductive type (e.g., `Nat.zero = Nat.succ n`).
///
/// Returns `Ok(true)` if the goal was closed, `Ok(false)` if the hypothesis
/// does not match the pattern. On error the proof state is unchanged.
fn try_discriminate_hyp(
    state: &mut ProofState,
    goal: &Goal,
    decl: &LocalDecl,
) -> Result<bool, TacticError> {
    let ty = state.metas.instantiate(&decl.ty);
    let ty_whnf = state.whnf(goal, &ty);

    // Check if it's an equality
    let (_eq_type, lhs, rhs, _eq_levels) = match match_equality(&ty_whnf) {
        Ok(tuple) => tuple,
        Err(_) => return Ok(false),
    };

    let lhs_whnf = state.whnf(goal, &lhs);
    let rhs_whnf = state.whnf(goal, &rhs);

    let lhs_head = lhs_whnf.get_app_fn();
    let rhs_head = rhs_whnf.get_app_fn();

    let lhs_name = match lhs_head.kind() {
        ExprKind::Const(name, _) => name.clone(),
        _ => return Ok(false),
    };
    let rhs_name = match rhs_head.kind() {
        ExprKind::Const(name, _) => name.clone(),
        _ => return Ok(false),
    };

    // Same constructor → not a discrimination target
    if lhs_name == rhs_name {
        return Ok(false);
    }

    // Both must be constructors of the same inductive type
    let lhs_ctor = match state.env.get_constructor(&lhs_name) {
        Some(c) => c.clone(),
        None => return Ok(false),
    };
    let rhs_ctor = match state.env.get_constructor(&rhs_name) {
        Some(c) => c.clone(),
        None => return Ok(false),
    };

    if lhs_ctor.inductive_name != rhs_ctor.inductive_name {
        return Ok(false);
    }

    // Build T.noConfusion proof
    let ind_name = &lhs_ctor.inductive_name;
    let no_confusion_name = Name::from_string(&format!("{ind_name}.noConfusion"));

    let nc_level_count = state
        .env
        .get_const(&no_confusion_name)
        .ok_or_else(|| TacticError::EnvironmentMissing {
            constant: no_confusion_name.to_string(),
        })?
        .level_params
        .len();

    let ind_levels = match lhs_head.kind() {
        ExprKind::Const(_, lvls) => lvls.to_vec(),
        _ => vec![],
    };
    let nc_levels = if nc_level_count > ind_levels.len() {
        let motive_level = state
            .infer_type(goal, &goal.target)
            .ok()
            .and_then(|ty| match ty.kind() {
                ExprKind::Sort(level) => Some(level.clone()),
                _ => None,
            })
            .unwrap_or_else(Level::zero);
        [vec![motive_level], ind_levels].concat()
    } else {
        ind_levels
    };

    let nc = Expr::const_(no_confusion_name, nc_levels);
    let mut proof = nc;
    proof = Expr::app(proof, goal.target.clone());
    proof = Expr::app(proof, lhs_whnf.clone());
    proof = Expr::app(proof, rhs_whnf.clone());
    proof = Expr::app(proof, Expr::fvar(decl.fvar));

    state.close_goal(goal, proof)?;
    Ok(true)
}

/// Try to close the goal from `h : True = False` or `h : False = True`.
///
/// Returns `Ok(true)` if the goal was closed, `Ok(false)` if the hypothesis
/// does not match.
fn try_true_eq_false(
    state: &mut ProofState,
    goal: &Goal,
    decl: &LocalDecl,
) -> Result<bool, TacticError> {
    let ty = state.metas.instantiate(&decl.ty);
    let ty_whnf = state.whnf(goal, &ty);

    let (eq_type, lhs, rhs, eq_levels) = match match_equality(&ty_whnf) {
        Ok(tuple) => tuple,
        Err(_) => return Ok(false),
    };

    let lhs_whnf = state.whnf(goal, &lhs);
    let rhs_whnf = state.whnf(goal, &rhs);

    // Case 1: True = False
    // Case 2: False = True (use Eq.symm first)
    let (is_true_false, needs_symm) = if is_true_const(&lhs_whnf) && is_false_const(&rhs_whnf) {
        (true, false)
    } else if is_false_const(&lhs_whnf) && is_true_const(&rhs_whnf) {
        (true, true)
    } else {
        (false, false)
    };

    if !is_true_false {
        return Ok(false);
    }

    // Build a proof of False from h : True = False
    // Strategy: True.intro : True, then subst h into True to get False
    // Or more directly: h ▸ True.intro should give False
    //
    // Concrete approach: Eq.mp h True.intro
    // Eq.mp : {α β : Sort u} → α = β → α → β
    // Eq.mp (h : True = False) (True.intro : True) : False
    let true_const = Expr::const_(Name::from_string("True"), vec![]);
    let false_const = Expr::const_(Name::from_string("False"), vec![]);

    // Build the hypothesis expression, applying Eq.symm if needed
    let hyp_expr = if needs_symm {
        // Eq.symm {Prop} {False} {True} h : True = False
        let symm = Expr::const_(Name::from_string("Eq.symm"), eq_levels.clone());
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(symm, eq_type), false_const.clone()),
                true_const.clone(),
            ),
            Expr::fvar(decl.fvar),
        )
    } else {
        Expr::fvar(decl.fvar)
    };

    // Eq.mp {Prop} {True} {False} hyp True.intro : False
    let eq_mp = Expr::const_(Name::from_string("Eq.mp"), vec![Level::succ(Level::zero())]);
    let false_proof = Expr::app(
        Expr::app(
            Expr::app(Expr::app(eq_mp, Expr::prop()), true_const),
            false_const,
        ),
        hyp_expr,
    );
    let false_proof = Expr::app(
        false_proof,
        Expr::const_(Name::from_string("True.intro"), vec![]),
    );

    // Now use False.elim to close the goal
    let false_elim = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
    let proof = Expr::app(Expr::app(false_elim, goal.target.clone()), false_proof);

    state.close_goal(goal, proof)?;
    Ok(true)
}

/// Try to close the goal by finding `h1 : P` and `h2 : P → False` in context.
///
/// O(n²) pairwise search over hypotheses. Returns `Ok(true)` if goal was closed.
fn try_absurd_pair(
    state: &mut ProofState,
    goal: &Goal,
    false_type: &Expr,
) -> Result<bool, TacticError> {
    for decl1 in &goal.local_ctx {
        let ty1 = state.metas.instantiate(&decl1.ty);
        let ty1_whnf = state.whnf(goal, &ty1);

        for decl2 in &goal.local_ctx {
            if decl1.fvar == decl2.fvar {
                continue;
            }
            let ty2 = state.metas.instantiate(&decl2.ty);
            let ty2_whnf = state.whnf(goal, &ty2);

            if let ExprKind::Pi(_, domain, codomain) = ty2_whnf.kind() {
                let domain_whnf = state.whnf(goal, domain);
                let codomain_whnf = state.whnf(goal, codomain);

                if state.is_def_eq(goal, &domain_whnf, &ty1_whnf)
                    && state.is_def_eq(goal, &codomain_whnf, false_type)
                {
                    let absurd_name = Name::from_string("absurd");
                    if state.env.get_const(&absurd_name).is_some() {
                        let absurd = Expr::const_(absurd_name, vec![Level::zero()]);
                        let proof = Expr::app(
                            Expr::app(
                                Expr::app(Expr::app(absurd, ty1_whnf.clone()), goal.target.clone()),
                                Expr::fvar(decl1.fvar),
                            ),
                            Expr::fvar(decl2.fvar),
                        );
                        state.close_goal(goal, proof)?;
                        return Ok(true);
                    }
                    // Fallback: False.elim {goal} (h2 h1)
                    let false_elim =
                        Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
                    let proof = Expr::app(
                        Expr::app(false_elim, goal.target.clone()),
                        Expr::app(Expr::fvar(decl2.fvar), Expr::fvar(decl1.fvar)),
                    );
                    state.close_goal(goal, proof)?;
                    return Ok(true);
                }
            }
        }
    }
    Ok(false)
}

/// Enhanced `contradiction` tactic.
///
/// Searches the local context for contradictions using these patterns
/// (checked in order):
///
/// 1. `h : False` — directly applies `False.elim`
/// 2. `h : True = False` or `h : False = True` — derives `False` via `Eq.mp`
/// 3. `h : C₁ args = C₂ args` where `C₁ ≠ C₂` — constructor discrimination
/// 4. `h1 : P` + `h2 : ¬P` (or `h2 : P → False`) — applies `absurd`
///
/// # Contract
///
/// REQUIRES: `ctx.state.goals` is non-empty
/// ENSURES: On Ok, the current goal is closed
/// ENSURES: On Err(NoProgress), no matching contradiction pattern found
/// ENSURES: Search is O(n²) in hypothesis count for the P/¬P pattern
pub fn eval_contradiction(ctx: &mut TacticCtx<'_>) -> TacticResult {
    let goal = ctx
        .state
        .current_goal()
        .ok_or(TacticError::NoGoals)?
        .clone();
    let false_type = Expr::const_(Name::from_string("False"), vec![]);

    // Pattern 1: h : False
    for decl in &goal.local_ctx {
        let ty = ctx.state.metas.instantiate(&decl.ty);
        let ty_whnf = ctx.state.whnf(&goal, &ty);
        if ctx.state.is_def_eq(&goal, &ty_whnf, &false_type) {
            let false_elim = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
            let proof = Expr::app(
                Expr::app(false_elim, goal.target.clone()),
                Expr::fvar(decl.fvar),
            );
            return ctx.state.close_goal(&goal, proof);
        }
    }

    // Pattern 2: h : True = False or h : False = True
    for decl in &goal.local_ctx {
        if try_true_eq_false(ctx.state, &goal, decl)? {
            return Ok(());
        }
    }

    // Pattern 3: h : C₁ args = C₂ args (constructor discrimination)
    for decl in &goal.local_ctx {
        if try_discriminate_hyp(ctx.state, &goal, decl)? {
            return Ok(());
        }
    }

    // Pattern 4: h1 : P and h2 : P → False (i.e., ¬P)
    if try_absurd_pair(ctx.state, &goal, &false_type)? {
        return Ok(());
    }

    Err(TacticError::NoProgress {
        tactic: "contradiction".into(),
    })
}

/// Enhanced `exfalso` tactic via `TacticCtx`.
///
/// Changes the current goal to `False` using `False.elim`.
///
/// # Contract
///
/// REQUIRES: `ctx.state.goals` is non-empty
/// REQUIRES: `False.elim` exists in the environment
/// ENSURES: On Ok, current goal is replaced with a `False` goal
/// ENSURES: On Err(EnvironmentMissing), `False.elim` not loaded
pub fn eval_exfalso(ctx: &mut TacticCtx<'_>) -> TacticResult {
    super::connective::exfalso(ctx.state)
}

/// The `absurd` tactic: given `proof : P` and `neg_proof : ¬P`, close any goal.
///
/// Constructs `absurd proof neg_proof : goal.target` using the `absurd` constant
/// from the environment, or falls back to `False.elim (neg_proof proof)`.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `proof : P` and `neg_proof : P → False` for some proposition `P`
/// ENSURES: On Ok, the current goal is closed
/// ENSURES: On Err, proof state is unchanged
pub fn eval_absurd(state: &mut ProofState, proof: Expr, neg_proof: Expr) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Infer the type of the proof to get P
    let p_ty = state
        .infer_type(&goal, &proof)
        .map_err(|_| TacticError::TypeMismatch {
            expected: "a well-typed term".into(),
            actual: "could not infer type of proof argument".into(),
        })?;

    // Check that neg_proof has type P → False
    let neg_ty = state
        .infer_type(&goal, &neg_proof)
        .map_err(|_| TacticError::TypeMismatch {
            expected: "a well-typed term".into(),
            actual: "could not infer type of negation argument".into(),
        })?;

    let false_type = Expr::const_(Name::from_string("False"), vec![]);
    let neg_whnf = state.whnf(&goal, &neg_ty);
    match neg_whnf.kind() {
        ExprKind::Pi(_, domain, codomain) => {
            let domain_whnf = state.whnf(&goal, domain);
            let codomain_whnf = state.whnf(&goal, codomain);
            let p_whnf = state.whnf(&goal, &p_ty);

            if !state.is_def_eq(&goal, &domain_whnf, &p_whnf) {
                return Err(TacticError::TypeMismatch {
                    expected: format!("{p_ty:?} → False"),
                    actual: format!("{neg_ty:?}"),
                });
            }
            if !state.is_def_eq(&goal, &codomain_whnf, &false_type) {
                return Err(TacticError::TypeMismatch {
                    expected: "codomain to be False".into(),
                    actual: format!("{codomain:?}"),
                });
            }
        }
        _ => {
            return Err(TacticError::TypeMismatch {
                expected: "negation (P → False)".into(),
                actual: format!("{neg_ty:?}"),
            });
        }
    }

    // Try using the absurd constant if available
    let absurd_name = Name::from_string("absurd");
    if state.env.get_const(&absurd_name).is_some() {
        let absurd = Expr::const_(absurd_name, vec![Level::zero()]);
        let proof_term = Expr::app(
            Expr::app(
                Expr::app(Expr::app(absurd, p_ty), goal.target.clone()),
                proof,
            ),
            neg_proof,
        );
        return state.close_goal(&goal, proof_term);
    }

    // Fallback: False.elim {goal} (neg_proof proof)
    let false_elim = Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]);
    let proof_term = Expr::app(
        Expr::app(false_elim, goal.target.clone()),
        Expr::app(neg_proof, proof),
    );
    state.close_goal(&goal, proof_term)
}
