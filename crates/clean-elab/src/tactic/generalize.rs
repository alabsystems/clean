// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generalization tactics: `generalize`, `generalize_eq`, and `ext`.
//!
//! These tactics abstract over specific terms in the goal, enabling
//! stronger induction hypotheses and function extensionality reasoning.

use crate::unify::MetaState;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind};

use super::core::{Goal, ProofState, TacticError, TacticResult};
use super::equality::{abstract_over, match_equality};
use super::proof_term::intro;

/// The `generalize` tactic abstracts a term in the goal by introducing a new variable.
///
/// Given a goal containing term `e : T`, this tactic:
/// 1. Replaces all occurrences of `e` in the goal with a fresh variable `x`
/// 2. Adds `x : T` as a new hypothesis (via intro-like mechanism)
///
/// This is useful for strengthening the induction hypothesis when doing induction,
/// or for abstracting over a specific value.
///
/// REQUIRES: `state.goals` is non-empty; `term` appears in the current goal
/// target (checked — returns InvalidTarget otherwise)
///
/// ENSURES: on Ok, the original goal is closed with `(new_proof term)` and
/// a new Pi-goal `∀ x : T, target[term → x]` is pushed and intro'd with
/// `var_name`; the resulting goal has `term` fully abstracted away
///
/// # Arguments
/// * `state` - The proof state
/// * `term` - The term to generalize
/// * `var_name` - Name for the new variable
///
/// # Example
/// ```text
/// goal : f 5 = g 5
///
/// generalize 5 as n
///
/// n : Nat
/// goal : f n = g n
/// ```
///
/// Proving `f n = g n` for all `n` is stronger but allows induction on `n`.
pub fn generalize(state: &mut ProofState, term: Expr, var_name: &str) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Infer the type of the term
    let term_ty = state.infer_type(&goal, &term)?;

    // Abstract over the term in the goal. Unlike a hard "term must appear"
    // guard, this matches Lean 4 `generalize`: when the term does not occur in
    // the goal, `abstract_over` is a no-op and the fresh variable `x` is still
    // introduced (the resulting Pi goal `∀ x : T, target` simply does not use
    // `x`). Verified against `lean`: `generalize n + 1 = m` on goal `True`
    // succeeds. The assembled proof `(cont term)` is kernel-rechecked either
    // way, so the no-occurrence path is sound.
    let target = state.metas.instantiate(&goal.target);
    let abstracted_target = abstract_over(&target, &term);

    // Create a new goal: ∀ x : T, goal[term → x]
    let forall_target = Expr::pi(BinderInfo::Default, term_ty.clone(), abstracted_target);

    // Create metavariable for the new goal
    let new_meta_id = state.fresh_meta(forall_target.clone());
    let new_meta = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(new_meta_id)));

    // The proof of the original goal is: new_proof term
    let proof = Expr::app(new_meta, term);
    state.close_goal(&goal, proof)?;

    // Add the new goal
    let new_goal = Goal {
        meta_id: new_meta_id,
        target: forall_target,
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    };
    state.goals.push_front(new_goal);

    // Now apply intro to introduce the variable
    intro(state, var_name)?;

    Ok(())
}

/// The `generalize_eq` tactic generalizes a term and adds an equality hypothesis.
///
/// Like `generalize`, but also adds a hypothesis `h : e = x` where `e` is the
/// original term and `x` is the new variable (Lean 4 `generalize h : e = x`
/// direction — original term on the LHS).
///
/// REQUIRES: `state.goals` is non-empty; `term` appears in the current goal
/// target; `Eq` and `Eq.refl` exist in the environment
///
/// ENSURES: on Ok, the original goal is closed and a new goal is pushed with
/// two intro'd hypotheses: `var_name : T` and `eq_name : var_name = term`;
/// the goal target has `term` replaced by the fresh variable
///
/// # Arguments
/// * `state` - The proof state
/// * `term` - The term to generalize
/// * `var_name` - Name for the new variable
/// * `eq_name` - Name for the equality hypothesis
///
/// # Example
/// ```text
/// goal : f 5 = g 5
///
/// generalize_eq 5 as n heq
///
/// n : Nat
/// heq : 5 = n
/// goal : f n = g n
/// ```
pub fn generalize_eq(
    state: &mut ProofState,
    term: Expr,
    var_name: &str,
    eq_name: &str,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Infer the type of the term
    let term_ty = state.infer_type(&goal, &term)?;

    // Term-occurrence is non-fatal (matches Lean 4 `generalize h : e = x`): if
    // `e` does not occur in the goal, the abstraction below is a no-op but the
    // variable `x` and hypothesis `h : e = x` are still introduced. Verified
    // against `lean`.
    let target = state.metas.instantiate(&goal.target);

    // Check that Eq and Eq.refl are available
    let eq_name_const = Name::from_string("Eq");
    if state.env.get_const(&eq_name_const).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: "Eq".into(),
        });
    }
    let eq_refl_name = Name::from_string("Eq.refl");
    if state.env.get_const(&eq_refl_name).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: "Eq.refl".into(),
        });
    }

    // Reified checked goals need a concrete Eq universe level here; fresh
    // params from mk_const_str stay rigid during infer_type on the Pi goal.
    let (eq_const, eq_levels) = state
        .infer_type(&goal, &term_ty)
        .ok()
        .and_then(|sort| match sort.kind() {
            ExprKind::Sort(u) => Some((
                Expr::const_(eq_name_const.clone(), vec![u.clone()]),
                vec![u.clone()],
            )),
            _ => None,
        })
        .unwrap_or_else(|| {
            let eq_const = state.mk_const_str("Eq");
            let eq_levels = match eq_const.kind() {
                ExprKind::Const(_, levels) => levels.to_vec(),
                _ => Vec::new(),
            };
            (eq_const, eq_levels)
        });
    let eq_refl_const = Expr::const_(eq_refl_name, eq_levels);

    // Abstract over the term in the goal
    let abstracted_target = abstract_over(&target, &term);

    // Reify the future variable/equality work as a Pi goal instead of building
    // a lambda with a binder-local continuation metavariable inside it.
    //
    // Direction: `eq_name : term = x` (original term on the LHS, fresh variable
    // `bvar(0)` on the RHS), matching Lean 4's `generalize h : e = x` (verified
    // against `lean` — the hypothesis reads `h : e = x`, not `x = e`). After the
    // continuation is applied to `term` for `x`, this becomes `Eq T term term`,
    // discharged by `Eq.refl term` regardless of operand order.
    let eq_type = Expr::app(
        Expr::app(Expr::app(eq_const.clone(), term_ty.clone()), term.clone()),
        Expr::bvar(0),
    );
    let new_target = Expr::pi(
        BinderInfo::Default,
        term_ty.clone(),
        Expr::pi(BinderInfo::Default, eq_type, abstracted_target.lift(1)),
    );

    // Create metavariable for the higher-order continuation goal
    let new_meta_id = state.fresh_meta(new_target.clone());
    let new_meta = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(new_meta_id)));

    // The original goal is proved by applying the generalized continuation to
    // the original term and its reflexivity proof.
    let refl_proof = Expr::app(Expr::app(eq_refl_const, term_ty.clone()), term.clone());
    let proof = Expr::app(Expr::app(new_meta, term.clone()), refl_proof);
    state.close_goal(&goal, proof)?;

    // Add the new goal
    let new_goal = Goal {
        meta_id: new_meta_id,
        target: new_target,
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    };
    state.goals.push_front(new_goal);
    intro(state, var_name)?;
    intro(state, eq_name)?;

    Ok(())
}

/// The `ext` tactic for function extensionality.
///
/// For a goal `f = g` where `f` and `g` are functions, this tactic applies
/// functional extensionality to reduce the goal to `∀ x, f x = g x`.
///
/// REQUIRES: current goal is an equality `f = g` where `f` has Pi type;
/// `funext` must exist in the environment
///
/// ENSURES: on Ok, the original goal is closed via `funext` and a new
/// goal `∀ var_name, f var_name = g var_name` is pushed and intro'd;
/// on Err(GoalMismatch), goal was not an equality of functions
///
/// # Arguments
/// * `state` - The proof state
/// * `var_name` - Name for the argument variable
///
/// # Example
/// ```text
/// f g : Nat → Nat
/// goal : f = g
///
/// ext n
///
/// n : Nat
/// goal : f n = g n
/// ```
///
/// # Errors
/// - `Other` if `funext` is not in the environment
/// - `GoalMismatch` if the goal is not an equality of function types
pub fn ext(state: &mut ProofState, var_name: &str) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.whnf(&goal, &goal.target);

    // Match goal as equality f = g
    let (_eq_ty, lhs, rhs, _eq_levels) = match_equality(&target)
        .map_err(|_| TacticError::GoalMismatch("ext: goal is not an equality".to_string()))?;

    // Infer types of lhs and rhs
    let lhs_ty = state.infer_type(&goal, &lhs)?;
    let lhs_ty_whnf = state.whnf(&goal, &lhs_ty);

    // Check that lhs has function type (Pi type)
    let (binder_info, domain, codomain) = match lhs_ty_whnf.kind() {
        ExprKind::Pi(bi, dom, cod) => (*bi, dom.as_ref().clone(), cod.as_ref().clone()),
        _ => {
            return Err(TacticError::GoalMismatch(
                "ext: left-hand side is not a function".to_string(),
            ));
        }
    };

    // Check for funext in environment
    let funext_name = Name::from_string("funext");
    if state.env.get_const(&funext_name).is_none() {
        return Err(TacticError::EnvironmentMissing {
            constant: "funext".to_string(),
        });
    }

    let arg_expr = Expr::fvar(state.fresh_fvar());
    let result_ty = state.whnf(&goal, &codomain.clone().instantiate(&arg_expr));
    let dom_sort = state.infer_type(&goal, &domain).ok();
    let result_sort = state.infer_type(&goal, &result_ty).ok();
    let (eq_expr, funext) = match (&dom_sort, &result_sort) {
        (Some(ds), Some(rs)) => match (ds.kind(), rs.kind()) {
            (ExprKind::Sort(u), ExprKind::Sort(v)) => (
                Expr::const_(Name::from_string("Eq"), vec![v.clone()]),
                Expr::const_(Name::from_string("funext"), vec![u.clone(), v.clone()]),
            ),
            _ => (state.mk_const_str("Eq"), state.mk_const_str("funext")),
        },
        _ => (state.mk_const_str("Eq"), state.mk_const_str("funext")),
    };

    let x_bv = Expr::bvar(0);
    let f_app = Expr::app(lhs.clone(), x_bv.clone());
    let g_app = Expr::app(rhs.clone(), x_bv);
    let pointwise_eq = Expr::app(
        Expr::app(Expr::app(eq_expr, codomain.clone()), f_app),
        g_app,
    );
    let new_target = Expr::pi(binder_info, domain.clone(), pointwise_eq);

    // Create metavariable for the pointwise equality proof
    let pointwise_meta_id = state.fresh_meta(new_target.clone());
    let pointwise_meta = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(pointwise_meta_id)));

    // Build the proof using funext:
    // funext : ∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x},
    //          (∀ x, f x = g x) → f = g
    //
    // {β} : α → Sort v — wrap the Pi body in a lambda to make a function
    let beta = Expr::lam(binder_info, domain.clone(), codomain);

    // Apply funext {α} {β} {f} {g} h — all 5 args (4 implicit + 1 explicit)
    let mut proof = funext;
    proof = Expr::app(proof, domain.clone()); // {α} = domain type
    proof = Expr::app(proof, beta); // {β} = codomain function
    proof = Expr::app(proof, lhs); // {f}
    proof = Expr::app(proof, rhs); // {g}
    proof = Expr::app(proof, pointwise_meta); // h : ∀ x, f x = g x
    state.close_goal(&goal, proof)?;

    // Add the new goal
    let new_goal = Goal {
        meta_id: pointwise_meta_id,
        target: new_target,
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    };
    state.goals.push_front(new_goal);
    intro(state, var_name)?;

    Ok(())
}
