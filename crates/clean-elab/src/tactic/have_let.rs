// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Forward reasoning `let` tactic: introduce a local definition into the proof context.
//!
//! In Lean 4, `let x : T := val` introduces a local definition (as opposed to
//! `have`, which introduces a hypothesis without a definitional value). The key
//! difference is that `let` bindings are transparent to the type checker --
//! the body can unfold the definition during type checking, while `have`
//! hypotheses are opaque (the proof term is erased from the context type).
//!
//! # Relationship to other tactics
//!
//! - [`super::forward::have_`] -- introduces hypothesis `h : T` (opaque proof)
//! - [`super::instance::let_i`] -- `letI`, like `let` but also registers as a typeclass instance
//! - [`let_`] -- plain local definition (this module)
//!
//! # Architecture
//!
//! The `let` tactic works by:
//! 1. Optionally creating a subgoal for the value (if no value is provided)
//! 2. Adding `x : T := val` as a `LocalDecl` with `value = Some(val)` to the context
//! 3. Closing the original goal with `Expr::let_named` that wraps the continuation

use crate::unify::{MetaState, Unifier, UnifyResult};
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use super::core::{Goal, LocalDecl, ProofState, TacticError, TacticResult};

/// Introduce a local definition into the proof context.
///
/// The `let` tactic introduces a named local definition that is transparent
/// to the type checker. Given `let x : T := val`, it:
/// 1. Verifies that `val` has type `T` (if provided)
/// 2. Adds `x : T := val` to the local context with the value visible
/// 3. Continues with the original goal in the extended context
///
/// Unlike `have`, the value is retained in the `LocalDecl` so the kernel
/// can unfold it during definitional equality checks.
///
/// # Arguments
/// * `state` - The proof state
/// * `name` - Name for the new local definition
/// * `ty` - Type of the definition
/// * `value` - Optional value. If `None`, creates a subgoal for the value.
///
/// # Example
/// ```text
/// // Goal: P
/// let_("x", Nat, Some(zero))
/// // Now have x : Nat := 0 in context, still need to prove P
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `ty` is a well-typed expression in the current environment
/// REQUIRES: If `value` is `Some(v)`, then `v` must have type unifiable with `ty`
/// ENSURES: On Ok with `Some(v)`, original goal closed with let-binding;
///          1 new goal pushed with `x : ty := v` in local context
/// ENSURES: On Ok with `None`, original goal closed; 2 new goals pushed
///          (value subgoal + continuation with `x : ty` in context)
/// ENSURES: The `LocalDecl` for `x` has `value = Some(v)` (transparent to type checker)
/// ENSURES: On Err(TypeMismatch), value type does not unify with `ty`; state unchanged
pub fn let_(state: &mut ProofState, name: &str, ty: Expr, value: Option<Expr>) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    if let Some(val) = value {
        // Verify the value has the expected type
        let val_ty = state.infer_type(&goal, &val)?;
        let ty_inst = state.metas.instantiate(&ty);
        let ctx = state.build_local_ctx(&goal);

        let unify_result = {
            let (metas, env) = state.metas_and_env();
            Unifier::with_env(metas, env, ctx).unify(&val_ty, &ty_inst)
        };
        match unify_result {
            UnifyResult::Success => {
                // Value is valid - add to context as a let-binding with value retained
                let fvar = state.fresh_fvar();

                let local_decl = LocalDecl {
                    fvar,
                    name: name.to_string(),
                    ty: ty.clone(),
                    value: Some(val.clone()),
                };

                // Create new goal with extended context
                let mut new_ctx = goal.local_ctx.clone();
                new_ctx.push(local_decl);

                // Create a new metavariable for the continuation
                let new_meta_id = state.fresh_meta_in_context(goal.target.clone(), &new_ctx);
                let new_meta_expr =
                    Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(new_meta_id)));

                // The proof of the original goal is:
                // let x : T := val in <continuation>
                let proof_term = Expr::let_named(
                    Name::from_string(name),
                    ty,
                    val,
                    new_meta_expr.abstract_fvar(fvar),
                    false,
                );

                state.close_goal(&goal, proof_term)?;

                // Add the new goal with x : T := val in context
                let new_goal = Goal {
                    meta_id: new_meta_id,
                    target: goal.target.clone(),
                    local_ctx: new_ctx,
                    tag: None,
                };

                state.goals.push_front(new_goal);
                Ok(())
            }
            UnifyResult::Failure(msg) => Err(TacticError::TypeMismatch {
                expected: format!("{ty_inst:?}"),
                actual: msg,
            }),
            UnifyResult::Stuck => Err(TacticError::UnificationFailed(
                "unification stuck while checking let value type".to_string(),
            )),
        }
    } else {
        // No value provided - create two goals:
        // 1. Prove T (the value)
        // 2. Continue original proof with x : T := <val> available

        let fvar = state.fresh_fvar();

        // Create the value metavariable in the original context.
        let val_meta_id = state.fresh_meta(ty.clone());
        let val_meta_expr = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(val_meta_id)));

        // The continuation can also use the transparent let local, so stamp
        // its metavariable with the extended context.
        let local_decl = LocalDecl {
            fvar,
            name: name.to_string(),
            ty: ty.clone(),
            value: Some(val_meta_expr.clone()),
        };
        let mut new_ctx = goal.local_ctx.clone();
        new_ctx.push(local_decl);
        let cont_meta_id = state.fresh_meta_in_context(goal.target.clone(), &new_ctx);
        let cont_meta_expr = Expr::from_kind(ExprKind::FVar(MetaState::to_fvar(cont_meta_id)));

        // The proof of the original goal is:
        // let x : T := <val_proof> in <continuation>
        let proof_term = Expr::let_named(
            Name::from_string(name),
            ty.clone(),
            val_meta_expr.clone(),
            cont_meta_expr.abstract_fvar(fvar),
            false,
        );

        state.close_goal(&goal, proof_term)?;

        // Goal 1: produce the value of type T
        let val_goal = Goal {
            meta_id: val_meta_id,
            target: ty,
            local_ctx: goal.local_ctx.clone(),
            tag: None,
        };

        // Goal 2: prove the original target with x : T := val available
        let cont_goal = Goal {
            meta_id: cont_meta_id,
            target: goal.target.clone(),
            local_ctx: new_ctx,
            tag: None,
        };

        // Insert goals (value first, then continuation)
        state.goals.push_front(cont_goal);
        state.goals.push_front(val_goal);

        Ok(())
    }
}
