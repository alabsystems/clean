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
use clean_kernel::{Expr, FVarId};

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
pub fn let_(
    state: &mut ProofState,
    name: &clean_parser::SurfaceName,
    ty: Expr,
    value: Option<Expr>,
) -> TacticResult {
    let_binding(state, name, ty, value, false)
}

/// Marker for a checked let whose RHS is substituted after the continuation is closed.
pub(super) static INLINE_LET_MARKER: std::sync::LazyLock<clean_kernel::MDataMap> =
    std::sync::LazyLock::new(|| {
        vec![(
            clean_kernel::Name::from_string("_clean.tactic.inlineLet"),
            clean_kernel::MDataValue::Bool(true),
        )]
    });

pub(super) fn let_binding(
    state: &mut ProofState,
    name: &clean_parser::SurfaceName,
    ty: Expr,
    value: Option<Expr>,
    inline: bool,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    if let Some(val) = &value {
        let val_ty = state.infer_type(&goal, val)?;
        let ty_inst = state.metas.instantiate(&ty);
        let ctx = state.build_local_ctx(&goal);
        let (metas, env) = state.metas_and_env();
        match Unifier::with_env(metas, env, ctx).unify(&val_ty, &ty_inst) {
            UnifyResult::Success => {}
            UnifyResult::Failure(msg) => {
                return Err(TacticError::TypeMismatch {
                    expected: format!("{ty_inst}"),
                    actual: msg,
                })
            }
            UnifyResult::Stuck => {
                return Err(TacticError::UnificationFailed(
                    "unification stuck while checking let value type".to_string(),
                ))
            }
        }
    }

    // A let adds exactly one binder in the destination goal. A sibling may have
    // advanced the global cursor beyond that depth.
    let base = state.goal_binder_base(&goal);
    state.next_fvar = state.next_fvar.max(base + 1);
    let fvar = FVarId::new(base);
    let (value, obligation) = match value {
        Some(val) => (val, None),
        None => {
            let id = state.fresh_meta(ty.clone());
            (Expr::fvar(MetaState::to_fvar(id)), Some(id))
        }
    };
    let mut new_ctx = goal.local_ctx.clone();
    new_ctx.push(LocalDecl {
        binder_info: Default::default(),
        fvar,
        name: name.clone(),
        ty: ty.clone(),
        value: Some(value.clone()),
    });
    let cont = state.fresh_meta_in_context(goal.target.clone(), &new_ctx);
    let body = Expr::fvar(MetaState::to_fvar(cont)).abstract_fvar(fvar);
    let proof = Expr::let_named(name.name().clone(), ty.clone(), value, body, false);
    // Keep the binder around the unsolved continuation for the scope checker.
    let proof = if inline {
        Expr::mdata(INLINE_LET_MARKER.clone(), proof)
    } else {
        proof
    };
    state.close_goal(&goal, proof)?;
    state.goals.push_front(Goal {
        meta_id: cont,
        target: goal.target,
        local_ctx: new_ctx,
        case_binders: goal.case_binders,
        tag: goal.tag,
    });
    if let Some(id) = obligation {
        state.goals.push_front(Goal {
            meta_id: id,
            target: ty,
            local_ctx: goal.local_ctx,
            case_binders: Vec::new(),
            tag: None,
        });
    }
    Ok(())
}
