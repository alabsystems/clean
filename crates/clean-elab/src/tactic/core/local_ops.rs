// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-carrying local-declaration replacement helpers.

use std::collections::VecDeque;

use clean_kernel::{Expr, ExprKind, FVarId, Name};

use super::{Goal, LocalDecl, ProofState, TacticError};
use crate::unify::MetaState;

#[derive(Clone)]
struct LocalReplaceSnapshot {
    goals: VecDeque<Goal>,
    metas: MetaState,
    next_fvar: u64,
}

impl LocalReplaceSnapshot {
    fn restore(self, state: &mut ProofState) {
        state.goals = self.goals;
        state.metas = self.metas;
        state.next_fvar = self.next_fvar;
        state.invalidate_tc_cache();
    }
}

impl ProofState {
    pub(crate) fn replace_local_decl_type_validated(
        &mut self,
        hyp_fvar: FVarId,
        new_ty: Expr,
    ) -> Result<(), TacticError> {
        let goal = self.current_goal().ok_or(TacticError::NoGoals)?.clone();
        let hyp_idx = find_local_decl_index(&goal, hyp_fvar)?;
        let old_decl = goal
            .local_ctx
            .get(hyp_idx)
            .cloned()
            .expect("invariant: replace_local_decl index came from current goal");
        let old_ty = self.metas.instantiate(&old_decl.ty);
        let new_ty = self.metas.instantiate(&new_ty);
        if old_ty != new_ty && !self.is_def_eq(&goal, &old_ty, &new_ty) {
            return Err(TacticError::GoalMismatch(format!(
                "replace_local_decl_type_validated: replacing local '{}' with a non-definitionally-equal type requires an explicit proof",
                old_decl.name
            )));
        }

        // Structural validation alone is not proof authority: changing the
        // type attached to an existing FVar would retype both the focused goal
        // and its immutable metavariable scope in place.  The def-eq path uses
        // the shared proof-carrying replacement boundary, which mints a fresh
        // continuation metavariable with an exact context snapshot.
        self.replace_local_decl_def_eq(hyp_fvar, new_ty)
    }

    pub(crate) fn replace_local_decl_with_cast(
        &mut self,
        hyp_fvar: FVarId,
        new_ty: Expr,
        cast_expr: Expr,
    ) -> Result<(), TacticError> {
        let goal = self.current_goal().ok_or(TacticError::NoGoals)?.clone();
        let hyp_idx = find_local_decl_index(&goal, hyp_fvar)?;
        replace_local_decl_core(self, &goal, hyp_idx, new_ty, cast_expr)
    }

    pub(crate) fn replace_local_decl_with_value(
        &mut self,
        hyp_fvar: FVarId,
        new_ty: Expr,
        new_value: Expr,
    ) -> Result<FVarId, TacticError> {
        let goal = self.current_goal().ok_or(TacticError::NoGoals)?.clone();
        let hyp_idx = find_local_decl_index(&goal, hyp_fvar)?;
        let old_decl = goal
            .local_ctx
            .get(hyp_idx)
            .cloned()
            .expect("invariant: replace_local_decl index came from current goal");
        let new_ty = self.metas.instantiate(&new_ty);
        let new_value = self.metas.instantiate(&new_value);
        let value_ty = self.infer_type(&goal, &new_value)?;
        if !self.is_def_eq(&goal, &value_ty, &new_ty) {
            return Err(TacticError::TypeMismatch {
                expected: format!("{:?}", self.metas.instantiate(&new_ty)),
                actual: format!("{:?}", self.metas.instantiate(&value_ty)),
            });
        }

        let snapshot = LocalReplaceSnapshot {
            goals: self.goals.clone(),
            metas: self.metas.clone(),
            next_fvar: self.next_fvar,
        };

        let new_fvar = self.fresh_fvar();
        let replacement_goal = build_value_shadow_goal(
            self,
            &goal,
            hyp_idx,
            &old_decl,
            new_fvar,
            new_ty.clone(),
            new_value.clone(),
        );
        if let Err(err) =
            validate_rewritten_goal_with_cache_reset(self, &replacement_goal, &old_decl.name)
        {
            snapshot.restore(self);
            return Err(err);
        }

        // A replacement value proves only `new_ty`; it does not prove that the
        // old local and the new value are equal.  Therefore dependent suffix
        // declarations and the target must keep referring to the old (now
        // hidden) local.  Introduce the visible replacement as a let-bound
        // local and connect an exact-context continuation meta to the original
        // goal with an actual proof term instead of widening/retyping the old
        // goal in place.
        let new_meta_id = self
            .fresh_meta_in_context(replacement_goal.target.clone(), &replacement_goal.local_ctx);
        let new_meta_expr = Expr::fvar(MetaState::to_fvar(new_meta_id));
        let proof = Expr::let_named(
            Name::from_string(&old_decl.name),
            new_ty,
            new_value,
            new_meta_expr.abstract_fvar(new_fvar),
            false,
        );

        if let Err(err) = self.close_goal_with_bound_locals(&goal, proof, &[(new_fvar, 1)]) {
            snapshot.restore(self);
            return Err(err);
        }

        self.goals.push_front(Goal {
            meta_id: new_meta_id,
            target: replacement_goal.target,
            local_ctx: replacement_goal.local_ctx,
            tag: replacement_goal.tag,
        });
        Ok(new_fvar)
    }

    pub(crate) fn replace_local_decl_def_eq(
        &mut self,
        hyp_fvar: FVarId,
        new_ty: Expr,
    ) -> Result<(), TacticError> {
        let goal = self.current_goal().ok_or(TacticError::NoGoals)?.clone();
        let hyp_idx = find_local_decl_index(&goal, hyp_fvar)?;
        let old_decl = goal
            .local_ctx
            .get(hyp_idx)
            .cloned()
            .expect("invariant: replace_local_decl index came from current goal");

        if old_decl.ty == new_ty {
            return Ok(());
        }

        if !self.is_def_eq(&goal, &old_decl.ty, &new_ty) {
            return Err(TacticError::GoalMismatch(
                "replace_local_decl_def_eq: new type is not definitionally equal \
                 to the current local declaration type"
                    .into(),
            ));
        }

        replace_local_decl_core(self, &goal, hyp_idx, new_ty, Expr::fvar(old_decl.fvar))
    }

    pub(crate) fn rewrite_local_decl_types_def_eq<F>(
        &mut self,
        mut rewrite: F,
    ) -> Result<(), TacticError>
    where
        F: FnMut(&Expr) -> Expr,
    {
        let local_ctx_len = self
            .current_goal()
            .ok_or(TacticError::NoGoals)?
            .local_ctx
            .len();
        for hyp_idx in 0..local_ctx_len {
            let (hyp_fvar, current_ty) = {
                let goal = self.current_goal().ok_or(TacticError::NoGoals)?;
                let hyp_decl = goal
                    .local_ctx
                    .get(hyp_idx)
                    .expect("invariant: hyp_idx came from current goal length");
                (hyp_decl.fvar, hyp_decl.ty.clone())
            };
            let new_ty = rewrite(&current_ty);
            if new_ty != current_ty {
                self.replace_local_decl_def_eq(hyp_fvar, new_ty)?;
            }
        }
        Ok(())
    }

    pub(crate) fn rewrite_named_local_decl_type_def_eq<F>(
        &mut self,
        hyp_name: &str,
        rewrite: F,
    ) -> Result<(), TacticError>
    where
        F: FnOnce(&Expr) -> Expr,
    {
        let (hyp_fvar, current_ty) = {
            let goal = self.current_goal().ok_or(TacticError::NoGoals)?;
            let hyp_decl = goal
                .local_ctx
                .iter()
                .find(|decl| decl.name == hyp_name)
                .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;
            (hyp_decl.fvar, hyp_decl.ty.clone())
        };
        let new_ty = rewrite(&current_ty);
        if new_ty == current_ty {
            return Ok(());
        }
        self.replace_local_decl_def_eq(hyp_fvar, new_ty)
    }
}

fn replace_local_decl_core(
    state: &mut ProofState,
    goal: &Goal,
    hyp_idx: usize,
    new_ty: Expr,
    cast_expr: Expr,
) -> Result<(), TacticError> {
    let old_decl = goal
        .local_ctx
        .get(hyp_idx)
        .cloned()
        .expect("invariant: replace_local_decl index came from goal.local_ctx");
    reject_unavailable_local_refs(state, goal, hyp_idx, &old_decl.name, &new_ty)?;

    let snapshot = LocalReplaceSnapshot {
        goals: state.goals.clone(),
        metas: state.metas.clone(),
        next_fvar: state.next_fvar,
    };

    let cast_ty = match state.infer_type(goal, &cast_expr) {
        Ok(ty) => ty,
        Err(err) => {
            snapshot.restore(state);
            return Err(TacticError::TypeCheckFailed(format!(
                "replace_local_decl: replacement proof for '{}' is ill-typed: {err}",
                old_decl.name
            )));
        }
    };
    if !state.is_def_eq(goal, &cast_ty, &new_ty) {
        let expected = format!("{:?}", state.metas().instantiate(&new_ty));
        let actual = format!("{:?}", state.metas().instantiate(&cast_ty));
        snapshot.restore(state);
        return Err(TacticError::TypeMismatch { expected, actual });
    }

    let new_fvar = state.fresh_fvar();
    let replacement = Expr::fvar(new_fvar);

    let mut new_ctx = goal.local_ctx.clone();
    new_ctx[hyp_idx] = LocalDecl {
        fvar: new_fvar,
        name: old_decl.name.clone(),
        ty: new_ty.clone(),
        value: None,
    };

    let new_target = goal.target.subst_fvar(old_decl.fvar, &replacement);
    for decl in new_ctx.iter_mut().skip(hyp_idx + 1) {
        decl.ty = decl.ty.subst_fvar(old_decl.fvar, &replacement);
        decl.value = decl
            .value
            .as_ref()
            .map(|value| value.subst_fvar(old_decl.fvar, &replacement));
    }

    let validation_goal = Goal {
        meta_id: goal.meta_id,
        target: new_target.clone(),
        local_ctx: new_ctx.clone(),
        tag: goal.tag.clone(),
    };
    let validation =
        validate_rewritten_goal_with_cache_reset(state, &validation_goal, &old_decl.name);
    if let Err(err) = validation {
        snapshot.clone().restore(state);
        return Err(err);
    }

    let new_meta_id = state.fresh_meta_in_context(new_target.clone(), &new_ctx);
    let new_meta_expr = Expr::fvar(MetaState::to_fvar(new_meta_id));
    let proof = Expr::let_named(
        Name::from_string(&old_decl.name),
        new_ty.clone(),
        cast_expr,
        new_meta_expr.abstract_fvar(new_fvar),
        false,
    );

    if let Err(err) = state.close_goal_with_bound_locals(goal, proof, &[(new_fvar, 1)]) {
        snapshot.restore(state);
        return Err(err);
    }

    state.goals.push_front(Goal {
        meta_id: new_meta_id,
        target: new_target,
        local_ctx: new_ctx,
        tag: goal.tag.clone(),
    });
    Ok(())
}

fn build_value_shadow_goal(
    state: &ProofState,
    goal: &Goal,
    hyp_idx: usize,
    old_decl: &LocalDecl,
    new_fvar: FVarId,
    new_ty: Expr,
    new_value: Expr,
) -> Goal {
    let insert_after_idx = find_insert_after_index(state, goal, hyp_idx, [&new_ty, &new_value]);
    let insert_idx = insert_after_idx + 1;

    let mut new_ctx = goal.local_ctx.clone();
    new_ctx[hyp_idx].name = hidden_old_local_name(&old_decl.name, old_decl.fvar);
    new_ctx.insert(
        insert_idx,
        LocalDecl {
            fvar: new_fvar,
            name: old_decl.name.clone(),
            ty: new_ty,
            value: Some(new_value),
        },
    );

    Goal {
        meta_id: goal.meta_id,
        target: goal.target.clone(),
        local_ctx: new_ctx,
        tag: goal.tag.clone(),
    }
}

fn find_insert_after_index(
    state: &ProofState,
    goal: &Goal,
    hyp_idx: usize,
    exprs: [&Expr; 2],
) -> usize {
    let mut insert_after_idx = hyp_idx;
    for expr in exprs {
        let refs = crate::tactic::hypothesis::collect_fvars(&state.metas.instantiate(expr));
        for (idx, decl) in goal.local_ctx.iter().enumerate() {
            if refs.contains(&decl.fvar) && idx > insert_after_idx {
                insert_after_idx = idx;
            }
        }
    }
    insert_after_idx
}

fn hidden_old_local_name(name: &str, fvar: FVarId) -> String {
    format!("_replaced_{name}_{}", fvar.as_u64())
}

fn validate_rewritten_goal_with_cache_reset(
    state: &ProofState,
    goal: &Goal,
    hyp_name: &str,
) -> Result<(), TacticError> {
    state.invalidate_tc_cache();
    let validation = validate_rewritten_goal(state, goal, hyp_name);
    // Validation runs under a temporary rewritten local context, so those
    // caches must not survive into close_goal on the original goal.
    state.invalidate_tc_cache();
    validation
}

fn find_local_decl_index(goal: &Goal, hyp_fvar: FVarId) -> Result<usize, TacticError> {
    goal.local_ctx
        .iter()
        .position(|decl| decl.fvar == hyp_fvar)
        .ok_or_else(|| TacticError::InvalidTarget {
            tactic: "replace_local_decl".into(),
            detail: format!("unknown local declaration: {hyp_fvar:?}"),
        })
}

fn reject_unavailable_local_refs(
    state: &ProofState,
    goal: &Goal,
    hyp_idx: usize,
    hyp_name: &str,
    new_ty: &Expr,
) -> Result<(), TacticError> {
    let new_ty_fvars = crate::tactic::hypothesis::collect_fvars(&state.metas.instantiate(new_ty));
    for decl in goal.local_ctx.iter().skip(hyp_idx) {
        if !new_ty_fvars.contains(&decl.fvar) {
            continue;
        }

        let detail = if decl.fvar == goal.local_ctx[hyp_idx].fvar {
            format!(
                "cannot replace local '{hyp_name}' with a type that refers to the \
                 local being replaced"
            )
        } else {
            format!(
                "cannot replace local '{hyp_name}' with a type that depends on later \
                 local '{}'",
                decl.name
            )
        };
        return Err(TacticError::InvalidTarget {
            tactic: "replace_local_decl".into(),
            detail,
        });
    }
    Ok(())
}

fn validate_rewritten_goal(
    state: &ProofState,
    goal: &Goal,
    hyp_name: &str,
) -> Result<(), TacticError> {
    let detail_prefix =
        format!("replace_local_decl: rewriting local '{hyp_name}' produced an ill-typed goal");

    let target_sort = state
        .infer_type(goal, &goal.target)
        .map_err(|err| TacticError::TypeCheckFailed(format!("{detail_prefix}: target: {err}")))?;
    if !matches!(target_sort.kind(), ExprKind::Sort(_)) {
        return Err(TacticError::TypeCheckFailed(format!(
            "{detail_prefix}: target is not a proposition/type: {target_sort:?}"
        )));
    }
    // Wave 98 (Gap 17): the default `infer_type` runs in
    // `infer_only=true`, which skips App-argument and Let-body type
    // checks. Re-check the target strictly so dependent rewrites that
    // produce well-headed-but-ill-typed Apps (e.g.
    // `Witness {x=y} h_g` where `h_g : g x = g y`) fail-closed.
    state
        .check_type_strict(goal, &goal.target, &target_sort)
        .map_err(|err| {
            TacticError::TypeCheckFailed(format!("{detail_prefix}: target strict-check: {err:?}"))
        })?;

    for decl in &goal.local_ctx {
        let decl_sort = state.infer_type(goal, &decl.ty).map_err(|err| {
            TacticError::TypeCheckFailed(format!(
                "{detail_prefix}: local '{name}' type: {err}",
                name = decl.name
            ))
        })?;
        if !matches!(decl_sort.kind(), ExprKind::Sort(_)) {
            return Err(TacticError::TypeCheckFailed(format!(
                "{detail_prefix}: local '{name}' does not have a sort-valued type: {decl_sort:?}",
                name = decl.name
            )));
        }
        // Wave 98 (Gap 17): strict-check the local's *type* — App
        // arguments inside the type must agree with their domains.
        state
            .check_type_strict(goal, &decl.ty, &decl_sort)
            .map_err(|err| {
                TacticError::TypeCheckFailed(format!(
                    "{detail_prefix}: local '{name}' type strict-check: {err:?}",
                    name = decl.name
                ))
            })?;

        if let Some(value) = &decl.value {
            // Wave 98 (Gap 17): use the strict `check_type` here so
            // an ill-typed let-binding value (after substitution) is
            // rejected even when its "head" looks acceptable in
            // infer-only mode.
            state
                .check_type_strict(goal, value, &decl.ty)
                .map_err(|err| {
                    TacticError::TypeCheckFailed(format!(
                        "{detail_prefix}: local '{name}' value strict-check: {err:?}",
                        name = decl.name
                    ))
                })?;
        }
    }

    Ok(())
}

const _: fn(&mut ProofState, FVarId, Expr, Expr) -> Result<(), TacticError> =
    ProofState::replace_local_decl_with_cast;
const _: fn(&mut ProofState, FVarId, Expr, Expr) -> Result<FVarId, TacticError> =
    ProofState::replace_local_decl_with_value;
const _: fn(&mut ProofState, FVarId, Expr) -> Result<(), TacticError> =
    ProofState::replace_local_decl_def_eq;
const _: fn(&mut ProofState, FVarId, Expr) -> Result<(), TacticError> =
    ProofState::replace_local_decl_type_validated;

#[cfg(test)]
impl ProofState {
    pub(crate) fn validate_rewritten_goal_for_test(
        &self,
        goal: &Goal,
        hyp_name: &str,
    ) -> Result<(), TacticError> {
        validate_rewritten_goal(self, goal, hyp_name)
    }

    pub(crate) fn validate_rewritten_goal_with_cache_reset_for_test(
        &self,
        goal: &Goal,
        hyp_name: &str,
    ) -> Result<(), TacticError> {
        validate_rewritten_goal_with_cache_reset(self, goal, hyp_name)
    }
}
