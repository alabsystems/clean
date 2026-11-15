// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-carrying local-declaration replacement helpers, and the kernel
//! context in which `have` locals, as in Lean, have no reduction-visible value.

use std::collections::VecDeque;

use clean_kernel::{Expr, ExprKind, FVarId, MDataValue, Name};

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
        self.replace_local_decl_with_cast_fvar(hyp_fvar, new_ty, cast_expr)
            .map(|_| ())
    }

    /// Return the actual replacement local after the checked cast succeeds.
    pub(crate) fn replace_local_decl_with_cast_fvar(
        &mut self,
        hyp_fvar: FVarId,
        new_ty: Expr,
        cast_expr: Expr,
    ) -> Result<FVarId, TacticError> {
        let goal = self.current_goal().ok_or(TacticError::NoGoals)?.clone();
        let hyp_idx = find_local_decl_index(&goal, hyp_fvar)?;
        replace_local_decl_core(self, &goal, hyp_idx, new_ty, cast_expr, Dependents::KeepOld)
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
                expected: format!("{}", self.metas.instantiate(&new_ty)),
                actual: format!("{}", self.metas.instantiate(&value_ty)),
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
            old_decl.name.name().clone(),
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
            case_binders: replacement_goal.case_binders.clone(),
            tag: replacement_goal.tag,
        });
        Ok(new_fvar)
    }

    /// Forget the let-VALUE of a local of the current goal, leaving an opaque
    /// hypothesis of the same type — what a Lean `have` is, and what `replace`
    /// needs when the new hypothesis was DEFINED from the one being cleared.
    /// Information is only removed (every term typed against the opaque local
    /// is typed against the let-bound one too) and the assembled proof is
    /// kernel-re-checked, so no obligation arises. A local with no value, or
    /// one that is absent, is left as it is.
    pub(crate) fn forget_local_decl_value(&mut self, fvar: FVarId) -> Result<(), TacticError> {
        let goal = self.current_goal_mut().ok_or(TacticError::NoGoals)?;
        if let Some(decl) = goal.local_ctx.iter_mut().find(|d| d.fvar == fvar) {
            decl.value = None;
        }
        self.invalidate_tc_cache();
        Ok(())
    }

    pub(crate) fn replace_local_decl_def_eq(
        &mut self,
        hyp_fvar: FVarId,
        new_ty: Expr,
    ) -> Result<(), TacticError> {
        self.replace_local_decl_def_eq_fvar(hyp_fvar, new_ty)
            .map(|_| ())
    }

    /// Return the retained or replacement local after def-eq validation.
    pub(crate) fn replace_local_decl_def_eq_fvar(
        &mut self,
        hyp_fvar: FVarId,
        new_ty: Expr,
    ) -> Result<FVarId, TacticError> {
        let goal = self.current_goal().ok_or(TacticError::NoGoals)?.clone();
        let hyp_idx = find_local_decl_index(&goal, hyp_fvar)?;
        let old_decl = goal
            .local_ctx
            .get(hyp_idx)
            .cloned()
            .expect("invariant: replace_local_decl index came from current goal");

        if old_decl.ty == new_ty {
            return Ok(old_decl.fvar);
        }

        if !self.is_def_eq(&goal, &old_decl.ty, &new_ty) {
            return Err(TacticError::GoalMismatch(
                "replace_local_decl_def_eq: new type is not definitionally equal \
                 to the current local declaration type"
                    .into(),
            ));
        }

        replace_local_decl_core(
            self,
            &goal,
            hyp_idx,
            new_ty,
            Expr::fvar(old_decl.fvar),
            Dependents::Retarget,
        )
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
        hyp_name: &clean_parser::SurfaceName,
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
                .rev()
                .find(|decl| crate::tactic::pattern::names::hypothesis_named(&decl.name, hyp_name))
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

/// What the locals after a replaced hypothesis (and the target) refer to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Dependents {
    /// The new local proves a DEFINITIONALLY EQUAL type (`change … at h`,
    /// Lean's `replaceLocalDeclDefEq`, which edits the type in place): when
    /// the new local can stay at the old one's position, dependents are
    /// retargeted to it.
    Retarget,
    /// The new local proves a DIFFERENT type (`rw … at h`, Lean's
    /// `replaceLocalDecl` = `assertAfter` + `clear`): dependents keep the old
    /// local, which survives under a hidden name when anything mentions it.
    /// Retargeting them made `(h : a = 5) (hp : h = h)` ill-typed after `rw
    /// [hab] at h`, which pinned Lean 4.8.0 accepts (review r4t u1).
    KeepOld,
}

fn replace_local_decl_core(
    state: &mut ProofState,
    goal: &Goal,
    hyp_idx: usize,
    new_ty: Expr,
    cast_expr: Expr,
    dependents: Dependents,
) -> Result<FVarId, TacticError> {
    let old_decl = goal
        .local_ctx
        .get(hyp_idx)
        .cloned()
        .expect("invariant: replace_local_decl index came from goal.local_ctx");
    reject_self_reference(state, goal, hyp_idx, &old_decl.name, &new_ty)?;

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
        let expected = crate::error_render::term(&state.metas().instantiate(&new_ty));
        let actual = crate::error_render::term(&state.metas().instantiate(&cast_ty));
        snapshot.restore(state);
        return Err(TacticError::TypeMismatch { expected, actual });
    }

    let new_fvar = state.fresh_fvar();
    let replacement = Expr::fvar(new_fvar);
    let new_decl = LocalDecl {
        binder_info: old_decl.binder_info,
        fvar: new_fvar,
        name: old_decl.name.clone(),
        ty: new_ty.clone(),
        value: None,
    };

    // Lean's `replaceLocalDecl` (`Meta/Tactic/Replace.lean`): the new local
    // goes after the LAST local its type mentions (`findMaxFVar`, then
    // `assertAfter`), and the old one is cleared when nothing depends on it.
    // `rw [hab] at h` with `h : a + 0 = 5` declared BEFORE `b` gives
    // `h : b + 0 = 5`, which must follow `b` (G38, ledger (108)); Clean
    // refused it ("depends on later local").
    let insert_after_idx = find_insert_after_index(state, goal, hyp_idx, &[&new_ty]);
    let (new_target, new_ctx) = if insert_after_idx == hyp_idx && dependents == Dependents::Retarget
    {
        let mut new_ctx = goal.local_ctx.clone();
        new_ctx[hyp_idx] = new_decl;
        let new_target = goal.target.subst_fvar(old_decl.fvar, &replacement);
        for decl in new_ctx.iter_mut().skip(hyp_idx + 1) {
            decl.ty = decl.ty.subst_fvar(old_decl.fvar, &replacement);
            decl.value = decl
                .value
                .as_ref()
                .map(|value| value.subst_fvar(old_decl.fvar, &replacement));
        }
        (new_target, new_ctx)
    } else {
        (
            goal.target.clone(),
            assert_after_ctx(state, goal, hyp_idx, insert_after_idx, new_decl),
        )
    };

    let validation_goal = Goal {
        meta_id: goal.meta_id,
        target: new_target.clone(),
        local_ctx: new_ctx.clone(),
        case_binders: goal
            .case_binders
            .iter()
            .map(|id| if *id == old_decl.fvar { new_fvar } else { *id })
            .collect(),
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
        old_decl.name.name().clone(),
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
        case_binders: goal
            .case_binders
            .iter()
            .map(|id| if *id == old_decl.fvar { new_fvar } else { *id })
            .collect(),
        tag: goal.tag.clone(),
    });
    Ok(new_fvar)
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
    let insert_after_idx = find_insert_after_index(state, goal, hyp_idx, &[&new_ty, &new_value]);
    let insert_idx = insert_after_idx + 1;

    let mut new_ctx = goal.local_ctx.clone();
    new_ctx[hyp_idx].name = hidden_old_local_name(&old_decl.name, old_decl.fvar);
    new_ctx.insert(
        insert_idx,
        LocalDecl {
            binder_info: old_decl.binder_info,
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
        case_binders: goal
            .case_binders
            .iter()
            .map(|id| if *id == old_decl.fvar { new_fvar } else { *id })
            .collect(),
        tag: goal.tag.clone(),
    }
}

fn find_insert_after_index(
    state: &ProofState,
    goal: &Goal,
    hyp_idx: usize,
    exprs: &[&Expr],
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

fn hidden_old_local_name(
    name: &clean_parser::SurfaceName,
    fvar: FVarId,
) -> clean_parser::SurfaceName {
    clean_parser::SurfaceName::from_name(name.name().clone().str("_replaced").num(fvar.as_u64()))
}

fn validate_rewritten_goal_with_cache_reset(
    state: &ProofState,
    goal: &Goal,
    hyp_name: &clean_parser::SurfaceName,
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
            detail: format!(
                "unknown local declaration: {}",
                crate::error_render::fvar(hyp_fvar, None)
            ),
        })
}

/// Refuse a replacement type that mentions the local it replaces: no
/// placement makes `h : P h` well-formed.
fn reject_self_reference(
    state: &ProofState,
    goal: &Goal,
    hyp_idx: usize,
    hyp_name: &clean_parser::SurfaceName,
    new_ty: &Expr,
) -> Result<(), TacticError> {
    let new_ty_fvars = crate::tactic::hypothesis::collect_fvars(&state.metas.instantiate(new_ty));
    if new_ty_fvars.contains(&goal.local_ctx[hyp_idx].fvar) {
        return Err(TacticError::InvalidTarget {
            tactic: "replace_local_decl".into(),
            detail: format!(
                "cannot replace local '{hyp_name}' with a type that refers to the \
                 local being replaced"
            ),
        });
    }
    Ok(())
}

/// The context of Lean's `assertAfter` + `clear`: `new_decl` placed right
/// after `local_ctx[insert_after_idx]` (the last local its type mentions, or
/// the old local itself when none is later), and the old local at `hyp_idx`
///
/// * dropped when no later local and not the target mentions it (Lean's
///   `clear` succeeds), or
/// * kept under a hidden name when something does (Lean's `clear` fails and
///   the old local stays, shadowed by the new one); its dependents keep
///   referring to it, since the new local proves a DIFFERENT type.
fn assert_after_ctx(
    state: &ProofState,
    goal: &Goal,
    hyp_idx: usize,
    insert_after_idx: usize,
    new_decl: LocalDecl,
) -> Vec<LocalDecl> {
    let old_fvar = goal.local_ctx[hyp_idx].fvar;
    let mentions_old = |e: &Expr| {
        crate::tactic::hypothesis::collect_fvars(&state.metas.instantiate(e)).contains(&old_fvar)
    };
    let has_dependents =
        mentions_old(&goal.target)
            || goal.local_ctx.iter().skip(hyp_idx + 1).any(|decl| {
                mentions_old(&decl.ty) || decl.value.as_ref().is_some_and(mentions_old)
            });
    let mut new_ctx = goal.local_ctx.clone();
    new_ctx.insert(insert_after_idx + 1, new_decl);
    if has_dependents {
        new_ctx[hyp_idx].name = hidden_old_local_name(&goal.local_ctx[hyp_idx].name, old_fvar);
    } else {
        new_ctx.remove(hyp_idx);
    }
    new_ctx
}

fn validate_rewritten_goal(
    state: &ProofState,
    goal: &Goal,
    hyp_name: &clean_parser::SurfaceName,
) -> Result<(), TacticError> {
    let detail_prefix =
        format!("replace_local_decl: rewriting local '{hyp_name}' produced an ill-typed goal");

    let target_sort = state
        .infer_type(goal, &goal.target)
        .map_err(|err| TacticError::TypeCheckFailed(format!("{detail_prefix}: target: {err}")))?;
    if !matches!(target_sort.kind(), ExprKind::Sort(_)) {
        return Err(TacticError::TypeCheckFailed(format!(
            "{detail_prefix}: target is not a proposition/type: {}",
            crate::error_render::term(&target_sort)
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
            TacticError::TypeCheckFailed(format!("{detail_prefix}: target strict-check: {err}"))
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
                "{detail_prefix}: local '{name}' does not have a sort-valued type: {}",
                crate::error_render::term(&decl_sort),
                name = decl.name
            )));
        }
        // Wave 98 (Gap 17): strict-check the local's *type* — App
        // arguments inside the type must agree with their domains.
        state
            .check_type_strict(goal, &decl.ty, &decl_sort)
            .map_err(|err| {
                TacticError::TypeCheckFailed(format!(
                    "{detail_prefix}: local '{name}' type strict-check: {err}",
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
                        "{detail_prefix}: local '{name}' value strict-check: {err}",
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

/// The metadata key marking a `have` local's value ([`have_value`]).
const HAVE_MARKER: &str = "_clean_have";

/// `pf` as the value of a local the `have` tactic makes.
///
/// Lean retains a nondependent have value but hides it from reduction. Clean
/// keeps the proof as the value and
/// marks it, so the DECLARATION says it is a `have`: every copy of the goal's
/// context and every rewrite of the value (`replace_local_decl_*` substitutes
/// into it) keeps the mark, while a `let` with an equal value in a sibling
/// goal, even one minted with the same id, is a `let` (DECISIONS R127). The
/// kernel ignores metadata. Reduction and elaboration contexts expose only
/// [`LocalDecl::reduction_value`], while the stored proof remains available
/// for proof assembly, scope checks and backward dependency queries.
pub(crate) fn have_value(pf: Expr) -> Expr {
    Expr::mdata(
        vec![(Name::from_string(HAVE_MARKER), MDataValue::Bool(true))],
        pf,
    )
}

/// Whether the stored value carries the existing opaque-have marker.
fn is_have_value(value: &Expr) -> bool {
    matches!(value.kind(), ExprKind::MData(data, _)
        if data.iter().any(|(key, _)| key == &Name::from_string(HAVE_MARKER)))
}

/// The shared reduction view of a retained local value. Scope snapshots and
/// proof assembly keep the original value; only computation hides marked haves.
pub(crate) fn local_value_for_reduction(value: Option<&Expr>) -> Option<&Expr> {
    value.filter(|value| !is_have_value(value))
}

impl LocalDecl {
    /// Whether this local is one the `have` tactic made ([`have_value`]).
    pub(crate) fn is_have(&self) -> bool {
        self.value.as_ref().is_some_and(is_have_value)
    }

    /// The value visible to reduction and term elaboration. A marked `have`
    /// remains a rigid local; its checked proof is retained in `value` for
    /// proof assembly and dependency validation. Genuine lets stay reducible.
    pub(crate) fn reduction_value(&self) -> Option<&Expr> {
        local_value_for_reduction(self.value.as_ref())
    }
}

#[cfg(test)]
impl ProofState {
    pub(crate) fn validate_rewritten_goal_for_test(
        &self,
        goal: &Goal,
        hyp_name: &clean_parser::SurfaceName,
    ) -> Result<(), TacticError> {
        validate_rewritten_goal(self, goal, hyp_name)
    }

    pub(crate) fn validate_rewritten_goal_with_cache_reset_for_test(
        &self,
        goal: &Goal,
        hyp_name: &clean_parser::SurfaceName,
    ) -> Result<(), TacticError> {
        validate_rewritten_goal_with_cache_reset(self, goal, hyp_name)
    }
}
