// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helper logic for checked `refine` goal translation.

use crate::unify::{MetaId, MetaState};
use clean_kernel::{Expr, ExprFolder, ExprKind, FVarId};
use std::collections::{HashMap, HashSet};

use super::super::core::{Goal, ProofState, TacticError, TacticResult};
use super::super::registry::RefinePendingGoal;

#[derive(Debug, Clone)]
pub(crate) struct PendingRefineGoal {
    pub(crate) meta_id: MetaId,
    pub(crate) locals: Vec<crate::tactic::registry::RefinePendingLocal>,
    pub(crate) tag: Option<String>,
}

/// Bridge elaborated refine terms into the tactic proof state.
///
/// Translates elaborator-scope metavariables into tactic-scope metavariables,
/// closes the current goal with the translated term, and pushes new goals
/// for each pending meta.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `elab_metas` contains entries for all IDs in `pending_metas`
/// REQUIRES: `term` is a well-typed expression in `elab_metas`'s context
/// ENSURES: On Ok, the current goal is closed and `pending_metas.len()` new goals are pushed
/// ENSURES: On Err(NoGoals), no goals exist; state unchanged
/// ENSURES: On Err(ElaborationFailed), an elaborator meta is missing; state unchanged
#[cfg(test)]
pub(crate) fn refine_elaborated(
    state: &mut ProofState,
    term: Expr,
    elab_metas: &MetaState,
    pending_metas: &[MetaId],
) -> TacticResult {
    let pending_goals = pending_metas
        .iter()
        .copied()
        .map(|meta_id| PendingRefineGoal {
            meta_id,
            locals: Vec::new(),
            tag: None,
        })
        .collect::<Vec<_>>();
    refine_elaborated_with_goals(state, term, elab_metas, &pending_goals)
}

pub(crate) fn refine_elaborated_from_pending(
    state: &mut ProofState,
    term: Expr,
    elab_metas: &MetaState,
    pending_goals: &[RefinePendingGoal],
) -> TacticResult {
    refine_elaborated_from_pending_with_tags(state, term, elab_metas, pending_goals, &[])
}

pub(crate) fn refine_elaborated_from_pending_with_tags(
    state: &mut ProofState,
    term: Expr,
    elab_metas: &MetaState,
    pending_goals: &[RefinePendingGoal],
    tags: &[Option<String>],
) -> TacticResult {
    if !tags.is_empty() && tags.len() != pending_goals.len() {
        return Err(TacticError::ElaborationFailed {
            detail: format!(
                "refine tag count {} did not match pending goal count {}",
                tags.len(),
                pending_goals.len()
            ),
        });
    }
    let pending_goals = pending_goals
        .iter()
        .enumerate()
        .map(|(idx, goal)| PendingRefineGoal {
            meta_id: goal.meta_id,
            locals: goal.locals.clone(),
            // An explicit `tags` slice (e.g. the `match` tactic's `match_N`
            // tags) overrides; otherwise fall back to the tag the goal already
            // carries — the `?name` synthetic-hole name recorded during
            // elaboration — so `case name => …` can select it.
            tag: match tags.get(idx) {
                Some(tag) => tag.clone(),
                None => goal.tag.clone(),
            },
        })
        .collect::<Vec<_>>();
    refine_elaborated_with_goals(state, term, elab_metas, &pending_goals)
}

pub(crate) fn refine_elaborated_with_goals(
    state: &mut ProofState,
    term: Expr,
    elab_metas: &MetaState,
    pending_goals: &[PendingRefineGoal],
) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let mut mapping = HashMap::new();
    // Several branch metavariables can capture the same elaborator local. This
    // happens for a column-split match: every leaf goal sees the outer
    // constructor fields, while each leaf adds only its own inner-pattern
    // binders. Preserve that sharing when crossing into ProofState. Allocating
    // the common prefix afresh for every goal changes FVar identities in later
    // goals, so their assignments no longer fit the binders surrounding the
    // translated match term (all goals can close while the root proof remains
    // unconstructible).
    let mut shared_local_fvars: HashMap<FVarId, (FVarId, String, Expr)> = HashMap::new();
    let mut new_goals = Vec::new();

    for pending_goal in pending_goals {
        let meta =
            elab_metas
                .get(pending_goal.meta_id)
                .ok_or_else(|| TacticError::ElaborationFailed {
                    detail: format!(
                        "refine referenced missing elaborator meta {:?}",
                        pending_goal.meta_id
                    ),
                })?;
        let mut local_ctx = goal.local_ctx.clone();
        let mut local_fvars = HashMap::new();
        for local in &pending_goal.locals {
            let translated_local_ty = remap_elab_metas(&local.ty, &mapping, elab_metas)?;
            let translated_local_ty = remap_pending_local_fvars(&translated_local_ty, &local_fvars);
            let translated_local_fvar = if let Some((translated, prior_name, prior_ty)) =
                shared_local_fvars.get(&local.fvar)
            {
                if prior_name != &local.name || prior_ty != &translated_local_ty {
                    return Err(TacticError::ElaborationFailed {
                        detail: format!(
                            "shared refine local {:?} changed from `{}` : {:?} to `{}` : {:?}",
                            local.fvar, prior_name, prior_ty, local.name, translated_local_ty
                        ),
                    });
                }
                *translated
            } else {
                let translated = state.fresh_fvar();
                shared_local_fvars.insert(
                    local.fvar,
                    (translated, local.name.clone(), translated_local_ty.clone()),
                );
                translated
            };
            local_fvars.insert(local.fvar, translated_local_fvar);
            local_ctx.push(crate::tactic::LocalDecl {
                fvar: translated_local_fvar,
                name: local.name.clone(),
                ty: translated_local_ty,
                value: None,
            });
        }
        let translated_ty = remap_elab_metas(&meta.ty, &mapping, elab_metas)?;
        let translated_ty = remap_pending_local_fvars(&translated_ty, &local_fvars);
        let new_meta_id = state.fresh_meta_in_context(translated_ty.clone(), &local_ctx);
        state.invalidate_tc_cache();
        mapping.insert(pending_goal.meta_id, new_meta_id);
        new_goals.push(Goal {
            meta_id: new_meta_id,
            target: translated_ty,
            local_ctx,
            tag: pending_goal.tag.clone(),
        });
    }

    let translated_term = remap_elab_metas(&term, &mapping, elab_metas)?;
    finish_refine(state, &goal, translated_term, new_goals)
}

/// Close the current goal with `proof` and push `new_goals` to the front.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty and `goal` is the current front goal
/// REQUIRES: `proof` is a well-typed expression matching `goal.target`
/// ENSURES: On Ok, `goal` is closed and `new_goals` are pushed in reverse order to front
/// ENSURES: On Err, `close_goal` failed; state may be partially modified
pub(crate) fn finish_refine(
    state: &mut ProofState,
    goal: &Goal,
    proof: Expr,
    new_goals: Vec<Goal>,
) -> TacticResult {
    state.close_goal(goal, proof)?;
    for new_goal in new_goals.into_iter().rev() {
        state.goals.push_front(new_goal);
    }
    Ok(())
}

/// Recursively elaborate an expression, replacing placeholder constants with
/// fresh metavariables and type-checking application arguments.
///
/// # Contract
///
/// REQUIRES: `goal` is a valid goal in `state`
/// REQUIRES: `expr` is well-formed in the goal's local context
/// ENSURES: On Ok, returns `(elaborated_expr, inferred_type)` where placeholders are
///   replaced by fresh meta-FVars and corresponding goals are appended to `new_goals`
/// ENSURES: On Err(ElaborationFailed), a placeholder has no expected type or
///   an application head is not a function type
/// ENSURES: On Err(TypeMismatch), argument type does not match function's parameter type
pub(crate) fn elaborate_placeholder_term(
    state: &mut ProofState,
    goal: &Goal,
    expr: &Expr,
    expected_ty: Option<&Expr>,
    new_goals: &mut Vec<Goal>,
) -> Result<(Expr, Expr), TacticError> {
    match expr.kind() {
        ExprKind::Const(name, _) if is_placeholder_name(&name.to_string()) => {
            let expected_ty = expected_ty.ok_or_else(|| TacticError::ElaborationFailed {
                detail: "refine placeholder requires an expected type".into(),
            })?;
            let expected_ty = state.metas.instantiate(expected_ty);
            let new_meta_id = state.fresh_meta(expected_ty.clone());
            state.invalidate_tc_cache();
            new_goals.push(Goal {
                meta_id: new_meta_id,
                target: expected_ty.clone(),
                local_ctx: goal.local_ctx.clone(),
                tag: None,
            });
            Ok((Expr::fvar(MetaState::to_fvar(new_meta_id)), expected_ty))
        }
        ExprKind::App(func, arg) => {
            let (refined_func, func_ty) =
                elaborate_placeholder_term(state, goal, func, None, new_goals)?;
            let func_ty = state.whnf(goal, &func_ty);
            let (arg_ty, body_ty) = match func_ty.kind() {
                ExprKind::Pi(_, arg_ty, body_ty) => {
                    (arg_ty.as_ref().clone(), body_ty.as_ref().clone())
                }
                _ => {
                    return Err(TacticError::ElaborationFailed {
                        detail: format!(
                            "refine application expected a function type, got {func_ty:?}"
                        ),
                    });
                }
            };
            let (refined_arg, actual_arg_ty) =
                elaborate_placeholder_term(state, goal, arg, Some(&arg_ty), new_goals)?;
            let expected_arg_ty = state.metas.instantiate(&arg_ty);
            let actual_arg_ty = state.whnf(goal, &actual_arg_ty);
            if !state.is_def_eq(goal, &actual_arg_ty, &expected_arg_ty) {
                return Err(TacticError::TypeMismatch {
                    expected: format!("{expected_arg_ty:?}"),
                    actual: format!("{actual_arg_ty:?}"),
                });
            }

            let result_ty = state.metas.instantiate(&body_ty.instantiate(&refined_arg));
            let result_ty = state.whnf(goal, &result_ty);
            if let Some(expected_ty) = expected_ty {
                let expected_ty = state.metas.instantiate(expected_ty);
                if !state.is_def_eq(goal, &result_ty, &expected_ty) {
                    return Err(TacticError::TypeMismatch {
                        expected: format!("{expected_ty:?}"),
                        actual: format!("{result_ty:?}"),
                    });
                }
            }
            Ok((Expr::app(refined_func, refined_arg), result_ty))
        }
        _ => {
            let inferred_ty = state.infer_type(goal, expr)?;
            if let Some(expected_ty) = expected_ty {
                let expected_ty = state.metas.instantiate(expected_ty);
                let actual_ty = state.whnf(goal, &inferred_ty);
                if !state.is_def_eq(goal, &actual_ty, &expected_ty) {
                    return Err(TacticError::TypeMismatch {
                        expected: format!("{expected_ty:?}"),
                        actual: format!("{actual_ty:?}"),
                    });
                }
            }
            Ok((expr.clone(), inferred_ty))
        }
    }
}

/// Check if a name represents a refine placeholder (`_`, `?`, or `?_`-prefixed).
///
/// ENSURES: Returns `true` iff `name` is `"_"`, `"?"`, or starts with `"?_"`
pub(crate) fn is_placeholder_name(name: &str) -> bool {
    name == "_" || name == "?" || name.starts_with("?_")
}

struct ElabMetaRemapper<'a> {
    mapping: &'a HashMap<MetaId, MetaId>,
    elab_metas: &'a MetaState,
    residual: Vec<MetaId>,
    seen: HashSet<MetaId>,
}

impl ExprFolder for ElabMetaRemapper<'_> {
    fn fold_fvar(&mut self, id: FVarId) -> Expr {
        let Some(meta_id) = MetaState::from_fvar(id) else {
            return Expr::fvar(id);
        };
        if let Some(mapped) = self.mapping.get(&meta_id) {
            return Expr::fvar(MetaState::to_fvar(*mapped));
        }
        if self
            .elab_metas
            .get(meta_id)
            .is_some_and(|meta| meta.assignment.is_none())
            && self.seen.insert(meta_id)
        {
            self.residual.push(meta_id);
        }
        Expr::fvar(id)
    }
}

/// Instantiate and remap elaborator metavariables in `expr` to tactic-scope IDs.
///
/// # Contract
///
/// REQUIRES: `mapping` maps elaborator MetaIds to tactic-scope MetaIds
/// REQUIRES: `elab_metas` provides instantiation for assigned elaborator metas
/// ENSURES: On Ok, all mapped meta-FVars are replaced with tactic-scope equivalents
/// ENSURES: On Err(ElaborationFailed), unresolved elaborator metas remain after remapping
fn remap_elab_metas(
    expr: &Expr,
    mapping: &HashMap<MetaId, MetaId>,
    elab_metas: &MetaState,
) -> Result<Expr, TacticError> {
    let instantiated = elab_metas.instantiate(expr);
    let instantiated = elab_metas.instantiate_levels(&instantiated);
    let mut remapper = ElabMetaRemapper {
        mapping,
        elab_metas,
        residual: Vec::new(),
        seen: HashSet::new(),
    };
    let remapped = remapper.fold_expr(&instantiated);
    if remapper.residual.is_empty() {
        Ok(remapped)
    } else {
        Err(TacticError::ElaborationFailed {
            detail: format!(
                "refine term retains unresolved elaborator metas {:?}",
                remapper.residual
            ),
        })
    }
}

fn remap_pending_local_fvars(expr: &Expr, mapping: &HashMap<FVarId, FVarId>) -> Expr {
    if mapping.is_empty() || !expr.has_fvar_quick() {
        return expr.clone();
    }

    struct PendingLocalFVarRemapper<'a> {
        mapping: &'a HashMap<FVarId, FVarId>,
    }

    impl ExprFolder for PendingLocalFVarRemapper<'_> {
        fn fold_fvar(&mut self, id: FVarId) -> Expr {
            self.mapping
                .get(&id)
                .copied()
                .map(Expr::fvar)
                .unwrap_or_else(|| Expr::fvar(id))
        }
    }

    let mut remapper = PendingLocalFVarRemapper { mapping };
    remapper.fold_expr(expr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tactic::registry::{RefinePendingGoal, RefinePendingLocal};
    use clean_kernel::{BinderInfo, Environment, Level, Name};

    #[test]
    fn test_refine_elaborated_from_pending_remaps_gapped_local_fvars() {
        let mut env = Environment::new();
        env.init_nat().expect("Nat init should succeed");

        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let mut state = ProofState::new(env, Expr::arrow(nat.clone(), nat.clone()));
        let mut elab_metas = MetaState::new();
        let branch_fvar = FVarId::new(7);
        let branch_meta = elab_metas.fresh_with_locals(
            nat.clone(),
            vec![("k".to_string(), branch_fvar, nat.clone())],
        );
        let term = Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::fvar(MetaState::to_fvar(branch_meta)),
        );

        refine_elaborated_from_pending(
            &mut state,
            term,
            &elab_metas,
            &[RefinePendingGoal {
                meta_id: branch_meta,
                locals: vec![RefinePendingLocal {
                    name: "k".to_string(),
                    fvar: branch_fvar,
                    ty: nat.clone(),
                }],
                tag: None,
            }],
        )
        .expect("pending refine goal should translate into a tactic subgoal");

        let goal = state
            .current_goal()
            .expect("translated refine should leave one pending subgoal")
            .clone();
        assert_eq!(
            goal.local_ctx.len(),
            1,
            "translated pending goal should expose the captured branch local"
        );
        assert_ne!(
            goal.local_ctx[0].fvar, branch_fvar,
            "bridge must remap elaborator local IDs into tactic-local IDs"
        );

        state
            .close_goal(&goal, Expr::fvar(goal.local_ctx[0].fvar))
            .expect("branch local should close the translated subgoal");

        assert!(
            state.is_complete(),
            "closing the translated subgoal should complete the proof"
        );
        assert_eq!(
            state.closed_proof(),
            Some(Expr::lam(BinderInfo::Default, nat, Expr::bvar(0))),
            "closed proof should use the lambda binder, not the elaborator branch FVar"
        );
    }

    #[test]
    fn test_refine_pending_goals_preserve_shared_captured_local_identity() {
        let env = Environment::with_prelude();
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let prod_nat = Expr::apps(
            Expr::const_(
                Name::from_string("Prod"),
                vec![Level::zero(), Level::zero()],
            ),
            [nat.clone(), nat.clone()],
        );
        let mut state = ProofState::new(env, Expr::arrow(nat.clone(), prod_nat));
        let mut elab_metas = MetaState::new();
        let shared_fvar = FVarId::new(17);
        let captured = vec![("x".to_string(), shared_fvar, nat.clone())];
        let left = elab_metas.fresh_with_locals(nat.clone(), captured.clone());
        let right = elab_metas.fresh_with_locals(nat.clone(), captured);
        let pair = Expr::apps(
            Expr::const_(
                Name::from_string("Prod.mk"),
                vec![Level::zero(), Level::zero()],
            ),
            [
                nat.clone(),
                nat.clone(),
                Expr::fvar(MetaState::to_fvar(left)),
                Expr::fvar(MetaState::to_fvar(right)),
            ],
        );
        let term = Expr::lam(BinderInfo::Default, nat.clone(), pair);
        let pending_local = RefinePendingLocal {
            name: "x".to_string(),
            fvar: shared_fvar,
            ty: nat.clone(),
        };

        refine_elaborated_from_pending(
            &mut state,
            term,
            &elab_metas,
            &[
                RefinePendingGoal {
                    meta_id: left,
                    locals: vec![pending_local.clone()],
                    tag: None,
                },
                RefinePendingGoal {
                    meta_id: right,
                    locals: vec![pending_local],
                    tag: None,
                },
            ],
        )
        .expect("two pending branches with one captured binder should translate");

        let first = state.current_goal().expect("first branch goal").clone();
        let shared = first.local_ctx[0].fvar;
        state
            .close_goal(&first, Expr::fvar(shared))
            .expect("shared local should close first branch");
        let second = state.current_goal().expect("second branch goal").clone();
        assert_eq!(
            second.local_ctx[0].fvar, shared,
            "the same captured elaborator local must keep one tactic FVar identity"
        );
        state
            .close_goal(&second, Expr::fvar(shared))
            .expect("shared local should close second branch");

        assert!(state.is_complete());
        let expected_pair = Expr::apps(
            Expr::const_(
                Name::from_string("Prod.mk"),
                vec![Level::zero(), Level::zero()],
            ),
            [nat.clone(), nat.clone(), Expr::bvar(0), Expr::bvar(0)],
        );
        assert_eq!(
            state.closed_proof(),
            Some(Expr::lam(BinderInfo::Default, nat, expected_pair))
        );
    }
}
