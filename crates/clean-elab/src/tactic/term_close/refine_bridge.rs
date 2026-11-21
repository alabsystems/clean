// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared helper logic for checked `refine` goal translation.

use crate::unify::{MetaId, MetaState};
use clean_kernel::{name::NameInner, Expr, ExprFolder, ExprKind, FVarId, Name};
use clean_parser::SurfaceName;
use std::collections::{HashMap, HashSet};

use super::super::core::{Goal, ProofState, TacticError, TacticResult};
use super::super::registry::RefinePendingGoal;

#[derive(Debug, Clone)]
pub(crate) struct PendingRefineGoal {
    pub(crate) meta_id: MetaId,
    pub(crate) locals: Vec<crate::tactic::registry::RefinePendingLocal>,
    pub(crate) tag: Option<SurfaceName>,
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
    tags: &[Option<SurfaceName>],
) -> TacticResult {
    let pending_goals = tagged_pending_goals(pending_goals, tags)?;
    refine_elaborated_with_goals(state, term, elab_metas, &pending_goals)
}

/// [`refine_elaborated_from_pending_with_tags`] for an elaborated
/// ELIMINATOR application whose minor premises bind the arms' pattern
/// variables over still-open goals — the term of a tactic `match` (`refine
/// match … with | p => ?armᵢ`, Lean's own expansion).
///
/// Each open arm goal's stored target names the pattern variables as the
/// tactic FVars of its own scope, while the minor premise binds them as
/// lambda binders. That is exactly the assembled-recursor shape of `cases`
/// and `induction` (#38): strict inference compares the minor premise's
/// BVar-bound type with the meta's FVar-carrying stored type and refuses a
/// valid term ("expected (n : Nat) → motive (some n), got Nat → T[some n✝]").
/// So the term is closed as they close theirs (`close_goal_assembled`):
/// leniently inferred, its type def-eq-checked against the goal target, and
/// re-checked STRICTLY by `verify_tactic_proof` once the arms are solved —
/// and by the kernel at registration.
pub(crate) fn refine_eliminator_from_pending_with_tags(
    state: &mut ProofState,
    term: Expr,
    elab_metas: &MetaState,
    pending_goals: &[RefinePendingGoal],
    tags: &[Option<SurfaceName>],
) -> TacticResult {
    let pending_goals = tagged_pending_goals(pending_goals, tags)?;
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let (mapping, new_goals) = import_pending_goals_with(
        state,
        &goal,
        elab_metas,
        &pending_goals,
        PendingLocalIds::ByDepth,
    )?;
    let translated_term = remap_elab_metas(&term, &mapping, elab_metas)?;
    state.close_goal_assembled(&goal, translated_term)?;
    for new_goal in new_goals.into_iter().rev() {
        state.goals.push_front(new_goal);
    }
    Ok(())
}

/// The pending goals of an elaborated refine term, each carrying its tag:
/// the explicit `tags` entry when one is given, else the tag the goal
/// already carries.
fn tagged_pending_goals(
    pending_goals: &[RefinePendingGoal],
    tags: &[Option<SurfaceName>],
) -> Result<Vec<PendingRefineGoal>, TacticError> {
    if !tags.is_empty() && tags.len() != pending_goals.len() {
        return Err(TacticError::ElaborationFailed {
            detail: format!(
                "refine tag count {} did not match pending goal count {}",
                tags.len(),
                pending_goals.len()
            ),
        });
    }
    Ok(pending_goals
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
        .collect())
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
    // Each hole's captured locals are binders of `term` stacked over `goal`,
    // and `close_fvars` resolves them positionally once the holes are solved,
    // so they are numbered by depth from the goal's binder base — never from
    // the global counter, which other machinery (discharged subgoals, `simp`
    // scratch locals, rewrite validation) advances past that base (#2533).
    let (mapping, new_goals) = import_pending_goals_with(
        state,
        &goal,
        elab_metas,
        pending_goals,
        PendingLocalIds::ByDepth,
    )?;
    let translated_term = remap_elab_metas(&term, &mapping, elab_metas)?;
    finish_refine(state, &goal, translated_term, new_goals)
}

/// Import an OPEN elaborated term — one elaborated with no expected type,
/// a `rw` rule — into the proof state: every metavariable its elaboration
/// left open becomes a tactic-scope metavariable (with the goal's context
/// plus the locals it captured), and the term is rewritten to mention those.
/// Nothing is closed: the caller solves the imported metavariables against
/// the goal (`rw` unifies the rewritten side with a subterm) and may push the
/// goals of any that remain as side goals.
///
/// ENSURES: On Ok, the returned term mentions no elaborator metavariable, and
/// the returned goals are the imported metavariables in `pending_goals` order
pub(crate) fn import_open_term(
    state: &mut ProofState,
    term: Expr,
    elab_metas: &MetaState,
    pending_goals: &[RefinePendingGoal],
) -> Result<(Expr, Vec<Goal>), TacticError> {
    import_term_with(
        state,
        term,
        elab_metas,
        pending_goals,
        PendingLocalIds::Fresh,
    )
}

/// Import a value whose lifted goals occur under the value's own binders.
pub(crate) fn import_lifted_term(
    state: &mut ProofState,
    term: Expr,
    elab_metas: &MetaState,
    pending_goals: &[RefinePendingGoal],
) -> Result<(Expr, Vec<Goal>), TacticError> {
    import_term_with(
        state,
        term,
        elab_metas,
        pending_goals,
        PendingLocalIds::ByDepth,
    )
}

fn import_term_with(
    state: &mut ProofState,
    term: Expr,
    elab_metas: &MetaState,
    pending_goals: &[RefinePendingGoal],
    ids: PendingLocalIds,
) -> Result<(Expr, Vec<Goal>), TacticError> {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let pending_goals = tagged_pending_goals(pending_goals, &[])?;
    let (mapping, new_goals) =
        import_pending_goals_with(state, &goal, elab_metas, &pending_goals, ids)?;
    let translated_term = remap_elab_metas(&term, &mapping, elab_metas)?;
    Ok((translated_term, new_goals))
}

/// How the tactic FVar of a pending goal's captured local is chosen.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PendingLocalIds {
    /// From the global counter (`fresh_fvar`). Used only by
    /// `import_open_term` (`rw` rules, `simp` arguments, `rcases` type
    /// ascriptions); an ordinary `refine` numbers its holes' locals `ByDepth`.
    Fresh,
    /// By binder depth: the `k`-th local a pending goal captures — the `k`-th
    /// binder enclosing its hole below the goal's own proof position — gets
    /// `goal_binder_base(goal) + k`, the id `close_fvars` resolves at that
    /// depth. Sibling goals then reuse ids at equal depths, exactly as the
    /// branches of `cases` do (`cases_core`'s per-branch reset): every arm of
    /// an eliminator, and every hole of an ordinary `refine` term, sits under
    /// its own binder chain. A global counter numbered the
    /// SECOND binding arm's first local one past the first arm's, at depth 0
    /// of its own lambda, and its assignment was refused as a scope
    /// violation. A local shared by several goals (a column-split match's
    /// common prefix) keeps the one id it got first.
    ByDepth,
}

fn import_pending_goals_with(
    state: &mut ProofState,
    goal: &Goal,
    elab_metas: &MetaState,
    pending_goals: &[PendingRefineGoal],
    ids: PendingLocalIds,
) -> Result<(HashMap<MetaId, MetaId>, Vec<Goal>), TacticError> {
    let depth_base = state.goal_binder_base(goal);
    let mut depth_max = state.next_fvar;
    let mut mapping = HashMap::new();
    // Several branch metavariables can capture the same elaborator local. This
    // happens for a column-split match: every leaf goal sees the outer
    // constructor fields, while each leaf adds only its own inner-pattern
    // binders. Preserve that sharing when crossing into ProofState. Allocating
    // the common prefix afresh for every goal changes FVar identities in later
    // goals, so their assignments no longer fit the binders surrounding the
    // translated match term (all goals can close while the root proof remains
    // unconstructible).
    let mut shared_local_fvars: HashMap<FVarId, (FVarId, SurfaceName, Expr)> = HashMap::new();
    let mut new_goals = Vec::new();

    for pending_goal in pending_goals {
        let meta =
            elab_metas
                .get(pending_goal.meta_id)
                .ok_or_else(|| TacticError::ElaborationFailed {
                    detail: format!(
                        "refine referenced missing elaborator meta ?m{}",
                        pending_goal.meta_id.0
                    ),
                })?;
        let mut local_ctx = goal.local_ctx.clone();
        let mut local_fvars = HashMap::new();
        let mut introduced_binders = Vec::new();
        for (depth, local) in pending_goal.locals.iter().enumerate() {
            let translated_local_ty = remap_elab_metas(&local.ty, &mapping, elab_metas)?;
            let translated_local_ty = remap_pending_local_fvars(&translated_local_ty, &local_fvars);
            let translated_local_fvar = if let Some((translated, prior_name, prior_ty)) =
                shared_local_fvars.get(&local.fvar)
            {
                if !prior_name.same_syntax(&local.name) || prior_ty != &translated_local_ty {
                    return Err(TacticError::ElaborationFailed {
                        detail: format!(
                            "shared refine local {} changed from `{}` : {} to `{}` : {}",
                            crate::error_render::fvar(local.fvar, None),
                            prior_name,
                            crate::error_render::term(prior_ty),
                            local.name,
                            crate::error_render::term(&translated_local_ty)
                        ),
                    });
                }
                *translated
            } else {
                let translated = match ids {
                    PendingLocalIds::Fresh => state.fresh_fvar(),
                    PendingLocalIds::ByDepth => {
                        let id = depth_base.saturating_add(depth as u64);
                        depth_max = depth_max.max(id.saturating_add(1));
                        FVarId::new(id)
                    }
                };
                shared_local_fvars.insert(
                    local.fvar,
                    (translated, local.name.clone(), translated_local_ty.clone()),
                );
                translated
            };
            local_fvars.insert(local.fvar, translated_local_fvar);
            introduced_binders.push(translated_local_fvar);
            local_ctx.push(crate::tactic::LocalDecl {
                binder_info: Default::default(),
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
            // A named hole starts a new case: its positional binders are only
            // the locals introduced by this pending goal, in captured order.
            // An unnamed successor keeps the existing case's exact IDs.
            tag: pending_goal.tag.clone().or_else(|| goal.tag.clone()),
            case_binders: if pending_goal.tag.is_some() {
                introduced_binders
            } else {
                goal.case_binders.clone()
            },
        });
    }
    // Depth-chosen ids never pull the global counter back: unrelated later
    // allocations stay past every id handed out here.
    state.next_fvar = state.next_fvar.max(depth_max);
    Ok((mapping, new_goals))
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
        ExprKind::Const(name, _) if is_placeholder_name(name) => {
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
                tag: goal.tag.clone(),
                case_binders: goal.case_binders.clone(),
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
                            "refine application expected a function type, got {}",
                            crate::error_render::term(&func_ty)
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
                    expected: format!("{expected_arg_ty}"),
                    actual: format!("{actual_arg_ty}"),
                });
            }

            let result_ty = state.metas.instantiate(&body_ty.instantiate(&refined_arg));
            let result_ty = state.whnf(goal, &result_ty);
            if let Some(expected_ty) = expected_ty {
                let expected_ty = state.metas.instantiate(expected_ty);
                if !state.is_def_eq(goal, &result_ty, &expected_ty) {
                    return Err(TacticError::TypeMismatch {
                        expected: format!("{expected_ty}"),
                        actual: format!("{result_ty}"),
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
                        expected: format!("{expected_ty}"),
                        actual: format!("{actual_ty}"),
                    });
                }
            }
            Ok((expr.clone(), inferred_ty))
        }
    }
}

/// Check the legacy atomic-constant refine placeholder convention.
///
/// Typed source holes use elaborator metas; this older kernel-expression API
/// recognizes only one actual Str component, never a projected hierarchy.
pub(crate) fn is_placeholder_name(name: &Name) -> bool {
    matches!(name.inner(), NameInner::Str(parent, text)
        if parent.is_anon() && (text.as_ref() == "_" || text.as_ref() == "?" || text.starts_with("?_")))
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
                "refine term retains unresolved elaborator metas {}",
                crate::error_render::opaque(&remapper.residual)
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

    fn case_state(target: impl FnOnce(&Expr) -> Expr) -> (ProofState, Expr, FVarId) {
        let mut env = Environment::default();
        env.init_nat().expect("Nat init");
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let outer = FVarId::new(0);
        let mut state = ProofState::with_context(
            env,
            target(&nat),
            vec![crate::tactic::LocalDecl {
                binder_info: Default::default(),
                fvar: outer,
                name: SurfaceName::component("outer.field", true),
                ty: nat.clone(),
                value: None,
            }],
        );
        let goal = state.goals.front_mut().unwrap();
        goal.tag = Some(SurfaceName::component("outer.case", true));
        goal.case_binders = vec![outer];
        (state, nat, outer)
    }

    #[test]
    fn typed_refine_named_cases_bind_only_new_locals_and_keep_exact_tags() {
        let names = [
            Name::anon().str("branch.dot"),
            Name::anon().str("branch").str("dot"),
            Name::anon().str("branch").str("7"),
            Name::anon().str("branch").num(7),
        ];
        for (index, name) in names.iter().enumerate() {
            let (mut state, nat, outer) =
                case_state(|nat| Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat.clone())));
            let mut elab_metas = MetaState::new();
            let local_name = SurfaceName::from_name(name.clone());
            let branch_fvar = FVarId::new(17);
            let second_fvar = FVarId::new(27);
            let second_name = SurfaceName::component("second", false);
            let branch_meta = elab_metas.fresh_with_locals(
                nat.clone(),
                vec![
                    (local_name.clone(), branch_fvar, nat.clone()),
                    (second_name.clone(), second_fvar, nat.clone()),
                ],
            );
            let actual_tag = SurfaceName::from_name(names[(index + 1) % names.len()].clone());
            let term = Expr::lam(
                BinderInfo::Default,
                nat.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    nat.clone(),
                    Expr::fvar(MetaState::to_fvar(branch_meta)),
                ),
            );
            refine_elaborated_from_pending_with_tags(
                &mut state,
                term,
                &elab_metas,
                &[RefinePendingGoal {
                    meta_id: branch_meta,
                    locals: vec![
                        RefinePendingLocal {
                            name: local_name.clone(),
                            fvar: branch_fvar,
                            ty: nat.clone(),
                        },
                        RefinePendingLocal {
                            name: second_name.clone(),
                            fvar: second_fvar,
                            ty: nat,
                        },
                    ],
                    tag: Some(local_name.clone()),
                }],
                &[Some(actual_tag.clone())],
            )
            .expect("typed named branch bridge");
            let goal = state.current_goal().unwrap().clone();
            assert_eq!(goal.tag, Some(actual_tag));
            assert_eq!(goal.local_ctx.len(), 3);
            assert_eq!(goal.local_ctx[1].name, local_name);
            assert_eq!(goal.local_ctx[2].name, second_name);
            assert_eq!(
                goal.case_binders,
                vec![goal.local_ctx[1].fvar, goal.local_ctx[2].fvar]
            );
            assert!(!goal.case_binders.contains(&outer));
            state
                .close_goal(&goal, Expr::fvar(goal.local_ctx[2].fvar))
                .expect("checked branch close");
            assert!(state.is_complete());
        }
    }

    #[test]
    fn typed_refine_unnamed_successor_keeps_existing_case_identity() {
        let (mut state, nat, outer) = case_state(Clone::clone);
        let before = state.current_goal().unwrap().clone();
        let mut elab_metas = MetaState::new();
        let pending = elab_metas.fresh(nat);
        refine_elaborated_from_pending(
            &mut state,
            Expr::fvar(MetaState::to_fvar(pending)),
            &elab_metas,
            &[RefinePendingGoal {
                meta_id: pending,
                locals: vec![],
                tag: None,
            }],
        )
        .expect("unnamed successor bridge");
        let after = state.current_goal().unwrap().clone();
        assert_eq!(after.tag, before.tag);
        assert_eq!(after.case_binders, before.case_binders);
        state
            .close_goal(&after, Expr::fvar(outer))
            .expect("checked outer local close");
        assert!(state.is_complete());
    }

    #[test]
    fn typed_refine_legacy_placeholder_dispatch_is_atomic_not_display_based() {
        for text in ["_", "?", "?_hole"] {
            let atomic = Name::anon().str(text);
            assert!(is_placeholder_name(&atomic));
            assert_eq!(
                super::super::refine::count_placeholders(&Expr::const_(atomic.clone(), vec![])),
                1
            );
            assert!(!is_placeholder_name(&atomic.clone().str("field")));
            assert!(!is_placeholder_name(&atomic.num(7)));
        }
        assert!(!is_placeholder_name(&Name::anon()));
        assert!(!is_placeholder_name(&Name::anon().num(7)));
        let (mut state, _, outer) = case_state(Clone::clone);
        let before = state.current_goal().unwrap().clone();
        super::super::refine::refine(&mut state, Expr::const_(Name::anon().str("_"), vec![]))
            .expect("legacy placeholder bridge");
        let after = state.current_goal().unwrap().clone();
        assert_eq!(after.tag, before.tag);
        assert_eq!(after.case_binders, before.case_binders);
        state
            .close_goal(&after, Expr::fvar(outer))
            .expect("checked placeholder close");
        assert!(state.is_complete());
    }

    #[test]
    fn typed_assertion_resets_new_proof_case_and_preserves_continuation() {
        let (mut state, nat, outer) = case_state(Clone::clone);
        let before = state.current_goal().unwrap().clone();
        let name = SurfaceName::component("asserted.dot", true);
        super::super::assert_(&mut state, &name, nat).expect("typed assertion");
        let proof = state.current_goal().unwrap().clone();
        assert!(proof.tag.is_none());
        assert!(proof.case_binders.is_empty());
        state
            .close_goal(&proof, Expr::fvar(outer))
            .expect("checked assertion proof");
        let continuation = state.current_goal().unwrap().clone();
        assert_eq!(continuation.tag, before.tag);
        assert_eq!(continuation.case_binders, before.case_binders);
        let asserted = continuation.local_ctx.last().unwrap();
        assert_eq!(asserted.name, name);
        assert_ne!(asserted.name, SurfaceName::generated_path("asserted.dot"));
        state
            .close_goal(&continuation, Expr::fvar(asserted.fvar))
            .expect("checked continuation");
        assert!(state.is_complete());
    }

    #[test]
    fn typed_refine_shared_local_refuses_changed_lexical_annotation() {
        let (mut state, nat, _) = case_state(|nat| Expr::arrow(nat.clone(), nat.clone()));
        let mut elab_metas = MetaState::new();
        let shared = FVarId::new(17);
        let plain = SurfaceName::component("_", false);
        let quoted = SurfaceName::component("_", true);
        assert_eq!(plain, quoted);
        assert!(!plain.same_syntax(&quoted));
        let left =
            elab_metas.fresh_with_locals(nat.clone(), vec![(plain.clone(), shared, nat.clone())]);
        let right =
            elab_metas.fresh_with_locals(nat.clone(), vec![(quoted.clone(), shared, nat.clone())]);
        let error = refine_elaborated_from_pending(
            &mut state,
            Expr::lam(
                BinderInfo::Default,
                nat.clone(),
                Expr::fvar(MetaState::to_fvar(left)),
            ),
            &elab_metas,
            &[
                RefinePendingGoal {
                    meta_id: left,
                    locals: vec![RefinePendingLocal {
                        name: plain,
                        fvar: shared,
                        ty: nat.clone(),
                    }],
                    tag: None,
                },
                RefinePendingGoal {
                    meta_id: right,
                    locals: vec![RefinePendingLocal {
                        name: quoted,
                        fvar: shared,
                        ty: nat,
                    }],
                    tag: None,
                },
            ],
        )
        .expect_err("one captured FVar cannot change wildcard visibility");
        assert!(
            matches!(error, TacticError::ElaborationFailed { detail } if detail.contains("shared refine local"))
        );
        assert!(!state.is_complete());
    }

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
            vec![(SurfaceName::component("k", false), branch_fvar, nat.clone())],
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
                    name: SurfaceName::component("k", false),
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
        let captured = vec![(SurfaceName::component("x", false), shared_fvar, nat.clone())];
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
            name: SurfaceName::component("x", false),
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
