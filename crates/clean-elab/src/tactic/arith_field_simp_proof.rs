// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-carry helpers for top-level `field_simp` equality rewrites.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use super::{Goal, ProofState, TacticError};
use crate::unify::{MetaId, MetaState, Unifier, UnifyResult};

#[derive(Debug)]
pub(crate) struct FieldSimpRewrite {
    pub(crate) new_target: Expr,
    pub(crate) target_eq_proof: Expr,
    pub(crate) side_goals: Vec<Goal>,
}

struct TheoremApplyResult {
    side_goals: Vec<Goal>,
    introduced_meta_ids: Vec<MetaId>,
}

#[derive(Clone, Copy, Debug)]
enum FieldSimpTheorem {
    DivEqIff,
    EqDivIffMulEq,
    DivEqDivIff,
}

impl FieldSimpTheorem {
    fn for_division_shape(has_lhs_div: bool, has_rhs_div: bool) -> Result<Self, TacticError> {
        match (has_lhs_div, has_rhs_div) {
            (true, false) => Ok(Self::DivEqIff),
            (false, true) => Ok(Self::EqDivIffMulEq),
            (true, true) => Ok(Self::DivEqDivIff),
            (false, false) => Err(TacticError::NoProgress {
                tactic: "field_simp".to_string(),
            }),
        }
    }

    fn constant_name(self) -> &'static str {
        match self {
            Self::DivEqIff => "div_eq_iff",
            Self::EqDivIffMulEq => "eq_div_iff_mul_eq",
            Self::DivEqDivIff => "div_eq_div_iff",
        }
    }

    fn expected_side_goal_count(self) -> usize {
        match self {
            Self::DivEqIff | Self::EqDivIffMulEq => 1,
            Self::DivEqDivIff => 2,
        }
    }
}

pub(crate) fn build_top_level_rewrite(
    state: &mut ProofState,
    goal: &Goal,
    has_lhs_div: bool,
    has_rhs_div: bool,
) -> Result<FieldSimpRewrite, TacticError> {
    let theorem = FieldSimpTheorem::for_division_shape(has_lhs_div, has_rhs_div)?;
    require_consts(
        state,
        &[
            "Iff",
            "Iff.mp",
            "Iff.mpr",
            "propext",
            theorem.constant_name(),
        ],
    )?;

    let old_target = state.metas().instantiate(&goal.target);
    let (iff_target, rhs_meta_id) = make_theorem_goal(state, goal, &old_target);

    let mut sub = state.clone_with_fresh_goal_target(iff_target.clone());
    let root_meta_id = sub
        .current_goal()
        .expect("fresh field_simp sub-state must have a root goal")
        .meta_id;
    let rhs_scope = state.meta_scope_for_context(&goal.local_ctx);
    sub.metas_mut()
        .ensure_meta_with_locals(rhs_meta_id, Expr::prop(), rhs_scope);

    let theorem_apply = apply_theorem_collect_goals(&mut sub, theorem)?;
    let theorem_goal_ids: Vec<MetaId> = theorem_apply
        .side_goals
        .iter()
        .map(|goal| goal.meta_id)
        .collect();

    let rhs_assignment =
        sub.metas()
            .get_assignment(rhs_meta_id)
            .ok_or_else(|| TacticError::InvalidTarget {
                tactic: "field_simp".to_string(),
                detail: format!(
                    "{} did not determine the rewritten target",
                    theorem.constant_name()
                ),
            })?;
    let new_target = sub.metas().instantiate(rhs_assignment);

    let instantiated_old_target = sub.metas().instantiate(&goal.target);
    let instantiated_iff_target = sub.metas().instantiate(&iff_target);
    let (iff_lhs, iff_rhs) =
        match_iff(&instantiated_iff_target).ok_or_else(|| TacticError::InvalidTarget {
            tactic: "field_simp".to_string(),
            detail: "theorem application did not leave an instantiated Iff target".to_string(),
        })?;
    if iff_lhs != instantiated_old_target || iff_rhs != new_target {
        return Err(TacticError::InvalidTarget {
            tactic: "field_simp".to_string(),
            detail: "theorem-backed rewrite target drifted from the instantiated Iff result"
                .to_string(),
        });
    }

    let iff_proof = sub
        .metas()
        .get_assignment(root_meta_id)
        .map(|proof| sub.metas().instantiate(proof))
        .ok_or_else(|| {
            TacticError::TypeCheckFailed(
                "field_simp: theorem application left the rewrite proof unassigned".to_string(),
            )
        })?;
    let target_eq_proof = mk_prop_eq_from_iff(&instantiated_old_target, &new_target, iff_proof);

    verify_helper_metas(
        &sub,
        rhs_meta_id,
        &theorem_apply.introduced_meta_ids,
        &theorem_goal_ids,
        theorem.expected_side_goal_count(),
        theorem.constant_name(),
    )?;

    state.merge_meta_state(&sub);

    Ok(FieldSimpRewrite {
        new_target,
        target_eq_proof,
        side_goals: theorem_apply.side_goals,
    })
}

fn require_consts(state: &ProofState, constants: &[&str]) -> Result<(), TacticError> {
    for constant in constants {
        if state
            .env()
            .get_const(&Name::from_string(constant))
            .is_none()
        {
            return Err(TacticError::EnvironmentMissing {
                constant: (*constant).to_string(),
            });
        }
    }
    Ok(())
}

fn make_theorem_goal(state: &ProofState, goal: &Goal, old_target: &Expr) -> (Expr, MetaId) {
    let mut scratch_metas = state.metas().clone();
    let scope = state.meta_scope_for_context(&goal.local_ctx);
    // Predict the two IDs that clone_with_fresh_goal_target and the imported
    // RHS hole will allocate, while preserving the exact goal scope.
    let _predicted_root_meta = scratch_metas.fresh_with_locals(Expr::prop(), scope.clone());
    let rhs_meta_id = scratch_metas.fresh_with_locals(Expr::prop(), scope);
    let rhs_meta = Expr::fvar(MetaState::to_fvar(rhs_meta_id));
    (make_iff(old_target, &rhs_meta), rhs_meta_id)
}

fn make_iff(lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), lhs.clone()),
        rhs.clone(),
    )
}

fn match_iff(expr: &Expr) -> Option<(Expr, Expr)> {
    if let ExprKind::App(f1, rhs) = expr.kind() {
        if let ExprKind::App(f2, lhs) = f1.kind() {
            if let ExprKind::Const(name, _) = f2.kind() {
                if name.to_string() == "Iff" {
                    return Some(((**lhs).clone(), (**rhs).clone()));
                }
            }
        }
    }
    None
}

fn mk_prop_eq_from_iff(lhs: &Expr, rhs: &Expr, iff_proof: Expr) -> Expr {
    // `propext : {a b : Prop} → (a ↔ b) → a = b` takes the `Iff` proof directly
    // (see `clean-kernel/src/env/logic.rs::init_propext`). Apply it to the two
    // (implicit) Prop arguments and then the `iff_proof`. The previous form
    // applied `propext` to extracted `Iff.mp`/`Iff.mpr` implications as if its
    // signature were `(a → b) → (b → a) → a = b`, producing an ill-typed term the
    // kernel rejected (`NotAFunction`).
    let mut proof = Expr::const_(Name::from_string("propext"), vec![]);
    proof = Expr::app(proof, lhs.clone());
    proof = Expr::app(proof, rhs.clone());
    proof = Expr::app(proof, iff_proof);
    proof
}

fn apply_theorem_collect_goals(
    state: &mut ProofState,
    theorem: FieldSimpTheorem,
) -> Result<TheoremApplyResult, TacticError> {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let theorem_const = state.mk_const_str(theorem.constant_name());
    let theorem_ty = state.infer_type(&goal, &theorem_const)?;
    let mut theorem_meta_ids = Vec::new();
    apply_aux_collect_goals(
        state,
        &goal,
        theorem_const,
        theorem_ty,
        &mut theorem_meta_ids,
    )?;
    let introduced_meta_ids = theorem_meta_ids.clone();

    let side_goals = theorem_meta_ids
        .iter()
        .copied()
        .filter(|meta_id| !state.metas().is_assigned(*meta_id))
        .map(|meta_id| Goal {
            meta_id,
            target: state
                .metas()
                .get(meta_id)
                .map(|meta| state.metas().instantiate(&meta.ty))
                .expect("fresh theorem metavariables must exist"),
            local_ctx: goal.local_ctx.clone(),
            tag: Some("field_simp:ne_zero".to_string()),
        })
        .collect();

    Ok(TheoremApplyResult {
        side_goals,
        introduced_meta_ids,
    })
}

fn apply_aux_collect_goals(
    state: &mut ProofState,
    goal: &Goal,
    func: Expr,
    func_ty: Expr,
    theorem_meta_ids: &mut Vec<MetaId>,
) -> Result<(), TacticError> {
    let func_ty = state.whnf(goal, &func_ty);
    let target = state.metas().instantiate(&goal.target);

    match func_ty.kind() {
        ExprKind::Pi(_bi, domain, codomain) => {
            let arg_meta_id = state.fresh_meta_in_context((**domain).clone(), &goal.local_ctx);
            theorem_meta_ids.push(arg_meta_id);
            let arg_meta = Expr::fvar(MetaState::to_fvar(arg_meta_id));
            let applied = Expr::app(func.clone(), arg_meta.clone());
            let new_ty = codomain.instantiate(&arg_meta);

            let ctx = state.build_local_ctx(goal);
            let unify_result = {
                let (metas, env) = state.metas_and_env();
                Unifier::with_env(metas, env, ctx).unify(&new_ty, &target)
            };
            match unify_result {
                UnifyResult::Success => {
                    state.close_goal(goal, applied)?;
                    Ok(())
                }
                UnifyResult::Failure(_) | UnifyResult::Stuck => {
                    apply_aux_collect_goals(state, goal, applied, new_ty, theorem_meta_ids)
                }
            }
        }
        _ => {
            let ctx = state.build_local_ctx(goal);
            let unify_result = {
                let (metas, env) = state.metas_and_env();
                Unifier::with_env(metas, env, ctx).unify(&func_ty, &target)
            };
            match unify_result {
                UnifyResult::Success => {
                    state.close_goal(goal, func)?;
                    Ok(())
                }
                UnifyResult::Failure(msg) => Err(TacticError::TypeMismatch {
                    expected: format!("{target:?}"),
                    actual: msg,
                }),
                UnifyResult::Stuck => Err(TacticError::UnificationFailed(
                    "field_simp theorem application: unification stuck".to_string(),
                )),
            }
        }
    }
}

fn verify_helper_metas(
    state: &ProofState,
    rhs_meta_id: MetaId,
    introduced_meta_ids: &[MetaId],
    theorem_goal_ids: &[MetaId],
    expected_side_goal_count: usize,
    theorem_name: &str,
) -> Result<(), TacticError> {
    if !state.metas().is_assigned(rhs_meta_id) {
        return Err(TacticError::InvalidTarget {
            tactic: "field_simp".to_string(),
            detail: format!("{theorem_name} left the rewritten target metavariable unresolved"),
        });
    }

    if theorem_goal_ids.len() != expected_side_goal_count {
        return Err(TacticError::InvalidTarget {
            tactic: "field_simp".to_string(),
            detail: format!(
                "{theorem_name} left {} side goal(s); expected {expected_side_goal_count}",
                theorem_goal_ids.len()
            ),
        });
    }

    let hidden_meta_ids: Vec<_> = introduced_meta_ids
        .iter()
        .copied()
        .filter(|meta_id| !state.metas().is_assigned(*meta_id))
        .filter(|meta_id| !theorem_goal_ids.contains(meta_id))
        .collect();
    if !hidden_meta_ids.is_empty() {
        return Err(TacticError::InvalidTarget {
            tactic: "field_simp".to_string(),
            detail: format!(
                "{theorem_name} left hidden unassigned metavariables instead of visible premise goals"
            ),
        });
    }

    for meta_id in theorem_goal_ids {
        let target = state
            .metas()
            .get(*meta_id)
            .map(|meta| state.metas().instantiate(&meta.ty))
            .expect("field_simp theorem goals must exist in MetaState");
        if !is_ne_target(&target) {
            return Err(TacticError::InvalidTarget {
                tactic: "field_simp".to_string(),
                detail: format!("{theorem_name} produced a non-`Ne` premise target: {target:?}"),
            });
        }
    }

    Ok(())
}

fn is_ne_target(target: &Expr) -> bool {
    match target.kind() {
        ExprKind::App(f, _) => match f.kind() {
            ExprKind::App(f, _) => match f.kind() {
                ExprKind::App(f, _) => matches!(
                    f.kind(),
                    ExprKind::Const(name, _) if name.to_string() == "Ne"
                ),
                _ => false,
            },
            _ => false,
        },
        _ => false,
    }
}
