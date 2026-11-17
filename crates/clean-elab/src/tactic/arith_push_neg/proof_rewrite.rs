// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId};

use super::super::simp::{mk_congr, mk_congr_arg, mk_congr_fun, mk_funext};
use super::super::{Goal, ProofState, TacticError};
use super::proof_rules::{
    mk_nat_not_ge_eq, mk_nat_not_gt_eq, mk_nat_not_le_eq, mk_nat_not_lt_eq, mk_not_and_eq,
    mk_not_exists_eq, mk_not_forall_eq, mk_not_imp_eq, mk_not_not_eq, mk_not_or_eq,
};
use super::proof_utils::{
    compose_rewrite_steps, is_nat_type, mk_by_contradiction, mk_iff_intro, mk_lambda,
    mk_prop_eq_from_iff, require_consts, PropRewriteResult,
};
use super::{
    is_prop, is_raw_nat_rel, make_and, make_forall_push_neg, make_not, make_or, match_and,
    match_exists_push_neg, match_ge, match_gt, match_le_any, match_lt_any, match_not_head,
    match_or, nat_le_raw, nat_lt_raw,
};

fn lift_wrapper_rewrite_with_congr_arg<F>(
    state: &ProofState,
    goal: &Goal,
    inner: &Expr,
    inner_result: PropRewriteResult,
    wrap: F,
    failure_context: &'static str,
) -> Result<PropRewriteResult, TacticError>
where
    F: Fn(Expr) -> Expr,
{
    let PropRewriteResult {
        expr: rewritten_inner,
        proof: inner_proof,
    } = inner_result;
    let wrapped_expr = wrap(rewritten_inner.clone());
    let proof = match inner_proof.as_ref() {
        Some(inner_proof) => {
            let inner_ty = state.infer_type(goal, inner)?;
            let wrap_fn = Expr::lam(BinderInfo::Default, inner_ty, wrap(Expr::bvar(0)));
            Some(
                mk_congr_arg(state, goal, &wrap_fn, inner, &rewritten_inner, inner_proof)
                    .ok_or_else(|| TacticError::TypeCheckFailed(failure_context.into()))?,
            )
        }
        None => None,
    };
    Ok(PropRewriteResult {
        expr: wrapped_expr,
        proof,
    })
}

/// Mathlib's `isProp ty`: the binder type is itself a proposition (its type
/// is `Prop`), not the sort `Prop`.
/// REQUIRES: `dom` is a binder type in `goal`'s context.
/// ENSURES: `Err` when `dom`'s type cannot be inferred there (a binder bound
/// outside it), so a negation is never classified by a guess.
fn binder_is_proposition(state: &ProofState, goal: &Goal, dom: &Expr) -> Result<bool, TacticError> {
    if dom.has_loose_bvars() {
        return Err(TacticError::TypeCheckFailed(
            "push_neg: cannot classify a binder type that mentions an enclosing binder".into(),
        ));
    }
    let sort = state.infer_type(goal, dom)?;
    Ok(matches!(state.whnf(goal, &sort).kind(), ExprKind::Sort(level) if level.is_zero()))
}

fn rewrite_not_head_with_proof(
    state: &mut ProofState,
    goal: &Goal,
    expr: &Expr,
) -> Result<Option<PropRewriteResult>, TacticError> {
    // Mathlib's `push_neg` reads only the `Not` head, at the top and for the
    // double negation: `P → False` is not pushed, and `¬(P → False)` is the
    // implication row (`P ∧ ¬False`), not `P`.
    let Some(inner) = match_not_head(expr) else {
        return Ok(None);
    };

    if let Some(inner_inner) = match_not_head(&inner) {
        return Ok(Some(super::proof_utils::mk_prop_rewrite_result(
            inner_inner.clone(),
            mk_not_not_eq(state, &inner_inner)?,
        )));
    }

    if let Some((p, q)) = match_and(&inner) {
        let new_expr = make_or(&make_not(&p), &make_not(&q));
        return Ok(Some(super::proof_utils::mk_prop_rewrite_result(
            new_expr,
            mk_not_and_eq(state, &p, &q)?,
        )));
    }

    if let Some((p, q)) = match_or(&inner) {
        let new_expr = make_and(&make_not(&p), &make_not(&q));
        return Ok(Some(super::proof_utils::mk_prop_rewrite_result(
            new_expr,
            mk_not_or_eq(state, &p, &q)?,
        )));
    }

    // `¬∀`: Mathlib's `forallE` row. `¬(P → Q)` becomes `P ∧ ¬Q`
    // (`not_implies_eq`) exactly when the binder type is a PROPOSITION and the
    // body does not mention the bound variable (`isProp ty &&
    // !body.hasLooseBVars`); every other binder, a proof-dependent one
    // included, is `∃ x, ¬P x` (`not_forall_eq`).
    if let ExprKind::Pi(_, dom, cod) = inner.kind() {
        if binder_is_proposition(state, goal, dom)? && !cod.has_loose_bvar(0) {
            if cod.has_loose_bvars() {
                return Err(TacticError::TypeCheckFailed(
                    "push_neg: cannot split an implication whose conclusion mentions an enclosing binder".into(),
                ));
            }
            let q = (**cod).clone();
            let p = (**dom).clone();
            let new_expr = make_and(&p, &make_not(&q));
            return Ok(Some(super::proof_utils::mk_prop_rewrite_result(
                new_expr,
                mk_not_imp_eq(state, &p, &q)?,
            )));
        }
        let binder_ty = (**dom).clone();
        let body = (**cod).clone();
        let new_expr =
            super::proof_utils::mk_exists_prop(state, goal, &binder_ty, &make_not(&body))?;
        return Ok(Some(super::proof_utils::mk_prop_rewrite_result(
            new_expr,
            mk_not_forall_eq(state, goal, &binder_ty, &body)?,
        )));
    }

    if let Some((binder_ty, body)) = match_exists_push_neg(&inner) {
        let new_expr = make_forall_push_neg(&binder_ty, &make_not(&body));
        return Ok(Some(super::proof_utils::mk_prop_rewrite_result(
            new_expr,
            mk_not_exists_eq(state, goal, &binder_ty, &body)?,
        )));
    }

    // `¬(a ≤ b)` → `b < a` (Nat), in EITHER spelling: the `LE.le` typeclass
    // spine or the raw `Nat.le a b` constant application. `raw` is threaded
    // into the rule so both sides of the emitted `Eq` keep the spelling the
    // hypothesis / goal actually had — the rewrite is sound either way (the two
    // are definitionally equal), but a raw result matches a raw goal
    // SYNTACTICALLY, which is what the downstream solver and `close_goal` want.
    if let Some((ty, lhs, rhs)) = match_le_any(&inner) {
        if is_nat_type(&ty) {
            let raw = is_raw_nat_rel(&inner);
            let new = if raw {
                nat_lt_raw(rhs.clone(), lhs.clone())
            } else {
                super::super::tc_app::nat_lt_tc(rhs.clone(), lhs.clone())
            };
            return Ok(Some(super::proof_utils::mk_prop_rewrite_result(
                new,
                mk_nat_not_le_eq(state, &lhs, &rhs, raw)?,
            )));
        }
    }

    if let Some((ty, lhs, rhs)) = match_lt_any(&inner) {
        if is_nat_type(&ty) {
            let raw = is_raw_nat_rel(&inner);
            let new = if raw {
                nat_le_raw(rhs.clone(), lhs.clone())
            } else {
                super::super::tc_app::nat_le_tc(rhs.clone(), lhs.clone())
            };
            return Ok(Some(super::proof_utils::mk_prop_rewrite_result(
                new,
                mk_nat_not_lt_eq(state, &lhs, &rhs, raw)?,
            )));
        }
    }

    // `¬(a ≥ b)` → `a < b` (Nat). `a ≥ b` ≡ `b ≤ a`, so this reuses `Nat.not_le`.
    if let Some((ty, lhs, rhs)) = match_ge(&inner) {
        if is_nat_type(&ty) {
            return Ok(Some(super::proof_utils::mk_prop_rewrite_result(
                super::super::tc_app::nat_lt_tc(lhs.clone(), rhs.clone()),
                mk_nat_not_ge_eq(state, &lhs, &rhs)?,
            )));
        }
    }

    // `¬(a > b)` → `a ≤ b` (Nat). `a > b` ≡ `b < a`, so this reuses `Nat.not_lt`.
    if let Some((ty, lhs, rhs)) = match_gt(&inner) {
        if is_nat_type(&ty) {
            return Ok(Some(super::proof_utils::mk_prop_rewrite_result(
                super::super::tc_app::nat_le_tc(lhs.clone(), rhs.clone()),
                mk_nat_not_gt_eq(state, &lhs, &rhs)?,
            )));
        }
    }

    Ok(None)
}

pub(crate) fn push_neg_expr_with_proof(
    state: &mut ProofState,
    goal: &Goal,
    expr: &Expr,
) -> Result<PropRewriteResult, TacticError> {
    if let Some(step) = rewrite_not_head_with_proof(state, goal, expr)? {
        let recursive = push_neg_expr_with_proof(state, goal, &step.expr)?;
        return compose_rewrite_steps(state, goal, step, recursive);
    }

    match expr.kind() {
        ExprKind::Lam(bi, ty, body) => {
            let body_result = push_neg_expr_with_proof(state, goal, body)?;
            if body_result.expr != **body {
                let proof = match body_result.proof.as_ref() {
                    Some(body_proof) => Some(
                        mk_funext(state, goal, ty, body, &body_result.expr, body_proof)
                            .ok_or_else(|| {
                                TacticError::TypeCheckFailed(
                                    "push_neg: failed to lift lambda-body rewrite with funext"
                                        .into(),
                                )
                            })?,
                    ),
                    None => None,
                };
                return Ok(PropRewriteResult {
                    expr: Expr::lam(*bi, (**ty).clone(), body_result.expr),
                    proof,
                });
            }
        }
        ExprKind::Pi(bi, dom, cod) if !is_prop(dom) => {
            let body_result = push_neg_expr_with_proof(state, goal, cod)?;
            if body_result.expr != **cod {
                let proof = match body_result.proof.as_ref() {
                    Some(body_proof) => Some(super::proof_utils::mk_push_neg_forall_congr(
                        state,
                        dom,
                        cod,
                        &body_result.expr,
                        body_proof,
                    )?),
                    None => None,
                };
                return Ok(PropRewriteResult {
                    expr: Expr::pi(*bi, (**dom).clone(), body_result.expr),
                    proof,
                });
            }
        }
        ExprKind::Proj(name, idx, inner) => {
            let inner_result = push_neg_expr_with_proof(state, goal, inner)?;
            if inner_result.expr != **inner {
                return lift_wrapper_rewrite_with_congr_arg(
                    state,
                    goal,
                    inner,
                    inner_result,
                    |rewritten_inner| Expr::proj(name.clone(), *idx, rewritten_inner),
                    "push_neg: failed to lift projection rewrite with congrArg",
                );
            }
        }
        ExprKind::MData(md, inner) => {
            let inner_result = push_neg_expr_with_proof(state, goal, inner)?;
            if inner_result.expr != **inner {
                return lift_wrapper_rewrite_with_congr_arg(
                    state,
                    goal,
                    inner,
                    inner_result,
                    |rewritten_inner| Expr::mdata(md.clone(), rewritten_inner),
                    "push_neg: failed to lift metadata rewrite with congrArg",
                );
            }
        }
        ExprKind::Squash(inner) => {
            let inner_result = push_neg_expr_with_proof(state, goal, inner)?;
            if inner_result.expr != **inner {
                return lift_wrapper_rewrite_with_congr_arg(
                    state,
                    goal,
                    inner,
                    inner_result,
                    |rewritten_inner| {
                        Expr::from_kind(ExprKind::Squash(std::sync::Arc::new(rewritten_inner)))
                    },
                    "push_neg: failed to lift squash rewrite with congrArg",
                );
            }
        }
        ExprKind::App(f, arg) => {
            let f_result = push_neg_expr_with_proof(state, goal, f)?;
            let arg_result = push_neg_expr_with_proof(state, goal, arg)?;
            if f_result.expr != **f || arg_result.expr != **arg {
                let proof = match (f_result.proof.as_ref(), arg_result.proof.as_ref()) {
                    (Some(hf), Some(ha)) => Some(
                        mk_congr(
                            state,
                            goal,
                            f,
                            &f_result.expr,
                            arg,
                            &arg_result.expr,
                            hf,
                            ha,
                        )
                        .ok_or_else(|| {
                            TacticError::TypeCheckFailed(
                                "push_neg: failed to lift App rewrite with congr".into(),
                            )
                        })?,
                    ),
                    (Some(hf), None) => Some(
                        mk_congr_fun(state, goal, f, &f_result.expr, arg, hf).ok_or_else(|| {
                            TacticError::TypeCheckFailed(
                                "push_neg: failed to lift function rewrite with congrFun".into(),
                            )
                        })?,
                    ),
                    (None, Some(ha)) => Some(
                        mk_congr_arg(state, goal, f, arg, &arg_result.expr, ha).ok_or_else(
                            || {
                                TacticError::TypeCheckFailed(
                                    "push_neg: failed to lift argument rewrite with congrArg"
                                        .into(),
                                )
                            },
                        )?,
                    ),
                    (None, None) => None,
                };
                return Ok(PropRewriteResult {
                    expr: Expr::app(f_result.expr, arg_result.expr),
                    proof,
                });
            }
        }
        _ => {}
    }

    Ok(PropRewriteResult {
        expr: expr.clone(),
        proof: None,
    })
}

pub(super) fn contrapose_with_proof(
    state: &mut ProofState,
    target: &Expr,
) -> Result<(Expr, Expr), TacticError> {
    let ExprKind::Pi(bi, dom, cod) = target.kind() else {
        return Err(TacticError::GoalMismatch(
            "contrapose: goal is not an implication".to_string(),
        ));
    };

    require_consts(
        state,
        &[
            "Classical.byContradiction",
            "False.elim",
            "Iff.intro",
            "Iff.mp",
            "Iff.mpr",
            "propext",
        ],
    )?;

    // `¬Q → ¬P`, both negations with the `Not` head as Mathlib's
    // `contrapose` states them; simp reads a negation off that head only.
    let not_cod = make_not(cod);
    let contrapositive = Expr::pi(*bi, not_cod.clone(), make_not(dom));
    let old_target = target.clone();

    let forward = mk_lambda(state, &old_target, |state, hpq| {
        mk_lambda(state, &not_cod, |state, hnot_q| {
            mk_lambda(state, dom, |_, hp| {
                Expr::app(hnot_q.clone(), Expr::app(hpq.clone(), hp))
            })
        })
    });

    let reverse_target = contrapositive.clone();
    let backward = mk_lambda(state, &reverse_target, |state, hcontra| {
        mk_lambda(state, dom, |state, hp| {
            mk_by_contradiction(state, cod, |_, hnot_q| {
                let not_p_proof = Expr::app(hcontra.clone(), hnot_q);
                Expr::app(not_p_proof, hp.clone())
            })
        })
    });

    let eq_proof = mk_prop_eq_from_iff(
        &old_target,
        &contrapositive,
        mk_iff_intro(&old_target, &contrapositive, forward, backward),
    );
    Ok((contrapositive, eq_proof))
}

pub(crate) fn build_local_hyp_cast(
    state: &ProofState,
    goal: &Goal,
    old_ty: &Expr,
    new_ty: &Expr,
    eq_proof: Expr,
    hyp_fvar: FVarId,
) -> Result<Expr, TacticError> {
    let alpha = state.infer_type(goal, old_ty)?;
    let sort_level = state
        .infer_type(goal, &alpha)
        .ok()
        .and_then(|sort| match sort.kind() {
            ExprKind::Sort(level) => Some(level.clone()),
            _ => None,
        })
        .ok_or_else(|| {
            TacticError::TypeCheckFailed(
                "contrapose_hyp: cannot infer Eq.subst universe for hypothesis cast".into(),
            )
        })?;
    let eq_subst = Expr::const_(Name::from_string("Eq.subst"), vec![sort_level]);
    let cast = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(eq_subst, alpha.clone()),
                    Expr::lam(BinderInfo::Default, alpha, Expr::bvar(0)),
                ),
                old_ty.clone(),
            ),
            new_ty.clone(),
        ),
        eq_proof,
    );
    Ok(Expr::app(cast, Expr::fvar(hyp_fvar)))
}
