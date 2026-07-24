// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Without loss of generality and assertion utility tactics
//!
//! This module provides tactics for:
//! - `suffices_to_show`: Alias for suffices with clearer semantics
//! - `wlog`: Without loss of generality transformations
//! - `push_neg_at`: Push negations through expressions
//! - `norm_num_at`: Normalize numerals in hypotheses

use std::sync::Arc;

use crate::stack_safe;
use crate::tactic::arith_push_neg::{build_local_hyp_cast, push_neg_expr_with_proof};
use crate::tactic::{
    extract_nat_literal, suffices_, Goal, LocalDecl, ProofState, TacticError, TacticResult,
};
use crate::unify::MetaState;
use clean_kernel::expr::ExprKind;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr};

// ============================================================================
// Additional utility tactics
// ============================================================================

/// `suffices_to_show` - alias for suffices with clearer semantics
/// REQUIRES: `state.goals` is non-empty if `suffices_` is expected to succeed.
/// ENSURES: Equivalent to `suffices_(state, "this", prop, cont)`.
pub fn suffices_to_show(state: &mut ProofState, prop: Expr, cont: Option<Expr>) -> TacticResult {
    suffices_(state, "this", prop, cont)
}

/// Build `Or.rec {P} {¬P} {motive} (fun h => ?pos) (fun h_neg => ?neg) (Classical.em P)`.
///
/// Returns the proof connecting two case-split metavariables via excluded middle.
/// Uses `Or.rec` (not `Or.elim` which doesn't exist in the kernel environment).
///
/// REQUIRES: `assumption`, `neg_assumption`, and `target` are well-formed
/// expressions.
/// ENSURES: Returned proof is rooted at `Or.rec` applied to
/// `Classical.em assumption`.
/// ENSURES: Positive and negative branches abstract `fvar_pos` and `fvar_neg`
/// respectively and fill `meta_pos` / `meta_neg`.
fn build_em_case_split(
    assumption: &Expr,
    neg_assumption: &Expr,
    target: &Expr,
    meta_pos: crate::unify::MetaId,
    meta_neg: crate::unify::MetaId,
    fvar_pos: clean_kernel::FVarId,
    fvar_neg: clean_kernel::FVarId,
) -> Expr {
    let em_app = Expr::app(
        Expr::const_(Name::from_string("Classical.em"), vec![]),
        assumption.clone(),
    );
    let branch_pos = Expr::lam(
        BinderInfo::Default,
        assumption.clone(),
        Expr::fvar(MetaState::to_fvar(meta_pos)).abstract_fvar(fvar_pos),
    );
    let branch_neg = Expr::lam(
        BinderInfo::Default,
        neg_assumption.clone(),
        Expr::fvar(MetaState::to_fvar(meta_neg)).abstract_fvar(fvar_neg),
    );
    // Or.rec has 0 universe params (Prop-valued inductive, elim-only-at-zero).
    // Or.rec {P} {¬P} {motive} branch_pos branch_neg em_p
    let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
    let or_type = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Or"), vec![]),
            assumption.clone(),
        ),
        neg_assumption.clone(),
    );
    let motive = Expr::lam(BinderInfo::Default, or_type, target.clone());
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(or_rec, assumption.clone()),
                        neg_assumption.clone(),
                    ),
                    motive,
                ),
                branch_pos,
            ),
            branch_neg,
        ),
        em_app,
    )
}

/// `wlog` - without loss of generality
///
/// Transforms goal by assuming a symmetric condition holds, creating subgoals
/// to prove the symmetry and the goal under the assumption.
///
/// Constructs `Or.rec (Classical.em assumption) (fun h => ?pos) (fun h_neg => ?neg)`
/// as the proof for the original goal.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok(())`, the original front goal is closed via an excluded
/// middle case split on `assumption`.
/// ENSURES: On `Ok(())`, two new front goals are pushed for the positive and
/// negative cases, with contexts extended by `assumption_name : assumption` and
/// `h_neg_{assumption_name} : assumption -> False` respectively.
/// ENSURES: On `Err(NoGoals)`, `state` is unchanged.
pub fn wlog(state: &mut ProofState, assumption_name: &str, assumption: Expr) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = goal.target.clone();

    // ¬assumption = assumption → False
    let false_type = Expr::const_(Name::from_string("False"), vec![]);
    let neg_assumption = Expr::pi(BinderInfo::Default, assumption.clone(), false_type);

    // ONE shared fvar for the hypothesis of BOTH branches (B104; same
    // binder-scope disease B103 fixed in `abs_cases` and `by_cases`/
    // `split_ite` carry the same cure). The positive and negative branches
    // are PARALLEL binders — each is its own `λ h => …` lambda directly under
    // `Or.rec`, both at binder depth 1. `close_fvars` closes a tactic FVar
    // `n` to a BVar only when `(n - base) < depth`, i.e. it assumes FVar ids
    // grow with binder *nesting* depth. Two distinct fvars would put the
    // second at offset 1 under a depth-1 binder, where the scope check
    // rejects the assignment ("captures out-of-scope local"). Because the
    // branches are disjoint scopes (a goal is solved before the next), both
    // binders can safely share ONE fvar id; each branch body then references
    // offset 0 at depth 1 and closes cleanly. The assembled term is still
    // kernel-rechecked by add_decl.
    let fvar_h = state.fresh_fvar();
    let fvar_pos = fvar_h;
    let fvar_neg = fvar_h;

    // Contexts with the assumption hypothesis added
    let mut ctx_pos = goal.local_ctx.clone();
    ctx_pos.push(LocalDecl {
        fvar: fvar_pos,
        name: assumption_name.to_string(),
        ty: assumption.clone(),
        value: None,
    });
    let mut ctx_neg = goal.local_ctx.clone();
    ctx_neg.push(LocalDecl {
        fvar: fvar_neg,
        name: format!("h_neg_{assumption_name}"),
        ty: neg_assumption.clone(),
        value: None,
    });

    let meta_pos = state.fresh_meta_in_context(target.clone(), &ctx_pos);
    let meta_neg = state.fresh_meta_in_context(target.clone(), &ctx_neg);

    let proof = build_em_case_split(
        &assumption,
        &neg_assumption,
        &target,
        meta_pos,
        meta_neg,
        fvar_pos,
        fvar_neg,
    );

    // Part of #2154: migrated from close_goal_unchecked via Or.elim → Or.rec fix.
    state.close_goal(&goal, proof)?;

    state.goals.push_front(Goal {
        meta_id: meta_neg,
        target: target.clone(),
        local_ctx: ctx_neg,
        tag: None,
    });
    state.goals.push_front(Goal {
        meta_id: meta_pos,
        target,
        local_ctx: ctx_pos,
        tag: None,
    });

    Ok(())
}

/// `push_neg_at` - push negations at a specific hypothesis
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: `hyp_name` names a local hypothesis in the current goal if
/// `Ok(())` is expected.
/// ENSURES: On `Ok(())`, the named hypothesis type is replaced via the
/// proof-carrying `replace_local_decl_with_cast` boundary.
/// ENSURES: On `Ok(())`, the goal target is unchanged.
/// ENSURES: On `Err(NoGoals)` or `Err(HypothesisNotFound)`, `state` is
/// unchanged.
pub fn push_neg_at(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    let hyp_decl = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?
        .clone();

    let result = push_neg_expr_with_proof(state, &goal, &hyp_decl.ty)?;

    if result.expr == hyp_decl.ty {
        let legacy_expr = push_negations_in_expr(&hyp_decl.ty);
        if legacy_expr == hyp_decl.ty {
            return Ok(());
        }
        return Err(TacticError::TypeCheckFailed(
            "push_neg_at: proof-carry rewrite left the hypothesis unchanged but legacy push_neg would rewrite it".into(),
        ));
    }

    let eq_proof = result.proof.ok_or_else(|| {
        TacticError::TypeCheckFailed(
            "push_neg_at: rewrite changed the type but produced no equality proof".into(),
        )
    })?;

    let hyp_cast = build_local_hyp_cast(
        state,
        &goal,
        &hyp_decl.ty,
        &result.expr,
        eq_proof,
        hyp_decl.fvar,
    )?;
    state.replace_local_decl_with_cast(hyp_decl.fvar, result.expr, hyp_cast)
}

/// Push ¬ through a binary connective: ¬(P op Q) → (¬P) result_op (¬Q)
/// REQUIRES: `args.len() == 1` and `args[0]` is the body of the surrounding
/// `Not` application.
/// ENSURES: Returns `Some` only when the inner expression is a binary
/// application of `connective`.
/// ENSURES: On `Some`, both operands are recursively negated and combined under
/// `result_connective`.
/// ENSURES: Returns `None` for all other shapes.
#[cfg_attr(not(test), allow(dead_code))]
fn push_neg_binary(args: &[&Expr], connective: &str, result_connective: &str) -> Option<Expr> {
    let inner = args[0];
    let inner_head = inner.get_app_fn();
    if let ExprKind::Const(inner_name, _) = inner_head.kind() {
        if inner_name.to_string() == connective {
            let inner_args = inner.get_app_args();
            if inner_args.len() == 2 {
                let not = || Expr::const_(Name::from_string("Not"), vec![]);
                let neg_p = Expr::app(not(), push_negations_in_expr(inner_args[0]));
                let neg_q = Expr::app(not(), push_negations_in_expr(inner_args[1]));
                let result_op = Expr::const_(Name::from_string(result_connective), vec![]);
                return Some(Expr::app(Expr::app(result_op, neg_p), neg_q));
            }
        }
    }
    None
}

/// Push negations through an expression
/// REQUIRES: `expr` is a well-formed kernel expression.
/// ENSURES: Double-negation elimination and De Morgan rewrites are applied
/// recursively where the recognized `Not`/`And`/`Or` patterns appear.
/// ENSURES: Non-matching nodes are rebuilt with recursively rewritten children
/// or cloned unchanged when atomic.
/// ENSURES: Recursive descent runs under `stack_safe`.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn push_negations_in_expr(expr: &Expr) -> Expr {
    stack_safe(|| {
        let head = expr.get_app_fn();
        let args = expr.get_app_args();

        if let ExprKind::Const(name, _) = head.kind() {
            if name.to_string() == "Not" && args.len() == 1 {
                // ¬¬P → P
                let inner = args[0];
                let inner_head = inner.get_app_fn();
                if let ExprKind::Const(inner_name, _) = inner_head.kind() {
                    if inner_name.to_string() == "Not" {
                        let inner_args = inner.get_app_args();
                        if inner_args.len() == 1 {
                            return push_negations_in_expr(inner_args[0]);
                        }
                    }
                }
                // ¬(P ∧ Q) → ¬P ∨ ¬Q
                if let Some(result) = push_neg_binary(&args, "And", "Or") {
                    return result;
                }
                // ¬(P ∨ Q) → ¬P ∧ ¬Q
                if let Some(result) = push_neg_binary(&args, "Or", "And") {
                    return result;
                }
            }
        }

        // Recurse into structure
        match expr.kind() {
            ExprKind::App(f, a) => Expr::app(push_negations_in_expr(f), push_negations_in_expr(a)),
            ExprKind::Lam(bi, ty, body) => Expr::lam(
                *bi,
                push_negations_in_expr(ty),
                push_negations_in_expr(body),
            ),
            ExprKind::Pi(bi, ty, body) => Expr::pi(
                *bi,
                push_negations_in_expr(ty),
                push_negations_in_expr(body),
            ),
            ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
                name.clone(),
                push_negations_in_expr(ty),
                push_negations_in_expr(val),
                push_negations_in_expr(body),
                *non_dep,
            ),
            ExprKind::Proj(name, idx, inner) => {
                Expr::proj(name.clone(), *idx, push_negations_in_expr(inner))
            }
            ExprKind::MData(md, inner) => Expr::mdata(md.clone(), push_negations_in_expr(inner)),
            ExprKind::Squash(inner) => {
                Expr::from_kind(ExprKind::Squash(Arc::new(push_negations_in_expr(inner))))
            }
            _ => expr.clone(),
        }
    })
}

/// `norm_num_at` - normalize numerals at a hypothesis
/// REQUIRES: `state.goals` is non-empty.
/// REQUIRES: `hyp_name` names a local hypothesis in the current goal if
/// `Ok(())` is expected.
/// ENSURES: On `Ok(())`, the named hypothesis type is replaced by
/// `normalize_numerals` of its previous type.
/// ENSURES: On `Ok(())`, the goal target is unchanged.
/// ENSURES: On `Err(NoGoals)` or `Err(HypothesisNotFound)`, `state` is
/// unchanged.
pub fn norm_num_at(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let hyp_decl = goal
        .local_ctx
        .iter()
        .find(|d| d.name == hyp_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;
    let hyp_fvar = hyp_decl.fvar;
    let hyp_ty = hyp_decl.ty.clone();

    // Normalize numerals in the hypothesis type
    let new_ty = normalize_numerals(&hyp_ty);

    state.replace_local_decl_def_eq(hyp_fvar, new_ty)
}

/// Normalize numeral expressions
/// REQUIRES: `expr` is a well-formed kernel expression.
/// ENSURES: Recognized literal `add`, `mul`, and `sub` applications are folded
/// into `Nat` literals, with subtraction using saturating semantics.
/// ENSURES: Unsupported operators and non-arithmetic shapes are rebuilt with
/// recursively normalized children or cloned unchanged when atomic.
/// ENSURES: Recursive descent runs under `stack_safe`.
pub(crate) fn normalize_numerals(expr: &Expr) -> Expr {
    stack_safe(|| match expr.kind() {
        // Try to evaluate arithmetic
        ExprKind::App(f, arg) => {
            let f_norm = normalize_numerals(f);
            let arg_norm = normalize_numerals(arg);

            // Check for binary operations on literals
            if let ExprKind::App(f2, arg1) = f_norm.kind() {
                if let ExprKind::Const(op, _) = f2.kind() {
                    let op_str = op.to_string();
                    if let (Some(n1), Some(n2)) =
                        (extract_nat_literal(arg1), extract_nat_literal(&arg_norm))
                    {
                        if op_str.contains("add") || op_str.contains("Add") {
                            return Expr::nat_lit((n1 + n2) as u64);
                        }
                        if op_str.contains("mul") || op_str.contains("Mul") {
                            return Expr::nat_lit((n1 * n2) as u64);
                        }
                        if op_str.contains("sub") || op_str.contains("Sub") {
                            return Expr::nat_lit(n1.saturating_sub(n2) as u64);
                        }
                    }
                }
            }

            Expr::app(f_norm, arg_norm)
        }
        ExprKind::Lam(bi, ty, body) => {
            Expr::lam(*bi, normalize_numerals(ty), normalize_numerals(body))
        }
        ExprKind::Pi(bi, ty, body) => {
            Expr::pi(*bi, normalize_numerals(ty), normalize_numerals(body))
        }
        ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
            name.clone(),
            normalize_numerals(ty),
            normalize_numerals(val),
            normalize_numerals(body),
            *non_dep,
        ),
        ExprKind::Proj(name, idx, inner) => {
            Expr::proj(name.clone(), *idx, normalize_numerals(inner))
        }
        ExprKind::MData(md, inner) => Expr::mdata(md.clone(), normalize_numerals(inner)),
        ExprKind::Squash(inner) => {
            Expr::from_kind(ExprKind::Squash(Arc::new(normalize_numerals(inner))))
        }
        _ => expr.clone(),
    })
}
