// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! N-ary `conv => congr` recombination fold (#2477 Phase 4).
//!
//! Folds per-focus equalities (one per head + argument) up the LEFT-NESTED
//! application spine into ONE candidate proof of the whole-application
//! equality `f a1 .. an = f' a1' .. an'`. The candidate is NOT trusted: the
//! caller hands it to `replace_target_eq`, which kernel-type-checks it against
//! `@Eq T old new` before any goal mutation (INV-4). The non-dependent
//! `mk_congr`/`mk_congr_fun`/`mk_congr_arg` family means a genuinely dependent
//! head merely FAILS that check (safe refusal), never miscertifies.
//!
//! Soundness invariants (see design):
//! - INV-1 positional fidelity: foci are consumed strictly in SOURCE order and
//!   the left-fold spine mirrors the kernel `App` nesting exactly.
//! - INV-2 no dropped/extra arg: every head + arg focus contributes exactly one
//!   equality; a never-touched focus uses `Eq.refl`.
//! - INV-3 right expr per sub-eq: each focus's `before`/`after` come from the
//!   decomposed application; a rewrite only mutates `after` of that focus.
//! - INV-5 refl is real: untouched foci use `mk_eq_refl` (foundational only).

use clean_kernel::tc::whnf_proof::{CongrArgArgs, EqProofBuilder};
use clean_kernel::{Expr, Level};

use super::conv_proof::infer_sort_level;
use super::core::ConvFocus;
use super::{Goal, ProofState, TacticError};

/// The resolved equality for one focus: `(before, after, eq_proof)`.
///
/// `eq_proof = None` means `before == after` (refl synthesized lazily so we
/// only pay for `Eq.refl` when a slot actually participates in a congr layer).
struct FocusEq {
    before: Expr,
    after: Expr,
    /// `Some(h : before = after)`, or `None` for an untouched (refl) focus.
    proof: Option<Expr>,
    /// Cached kernel type of `before` (== type of `after`).
    ty: Expr,
}

/// Recombine a single focus into its `before = after` equality.
///
/// If the focus was congr'd (has children), recursively recombine the child
/// tree first (the child's `original` is this focus's `before`). Otherwise use
/// the recorded `eq_proof` (or `None` for refl).
fn resolve_focus(
    state: &ProofState,
    goal: &Goal,
    focus: &ConvFocus,
) -> Result<FocusEq, TacticError> {
    if !focus.children.is_empty() {
        // Nested congr: the child fold proves `before = after` for this node.
        let (head, args) = focus
            .children
            .split_first()
            .ok_or_else(|| TacticError::TypeCheckFailed("conv congr: empty child focus".into()))?;
        let new_app = rebuild_app(args, head);
        let proof = recombine_foci(state, goal, &focus.before, head, args)?;
        return Ok(FocusEq {
            before: focus.before.clone(),
            after: new_app,
            proof,
            ty: focus.ty.clone(),
        });
    }
    Ok(FocusEq {
        before: focus.before.clone(),
        after: focus.after.clone(),
        proof: focus.eq_proof.clone(),
        ty: focus.ty.clone(),
    })
}

/// Rebuild the application `head.after a1.after .. an.after` (left-nested).
pub(crate) fn rebuild_app(args: &[ConvFocus], head: &ConvFocus) -> Expr {
    let mut acc = focus_after(head);
    for a in args {
        acc = Expr::app(acc, focus_after(a));
    }
    acc
}

/// The `after` expression for a focus, recursively rebuilding nested congr's.
fn focus_after(focus: &ConvFocus) -> Expr {
    if focus.children.is_empty() {
        return focus.after.clone();
    }
    let Some((head, args)) = focus.children.split_first() else {
        return focus.after.clone();
    };
    rebuild_app(args, head)
}

/// Fold per-focus equalities up the left-nested spine of `f a1 .. an`.
///
/// Returns `Ok(Some(proof))` where `proof : original = (f' a1' .. an')`, or
/// `Ok(None)` when nothing changed (caller takes the def-eq / refl path).
pub(crate) fn recombine_foci(
    state: &ProofState,
    goal: &Goal,
    original: &Expr,
    head: &ConvFocus,
    args: &[ConvFocus],
) -> Result<Option<Expr>, TacticError> {
    let head_eq = resolve_focus(state, goal, head)?;
    let arg_eqs: Vec<FocusEq> = args
        .iter()
        .map(|a| resolve_focus(state, goal, a))
        .collect::<Result<_, _>>()?;

    // Nothing changed anywhere: refl path (caller uses def-eq).
    let any_change = head_eq.proof.is_some() || arg_eqs.iter().any(|e| e.proof.is_some());
    if !any_change {
        return Ok(None);
    }

    // Running spine proof `e_{k-1} : P_{k-1} = P'_{k-1}` and the carried
    // before/after prefixes. `prefix_proof = None` means the prefix is
    // unchanged so far (refl), letting us pick the cheapest congr arm.
    let mut prefix_before = head_eq.before.clone();
    let mut prefix_after = head_eq.after.clone();
    let mut prefix_proof = head_eq.proof.clone();

    for arg in &arg_eqs {
        let alpha = arg.ty.clone();
        // β_k = type of `prefix_before arg.before` = type of P_k.
        let pk_before = Expr::app(prefix_before.clone(), arg.before.clone());
        let beta = state.infer_type(goal, &pk_before)?;

        let u = infer_sort_level(
            state,
            goal,
            &alpha,
            "conv congr: cannot infer argument-type universe",
        )?;
        let v = infer_sort_level(
            state,
            goal,
            &beta,
            "conv congr: cannot infer result-type universe",
        )?;

        let next_proof = combine_step(CombineStep {
            u,
            v,
            alpha,
            beta,
            prefix_before: &prefix_before,
            prefix_after: &prefix_after,
            prefix_proof: prefix_proof.as_ref(),
            arg,
        })?;

        prefix_before = Expr::app(prefix_before, arg.before.clone());
        prefix_after = Expr::app(prefix_after, arg.after.clone());
        prefix_proof = next_proof;
    }

    // `prefix_before` reconstructs the original left-nested application from the
    // foci; it must equal the captured `original` (INV-1 positional fidelity).
    if prefix_before != *original {
        return Err(TacticError::TypeCheckFailed(
            "conv congr: recombined LHS does not match the original application (INV-1)".into(),
        ));
    }
    let proof = prefix_proof.ok_or_else(|| {
        TacticError::TypeCheckFailed("conv congr: recombination produced no proof".into())
    })?;
    Ok(Some(proof))
}

struct CombineStep<'a> {
    u: Level,
    v: Level,
    alpha: Expr,
    beta: Expr,
    prefix_before: &'a Expr,
    prefix_after: &'a Expr,
    prefix_proof: Option<&'a Expr>,
    arg: &'a FocusEq,
}

/// One left-fold step: combine the running prefix eq with the current arg eq.
///
/// Picks the cheapest sound congr arm:
/// - both unchanged: carry refl (`None`).
/// - only arg changed: `congrArg` (prefix fixed).
/// - only prefix changed: `congrFun'` (arg fixed).
/// - both changed: `congr`.
fn combine_step(step: CombineStep<'_>) -> Result<Option<Expr>, TacticError> {
    let arg_changed = step.arg.proof.is_some();
    let prefix_changed = step.prefix_proof.is_some();

    match (prefix_changed, arg_changed) {
        (false, false) => Ok(None),
        (false, true) => {
            // congrArg f h_arg : f a = f a'  (prefix `f` fixed).
            let h_arg = step.arg.proof.clone().ok_or_else(arg_proof_missing)?;
            let f = step.prefix_before.clone();
            Ok(Some(EqProofBuilder::mk_congr_arg(CongrArgArgs {
                u: step.u,
                v: step.v,
                alpha: step.alpha,
                beta: step.beta,
                a1: step.arg.before.clone(),
                a2: step.arg.after.clone(),
                f,
                h: h_arg,
            })))
        }
        (true, false) => {
            // congrFun' h_prefix a : f a = f' a  (arg `a` fixed).
            let h_prefix = step
                .prefix_proof
                .cloned()
                .ok_or_else(prefix_proof_missing)?;
            Ok(Some(EqProofBuilder::mk_congr_fun(
                step.u,
                step.v,
                step.alpha,
                step.beta,
                step.prefix_before.clone(),
                step.prefix_after.clone(),
                h_prefix,
                step.arg.before.clone(),
            )))
        }
        (true, true) => {
            // congr h_prefix h_arg : f a = f' a'.
            let h_prefix = step
                .prefix_proof
                .cloned()
                .ok_or_else(prefix_proof_missing)?;
            let h_arg = step.arg.proof.clone().ok_or_else(arg_proof_missing)?;
            Ok(Some(EqProofBuilder::mk_congr(
                step.u,
                step.v,
                step.alpha,
                step.beta,
                step.prefix_before.clone(),
                step.prefix_after.clone(),
                step.arg.before.clone(),
                step.arg.after.clone(),
                h_prefix,
                h_arg,
            )))
        }
    }
}

fn arg_proof_missing() -> TacticError {
    TacticError::TypeCheckFailed("conv congr: missing argument equality proof".into())
}

fn prefix_proof_missing() -> TacticError {
    TacticError::TypeCheckFailed("conv congr: missing prefix equality proof".into())
}
