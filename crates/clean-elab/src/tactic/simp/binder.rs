// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Binder opening for the simp traversal.
//!
//! # Why simp must open binders
//!
//! Every proof term simp builds for a rewrite (`mk_congr_arg`, `mk_congr_fun`,
//! `mk_congr`, `mk_funext`, `mk_forall_congr`, `mk_pi_domain_congr`,
//! `mk_eq_trans_expr`) needs the *type* of the subterm it is rewriting, and it
//! gets that type from `ProofState::infer_type`, which routes to the kernel
//! type checker.
//!
//! The kernel cannot infer the type of a term with LOOSE bound variables. So
//! while simp descended into a binder by handing the raw
//! `ExprKind::Lam(_, ty, body)` payload straight to the recursion, every
//! subterm mentioning an ENCLOSING binder was an open term, every
//! `infer_type` on it failed, and every congruence builder returned `None`.
//!
//! That never produced a WRONG proof — the callers all fail closed — but it
//! did lose a real one: `simp` recorded `made_progress = true` with
//! `accumulated_proof = None`, which asserts "the change was definitional",
//! and `ProofState::replace_target_def_eq` then rejected the rewritten target.
//! Mathlib source elaboration saw that as `Tactic failed: goal mismatch:
//! replace_target_def_eq: new target is not definitionally equal to current
//! target`.
//!
//! The fix is the standard telescope discipline: open the binder with a fresh
//! free variable declared in an extended local context, recurse on the now
//! closed body, then abstract that free variable back out of BOTH the
//! rewritten body and its proof. `Expr::abstract_fvar` is the exact inverse of
//! `Expr::instantiate` on a fresh id (kernel contract, `expr/subst.rs`), so
//! the round trip reconstructs the original de Bruijn shape.

use std::sync::atomic::{AtomicU64, Ordering};

use clean_kernel::{Expr, FVarId};

use crate::tactic::core::{Goal, LocalDecl};

/// Highest id a simp binder temporary may take.
///
/// `MetaState` tags metavariables by SETTING BIT 63 of the `FVarId`
/// (`META_FVAR_TAG = 1 << 63`, `unify/meta_state/mod.rs`), so every id at or
/// above `1 << 63` already denotes a metavariable and pushing one into a
/// `LocalContext` collides with a live meta — `LocalContext::push_with_id`
/// panics on exactly that ("active duplicate FVarId"). Simp binder temporaries
/// therefore live strictly BELOW the tag, counting DOWN from its predecessor,
/// while the elaborator (`ElabCtx::fresh_fvar`) and the tactic layer
/// (`ProofState::fresh_fvar`) count UP from small ids. The two ends cannot meet
/// short of 2^63 allocations in one process.
const SIMP_BINDER_FVAR_TOP: u64 = (1u64 << 63) - 1;

/// Descending allocator for simp binder temporaries. See
/// [`SIMP_BINDER_FVAR_TOP`] for why it counts down.
static SIMP_BINDER_FVAR_CURSOR: AtomicU64 = AtomicU64::new(SIMP_BINDER_FVAR_TOP);

/// Allocate a binder temporary that is guaranteed not to be read as a
/// metavariable and not to collide with elaborator/tactic free variables.
fn fresh_binder_fvar() -> FVarId {
    let id = SIMP_BINDER_FVAR_CURSOR.fetch_sub(1, Ordering::Relaxed);
    debug_assert!(
        id & (1u64 << 63) == 0,
        "simp binder temporary must stay below the metavariable tag"
    );
    FVarId::new(id)
}

/// One opened binder: the extended goal, the fresh free variable standing for
/// the bound variable, and the body with `BVar(0)` instantiated to it.
pub(crate) struct OpenedBinder {
    /// The goal with `fvar` appended to its local context.
    pub(crate) goal: Goal,
    /// The fresh free variable that replaced `BVar(0)`.
    pub(crate) fvar: FVarId,
    /// The binder body, closed with respect to this binder.
    pub(crate) body: Expr,
}

/// Open a binder for the simp traversal.
///
/// `ty` must be closed in `goal`'s context, which it is whenever every
/// enclosing binder was opened the same way — the traversal starts at a goal
/// target, which is closed by construction.
///
/// # Contract
///
/// REQUIRES: `ty` has no loose bound variables in `goal`'s context
/// ENSURES: `opened.body.abstract_fvar(opened.fvar) == *body`
/// ENSURES: `opened.goal.local_ctx` is `goal.local_ctx` plus exactly one entry
///   whose `fvar` is fresh and below the metavariable tag, so it shadows no
///   hypothesis and decodes as no metavariable
pub(crate) fn open_binder(goal: &Goal, ty: &Expr, body: &Expr) -> OpenedBinder {
    let fvar = fresh_binder_fvar();
    let mut extended = goal.clone();
    extended.local_ctx.push(LocalDecl {
        fvar,
        name: format!("_simp_binder_{}", fvar.as_u64()),
        ty: ty.clone(),
        value: None,
    });
    let opened_body = body.instantiate(&Expr::fvar(fvar));
    OpenedBinder {
        goal: extended,
        fvar,
        body: opened_body,
    }
}
