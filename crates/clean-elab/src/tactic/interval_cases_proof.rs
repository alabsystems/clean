// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Interval-descent proof construction for `interval_cases` (#2533 family).
//!
//! This module is `interval_cases`-only. `fin_cases` keeps
//! [`super::finite_cases_proof::build_or_elim_chain`]; see the KNOWN GAP note
//! there.
//!
//! # Why a descent and not an `Or.rec`/`Classical.em` chain
//!
//! The previous `interval_cases` proof was a right-nested
//! `Or.rec … (Classical.em (n = vₖ))` chain whose true branch was an
//! *anonymous* lambda holding a bare sub-goal meta, and whose LAST branch had
//! no binder at all. Every sub-goal nevertheless advertised an equality
//! hypothesis `n_eq : n = vₖ` at an out-of-band FVar id (`ctx.len() + 1000`).
//! That id can never be structurally bound — `close_fvars` derives a tactic
//! FVar's binder nesting depth from `id - fvar_base` — so the last branch
//! literally ASSUMED `n = hi` with nothing proving it, and the immutable
//! goal-scope guard correctly rejected the whole assignment.
//!
//! An independent interim fix kept that chain, minted the NON-final
//! equalities goal-derived so the true-branch lambdas bind them, and WITHHELD
//! the last branch's equality, because the chain has no proof of it. That is
//! sound, but the last branch could not cite `n = hi`. The descent supplies
//! that proof, so every branch — the last included — carries its equality.
//! `fin_cases` still uses the interim chain
//! ([`super::finite_cases_proof::build_or_elim_chain`]).
//!
//! The fix is not to weaken the guard: it is to make every branch's equality
//! come from a REAL binder applied to a REAL proof. This module builds the
//! interval descent
//!
//! ```text
//! descend(idx, h_le : n ≤ v_idx) =
//!   Or.rec (n < v_idx) (n = v_idx) (λ _. target)
//!     (λ hlt. idx = 0 ? False.elim target (Nat.lt_irrefl n
//!                          (Nat.le_trans (succ n) v_0 n hlt h_lower))
//!                     : descend(idx-1, Nat.le_of_succ_le_succ n v_{idx-1} hlt))
//!     (λ n_eq. ?m_idx)
//!     (Nat.lt_or_eq_of_le n v_idx h_le)
//! ```
//!
//! so branch `idx`'s meta sits under exactly `values.len()-1-idx` `hlt`
//! binders plus its own `n_eq` binder. There is no bare-meta base case: the
//! `idx = 0` rung discharges `n < lo` against the caller's own lower bound.
//! Exhaustiveness is therefore PROVED, never assumed.
//!
//! This is the same algorithm as
//! [`super::omega_tactic::case_split`]'s `descend`, at a different termination
//! rung (`lo` here vs. `0` there) and hanging a sub-goal meta on each `heq`
//! binder instead of an `Or`-introduction. Unifying the two is tracked as a
//! follow-up; `case_split` stays byte-identical while this lands.
//!
//! # Literal representation is load-bearing
//!
//! Each descent step relies on `v_k ≡ Nat.succ v_{k-1}` **syntactically**, which
//! holds because `make_int_literal`/`make_nat_literal` emit `Nat.succ` chains.
//! Switching those to `Expr::nat_lit` would turn that identity into a literal-
//! normalization obligation for the kernel.
//!
//! # Scope discipline
//!
//! The assembled term mentions NO tactic-scope FVar: every binder it introduces
//! is referenced as `BVar(0)` from the root of its own lambda body, so
//! `abstract_fvar` is never called here. The binder FVar ids the CALLER records
//! in the sub-goal contexts must still be minted GOAL-DERIVED — one
//! `ProofState::goal_binder_base` read, then `base + j` for nesting position
//! `j` — see `interval_cases::build_interval_goals`.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, Level};

use super::core::{ProofState, TacticError};
use super::interval_cases::make_equality_type;
use super::tc_app;
use crate::stack_safe;
use crate::unify::{MetaId, MetaState};

/// Constants the descent term references.
///
/// Minimal environments (targeted `init_*` fixtures) may lack Nat order
/// theory entirely; the tactic fails closed with
/// [`TacticError::EnvironmentMissing`] rather than assembling a term that
/// cannot type-check.
pub(crate) const REQUIRED_CONSTANTS: [&str; 7] = [
    "Nat.lt_or_eq_of_le",
    "Nat.le_of_succ_le_succ",
    "Nat.le_trans",
    "Nat.lt_irrefl",
    "False.elim",
    "Or",
    "Or.rec",
];

/// Fail closed when any constant the descent needs is missing.
///
/// ENSURES: `Ok(())` iff every name in [`REQUIRED_CONSTANTS`] resolves in
///   `state.env()`
/// ENSURES: otherwise `Err(EnvironmentMissing)` naming the first absentee
pub(crate) fn require_constants(state: &ProofState) -> Result<(), TacticError> {
    for constant in REQUIRED_CONSTANTS {
        if state
            .env()
            .get_const(&Name::from_string(constant))
            .is_none()
        {
            return Err(TacticError::EnvironmentMissing {
                constant: constant.to_string(),
            });
        }
    }
    Ok(())
}

/// Immutable inputs shared by every rung of the descent.
struct Descent<'a> {
    /// The goal target, preserved verbatim in every branch.
    target: &'a Expr,
    /// `Expr::fvar(hyp.fvar)` — the variable being case-split.
    n: &'a Expr,
    /// Ascending consecutive `Nat` literals `[lo, …, hi]`.
    values: &'a [Expr],
    /// One sub-goal metavariable per value, in the same order.
    metas: &'a [MetaId],
    /// Proof of `values[0] ≤ n` (the `LE.le`, `LT.lt`, or raw `Nat.le` form —
    /// all definitionally equal).
    h_lower: &'a Expr,
}

/// Assemble the interval-descent proof of `target`.
///
/// REQUIRES: `values` are ascending consecutive `Nat` literals built by
///   `make_int_literal` (so `values[k] ≡ Nat.succ values[k-1]` syntactically)
/// REQUIRES: `values.len() == metas.len() >= 1`
/// REQUIRES: `h_le_top` proves `n ≤ values.last()`; `h_lower` proves
///   `values[0] ≤ n` (either the typeclass `LE.le` form or a defeq
///   `LT.lt` / raw `Nat.le` form)
/// REQUIRES: [`require_constants`] already succeeded for the ambient state
///
/// ENSURES: the returned term contains no tactic-scope FVar and no
///   `abstract_fvar` residue
/// ENSURES: `metas[k]` occurs at binder depth `values.len() - k` — under
///   exactly `values.len()-1-k` `hlt` binders plus its own `n_eq` binder
/// ENSURES: every `metas[k]` is the body of a `λ (n_eq : n = values[k])`
///   that `Or.rec` can only apply to a proof extracted from
///   `Nat.lt_or_eq_of_le n values[k] _`
pub(crate) fn build_interval_descent_proof(
    target: &Expr,
    n: &Expr,
    values: &[Expr],
    metas: &[MetaId],
    h_le_top: Expr,
    h_lower: &Expr,
) -> Result<Expr, TacticError> {
    if values.is_empty() || values.len() != metas.len() {
        return Err(TacticError::InvalidTarget {
            tactic: "interval_cases".into(),
            detail: format!(
                "interval descent needs one sub-goal per value (values: {}, metas: {})",
                values.len(),
                metas.len()
            ),
        });
    }
    let descent = Descent {
        target,
        n,
        values,
        metas,
        h_lower,
    };
    Ok(descent.at(values.len() - 1, h_le_top))
}

impl Descent<'_> {
    /// Proof of `target` from `h_le : n ≤ values[idx]`.
    ///
    /// `h_le` may reference `BVar(0)` of the caller's enclosing lambda: it is
    /// only ever placed in the major-premise application spine at the root of
    /// that lambda's body, never under a further binder, so no de Bruijn
    /// lifting is required.
    ///
    /// REQUIRES: `idx < self.values.len()`
    fn at(&self, idx: usize, h_le: Expr) -> Expr {
        stack_safe(|| {
            let v = self.values[idx].clone();
            let lt_ty = tc_app::nat_lt_tc(self.n.clone(), v.clone());
            let eq_ty = make_equality_type(
                &tc_app::nat_type(),
                self.n,
                &v,
                // Nat : Type 0 = Sort 1
                Level::succ(Level::zero()),
            );

            // major : n < v ∨ n = v
            let major = Expr::apps(cst("Nat.lt_or_eq_of_le"), [self.n.clone(), v.clone(), h_le]);

            // The motive is CONSTANT, so both minors must have type `target`
            // exactly. That is why sub-goals keep the original target rather
            // than specializing it to `target[n := v]`.
            let motive = Expr::lam(
                BinderInfo::Default,
                or_of(lt_ty.clone(), eq_ty.clone()),
                self.target.clone(),
            );

            // λ (n_eq : n = v). ?m_idx  — the branch's equality is BOUND here
            // and `Or.rec` can only supply the right disjunct as its argument.
            let minor_inr = Expr::lam(
                BinderInfo::Default,
                eq_ty.clone(),
                Expr::fvar(MetaState::to_fvar(self.metas[idx])),
            );

            let minor_inl = if idx == 0 {
                // λ (hlt : n < v_0).
                //   False.elim target
                //     (Nat.lt_irrefl n (Nat.le_trans (succ n) v_0 n hlt h_lower))
                //
                // `hlt : n < v_0` δ-reduces to `Nat.le (succ n) v_0`, so
                // `Nat.le_trans` composes it with `h_lower : v_0 ≤ n` to give
                // `Nat.le (succ n) n` ≡ `Nat.lt n n`, and `Nat.lt_irrefl`
                // closes the branch. This is what makes the interval
                // EXHAUSTIVE without a `Classical.em` appeal.
                let le_succ_n_n = Expr::apps(
                    cst("Nat.le_trans"),
                    [
                        Expr::app(cst("Nat.succ"), self.n.clone()),
                        v.clone(),
                        self.n.clone(),
                        Expr::bvar(0),
                        self.h_lower.clone(),
                    ],
                );
                let false_pf = Expr::apps(cst("Nat.lt_irrefl"), [self.n.clone(), le_succ_n_n]);
                Expr::lam(
                    BinderInfo::Default,
                    lt_ty.clone(),
                    Expr::apps(
                        // False.elim : {C : Sort u} → False → C; target : Prop
                        Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
                        [self.target.clone(), false_pf],
                    ),
                )
            } else {
                // λ (hlt : n < v_idx). descend(idx-1, …)
                //
                // `hlt : Nat.le (succ n) v_idx` and `v_idx ≡ Nat.succ v_{idx-1}`
                // syntactically, so `Nat.le_of_succ_le_succ` peels it to
                // `n ≤ v_{idx-1}`.
                let h_le_next = Expr::apps(
                    cst("Nat.le_of_succ_le_succ"),
                    [self.n.clone(), self.values[idx - 1].clone(), Expr::bvar(0)],
                );
                Expr::lam(
                    BinderInfo::Default,
                    lt_ty.clone(),
                    self.at(idx - 1, h_le_next),
                )
            };

            Expr::apps(
                cst("Or.rec"),
                [lt_ty, eq_ty, motive, minor_inl, minor_inr, major],
            )
        })
    }
}

/// `Const(name, [])` — every constant this module cites is level-monomorphic
/// except `False.elim`, which is built explicitly.
fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `@Or a b` (`Or` takes no universe arguments).
fn or_of(a: Expr, b: Expr) -> Expr {
    Expr::apps(cst("Or"), [a, b])
}
