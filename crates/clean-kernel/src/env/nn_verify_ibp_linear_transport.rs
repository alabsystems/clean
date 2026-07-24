// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T2 (#3490): Constructive proof terms for the `le_of_eq_of_le` and
//! `le_of_le_of_eq` transport lemmas over `Rat`.
//!
//! These helpers previously used `sorry_inhabit_pi`; they are now real
//! `Declaration::Theorem` proofs built directly from foundational
//! `Eq.subst` / `Eq.symm`. Zero domain axioms pulled into the closure.
//!
//! Split out of `nn_verify_ibp_linear.rs` for file-size compliance
//! (500-line limit). Part of #3490.

use super::decl_builder::EnvDeclBuilder;
use super::nn_verify_ibp_linear::IbpLinearConsts;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// `Eq.subst.{1} @Rat motive @a @b h_eq h_ma` — applied for `α = Rat`
/// (`Rat : Type`, so universe level `1`).
fn eq_subst_rat(
    c: &IbpLinearConsts,
    motive: Expr,
    a: Expr,
    b: Expr,
    h_eq: Expr,
    h_ma: Expr,
) -> Expr {
    let eq_subst = Expr::const_(
        Name::from_string("Eq.subst"),
        vec![Level::succ(Level::zero())],
    );
    Expr::apps(eq_subst, [c.rat.clone(), motive, a, b, h_eq, h_ma])
}

/// `Eq.symm.{1} @Rat @a @b h : Eq Rat b a` — applied for `α = Rat`.
fn eq_symm_rat(c: &IbpLinearConsts, a: Expr, b: Expr, h: Expr) -> Expr {
    let eq_symm = Expr::const_(
        Name::from_string("Eq.symm"),
        vec![Level::succ(Level::zero())],
    );
    Expr::apps(eq_symm, [c.rat.clone(), a, b, h])
}

/// Build proof term for `NNVerify.le_of_eq_of_le`:
/// `∀ a b c : Rat, Eq a b → b ≤ c → a ≤ c`.
///
/// Proof: `Eq.subst` with motive `λ x ↦ x ≤ c`, transporting along the
/// reversed equality `Eq.symm h_eq : Eq b a`, which carries
/// `h_le : b ≤ c` (i.e. `motive b`) to `a ≤ c` (i.e. `motive a`).
pub(super) fn build_le_of_eq_of_le_proof(c: &IbpLinearConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_eq_ty = c.rat_eq(a.clone(), bv.clone());
    let h_le_ty = c.rat_le(bv.clone(), cv.clone());
    let (h_eq_id, h_eq) = b.fresh_local(h_eq_ty.clone());
    let (h_le_id, h_le) = b.fresh_local(h_le_ty.clone());

    // motive : Rat → Prop = fun x => x ≤ c
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.rat_le(x, cv.clone());
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };

    // h_symm : Eq Rat b a
    let h_symm = eq_symm_rat(c, a.clone(), bv.clone(), h_eq);
    // Eq.subst @Rat motive b a h_symm h_le : motive a = (a ≤ c)
    let body = eq_subst_rat(c, motive, bv.clone(), a.clone(), h_symm, h_le);

    let e = b.mk_lam(h_le_id, BinderInfo::Default, h_le_ty, body);
    let e = b.mk_lam(h_eq_id, BinderInfo::Default, h_eq_ty, e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// Build proof term for `NNVerify.le_of_le_of_eq`:
/// `∀ a b c : Rat, a ≤ b → Eq b c → a ≤ c`.
///
/// Proof: `Eq.subst` with motive `λ x ↦ a ≤ x`, transporting
/// `h_le : a ≤ b` (i.e. `motive b`) along `h_eq : Eq b c` to `a ≤ c`.
pub(super) fn build_le_of_le_of_eq_proof(c: &IbpLinearConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());
    let (cv_id, cv) = b.fresh_local(c.rat.clone());
    let h_le_ty = c.rat_le(a.clone(), bv.clone());
    let h_eq_ty = c.rat_eq(bv.clone(), cv.clone());
    let (h_le_id, h_le) = b.fresh_local(h_le_ty.clone());
    let (h_eq_id, h_eq) = b.fresh_local(h_eq_ty.clone());

    // motive : Rat → Prop = fun x => a ≤ x
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.rat_le(a.clone(), x);
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };

    // Eq.subst @Rat motive b c h_eq h_le : motive c = (a ≤ c)
    let body = eq_subst_rat(c, motive, bv.clone(), cv.clone(), h_eq, h_le);

    let e = b.mk_lam(h_eq_id, BinderInfo::Default, h_eq_ty, body);
    let e = b.mk_lam(h_le_id, BinderInfo::Default, h_le_ty, e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}
