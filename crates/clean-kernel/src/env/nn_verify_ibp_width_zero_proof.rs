// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-term builder for the full `NNVerify.ibp_width_zero` theorem
//! (#3490 T4, #3476).
//!
//! Statement:
//! ```text
//! ∀ (n : Nat) (bnd : IntervalBounds n),
//!   (∀ i : Fin n, bnd.lower i = bnd.upper i)
//!   → ibp_width n bnd = Rat.zero
//! ```
//!
//! Proof architecture: `Nat.rec.{0}` at a dependent Prop-motive
//!   `motive = fun n => ∀ bnd, (∀ i, lower bnd i = upper bnd i)
//!                                     → ibp_width n bnd = Rat.zero`.
//!
//! * **Zero case** — `fun bnd h => @Eq.refl.{1} Rat Rat.zero`.
//!   The kernel iota-reduces `ibp_width 0 bnd` to `Rat.zero`, so
//!   `Eq.refl Rat Rat.zero` inhabits the goal.
//!
//! * **Succ case** — at `d, ih, bnd, h`, the goal reduces to
//!   `Rat.max (ibp_width d prefix_bnd)
//!            (Rat.sub (upper bnd (last d)) (lower bnd (last d)))
//!    = Rat.zero`
//!   where `prefix_bnd = IntervalBounds.mk d
//!                          (fun i => lower bnd (castSucc i))
//!                          (fun i => upper bnd (castSucc i))
//!                          (fun i => valid bnd (castSucc i))`.
//!
//!   We chain three sub-proofs:
//!   1. `e_ih : ibp_width d prefix_bnd = Rat.zero`
//!      via `ih prefix_bnd prefix_h`, with
//!      `prefix_h = fun i => h (castSucc i)`.
//!   2. `e_sub : Rat.sub (upper bnd (last d)) (lower bnd (last d))
//!             = Rat.zero`
//!      via `Eq.subst` with motive
//!      `fun x => Rat.sub (upper bnd (last d)) x = Rat.zero`,
//!      starting from `Rat.sub_self (upper bnd (last d))` and
//!      transporting along `Eq.symm (h (last d))`.
//!   3. Apply `Eq.subst` twice to `rat_max_zero_zero`:
//!      * inner: motive `fun y => Rat.max 0 y = 0`, transport from
//!        `0` to `Rat.sub (upper bnd (last d)) (lower bnd (last d))`
//!        via `Eq.symm e_sub`;
//!      * outer: motive `fun x => Rat.max x (Rat.sub ...) = 0`,
//!        transport from `0` to `ibp_width d prefix_bnd` via
//!        `Eq.symm e_ih`.
//!
//! Axiom profile: `Nat.rec`, `Eq.refl`, `Eq.subst`, `Eq.symm`
//! (foundational), plus the already-kernel-verified helper theorems
//! `Rat.sub_self` and `NNVerify.rat_max_zero_zero`, plus foundationally
//! promoted `Rat.max` family. Zero domain-specific axioms beyond those
//! already assumed by the existing Rat infrastructure.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for the `ibp_width_zero` full proof.
pub(super) struct IbpWidthZeroConsts {
    pub(super) nat: Expr,
    pub(super) nat_zero: Expr,
    pub(super) nat_succ: Expr,
    pub(super) nat_rec_prop: Expr,
    pub(super) rat: Expr,
    pub(super) rat_zero: Expr,
    pub(super) rat_sub: Expr,
    pub(super) rat_max: Expr,
    pub(super) rat_sub_self: Expr,
    pub(super) rat_max_zz: Expr,
    pub(super) fin: Expr,
    pub(super) fin_cast_succ: Expr,
    pub(super) fin_last: Expr,
    pub(super) ib: Expr,
    pub(super) ib_mk: Expr,
    pub(super) ibp_width: Expr,
    pub(super) eq: Expr,
    pub(super) eq_refl: Expr,
    pub(super) eq_symm: Expr,
    pub(super) eq_subst: Expr,
}

impl IbpWidthZeroConsts {
    pub(super) fn new() -> Self {
        let u1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            // `Nat.rec.{0}` — motive returns `Prop = Sort 0`.
            nat_rec_prop: Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_sub: Expr::const_(Name::from_string("Rat.sub"), vec![]),
            rat_max: Expr::const_(Name::from_string("Rat.max"), vec![]),
            rat_sub_self: Expr::const_(Name::from_string("Rat.sub_self"), vec![]),
            rat_max_zz: Expr::const_(Name::from_string("NNVerify.rat_max_zero_zero"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_cast_succ: Expr::const_(Name::from_string("Fin.castSucc"), vec![]),
            fin_last: Expr::const_(Name::from_string("Fin.last"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            ib_mk: Expr::const_(Name::from_string("NNVerify.IntervalBounds.mk"), vec![]),
            ibp_width: Expr::const_(Name::from_string("NNVerify.ibp_width"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![u1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![u1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![u1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![u1]),
        }
    }

    pub(super) fn ib_of(&self, d: Expr) -> Expr {
        Expr::app(self.ib.clone(), d)
    }

    pub(super) fn fin_of(&self, d: Expr) -> Expr {
        Expr::app(self.fin.clone(), d)
    }

    pub(super) fn succ_of(&self, d: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), d)
    }

    pub(super) fn rat_eq(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq.clone(), [self.rat.clone(), a, b])
    }

    pub(super) fn ibp_width_app(&self, n: Expr, bnd: Expr) -> Expr {
        Expr::apps(self.ibp_width.clone(), [n, bnd])
    }

    pub(super) fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }

    pub(super) fn maxr(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_max.clone(), [a, b])
    }

    /// `@Eq.refl.{1} Rat a`.
    pub(super) fn refl(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.rat.clone(), a])
    }

    /// `@Eq.symm.{1} Rat a b h`.
    pub(super) fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }

    /// `@Eq.subst.{1} Rat motive a b h_eq h_motive_a`.
    pub(super) fn subst(
        &self,
        motive: Expr,
        a: Expr,
        b: Expr,
        h_eq: Expr,
        h_motive_a: Expr,
    ) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h_motive_a],
        )
    }

    /// `castSucc.{d} i` — supplies the implicit `n=d`.
    pub(super) fn cast_succ_of(&self, d: Expr, i: Expr) -> Expr {
        Expr::apps(self.fin_cast_succ.clone(), [d, i])
    }

    /// `last d` — explicit `d`.
    pub(super) fn last_of(&self, d: Expr) -> Expr {
        Expr::app(self.fin_last.clone(), d)
    }

    /// The hypothesis type `∀ (i : Fin n), Eq Rat (lower bnd i) (upper bnd i)`.
    pub(super) fn hyp_ty(&self, n: Expr, bnd: Expr, builder: &EnvDeclBuilder) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(builder);
        let fin_n = self.fin_of(n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let lower_i = Expr::app(
            Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, bnd.clone()),
            i.clone(),
        );
        let upper_i = Expr::app(
            Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, bnd),
            i,
        );
        let body = self.rat_eq(lower_i, upper_i);
        let r = ch.mk_pi(i_id, BinderInfo::Default, fin_n, body);
        ch.finish_child(r)
    }
}

/// Build the full type:
/// `∀ (n : Nat) (bnd : IntervalBounds n),
///    (∀ i : Fin n, lower bnd i = upper bnd i)
///    → ibp_width n bnd = Rat.zero`.
pub(super) fn build_ibp_width_zero_full_type(c: &IbpWidthZeroConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let ib_n = c.ib_of(n.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    let hyp = c.hyp_ty(n.clone(), bnd.clone(), &b);
    let (h_id, _h) = b.fresh_local(hyp.clone());
    let concl = c.rat_eq(c.ibp_width_app(n.clone(), bnd), c.rat_zero.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the motive:
/// `fun (n : Nat) => ∀ bnd, (∀ i, lower bnd i = upper bnd i)
///                            → ibp_width n bnd = Rat.zero`.
pub(super) fn build_motive(c: &IbpWidthZeroConsts, outer: &EnvDeclBuilder) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(outer);
    let (n_id, n) = ch.fresh_local(c.nat.clone());
    let ib_n = c.ib_of(n.clone());
    let (bnd_id, bnd) = ch.fresh_local(ib_n.clone());
    let hyp = c.hyp_ty(n.clone(), bnd.clone(), &ch);
    let (h_id, _h) = ch.fresh_local(hyp.clone());
    let concl = c.rat_eq(c.ibp_width_app(n.clone(), bnd), c.rat_zero.clone());
    let body = ch.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let body = ch.mk_pi(bnd_id, BinderInfo::Default, ib_n, body);
    let r = ch.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
    ch.finish_child(r)
}

/// Zero case: `fun (bnd : IntervalBounds 0) (h : ∀ i, ...) =>
///                @Eq.refl.{1} Rat Rat.zero`.
pub(super) fn build_zero_case(c: &IbpWidthZeroConsts, outer: &EnvDeclBuilder) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(outer);
    let ib_zero = c.ib_of(c.nat_zero.clone());
    let (bnd_id, bnd) = ch.fresh_local(ib_zero.clone());
    let hyp = c.hyp_ty(c.nat_zero.clone(), bnd, &ch);
    let (h_id, _h) = ch.fresh_local(hyp.clone());
    let body = c.refl(c.rat_zero.clone());
    let r = ch.mk_lam(h_id, BinderInfo::Default, hyp, body);
    let r = ch.mk_lam(bnd_id, BinderInfo::Default, ib_zero, r);
    ch.finish_child(r)
}

/// Build the prefix `IntervalBounds.mk d (λi. lower bnd (castSucc i))
///                                        (λi. upper bnd (castSucc i))
///                                        (λi. valid bnd (castSucc i))`.
fn build_prefix_bnd(c: &IbpWidthZeroConsts, outer: &EnvDeclBuilder, d: &Expr, bnd: &Expr) -> Expr {
    let fin_d = c.fin_of(d.clone());
    let lower = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, bnd.clone());
    let upper = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, bnd.clone());
    let valid = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 2, bnd.clone());

    let lower_prefix = {
        let mut ch = EnvDeclBuilder::child_of(outer);
        let (i_id, i) = ch.fresh_local(fin_d.clone());
        let cast_i = c.cast_succ_of(d.clone(), i);
        let body = Expr::app(lower, cast_i);
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), body);
        ch.finish_child(r)
    };
    let upper_prefix = {
        let mut ch = EnvDeclBuilder::child_of(outer);
        let (i_id, i) = ch.fresh_local(fin_d.clone());
        let cast_i = c.cast_succ_of(d.clone(), i);
        let body = Expr::app(upper, cast_i);
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), body);
        ch.finish_child(r)
    };
    let valid_prefix = {
        let mut ch = EnvDeclBuilder::child_of(outer);
        let (i_id, i) = ch.fresh_local(fin_d.clone());
        let cast_i = c.cast_succ_of(d.clone(), i);
        let body = Expr::app(valid, cast_i);
        let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), body);
        ch.finish_child(r)
    };
    Expr::apps(
        c.ib_mk.clone(),
        [d.clone(), lower_prefix, upper_prefix, valid_prefix],
    )
}

/// Build `prefix_h : ∀ i : Fin d, lower prefix_bnd i = upper prefix_bnd i`
/// as `fun i : Fin d => h (castSucc d i)`.
///
/// Note: after iota on `IntervalBounds.mk`, `lower prefix_bnd i` reduces
/// to `lower bnd (castSucc i)`, and similarly for `upper`. So the type
/// expected by `ih prefix_bnd` is def-equal to
/// `∀ i : Fin d, lower bnd (castSucc i) = upper bnd (castSucc i)`,
/// which is what `fun i => h (castSucc i)` produces.
fn build_prefix_h(c: &IbpWidthZeroConsts, outer: &EnvDeclBuilder, d: &Expr, h: &Expr) -> Expr {
    let fin_d = c.fin_of(d.clone());
    let mut ch = EnvDeclBuilder::child_of(outer);
    let (i_id, i) = ch.fresh_local(fin_d.clone());
    let cast_i = c.cast_succ_of(d.clone(), i);
    let body = Expr::app(h.clone(), cast_i);
    let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d, body);
    ch.finish_child(r)
}

/// Build the succ-case body producing
/// `Rat.max (ibp_width d prefix_bnd) (Rat.sub upper_last lower_last)
///    = Rat.zero`,
/// given locals `d, ih, bnd, h` already bound in the lambda above.
fn build_succ_body(
    c: &IbpWidthZeroConsts,
    ch: &EnvDeclBuilder,
    d: &Expr,
    ih: &Expr,
    bnd: &Expr,
    h: &Expr,
) -> Expr {
    // prefix_bnd and prefix_h
    let prefix_bnd = build_prefix_bnd(c, ch, d, bnd);
    let prefix_h = build_prefix_h(c, ch, d, h);

    // e_ih : ibp_width d prefix_bnd = Rat.zero
    //   via ih prefix_bnd prefix_h.
    let e_ih = Expr::apps(ih.clone(), [prefix_bnd.clone(), prefix_h]);

    // last index and the last lower/upper.
    let last_i = c.last_of(d.clone());
    let lower = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, bnd.clone());
    let upper = Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, bnd.clone());
    let lower_last = Expr::app(lower, last_i.clone());
    let upper_last = Expr::app(upper, last_i);

    // h_last : lower bnd (last d) = upper bnd (last d) via h (last d).
    let h_last = Expr::app(h.clone(), c.last_of(d.clone()));
    // symm_h_last : upper bnd (last d) = lower bnd (last d).
    let symm_h_last = c.symm(lower_last.clone(), upper_last.clone(), h_last);

    // motive_sub : Rat → Prop = fun x => Rat.sub upper_last x = Rat.zero.
    //
    // Starting from base : Rat.sub upper_last upper_last = Rat.zero
    //   (via Rat.sub_self upper_last), Eq.subst with
    //   h_eq : upper_last = lower_last
    //   produces motive_sub lower_last : Rat.sub upper_last lower_last = 0.
    let motive_sub = {
        let mut ch2 = EnvDeclBuilder::child_of(ch);
        let (x_id, x) = ch2.fresh_local(c.rat.clone());
        let lhs = c.sub(upper_last.clone(), x);
        let body = c.rat_eq(lhs, c.rat_zero.clone());
        let r = ch2.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch2.finish_child(r)
    };
    let base_sub = Expr::app(c.rat_sub_self.clone(), upper_last.clone());
    let e_sub = c.subst(
        motive_sub,
        upper_last.clone(),
        lower_last.clone(),
        symm_h_last,
        base_sub,
    );
    // e_sub : Rat.sub upper_last lower_last = Rat.zero.

    let sub_expr = c.sub(upper_last.clone(), lower_last.clone());

    // Step 1: transport rat_max_zero_zero (`max 0 0 = 0`) through motive
    //   inner = fun y => Rat.max 0 y = 0 via Eq.symm e_sub (0 = sub).
    let motive_inner = {
        let mut ch2 = EnvDeclBuilder::child_of(ch);
        let (y_id, y) = ch2.fresh_local(c.rat.clone());
        let body = c.rat_eq(c.maxr(c.rat_zero.clone(), y), c.rat_zero.clone());
        let r = ch2.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body);
        ch2.finish_child(r)
    };
    let symm_e_sub = c.symm(sub_expr.clone(), c.rat_zero.clone(), e_sub);
    let step1 = c.subst(
        motive_inner,
        c.rat_zero.clone(),
        sub_expr.clone(),
        symm_e_sub,
        c.rat_max_zz.clone(),
    );
    // step1 : Rat.max Rat.zero (Rat.sub upper_last lower_last) = Rat.zero.

    // Step 2: transport step1 through motive
    //   outer = fun x => Rat.max x (Rat.sub upper_last lower_last) = 0
    //   via Eq.symm e_ih (0 = ibp_width d prefix_bnd).
    let ibw_prefix = c.ibp_width_app(d.clone(), prefix_bnd);
    let motive_outer = {
        let mut ch2 = EnvDeclBuilder::child_of(ch);
        let (x_id, x) = ch2.fresh_local(c.rat.clone());
        let body = c.rat_eq(c.maxr(x, sub_expr.clone()), c.rat_zero.clone());
        let r = ch2.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch2.finish_child(r)
    };
    let symm_e_ih = c.symm(ibw_prefix.clone(), c.rat_zero.clone(), e_ih);
    c.subst(
        motive_outer,
        c.rat_zero.clone(),
        ibw_prefix,
        symm_e_ih,
        step1,
    )
    // Final : Rat.max (ibp_width d prefix_bnd) (Rat.sub upper_last lower_last) = Rat.zero.
    // Kernel iota-reduces `ibp_width (succ d) bnd` to the LHS, so this
    // inhabits the succ case goal.
}

/// Succ case lambda:
/// `fun (d : Nat)
///      (ih : motive d)
///      (bnd : IntervalBounds (succ d))
///      (h : ∀ i : Fin (succ d), lower bnd i = upper bnd i)
///    => <body>`.
pub(super) fn build_succ_case(c: &IbpWidthZeroConsts, outer: &EnvDeclBuilder) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(outer);
    let (d_id, d) = ch.fresh_local(c.nat.clone());

    // Type of `ih`: `∀ bnd_d, (∀ i, lower bnd_d i = upper bnd_d i)
    //                          → ibp_width d bnd_d = 0`.
    let ih_ty = {
        let mut ch2 = EnvDeclBuilder::child_of(&ch);
        let ib_d = c.ib_of(d.clone());
        let (bnd_id, bnd) = ch2.fresh_local(ib_d.clone());
        let hyp = c.hyp_ty(d.clone(), bnd.clone(), &ch2);
        let (h_id, _h) = ch2.fresh_local(hyp.clone());
        let concl = c.rat_eq(c.ibp_width_app(d.clone(), bnd), c.rat_zero.clone());
        let r = ch2.mk_pi(h_id, BinderInfo::Default, hyp, concl);
        let r = ch2.mk_pi(bnd_id, BinderInfo::Default, ib_d, r);
        ch2.finish_child(r)
    };
    let (ih_id, ih) = ch.fresh_local(ih_ty.clone());

    let sd = c.succ_of(d.clone());
    let ib_sd = c.ib_of(sd.clone());
    let (bnd_id, bnd) = ch.fresh_local(ib_sd.clone());

    let hyp = c.hyp_ty(sd, bnd.clone(), &ch);
    let (h_id, h) = ch.fresh_local(hyp.clone());

    let body = build_succ_body(c, &ch, &d, &ih, &bnd, &h);

    let r = ch.mk_lam(h_id, BinderInfo::Default, hyp, body);
    let r = ch.mk_lam(bnd_id, BinderInfo::Default, ib_sd, r);
    let r = ch.mk_lam(ih_id, BinderInfo::Default, ih_ty, r);
    let r = ch.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), r);
    ch.finish_child(r)
}

/// Build the full proof value:
/// `fun (n : Nat) (bnd : IntervalBounds n) (h : ∀ i, ...)
///    => @Nat.rec.{0} motive zero_case succ_case n bnd h`.
pub(super) fn build_ibp_width_zero_full_value(c: &IbpWidthZeroConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let ib_n = c.ib_of(n.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_n.clone());
    let hyp = c.hyp_ty(n.clone(), bnd.clone(), &b);
    let (h_id, h) = b.fresh_local(hyp.clone());

    let motive = build_motive(c, &b);
    let zero_case = build_zero_case(c, &b);
    let succ_case = build_succ_case(c, &b);

    let rec_app = Expr::apps(
        c.nat_rec_prop.clone(),
        [motive, zero_case, succ_case, n.clone()],
    );
    let body = Expr::apps(rec_app, [bnd, h]);

    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
    let e = b.mk_lam(bnd_id, BinderInfo::Default, ib_n, e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}
