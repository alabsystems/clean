// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the telescoping `IsCauchy` for the dyadic
//! approximation (Stage B3, sqrt run #4, rung 6).
//!
//! # Why this module exists
//!
//! The keystone `NNReal.sqrt x · NNReal.sqrt x = ofRat x` (plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md` §8.5 rung 6) needs the
//! scaled dyadic approximation `a_n := ofNat(k_n) · inv(ofNat 2^n)` to be a
//! genuine `NNReal.CauSeq`. This module supplies the analytic frontier: the
//! antitone / monotonicity / telescoping bounds and, from them,
//! `IsCauchy (dyadicApprox x)` (after the trivial `NNRat`-lift in the def
//! module).
//!
//! Everything is built from the LANDED inv-arithmetic gears
//! (`Rat.inv_two_pow_succ`, `Rat.zero_lt_inv_two_pow`,
//! `Rat.exists_inv_two_pow_lt`), the LANDED digit-step bounds
//! (`Rat.dyadicNum_two_mul_le_succ`, `Rat.dyadicNum_succ_le_two_mul_succ`), and
//! the on-main `Rat`-order toolkit. NO new `Rat.inv` fact is invented; the only
//! new inv lemma here is the ANTITONE comparison `inv(2^n) ≤ inv(2^N)` for
//! `N ≤ n`, proven through the multiplicative-bridge idiom (never reasoning
//! about the `Rat.inv` `Quot.lift` body directly).
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.inv_le_inv_of_le : ∀ a b, Rat.lt 0 a → Rat.le a b → Rat.le (inv b)(inv a)`
//! - `Rat.inv_two_pow_le_of_le : ∀ N n, Nat.le N n →
//!       Rat.le (inv (ofNat 2^n)) (inv (ofNat 2^N))`  (the dyadic antitone fact)
//!
//! Every declaration is a checked `Theorem` through `self.add_decl`; every
//! theorem's transitive admitted-axiom closure is empty (foundational only).
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # The multiplicative-bridge proof of `inv_le_inv_of_le`
//!
//! Forward chain (no contradiction; `0<a`, `a≤b`, hence `0<b`):
//!   1. `h1 : 1 ≤ (inv a)·b`. From `a≤b` via `mul_le_mul_of_nonneg_left (inv a)`
//!      (`(inv a)·a ≤ (inv a)·b`) transported along `(inv a)·a = 1`.
//!   2. `h2 : inv b ≤ (inv b)·((inv a)·b)`. From `h1` via
//!      `mul_le_mul_of_nonneg_left (inv b)` (`(inv b)·1 ≤ (inv b)·((inv a)·b)`)
//!      transported along `(inv b)·1 = inv b`.
//!   3. `(inv b)·((inv a)·b) = inv a`: reassociate to `(inv a)·((inv b)·b)`,
//!      cancel `(inv b)·b = 1`, finish with `mul_one`. Transport `h2`'s RHS to
//!      land `inv b ≤ inv a`.
//!
//! # Universe note
//!
//! `Eq`/`Eq.refl`/`Eq.subst`/`Eq.trans`/`Eq.symm` over `Rat : Sort 1` are at
//! universe 1.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the dyadic telescoping layer.
pub(crate) struct CauchyConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_ofnat: Expr,
    // order / field bricks
    rat_mul_comm: Expr,
    rat_mul_assoc: Expr,
    rat_mul_one: Expr,
    rat_mul_inv_cancel: Expr,
    rat_mul_le_mul_of_nonneg_left: Expr,
    rat_inv_pos: Expr,
    rat_ne_zero_of_pos: Expr,
    rat_lt_of_lt_of_le: Expr,
    rat_lt_iff_le_not_le: Expr,
    rat_ofnat_le_ofnat_of_le: Expr,
    nat_pow_le_pow_right: Expr,
    // landed
    rat_zero_lt_ofnat_two_pow: Expr,
    // Eq machinery at universe 1.
    eq_rat: Expr,
    eq_refl: Expr,
    eq_subst: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    // And / Not / Iff for `0 ≤ x` extraction.
    and_c: Expr,
    and_left: Expr,
    not_c: Expr,
    iff_mp: Expr,
    nat_le: Expr,
}

impl CauchyConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_ofnat: k("Rat.ofNat"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            rat_mul_one: k("Rat.mul_one"),
            rat_mul_inv_cancel: k("Rat.mul_inv_cancel"),
            rat_mul_le_mul_of_nonneg_left: k("Rat.mul_le_mul_of_nonneg_left"),
            rat_inv_pos: k("Rat.inv_pos"),
            rat_ne_zero_of_pos: k("Rat.ne_zero_of_pos"),
            rat_lt_of_lt_of_le: k("Rat.lt_of_lt_of_le"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            rat_ofnat_le_ofnat_of_le: k("Rat.ofNat_le_ofNat_of_le"),
            nat_pow_le_pow_right: k("Nat.pow_le_pow_right"),
            rat_zero_lt_ofnat_two_pow: k("Rat.zero_lt_ofNat_two_pow"),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1]),
            and_c: k("And"),
            and_left: k("And.left"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
            nat_le: k("Nat.le"),
        }
    }

    // ── term constructors ───────────────────────────────────────────────────
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn nat_lit(&self, n: u32) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..n {
            e = self.succ(e);
        }
        e
    }
    fn npow2(&self, n: Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_lit(2), n])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn not_(&self, p: Expr) -> Expr {
        Expr::app(self.not_c.clone(), p)
    }
    fn and(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(self.and_c.clone(), [p, q])
    }
    fn ofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }

    // ── proof constructors ──────────────────────────────────────────────────
    fn eq_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat.clone(), a, b])
    }
    fn eq_refl(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.rat.clone(), a])
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn eq_subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    fn eq_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans.clone(),
            [self.rat.clone(), a, b, cc, hab, hbc],
        )
    }
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, cc])
    }
    /// `Rat.mul_one a : a·1 = a`.
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::app(self.rat_mul_one.clone(), a)
    }
    /// `Rat.mul_inv_cancel a h : a·(inv a) = 1`  (h : a = 0 → False).
    fn mul_inv_cancel(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_mul_inv_cancel.clone(), [a, h])
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c (h:b≤c)(ha:0≤a) : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(
            self.rat_mul_le_mul_of_nonneg_left.clone(),
            [a, b, cc, hbc, ha],
        )
    }
    /// `Rat.inv_pos b (0<b) : 0 < inv b`.
    fn inv_pos(&self, b: Expr, hpos: Expr) -> Expr {
        Expr::apps(self.rat_inv_pos.clone(), [b, hpos])
    }
    /// `Rat.ne_zero_of_pos b (0<b) : b = 0 → False`.
    fn ne_zero_of_pos(&self, b: Expr, hpos: Expr) -> Expr {
        Expr::apps(self.rat_ne_zero_of_pos.clone(), [b, hpos])
    }
    /// `Rat.lt_of_lt_of_le a b c (a<b)(b≤c) : a < c`.
    fn lt_of_lt_of_le(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.rat_lt_of_lt_of_le.clone(), [a, b, cc, h1, h2])
    }
    /// `0 ≤ x` from `0 < x`:  `And.left (Iff.mp (lt_iff_le_not_le 0 x) h)`.
    fn le_of_pos(&self, x: Expr, h_pos: Expr) -> Expr {
        let le0x = self.le(self.rat_zero.clone(), x.clone());
        let not_le_x0 = self.not_(self.le(x.clone(), self.rat_zero.clone()));
        let and_ty = self.and(le0x.clone(), not_le_x0.clone());
        let lt0x = self.lt(self.rat_zero.clone(), x.clone());
        let iff = Expr::apps(
            self.rat_lt_iff_le_not_le.clone(),
            [self.rat_zero.clone(), x],
        );
        let mp = Expr::apps(self.iff_mp.clone(), [lt0x, and_ty, iff, h_pos]);
        Expr::apps(self.and_left.clone(), [le0x, not_le_x0, mp])
    }
    /// `(inv b)·b = 1`  := `Eq.trans (mul_comm (inv b) b) (mul_inv_cancel b hb_ne)`.
    fn inv_mul_eq_one(&self, b: Expr, hb_ne: Expr) -> Expr {
        let inv_b = self.inv(b.clone());
        let invb_b = self.mul(inv_b.clone(), b.clone());
        let b_invb = self.mul(b.clone(), inv_b.clone());
        let comm = self.mul_comm(inv_b, b.clone());
        let cancel = self.mul_inv_cancel(b, hb_ne);
        self.eq_trans(invb_b, b_invb, self.rat_one.clone(), comm, cancel)
    }
}

impl Environment {
    /// Register the dyadic telescoping `IsCauchy` support layer. Idempotent.
    pub fn init_algebra_nnreal_sqrt_cauchy(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_and()?;
        self.init_iff()?;
        self.init_nat()?;
        // Rat.inv_pos / Rat.ne_zero_of_pos / Rat.zero_lt_ofNat_two_pow / inv_two_pow_succ.
        self.init_algebra_rat_inv_dyadic_step()?;
        // Rat.mul_comm / mul_assoc / mul_one / mul_inv_cancel.
        self.init_rat_field_inst()?;
        // Rat.mul_le_mul_of_nonneg_left.
        self.init_boolean_analysis_order_toolkit()?;
        // Rat.lt_of_lt_of_le.
        self.init_boolean_analysis_kkl_strictadd2()?;
        // Rat.lt_iff_le_not_le / Rat.le_total.
        self.init_rat_linear_order()?;
        self.register_rat_order_proofs()?;
        // Rat.ofNat_le_ofNat_of_le.
        self.register_rat_ofnat_le_ofnat_of_le()?;
        // Nat.pow_le_pow_right.
        self.register_nat_pow_le_pow_right_proof()?;

        let c = CauchyConsts::new();
        self.register_rat_inv_le_inv_of_le(&c)?;
        self.register_rat_inv_two_pow_le_of_le(&c)?;
        Ok(())
    }

    /// `Rat.inv_le_inv_of_le : ∀ a b, Rat.lt 0 a → Rat.le a b →
    ///     Rat.le (Rat.inv b) (Rat.inv a)`.
    fn register_rat_inv_le_inv_of_le(&mut self, c: &CauchyConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.inv_le_inv_of_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let zero = c.rat_zero.clone();
        let one = c.rat_one.clone();
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let hpos = c.lt(zero.clone(), a.clone());
            let (hp_id, _hp) = b.fresh_local(hpos.clone());
            let hab = c.le(a.clone(), bv.clone());
            let (hab_id, _hab) = b.fresh_local(hab.clone());
            let concl = c.le(c.inv(bv.clone()), c.inv(a.clone()));
            let e = b.mk_pi(hab_id, BinderInfo::Default, hab, concl);
            let e = b.mk_pi(hp_id, BinderInfo::Default, hpos, e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(c.rat.clone());
            let (bv_id, bv) = b.fresh_local(c.rat.clone());
            let hpos = c.lt(zero.clone(), a.clone());
            let (hp_id, hp) = b.fresh_local(hpos.clone());
            let hab_ty = c.le(a.clone(), bv.clone());
            let (hab_id, hab) = b.fresh_local(hab_ty.clone());

            let inv_a = c.inv(a.clone());
            let inv_b = c.inv(bv.clone());

            // 0<b := lt_of_lt_of_le 0 a b (0<a)(a≤b).
            let hb_pos =
                c.lt_of_lt_of_le(zero.clone(), a.clone(), bv.clone(), hp.clone(), hab.clone());
            // 0 ≤ inv a, 0 ≤ inv b.
            let inv_a_nonneg = c.le_of_pos(inv_a.clone(), c.inv_pos(a.clone(), hp.clone()));
            let inv_b_nonneg = c.le_of_pos(inv_b.clone(), c.inv_pos(bv.clone(), hb_pos.clone()));
            // a≠0, b≠0.
            let a_ne = c.ne_zero_of_pos(a.clone(), hp.clone());
            let b_ne = c.ne_zero_of_pos(bv.clone(), hb_pos.clone());

            // ── step1 : 1 ≤ (inv a)·b ────────────────────────────────────────
            let mle = c.mul_le_left(
                inv_a.clone(),
                a.clone(),
                bv.clone(),
                hab.clone(),
                inv_a_nonneg.clone(),
            );
            let inva_a = c.mul(inv_a.clone(), a.clone());
            let inva_b = c.mul(inv_a.clone(), bv.clone());
            let inva_a_eq_one = c.inv_mul_eq_one(a.clone(), a_ne);
            let motive1 = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.le(t, inva_b.clone());
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let step1 = c.eq_subst(motive1, inva_a.clone(), one.clone(), inva_a_eq_one, mle);

            // ── step2 : inv b ≤ (inv b)·((inv a)·b) ──────────────────────────
            let mle2 = c.mul_le_left(
                inv_b.clone(),
                one.clone(),
                inva_b.clone(),
                step1,
                inv_b_nonneg.clone(),
            );
            let invb_one = c.mul(inv_b.clone(), one.clone());
            let invb_inva_b = c.mul(inv_b.clone(), inva_b.clone());
            let invb_one_eq = c.mul_one(inv_b.clone());
            let motive2 = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.le(t, invb_inva_b.clone());
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let step2 = c.eq_subst(motive2, invb_one.clone(), inv_b.clone(), invb_one_eq, mle2);

            // ── step3 : (inv b)·((inv a)·b) = inv a ──────────────────────────
            let invb_inva = c.mul(inv_b.clone(), inv_a.clone());
            let invb_inva_times_b = c.mul(invb_inva.clone(), bv.clone());
            // e_assoc1 : (inv b)·((inv a)·b) = ((inv b)·(inv a))·b
            //   = Eq.symm (mul_assoc (inv b)(inv a) b).
            let assoc1 = c.mul_assoc(inv_b.clone(), inv_a.clone(), bv.clone());
            let e_assoc1 = c.eq_symm(invb_inva_times_b.clone(), invb_inva_b.clone(), assoc1);

            // e_comm : ((inv b)·(inv a))·b = ((inv a)·(inv b))·b
            //   transport mul_comm (inv b)(inv a) under motive (·)·b.
            let inva_invb = c.mul(inv_a.clone(), inv_b.clone());
            let inva_invb_times_b = c.mul(inva_invb.clone(), bv.clone());
            let comm = c.mul_comm(inv_b.clone(), inv_a.clone());
            let motive_c = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.eq_ty(invb_inva_times_b.clone(), c.mul(t, bv.clone()));
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let refl_base = c.eq_refl(invb_inva_times_b.clone());
            let e_comm = c.eq_subst(
                motive_c,
                invb_inva.clone(),
                inva_invb.clone(),
                comm,
                refl_base,
            );

            // e_assoc2 : ((inv a)·(inv b))·b = (inv a)·((inv b)·b).
            let invb_b = c.mul(inv_b.clone(), bv.clone());
            let inva_invb_b = c.mul(inv_a.clone(), invb_b.clone());
            let e_assoc2 = c.mul_assoc(inv_a.clone(), inv_b.clone(), bv.clone());

            // e_cancel : (inv a)·((inv b)·b) = (inv a)·1
            //   transport (inv b)·b = 1 under motive (inv a)·(·).
            let invb_b_eq_one = c.inv_mul_eq_one(bv.clone(), b_ne);
            let inva_one = c.mul(inv_a.clone(), one.clone());
            let motive_cancel = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.eq_ty(inva_invb_b.clone(), c.mul(inv_a.clone(), t));
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let refl_base2 = c.eq_refl(inva_invb_b.clone());
            let e_cancel = c.eq_subst(
                motive_cancel,
                invb_b.clone(),
                one.clone(),
                invb_b_eq_one,
                refl_base2,
            );

            // e_mulone : (inv a)·1 = inv a  := mul_one (inv a).
            let e_mulone = c.mul_one(inv_a.clone());

            // chain: (inv b)·((inv a)·b) = inv a.
            let t1 = c.eq_trans(
                invb_inva_b.clone(),
                invb_inva_times_b.clone(),
                inva_invb_times_b.clone(),
                e_assoc1,
                e_comm,
            );
            let t2 = c.eq_trans(
                invb_inva_b.clone(),
                inva_invb_times_b.clone(),
                inva_invb_b.clone(),
                t1,
                e_assoc2,
            );
            let t3 = c.eq_trans(
                invb_inva_b.clone(),
                inva_invb_b.clone(),
                inva_one.clone(),
                t2,
                e_cancel,
            );
            let step3 = c.eq_trans(
                invb_inva_b.clone(),
                inva_one.clone(),
                inv_a.clone(),
                t3,
                e_mulone,
            );

            // transport step2's RHS → inv a along step3:  motive t := inv b ≤ t.
            let motive_final = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.le(inv_b.clone(), t);
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let body = c.eq_subst(
                motive_final,
                invb_inva_b.clone(),
                inv_a.clone(),
                step3,
                step2,
            );

            let e = b.mk_lam(hab_id, BinderInfo::Default, hab_ty, body);
            let e = b.mk_lam(hp_id, BinderInfo::Default, hpos, e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.inv_two_pow_le_of_le : ∀ N n, Nat.le N n →
    ///     Rat.le (Rat.inv (Rat.ofNat (Nat.pow 2 n)))
    ///            (Rat.inv (Rat.ofNat (Nat.pow 2 N)))`.
    fn register_rat_inv_two_pow_le_of_le(&mut self, c: &CauchyConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.inv_two_pow_le_of_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let two_nat = c.nat_lit(2);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (cap_id, cap) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hle = c.nat_le(cap.clone(), n.clone());
            let (hle_id, _h) = b.fresh_local(hle.clone());
            let d_n = c.ofnat(c.npow2(n.clone()));
            let d_cap = c.ofnat(c.npow2(cap.clone()));
            let concl = c.le(c.inv(d_n), c.inv(d_cap));
            let e = b.mk_pi(hle_id, BinderInfo::Default, hle, concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(cap_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (cap_id, cap) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hle_ty = c.nat_le(cap.clone(), n.clone());
            let (hle_id, hle) = b.fresh_local(hle_ty.clone());

            let pow_cap = c.npow2(cap.clone());
            let pow_n = c.npow2(n.clone());
            let d_cap = c.ofnat(pow_cap.clone());
            let d_n = c.ofnat(pow_n.clone());

            // 1 ≤ 2 (Nat): Nat.le.step (Nat.le.refl 1) : Nat.le 1 (succ 1).
            let nat_le_refl_one = Expr::app(
                Expr::const_(Name::from_string("Nat.le.refl"), vec![]),
                c.nat_lit(1),
            );
            let one_le_two_nat = Expr::apps(
                Expr::const_(Name::from_string("Nat.le.step"), vec![]),
                [c.nat_lit(1), c.nat_lit(1), nat_le_refl_one],
            );
            // 2^cap ≤ 2^n (Nat).
            let nat_pow_le = Expr::apps(
                c.nat_pow_le_pow_right.clone(),
                [two_nat.clone(), cap.clone(), n.clone(), one_le_two_nat, hle],
            );
            // ofNat 2^cap ≤ ofNat 2^n (Rat).
            let rat_pow_le = Expr::apps(
                c.rat_ofnat_le_ofnat_of_le.clone(),
                [pow_cap.clone(), pow_n.clone(), nat_pow_le],
            );
            // 0 < ofNat 2^cap.
            let d_cap_pos = Expr::app(c.rat_zero_lt_ofnat_two_pow.clone(), cap.clone());
            // inv_le_inv_of_le (ofNat 2^cap)(ofNat 2^n)(0<d_cap)(d_cap≤d_n) : inv d_n ≤ inv d_cap.
            let body = Expr::apps(
                Expr::const_(Name::from_string("Rat.inv_le_inv_of_le"), vec![]),
                [d_cap, d_n, d_cap_pos, rat_pow_le],
            );

            let e = b.mk_lam(hle_id, BinderInfo::Default, hle_ty, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["Rat.inv_le_inv_of_le", "Rat.inv_two_pow_le_of_le"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_sqrt_cauchy()
            .expect("init_algebra_nnreal_sqrt_cauchy");
        env.init_algebra_nnreal_sqrt_cauchy().expect("idempotent");
        env
    }

    #[test]
    fn test_rat_sqrt_cauchy_present_and_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_rat_sqrt_cauchy_theorems_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
