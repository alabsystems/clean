// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer (ported from the sqrt layer; cbrtDyadicApprox mirrors dyadicApprox) — the dyadic approximation is NONDECREASING
//! (Stage B3, sqrt run #4, rung 6b).
//!
//! # Why this module exists
//!
//! The telescoping `IsCauchy` for `a_n := ofNat(k_n)·inv(2^n)` (plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md` §8.5 rung 6) needs the
//! per-step monotonicity `a_n ≤ a_{n+1}` (the LOWER side of the two-sided
//! bound). This module proves it from the LANDED digit-step lower bound
//! `Rat.cbrtDyadicNum_two_mul_le_succ` (`2k_n ≤ k_{n+1}`) and the LANDED inv step
//! factorization `Rat.inv_two_pow_succ`.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.cbrtDyadicApprox_le_succ : ∀ x n,
//!       Rat.le (Rat.cbrtDyadicApprox x n) (Rat.cbrtDyadicApprox x (Nat.succ n))`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # Proof
//!
//! `a_{n+1} = ofNat(k_{n+1})·iv_s`, `a_n = ofNat(k_n)·iv_n` where
//! `iv_n := inv(ofNat 2^n)`, `iv_s := inv(ofNat 2^{n+1})`.
//!   1. `2k_n ≤ k_{n+1}` (digit bound) ⟹ `ofNat(2k_n) ≤ ofNat(k_{n+1})`
//!      (`ofNat_le_ofNat_of_le`).
//!   2. Multiply right by `iv_s ≥ 0`: `ofNat(2k_n)·iv_s ≤ a_{n+1}`
//!      (`mul_le_mul_of_nonneg_right`).
//!   3. `ofNat(2k_n)·iv_s = a_n`: `ofNat(2k_n) = ofNat 2·ofNat k_n`
//!      (`ofNat_mul`); `iv_s = iv_n·inv 2` (`inv_two_pow_succ`); reassociate
//!      `(ofNat 2·ofNat k_n)·(iv_n·inv 2) = (ofNat 2·inv 2)·(ofNat k_n·iv_n)`
//!      (`mul_comm` + `mul_mul_mul_comm`); `ofNat 2·inv 2 = 1`
//!      (`mul_inv_cancel`); `1·(ofNat k_n·iv_n) = a_n` (`one_mul`). Transport
//!      step 2's LHS to `a_n`.
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

/// Pre-resolved handles for the dyadic monotonicity rung.
pub(crate) struct CbrtMonoStepConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_mul: Expr,
    nat_pow: Expr,
    rat: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_ofnat: Expr,
    rat_dyadic_num: Expr,
    rat_dyadic_approx: Expr,
    rat_ofnat_mul: Expr,
    rat_inv_two_pow_succ: Expr,
    rat_mul_comm: Expr,
    rat_mul_mul_mul_comm: Expr,
    rat_mul_inv_cancel: Expr,
    rat_one_mul: Expr,
    rat_mul_le_mul_of_nonneg_right: Expr,
    rat_ofnat_le_ofnat_of_le: Expr,
    rat_ne_zero_of_pos: Expr,
    rat_zero_lt_ofnat_two_pow: Expr,
    rat_zero_lt_inv_two_pow: Expr,
    rat_lt_iff_le_not_le: Expr,
    rat_dyadic_num_two_mul_le_succ: Expr,
    eq_rat: Expr,
    eq_refl: Expr,
    eq_subst: Expr,
    eq_trans: Expr,
    and_c: Expr,
    and_left: Expr,
    not_c: Expr,
    iff_mp: Expr,
}

impl CbrtMonoStepConsts {
    pub(crate) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_mul: k("Nat.mul"),
            nat_pow: k("Nat.pow"),
            rat: k("Rat"),
            rat_one: k("Rat.one"),
            rat_zero: k("Rat.zero"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_ofnat: k("Rat.ofNat"),
            rat_dyadic_num: k("Rat.cbrtDyadicNum"),
            rat_dyadic_approx: k("Rat.cbrtDyadicApprox"),
            rat_ofnat_mul: k("Rat.ofNat_mul"),
            rat_inv_two_pow_succ: k("Rat.inv_two_pow_succ"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_mul_mul_comm: k("Rat.mul_mul_mul_comm"),
            rat_mul_inv_cancel: k("Rat.mul_inv_cancel"),
            rat_one_mul: k("Rat.one_mul"),
            rat_mul_le_mul_of_nonneg_right: k("Rat.mul_le_mul_of_nonneg_right"),
            rat_ofnat_le_ofnat_of_le: k("Rat.ofNat_le_ofNat_of_le"),
            rat_ne_zero_of_pos: k("Rat.ne_zero_of_pos"),
            rat_zero_lt_ofnat_two_pow: k("Rat.zero_lt_ofNat_two_pow"),
            rat_zero_lt_inv_two_pow: k("Rat.zero_lt_inv_two_pow"),
            rat_lt_iff_le_not_le: k("Rat.lt_iff_le_not_le"),
            rat_dyadic_num_two_mul_le_succ: k("Rat.cbrtDyadicNum_two_mul_le_succ"),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1]),
            and_c: k("And"),
            and_left: k("And.left"),
            not_c: k("Not"),
            iff_mp: k("Iff.mp"),
        }
    }

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
    fn nmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_mul.clone(), [a, b])
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
    fn dnum(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_num.clone(), [x.clone(), n])
    }
    fn approx(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_approx.clone(), [x.clone(), n])
    }
    fn eq_ty(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_rat.clone(), [self.rat.clone(), a, b])
    }
    fn eq_refl(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl.clone(), [self.rat.clone(), a])
    }
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
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.rat_mul_mul_mul_comm.clone(), [a, b, cc, d])
    }
    fn mul_inv_cancel(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_mul_inv_cancel.clone(), [a, h])
    }
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(self.rat_one_mul.clone(), a)
    }
    /// `ofNat_mul m n : ofNat (Nat.mul m n) = ofNat m · ofNat n`.
    fn ofnat_mul(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_ofnat_mul.clone(), [m, n])
    }
    /// `inv_two_pow_succ n : inv(ofNat 2^{n+1}) = inv(ofNat 2^n)·inv(ofNat 2)`.
    fn inv_two_pow_succ(&self, n: Expr) -> Expr {
        Expr::app(self.rat_inv_two_pow_succ.clone(), n)
    }
    /// `mul_le_mul_of_nonneg_right a b c (h:b≤c)(ha:0≤a) : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, ha: Expr) -> Expr {
        Expr::apps(
            self.rat_mul_le_mul_of_nonneg_right.clone(),
            [a, b, cc, hbc, ha],
        )
    }
    fn ofnat_le(&self, m: Expr, n: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_ofnat_le_ofnat_of_le.clone(), [m, n, h])
    }
    fn ne_zero_of_pos(&self, b: Expr, hpos: Expr) -> Expr {
        Expr::apps(self.rat_ne_zero_of_pos.clone(), [b, hpos])
    }
    /// `0 ≤ x` from `0 < x`.
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
}

impl Environment {
    /// Register `Rat.cbrtDyadicApprox_le_succ`. Idempotent; axiom-free.
    pub fn init_algebra_nnreal_cbrt_cauchy_mono(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_and()?;
        self.init_iff()?;
        self.init_nat()?;
        // Rat.cbrtDyadicApprox + Rat.cbrtDyadicNum + Rat.ofNat.
        self.init_algebra_nnreal_cbrt_seq()?;
        // Rat.cbrtDyadicNum_two_mul_le_succ (digit lower bound).
        self.init_algebra_nnreal_cbrt_mono()?;
        // Rat.inv_two_pow_succ + Rat.zero_lt_inv_two_pow + Rat.zero_lt_ofNat_two_pow.
        self.init_algebra_rat_inv_dyadic_step()?;
        // Rat.ofNat_mul.
        self.register_rat_ofnat_mul()?;
        // Rat.mul_comm / one_mul / mul_inv_cancel.
        self.init_rat_field_inst()?;
        // Rat.mul_mul_mul_comm.
        self.register_rat_mul_mul_mul_comm_theorem()?;
        // Rat.mul_le_mul_of_nonneg_right.
        self.init_boolean_analysis_order_toolkit()?;
        // Rat.ofNat_le_ofNat_of_le.
        self.register_rat_ofnat_le_ofnat_of_le()?;
        self.init_rat_linear_order()?;

        let c = CbrtMonoStepConsts::new();
        self.register_cbrt_dyadic_approx_le_succ(&c)?;
        Ok(())
    }

    fn register_cbrt_dyadic_approx_le_succ(
        &mut self,
        c: &CbrtMonoStepConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.cbrtDyadicApprox_le_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let two = c.nat_lit(2);
        let of2 = c.ofnat(two.clone());
        let one = c.rat_one.clone();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let concl = c.le(c.approx(&x, n.clone()), c.approx(&x, c.succ(n.clone())));
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());

            let kn = c.dnum(&x, n.clone());
            let ks = c.dnum(&x, c.succ(n.clone()));
            let two_kn = c.nmul(two.clone(), kn.clone());
            let iv_n = c.inv(c.ofnat(c.npow2(n.clone())));
            let iv_s = c.inv(c.ofnat(c.npow2(c.succ(n.clone()))));
            let ofnat_kn = c.ofnat(kn.clone());
            let ofnat_ks = c.ofnat(ks.clone());
            let ofnat_2kn = c.ofnat(two_kn.clone());

            // a_n (defeq ofNat(k_n)·iv_n), a_s (defeq ofNat(k_s)·iv_s).
            let a_n = c.mul(ofnat_kn.clone(), iv_n.clone());

            // iv_s ≥ 0.
            let iv_s_pos = Expr::app(c.rat_zero_lt_inv_two_pow.clone(), c.succ(n.clone()));
            let iv_s_nonneg = c.le_of_pos(iv_s.clone(), iv_s_pos);

            // step1: ofNat(2k_n) ≤ ofNat(k_s).
            let hdig = Expr::apps(
                c.rat_dyadic_num_two_mul_le_succ.clone(),
                [x.clone(), n.clone()],
            );
            let hofnat = c.ofnat_le(two_kn.clone(), ks.clone(), hdig);

            // step2: ofNat(2k_n)·iv_s ≤ ofNat(k_s)·iv_s (= a_s defeq).
            let lhs2 = c.mul(ofnat_2kn.clone(), iv_s.clone());
            let rhs2 = c.mul(ofnat_ks.clone(), iv_s.clone());
            let hmul = c.mul_le_right(
                iv_s.clone(),
                ofnat_2kn.clone(),
                ofnat_ks.clone(),
                hofnat,
                iv_s_nonneg,
            );
            // hmul : lhs2 ≤ rhs2.  rhs2 is defeq a_s.

            // ── heq : ofNat(2k_n)·iv_s = a_n ─────────────────────────────────
            // e1 : ofNat(2k_n) = ofNat 2·ofNat k_n.
            let e1 = c.ofnat_mul(two.clone(), kn.clone());
            let of2_kn = c.mul(of2.clone(), ofnat_kn.clone());
            // L0 : ofNat(2k_n)·iv_s = (ofNat 2·ofNat k_n)·iv_s
            //   transport e1 under motive t := lhs2 = (t·iv_s); base refl.
            let l0 = {
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.eq_ty(lhs2.clone(), c.mul(t, iv_s.clone()));
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.eq_subst(
                    motive,
                    ofnat_2kn.clone(),
                    of2_kn.clone(),
                    e1,
                    c.eq_refl(lhs2.clone()),
                )
            };
            // e2 : iv_s = iv_n·inv 2.
            let e2 = c.inv_two_pow_succ(n.clone());
            let ivn_inv2 = c.mul(iv_n.clone(), c.inv(of2.clone()));
            // L1 : (ofNat 2·ofNat k_n)·iv_s = (ofNat 2·ofNat k_n)·(iv_n·inv 2)
            //   transport e2 under motive t := (of2_kn·iv_s) = (of2_kn·t); base refl.
            let of2kn_ivs = c.mul(of2_kn.clone(), iv_s.clone());
            let l1 = {
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.eq_ty(of2kn_ivs.clone(), c.mul(of2_kn.clone(), t));
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.eq_subst(
                    motive,
                    iv_s.clone(),
                    ivn_inv2.clone(),
                    e2,
                    c.eq_refl(of2kn_ivs.clone()),
                )
            };
            // L2 : (ofNat 2·ofNat k_n)·(iv_n·inv 2)
            //      = (ofNat 2·ofNat k_n)·(inv 2·iv_n)
            //   transport (mul_comm iv_n inv2) under motive t := (of2_kn·ivn_inv2) = (of2_kn·t).
            let inv2_ivn = c.mul(c.inv(of2.clone()), iv_n.clone());
            let of2kn_ivn_inv2 = c.mul(of2_kn.clone(), ivn_inv2.clone());
            let l2 = {
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.eq_ty(of2kn_ivn_inv2.clone(), c.mul(of2_kn.clone(), t));
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.eq_subst(
                    motive,
                    ivn_inv2.clone(),
                    inv2_ivn.clone(),
                    c.mul_comm(iv_n.clone(), c.inv(of2.clone())),
                    c.eq_refl(of2kn_ivn_inv2.clone()),
                )
            };
            // L3 : (ofNat 2·ofNat k_n)·(inv 2·iv_n) = (ofNat 2·inv 2)·(ofNat k_n·iv_n)
            //   = mul_mul_mul_comm (ofNat 2)(ofNat k_n)(inv 2)(iv_n).
            let of2_inv2 = c.mul(of2.clone(), c.inv(of2.clone()));
            let l3 = c.mmmc(
                of2.clone(),
                ofnat_kn.clone(),
                c.inv(of2.clone()),
                iv_n.clone(),
            );
            // L4 : (ofNat 2·inv 2)·(ofNat k_n·iv_n) = 1·(ofNat k_n·iv_n)
            //   transport (ofNat 2·inv 2 = 1) under motive t := (of2_inv2·a_n) = (t·a_n).
            let of2_ne = c.ne_zero_of_pos(
                of2.clone(),
                Expr::app(c.rat_zero_lt_ofnat_two_pow.clone(), c.nat_lit(1)),
            );
            // ofNat 2 ≡ ofNat (2^1) defeq, so zero_lt_ofNat_two_pow 1 : 0 < ofNat 2.
            let of2_inv2_eq_one = c.mul_inv_cancel(of2.clone(), of2_ne);
            let of2inv2_an = c.mul(of2_inv2.clone(), a_n.clone());
            let one_an = c.mul(one.clone(), a_n.clone());
            let l4 = {
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.eq_ty(of2inv2_an.clone(), c.mul(t, a_n.clone()));
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.eq_subst(
                    motive,
                    of2_inv2.clone(),
                    one.clone(),
                    of2_inv2_eq_one,
                    c.eq_refl(of2inv2_an.clone()),
                )
            };
            // L5 : 1·(ofNat k_n·iv_n) = ofNat k_n·iv_n = a_n  := one_mul a_n.
            let l5 = c.one_mul(a_n.clone());

            // chain heq : ofNat(2k_n)·iv_s = a_n.
            let t01 = c.eq_trans(
                lhs2.clone(),
                of2kn_ivs.clone(),
                of2kn_ivn_inv2.clone(),
                l0,
                l1,
            );
            let t012 = c.eq_trans(
                lhs2.clone(),
                of2kn_ivn_inv2.clone(),
                of2inv2_an.clone(),
                t01,
                {
                    // L2 then L3: (of2_kn·(inv2·iv_n)) = (of2_inv2·a_n).
                    // L2 : of2kn_ivn_inv2 = of2_kn·(inv2·iv_n); L3 : that = of2_inv2·a_n.
                    let of2kn_inv2ivn = c.mul(of2_kn.clone(), inv2_ivn.clone());
                    c.eq_trans(
                        of2kn_ivn_inv2.clone(),
                        of2kn_inv2ivn,
                        of2inv2_an.clone(),
                        l2,
                        l3,
                    )
                },
            );
            let t0123 = c.eq_trans(lhs2.clone(), of2inv2_an.clone(), one_an.clone(), t012, l4);
            let heq = c.eq_trans(lhs2.clone(), one_an.clone(), a_n.clone(), t0123, l5);

            // Transport hmul's LHS lhs2 → a_n along heq: motive t := t ≤ rhs2.
            let motive_final = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.le(t, rhs2.clone());
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let body = c.eq_subst(motive_final, lhs2.clone(), a_n.clone(), heq, hmul);
            // body : a_n ≤ rhs2  (rhs2 defeq a_s = approx x (succ n)).

            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
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

    const THEOREMS: &[&str] = &["Rat.cbrtDyadicApprox_le_succ"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cbrt_cauchy_mono()
            .expect("init_algebra_nnreal_cbrt_cauchy_mono");
        env.init_algebra_nnreal_cbrt_cauchy_mono()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_dyadic_mono_step_present_and_kernel_check() {
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
    fn test_dyadic_mono_step_constructive_empty_closure() {
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
