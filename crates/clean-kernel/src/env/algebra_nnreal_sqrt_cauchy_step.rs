// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — the per-step UPPER bound `a_{n+1} ≤ a_n + inv(2^{n+1})`
//! (Stage B3, sqrt run #4, rung 6c).
//!
//! # Why this module exists
//!
//! The telescoping `IsCauchy` step (plan
//! `designs/2026-06-18-kkl-real-sqrt-layer-plan.md` §8.5 rung 6) needs the
//! per-step UPPER increment bound: the dyadic approximation grows by at most
//! `inv(2^{n+1})` from `n` to `n+1`. With the matching LOWER bound (the landed
//! `Rat.dyadicApprox_le_succ`) this pins the increment into `[0, inv(2^{n+1})]`.
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - `Rat.ofNat_two_mul_inv_two_pow_succ : ∀ k n,
//!       Rat.mul (ofNat (Nat.mul 2 k)) (inv (ofNat 2^{n+1}))
//!         = Rat.mul (ofNat k) (inv (ofNat 2^n))`
//!   — the reusable "halving" identity (`(2k)/2^{n+1} = k/2^n`).
//! - `Rat.dyadicApprox_succ_le : ∀ x n,
//!       Rat.le (Rat.dyadicApprox x (Nat.succ n))
//!              (Rat.add (Rat.dyadicApprox x n) (inv (ofNat 2^{n+1})))`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.
//!
//! # Proof of `dyadicApprox_succ_le`
//!
//! `a_{n+1} = ofNat(k_{n+1})·iv_s`; the UPPER digit bound
//! `k_{n+1} ≤ 2k_n + 1` (`dyadicNum_succ_le_two_mul_succ`) ⟹ (cast)
//! `ofNat(k_{n+1}) ≤ ofNat(succ(2k_n))`; multiply right by `iv_s ≥ 0`:
//! `a_{n+1} ≤ ofNat(succ(2k_n))·iv_s`. Then
//! `ofNat(succ(2k_n))·iv_s = (ofNat(2k_n) + 1)·iv_s` (`add_natCast_one ⁻¹`)
//! `= ofNat(2k_n)·iv_s + 1·iv_s` (`right_distrib`)
//! `= a_n + iv_s` (the halving identity + `one_mul`). Transport.
//!
//! # Universe note
//!
//! `Eq`/`Eq.refl`/`Eq.subst`/`Eq.trans` over `Rat : Sort 1` are at universe 1.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles for the per-step upper-bound rung.
pub(crate) struct StepConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_mul: Expr,
    nat_pow: Expr,
    rat: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_ofnat: Expr,
    rat_dyadic_num: Expr,
    rat_dyadic_approx: Expr,
    rat_ofnat_mul: Expr,
    rat_inv_two_pow_succ: Expr,
    rat_add_natcast_one: Expr,
    rat_right_distrib: Expr,
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
    rat_dyadic_num_succ_le_two_mul_succ: Expr,
    rat_ofnat_two_mul_inv_two_pow_succ: Expr,
    eq_rat: Expr,
    eq_refl: Expr,
    eq_subst: Expr,
    eq_trans: Expr,
    eq_symm: Expr,
    and_c: Expr,
    and_left: Expr,
    not_c: Expr,
    iff_mp: Expr,
}

impl StepConsts {
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
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_ofnat: k("Rat.ofNat"),
            rat_dyadic_num: k("Rat.dyadicNum"),
            rat_dyadic_approx: k("Rat.dyadicApprox"),
            rat_ofnat_mul: k("Rat.ofNat_mul"),
            rat_inv_two_pow_succ: k("Rat.inv_two_pow_succ"),
            rat_add_natcast_one: k("Rat.add_natCast_one"),
            rat_right_distrib: k("Rat.right_distrib"),
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
            rat_dyadic_num_succ_le_two_mul_succ: k("Rat.dyadicNum_succ_le_two_mul_succ"),
            rat_ofnat_two_mul_inv_two_pow_succ: k("Rat.ofNat_two_mul_inv_two_pow_succ"),
            eq_rat: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_subst: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1]),
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
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
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
    fn eq_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    fn mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.rat_mul_mul_mul_comm.clone(), [a, b, cc, d])
    }
    fn mul_inv_cancel(&self, a: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_mul_inv_cancel.clone(), [a, h])
    }
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(self.rat_one_mul.clone(), a)
    }
    fn ofnat_mul(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_ofnat_mul.clone(), [m, n])
    }
    fn inv_two_pow_succ(&self, n: Expr) -> Expr {
        Expr::app(self.rat_inv_two_pow_succ.clone(), n)
    }
    /// `right_distrib a b c : (a+b)·c = a·c + b·c`.
    fn right_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_right_distrib.clone(), [a, b, cc])
    }
    /// `add_natCast_one k : ofNat k + 1 = ofNat (succ k)`
    /// (stated over `Rat.mk (Int.ofNat k) 1` ≡ `ofNat k`).
    fn add_natcast_one(&self, k: Expr) -> Expr {
        Expr::app(self.rat_add_natcast_one.clone(), k)
    }
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
    /// Register the per-step upper-bound rung. Idempotent; axiom-free.
    pub fn init_algebra_nnreal_sqrt_cauchy_step(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_and()?;
        self.init_iff()?;
        self.init_nat()?;
        self.init_algebra_nnreal_sqrt_seq()?; // dyadicApprox, dyadicNum, ofNat
        self.init_algebra_nnreal_sqrt_mono()?; // dyadicNum_succ_le_two_mul_succ
        self.init_algebra_rat_inv_dyadic_step()?; // inv_two_pow_succ, zero_lt_inv_two_pow, zero_lt_ofNat_two_pow
        self.register_rat_ofnat_mul()?;
        self.init_rat_field_inst()?; // mul_comm, one_mul, mul_inv_cancel, right_distrib
        self.register_rat_mul_mul_mul_comm_theorem()?;
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_right
        self.register_rat_ofnat_le_ofnat_of_le()?;
        self.register_fin_sum_const_one_theorems()?; // Rat.add_natCast_one
        self.init_rat_linear_order()?;

        let c = StepConsts::new();
        self.register_ofnat_two_mul_inv_two_pow_succ(&c)?;
        self.register_dyadic_approx_succ_le(&c)?;
        Ok(())
    }

    /// `Rat.ofNat_two_mul_inv_two_pow_succ : ∀ k n,
    ///   (ofNat (Nat.mul 2 k)) · inv(ofNat 2^{n+1}) = (ofNat k) · inv(ofNat 2^n)`.
    ///
    /// The halving identity. Same 5-link chain as the monotone step but with `k`
    /// a free `Nat` parameter (so it is reusable).
    fn register_ofnat_two_mul_inv_two_pow_succ(&mut self, c: &StepConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.ofNat_two_mul_inv_two_pow_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let two = c.nat_lit(2);
        let of2 = c.ofnat(two.clone());
        let one = c.rat_one.clone();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, kk) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let two_k = c.nmul(two.clone(), kk.clone());
            let iv_s = c.inv(c.ofnat(c.npow2(c.succ(n.clone()))));
            let iv_n = c.inv(c.ofnat(c.npow2(n.clone())));
            let lhs = c.mul(c.ofnat(two_k), iv_s);
            let rhs = c.mul(c.ofnat(kk.clone()), iv_n);
            let concl = c.eq_ty(lhs, rhs);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, kk) = b.fresh_local(c.nat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());

            let two_k = c.nmul(two.clone(), kk.clone());
            let iv_n = c.inv(c.ofnat(c.npow2(n.clone())));
            let iv_s = c.inv(c.ofnat(c.npow2(c.succ(n.clone()))));
            let ofnat_k = c.ofnat(kk.clone());
            let ofnat_2k = c.ofnat(two_k.clone());
            let a_n = c.mul(ofnat_k.clone(), iv_n.clone());

            let lhs = c.mul(ofnat_2k.clone(), iv_s.clone());
            let of2_k = c.mul(of2.clone(), ofnat_k.clone());
            let of2k_ivs = c.mul(of2_k.clone(), iv_s.clone());
            let ivn_inv2 = c.mul(iv_n.clone(), c.inv(of2.clone()));
            let of2kn_ivn_inv2 = c.mul(of2_k.clone(), ivn_inv2.clone());
            let inv2_ivn = c.mul(c.inv(of2.clone()), iv_n.clone());
            let of2kn_inv2ivn = c.mul(of2_k.clone(), inv2_ivn.clone());
            let of2_inv2 = c.mul(of2.clone(), c.inv(of2.clone()));
            let of2inv2_an = c.mul(of2_inv2.clone(), a_n.clone());
            let one_an = c.mul(one.clone(), a_n.clone());

            // L0 : ofNat(2k)·iv_s = (ofNat2·ofNat k)·iv_s  (ofNat_mul on left).
            let e1 = c.ofnat_mul(two.clone(), kk.clone());
            let l0 = {
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.eq_ty(lhs.clone(), c.mul(t, iv_s.clone()));
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.eq_subst(
                    motive,
                    ofnat_2k.clone(),
                    of2_k.clone(),
                    e1,
                    c.eq_refl(lhs.clone()),
                )
            };
            // L1 : (ofNat2·ofNat k)·iv_s = (ofNat2·ofNat k)·(iv_n·inv2)  (inv_two_pow_succ).
            let e2 = c.inv_two_pow_succ(n.clone());
            let l1 = {
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.eq_ty(of2k_ivs.clone(), c.mul(of2_k.clone(), t));
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.eq_subst(
                    motive,
                    iv_s.clone(),
                    ivn_inv2.clone(),
                    e2,
                    c.eq_refl(of2k_ivs.clone()),
                )
            };
            // L2 : (ofNat2·ofNat k)·(iv_n·inv2) = (ofNat2·ofNat k)·(inv2·iv_n)  (mul_comm).
            let l2 = {
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.eq_ty(of2kn_ivn_inv2.clone(), c.mul(of2_k.clone(), t));
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
            // L3 : (ofNat2·ofNat k)·(inv2·iv_n) = (ofNat2·inv2)·(ofNat k·iv_n)  (mmmc).
            let l3 = c.mmmc(
                of2.clone(),
                ofnat_k.clone(),
                c.inv(of2.clone()),
                iv_n.clone(),
            );
            // L4 : (ofNat2·inv2)·a_n = 1·a_n  (cancel ofNat2·inv2=1).
            let of2_ne = c.ne_zero_of_pos(
                of2.clone(),
                Expr::app(c.rat_zero_lt_ofnat_two_pow.clone(), c.nat_lit(1)),
            );
            let of2_inv2_eq_one = c.mul_inv_cancel(of2.clone(), of2_ne);
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
            // L5 : 1·a_n = a_n  (one_mul).
            let l5 = c.one_mul(a_n.clone());

            let t01 = c.eq_trans(
                lhs.clone(),
                of2k_ivs.clone(),
                of2kn_ivn_inv2.clone(),
                l0,
                l1,
            );
            let t012 = c.eq_trans(
                lhs.clone(),
                of2kn_ivn_inv2.clone(),
                of2inv2_an.clone(),
                t01,
                {
                    c.eq_trans(
                        of2kn_ivn_inv2.clone(),
                        of2kn_inv2ivn.clone(),
                        of2inv2_an.clone(),
                        l2,
                        l3,
                    )
                },
            );
            let t0123 = c.eq_trans(lhs.clone(), of2inv2_an.clone(), one_an.clone(), t012, l4);
            let body = c.eq_trans(lhs.clone(), one_an.clone(), a_n.clone(), t0123, l5);

            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.dyadicApprox_succ_le : ∀ x n,
    ///   le (dyadicApprox x (succ n)) (add (dyadicApprox x n) (inv(ofNat 2^{n+1})))`.
    fn register_dyadic_approx_succ_le(&mut self, c: &StepConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.dyadicApprox_succ_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let two = c.nat_lit(2);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let iv_s = c.inv(c.ofnat(c.npow2(c.succ(n.clone()))));
            let rhs = c.add(c.approx(&x, n.clone()), iv_s);
            let concl = c.le(c.approx(&x, c.succ(n.clone())), rhs);
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
            let succ_two_kn = c.succ(two_kn.clone());
            let iv_n = c.inv(c.ofnat(c.npow2(n.clone())));
            let iv_s = c.inv(c.ofnat(c.npow2(c.succ(n.clone()))));
            let ofnat_ks = c.ofnat(ks.clone());
            let ofnat_succ_2kn = c.ofnat(succ_two_kn.clone());
            let ofnat_2kn = c.ofnat(two_kn.clone());
            let a_n = c.mul(c.ofnat(kn.clone()), iv_n.clone());

            // iv_s ≥ 0.
            let iv_s_pos = Expr::app(c.rat_zero_lt_inv_two_pow.clone(), c.succ(n.clone()));
            let iv_s_nonneg = c.le_of_pos(iv_s.clone(), iv_s_pos);

            // hdig : k_s ≤ succ(2k_n).
            let hdig = Expr::apps(
                c.rat_dyadic_num_succ_le_two_mul_succ.clone(),
                [x.clone(), n.clone()],
            );
            let hofnat = c.ofnat_le(ks.clone(), succ_two_kn.clone(), hdig);
            // hmul : ofNat(k_s)·iv_s ≤ ofNat(succ 2k_n)·iv_s.  LHS defeq a_{n+1}.
            let lhs_mul = c.mul(ofnat_ks.clone(), iv_s.clone());
            let rhs_mul = c.mul(ofnat_succ_2kn.clone(), iv_s.clone());
            let hmul = c.mul_le_right(
                iv_s.clone(),
                ofnat_ks.clone(),
                ofnat_succ_2kn.clone(),
                hofnat,
                iv_s_nonneg,
            );
            // hmul : lhs_mul ≤ rhs_mul.

            // ── heq : ofNat(succ 2k_n)·iv_s = a_n + iv_s ─────────────────────
            // p1 : ofNat(succ 2k_n) = ofNat(2k_n) + 1  := Eq.symm (add_natCast_one (2k_n)).
            // add_natCast_one (2k_n) : (ofNat 2k_n) + 1 = ofNat (succ 2k_n).
            let ofnat_2kn_plus_one = c.add(ofnat_2kn.clone(), c.rat_one.clone());
            let ancl = c.add_natcast_one(two_kn.clone());
            let p1 = c.eq_symm(ofnat_2kn_plus_one.clone(), ofnat_succ_2kn.clone(), ancl);
            // L0 : ofNat(succ 2k_n)·iv_s = (ofNat 2k_n + 1)·iv_s
            //   transport p1 under motive t := rhs_mul = (t·iv_s); base refl.
            let plus_one_ivs = c.mul(ofnat_2kn_plus_one.clone(), iv_s.clone());
            let l0 = {
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.eq_ty(rhs_mul.clone(), c.mul(t, iv_s.clone()));
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.eq_subst(
                    motive,
                    ofnat_succ_2kn.clone(),
                    ofnat_2kn_plus_one.clone(),
                    p1,
                    c.eq_refl(rhs_mul.clone()),
                )
            };
            // L1 : (ofNat 2k_n + 1)·iv_s = ofNat(2k_n)·iv_s + 1·iv_s  (right_distrib).
            let of2kn_ivs = c.mul(ofnat_2kn.clone(), iv_s.clone());
            let one_ivs = c.mul(c.rat_one.clone(), iv_s.clone());
            let distrib_rhs = c.add(of2kn_ivs.clone(), one_ivs.clone());
            let l1 = c.right_distrib(ofnat_2kn.clone(), c.rat_one.clone(), iv_s.clone());
            // L2 : ofNat(2k_n)·iv_s + 1·iv_s = a_n + 1·iv_s
            //   transport (ofNat(2k_n)·iv_s = a_n) under motive t := distrib_rhs = (t + 1·iv_s).
            let halving = Expr::apps(
                c.rat_ofnat_two_mul_inv_two_pow_succ.clone(),
                [kn.clone(), n.clone()],
            );
            // halving : ofNat(Nat.mul 2 k_n)·iv_s = ofNat k_n·iv_n = a_n.
            let an_plus_one_ivs = c.add(a_n.clone(), one_ivs.clone());
            let l2 = {
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.eq_ty(distrib_rhs.clone(), c.add(t, one_ivs.clone()));
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.eq_subst(
                    motive,
                    of2kn_ivs.clone(),
                    a_n.clone(),
                    halving,
                    c.eq_refl(distrib_rhs.clone()),
                )
            };
            // L3 : a_n + 1·iv_s = a_n + iv_s   transport (1·iv_s = iv_s) under motive t := an_plus_one_ivs = (a_n + t).
            let an_plus_ivs = c.add(a_n.clone(), iv_s.clone());
            let one_mul_ivs = c.one_mul(iv_s.clone());
            let l3 = {
                let motive = {
                    let mut mb = EnvDeclBuilder::child_of(&b);
                    let (t_id, t) = mb.fresh_local(c.rat.clone());
                    let body = c.eq_ty(an_plus_one_ivs.clone(), c.add(a_n.clone(), t));
                    mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                c.eq_subst(
                    motive,
                    one_ivs.clone(),
                    iv_s.clone(),
                    one_mul_ivs,
                    c.eq_refl(an_plus_one_ivs.clone()),
                )
            };

            // chain heq : ofNat(succ 2k_n)·iv_s = a_n + iv_s.
            let t01 = c.eq_trans(
                rhs_mul.clone(),
                plus_one_ivs.clone(),
                distrib_rhs.clone(),
                l0,
                l1,
            );
            let t012 = c.eq_trans(
                rhs_mul.clone(),
                distrib_rhs.clone(),
                an_plus_one_ivs.clone(),
                t01,
                l2,
            );
            let heq = c.eq_trans(
                rhs_mul.clone(),
                an_plus_one_ivs.clone(),
                an_plus_ivs.clone(),
                t012,
                l3,
            );

            // transport hmul's RHS rhs_mul → (a_n + iv_s) along heq:
            //   motive t := lhs_mul ≤ t.  (lhs_mul defeq a_{n+1}.)
            let motive_final = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.le(lhs_mul.clone(), t);
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let body = c.eq_subst(
                motive_final,
                rhs_mul.clone(),
                an_plus_ivs.clone(),
                heq,
                hmul,
            );

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

    const THEOREMS: &[&str] = &[
        "Rat.ofNat_two_mul_inv_two_pow_succ",
        "Rat.dyadicApprox_succ_le",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_sqrt_cauchy_step()
            .expect("init_algebra_nnreal_sqrt_cauchy_step");
        env.init_algebra_nnreal_sqrt_cauchy_step()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_dyadic_step_present_and_kernel_check() {
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
    fn test_dyadic_step_constructive_empty_closure() {
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
