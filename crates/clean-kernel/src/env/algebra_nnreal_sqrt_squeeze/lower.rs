// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rung 7a-lower + 7b — the LOWER squeeze `a_n·a_n ≤ x` (the floor never
//! overshoots) and its consequence `a_n ≤ 1` on `x < 1`.

use super::SqueezeConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl SqueezeConsts {
    /// `0 ≤ inv(dyadicPow4 n)` from `0 < dyadicPow4 n` (rung) via `inv_pos` +
    /// `le_of_lt`.
    pub(super) fn zero_le_inv_pow4(&self, n: &Expr) -> Expr {
        let pow4 = self.pow4(n.clone());
        let h_pos = Expr::app(
            Expr::const_(Name::from_string("Rat.zero_lt_dyadicPow4"), vec![]),
            n.clone(),
        );
        let inv_pos = Expr::apps(
            Expr::const_(Name::from_string("Rat.inv_pos"), vec![]),
            [pow4.clone(), h_pos],
        );
        self.le_of_lt(self.inv(pow4), inv_pos)
    }

    /// `(b = 0 → False)` for `b := dyadicPow4 n` from positivity.
    pub(super) fn pow4_ne_zero(&self, n: &Expr) -> Expr {
        let pow4 = self.pow4(n.clone());
        let h_pos = Expr::app(
            Expr::const_(Name::from_string("Rat.zero_lt_dyadicPow4"), vec![]),
            n.clone(),
        );
        Expr::apps(self.rat_ne_zero_of_pos.clone(), [pow4, h_pos])
    }
}

impl Environment {
    /// `Rat.dyadicApprox_sq_le : ∀ x, 0≤x → ∀ n, a_n·a_n ≤ x`.
    ///
    /// `dyadicNum_sq_le x h0 n : (kn·kn) ≤ x·4^n`. Multiply by `inv(4^n) ≥ 0`
    /// (right): `(kn·kn)·inv(4^n) ≤ (x·4^n)·inv(4^n)`. Rewrite RHS
    /// `(x·4^n)·inv(4^n) = x·(4^n·inv 4^n) = x·1 = x`; rewrite LHS by
    /// `dyadicApprox_sq_eq` (symm) to `a_n·a_n`.
    pub(crate) fn register_dyadic_approx_sq_le(
        &mut self,
        c: &SqueezeConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.dyadicApprox_sq_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let dnum_sq_le = Expr::const_(Name::from_string("Rat.dyadicNum_sq_le"), vec![]);
        let sq_eq = Expr::const_(Name::from_string("Rat.dyadicApprox_sq_eq"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let h0_ty = c.le(c.rat_zero.clone(), x.clone());
            let (h0_id, _h0) = b.fresh_local(h0_ty.clone());
            let inner = {
                let mut ib = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = ib.fresh_local(c.nat.clone());
                let a = c.approx(&x, n.clone());
                let concl = c.le(c.mul(a.clone(), a), x.clone());
                ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
            };
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, inner);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let h0_ty = c.le(c.rat_zero.clone(), x.clone());
            let (h0_id, h0) = b.fresh_local(h0_ty.clone());
            let inner = {
                let mut ib = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = ib.fresh_local(c.nat.clone());

                let kn = c.ofnat(c.dnum(&x, n.clone()));
                let kk = c.mul(kn.clone(), kn.clone());
                let pow4 = c.pow4(n.clone());
                let x_pow4 = c.mul(x.clone(), pow4.clone());
                let inv4 = c.inv(pow4.clone());

                // h_inv : (kn·kn) ≤ x·4^n.
                let h_inv = Expr::apps(dnum_sq_le.clone(), [x.clone(), h0.clone(), n.clone()]);
                // h_mul : (kn·kn)·inv4 ≤ (x·4^n)·inv4   (mul_le_right inv4 kk (x·4^n) h_inv 0≤inv4).
                let h0_inv4 = c.zero_le_inv_pow4(&n);
                let h_mul =
                    c.mul_le_right(inv4.clone(), kk.clone(), x_pow4.clone(), h_inv, h0_inv4);

                // RHS rewrite: (x·4^n)·inv4 = x·(4^n·inv4) = x·1 = x.
                //   e_assoc : (x·4^n)·inv4 = x·(4^n·inv4).
                let e_assoc = c.mul_assoc(x.clone(), pow4.clone(), inv4.clone());
                //   cancel : 4^n·inv4 = 1   (mul_inv_cancel pow4 ne).
                let cancel = c.mul_inv_cancel(pow4.clone(), c.pow4_ne_zero(&n));
                //   congr (x·_) cancel : x·(4^n·inv4) = x·1.
                let pow4_inv4 = c.mul(pow4.clone(), inv4.clone());
                let f_x = {
                    let mut d = EnvDeclBuilder::child_of(&ib);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.mul(x.clone(), t);
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let e_congr = c.congr_arg(pow4_inv4.clone(), c.rat_one.clone(), f_x, cancel);
                //   mul_one x : x·1 = x.
                let e_mulone = c.mul_one(x.clone());
                //   chain RHS = x: (x·4^n)·inv4 = x·(4^n·inv4) = x·1 = x.
                let x_pow4_inv4 = c.mul(x_pow4.clone(), inv4.clone());
                let x_times1 = c.mul(x.clone(), c.rat_one.clone());
                let x_times_cancel = c.mul(x.clone(), pow4_inv4.clone());
                let rhs_t1 = c.trans(
                    x_pow4_inv4.clone(),
                    x_times_cancel.clone(),
                    x_times1.clone(),
                    e_assoc,
                    e_congr,
                );
                let rhs_eq_x = c.trans(
                    x_pow4_inv4.clone(),
                    x_times1.clone(),
                    x.clone(),
                    rhs_t1,
                    e_mulone,
                );

                // Transport h_mul along rhs_eq_x (right side) → (kn·kn)·inv4 ≤ x.
                //   motive_r (fun t => (kn·kn)·inv4 ≤ t).
                let kk_inv4 = c.mul(kk.clone(), inv4.clone());
                let motive_r = {
                    let mut d = EnvDeclBuilder::child_of(&ib);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.le(kk_inv4.clone(), t);
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let h_kk_le_x = c.subst(motive_r, x_pow4_inv4.clone(), x.clone(), rhs_eq_x, h_mul);

                // LHS rewrite: a_n·a_n = (kn·kn)·inv4 (dyadicApprox_sq_eq);
                //   transport h_kk_le_x along symm to get a_n·a_n ≤ x.
                let a = c.approx(&x, n.clone());
                let aa = c.mul(a.clone(), a.clone());
                let h_sq_eq = Expr::apps(sq_eq.clone(), [x.clone(), n.clone()]); // aa = kk·inv4
                let h_sq_eq_symm = c.symm(aa.clone(), kk_inv4.clone(), h_sq_eq); // kk·inv4 = aa
                let motive_l = {
                    let mut d = EnvDeclBuilder::child_of(&ib);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.le(t, x.clone());
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let body = c.subst(
                    motive_l,
                    kk_inv4.clone(),
                    aa.clone(),
                    h_sq_eq_symm,
                    h_kk_le_x,
                );

                ib.finish_child(ib.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, inner);
            b.finish(b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.dyadicApprox_le_one : ∀ x, 0≤x → x<1 → ∀ n, a_n ≤ 1`.
    ///
    /// `a_n·a_n ≤ x < 1 = 1·1`, so `a_n·a_n ≤ 1·1`; `le_of_sq_le_sq a_n 1
    /// (0≤a_n)(0≤1)` gives `a_n ≤ 1`.
    pub(crate) fn register_dyadic_approx_le_one(
        &mut self,
        c: &SqueezeConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.dyadicApprox_le_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let sq_le = Expr::const_(Name::from_string("Rat.dyadicApprox_sq_le"), vec![]);
        let zero_le_a = Expr::const_(Name::from_string("Rat.zero_le_dyadicApprox"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let h0_ty = c.le(c.rat_zero.clone(), x.clone());
            let (h0_id, _h0) = b.fresh_local(h0_ty.clone());
            let h1_ty = c.lt(x.clone(), c.rat_one.clone());
            let (h1_id, _h1) = b.fresh_local(h1_ty.clone());
            let inner = {
                let mut ib = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = ib.fresh_local(c.nat.clone());
                let a = c.approx(&x, n.clone());
                let concl = c.le(a, c.rat_one.clone());
                ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
            };
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, inner);
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e))
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let h0_ty = c.le(c.rat_zero.clone(), x.clone());
            let (h0_id, h0) = b.fresh_local(h0_ty.clone());
            let h1_ty = c.lt(x.clone(), c.rat_one.clone());
            let (h1_id, h1) = b.fresh_local(h1_ty.clone());
            let inner = {
                let mut ib = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = ib.fresh_local(c.nat.clone());

                let a = c.approx(&x, n.clone());
                let aa = c.mul(a.clone(), a.clone());
                let one = c.rat_one.clone();
                let one_one = c.mul(one.clone(), one.clone());

                // h_aa_le_x : a·a ≤ x.
                let h_aa_le_x = Expr::apps(sq_le.clone(), [x.clone(), h0.clone(), n.clone()]);
                // h_x_lt_1 : x < 1 (h1).
                // h_aa_lt_1 : a·a < 1   (lt_of_le_of_lt (a·a) x 1 h_aa_le_x h1).
                let h_aa_lt_1 =
                    c.lt_of_le_of_lt(aa.clone(), x.clone(), one.clone(), h_aa_le_x, h1.clone());
                // weaken to a·a ≤ 1 via the generic lt→le, then 1 = 1·1 to land
                // a·a ≤ 1·1.
                let h_aa_le_1 = c.le_of_lt_generic(aa.clone(), one.clone(), h_aa_lt_1);
                // 1 = 1·1: symm (mul_one 1).
                let e_1_eq_11 = c.symm(one_one.clone(), one.clone(), c.mul_one(one.clone()));
                // transport h_aa_le_1 : a·a ≤ 1 along (1 = 1·1) → a·a ≤ 1·1.
                let motive_r = {
                    let mut d = EnvDeclBuilder::child_of(&ib);
                    let (t_id, t) = d.fresh_local(c.rat.clone());
                    let body = c.le(aa.clone(), t);
                    d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let h_aa_le_11 =
                    c.subst(motive_r, one.clone(), one_one.clone(), e_1_eq_11, h_aa_le_1);

                // le_of_sq_le_sq a 1 (0≤a)(0≤1)(a·a ≤ 1·1) : a ≤ 1.
                let h0a = Expr::apps(zero_le_a.clone(), [x.clone(), n.clone()]);
                let h01 = c.zero_le_one();
                let body = c.le_of_sq_le_sq(a.clone(), one.clone(), h0a, h01, h_aa_le_11);

                ib.finish_child(ib.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, inner);
            let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
            b.finish(b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}
