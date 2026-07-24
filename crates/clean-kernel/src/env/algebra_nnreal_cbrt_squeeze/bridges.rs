// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cube scale bridges: `(ofNat 2^n)³ = 8^n`, `0 < 8^n`, `(inv 2^n)³ = inv(8^n)`,
//! and `a_n³ = ((ofNat k_n)³)·inv(8^n)`. The cube analogues of the sqrt layer's
//! `bridges.rs` (`²`/`4^n`).

use super::CbrtSqueezeConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl CbrtSqueezeConsts {
    /// Regroup `((a·b)·(a·b))·(a·b) = ((a·a)·a)·((b·b)·b)` as a `Rat` `Eq`.
    /// (Used with `a := tp`, `b := of2` for the pow8 bridge step, and `a := k_n`,
    /// `b := iv` for the cube_eq.) Mirrors the `cube_scale` regroup but with both
    /// factors generic. Built from two `mul_mul_mul_comm` + transports.
    pub(super) fn cube_regroup(&self, parent: &EnvDeclBuilder, a: &Expr, b: &Expr) -> Expr {
        let ab = self.mul(a.clone(), b.clone()); // A := a·b
        let cube_ab = self.cube(ab.clone()); // (A·A)·A
        let aa = self.mul(a.clone(), a.clone());
        let bb = self.mul(b.clone(), b.clone());
        // mmmc a b a b : (a·b)·(a·b) = (a·a)·(b·b) =: P.
        let p = self.mul(aa.clone(), bb.clone());
        let mmmc1 = self.mmmc(a.clone(), b.clone(), a.clone(), b.clone());
        // s1 : (A·A)·A = P·A   congr (· · A) mmmc1.
        let f1 = self.f_right(parent, ab.clone());
        let aa_ab = self.mul(ab.clone(), ab.clone());
        let s1 = self.congr_arg(aa_ab.clone(), p.clone(), f1, mmmc1);
        let p_a = self.mul(p.clone(), ab.clone());
        // mmmc (a·a)(b·b) a b : ((a·a)·(b·b))·(a·b) = ((a·a)·a)·((b·b)·b) =: Q.
        let mmmc2 = self.mmmc(aa.clone(), bb.clone(), a.clone(), b.clone());
        let aaa = self.mul(aa.clone(), a.clone()); // (a·a)·a
        let bbb = self.mul(bb.clone(), b.clone()); // (b·b)·b
        let q = self.mul(aaa.clone(), bbb.clone());
        // chain: (A·A)·A = P·A = Q.
        self.trans(cube_ab, p_a, q, s1, mmmc2)
    }

    fn f_right(&self, parent: &EnvDeclBuilder, t: Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(self.rat.clone());
        let body = self.mul(w, t);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.rat.clone(), body))
    }
    fn f_left(&self, parent: &EnvDeclBuilder, t: Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(self.rat.clone());
        let body = self.mul(t, w);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.rat.clone(), body))
    }
    pub(super) fn s_f_right(&self, parent: &EnvDeclBuilder, t: Expr) -> Expr {
        self.f_right(parent, t)
    }
    pub(super) fn s_f_left(&self, parent: &EnvDeclBuilder, t: Expr) -> Expr {
        self.f_left(parent, t)
    }
}

impl Environment {
    /// `Rat.ofNat_two_pow_cube_eq_pow8 : ∀ n, ((ofNat 2^n)·(ofNat 2^n))·(ofNat 2^n)
    ///   = cbrtDyadicPow8 n`. `Nat.rec`.
    pub(crate) fn register_ofnat_two_pow_cube_eq_pow8(
        &mut self,
        c: &CbrtSqueezeConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.ofNat_two_pow_cube_eq_pow8");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let goal = |n: &Expr| c.eq(c.cube(c.two_pow(n.clone())), c.pow8(n.clone()));
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), goal(&n)))
        };
        let value = build_cube_pow8_value(c, &goal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.zero_lt_cbrtDyadicPow8 : ∀ n, 0 < cbrtDyadicPow8 n`.
    /// `mul_pos ((tp·tp)) tp (0<tp·tp)(0<tp)`, transported along the bridge.
    pub(crate) fn register_zero_lt_cbrt_dyadic_pow8(
        &mut self,
        c: &CbrtSqueezeConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.zero_lt_cbrtDyadicPow8");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let bridge = Expr::const_(Name::from_string("Rat.ofNat_two_pow_cube_eq_pow8"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let concl = c.lt(c.rat_zero.clone(), c.pow8(n.clone()));
            b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let tp = c.two_pow(n.clone());
            let tptp = c.mul(tp.clone(), tp.clone());
            let cube = c.cube(tp.clone()); // (tp·tp)·tp
            let h_tptp = c.mul_pos(
                tp.clone(),
                tp.clone(),
                c.zero_lt_two_pow(n.clone()),
                c.zero_lt_two_pow(n.clone()),
            ); // 0 < tp·tp
            let h_cube = c.mul_pos(
                tptp.clone(),
                tp.clone(),
                h_tptp,
                c.zero_lt_two_pow(n.clone()),
            ); // 0 < (tp·tp)·tp
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = d.fresh_local(c.rat.clone());
                let body = c.lt(c.rat_zero.clone(), t);
                d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let h_eq = Expr::app(bridge.clone(), n.clone());
            let pow8 = c.pow8(n.clone());
            let body = c.subst(motive, cube, pow8, h_eq, h_cube);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.inv_two_pow_cube_eq_inv_pow8 : ∀ n,
    ///   (inv(2^n)·inv(2^n))·inv(2^n) = inv(cbrtDyadicPow8 n)`.
    /// `(inv tp · inv tp)·inv tp = inv((tp·tp)·tp)` (two `mul_inv` symm) then
    /// `congrArg Rat.inv` of the pow8 bridge.
    pub(crate) fn register_inv_two_pow_cube_eq_inv_pow8(
        &mut self,
        c: &CbrtSqueezeConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.inv_two_pow_cube_eq_inv_pow8");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let bridge = Expr::const_(Name::from_string("Rat.ofNat_two_pow_cube_eq_pow8"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let iv = c.inv_two_pow(n.clone());
            let lhs = c.cube(iv);
            let rhs = c.inv(c.pow8(n.clone()));
            b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), c.eq(lhs, rhs)))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let tp = c.two_pow(n.clone());
            let tptp = c.mul(tp.clone(), tp.clone());
            let cube_tp = c.cube(tp.clone()); // (tp·tp)·tp
            let iv = c.inv_two_pow(n.clone());
            let iviv = c.mul(iv.clone(), iv.clone());
            let cube_iv = c.cube(iv.clone()); // (iv·iv)·iv
            let hne = c.two_pow_ne_zero(n.clone());
            let hne_tptp = {
                // tp·tp ≠ 0 from mul_pos positivity.
                let h_pos = c.mul_pos(
                    tp.clone(),
                    tp.clone(),
                    c.zero_lt_two_pow(n.clone()),
                    c.zero_lt_two_pow(n.clone()),
                );
                Expr::apps(c.rat_ne_zero_of_pos.clone(), [tptp.clone(), h_pos])
            };
            // mul_inv tp tp : inv(tp·tp) = inv tp · inv tp.  symm → iv·iv = inv(tp·tp).
            let h_mi1 = c.mul_inv(tp.clone(), tp.clone(), hne.clone(), hne.clone());
            let h_iviv_eq = c.symm(c.inv(tptp.clone()), iviv.clone(), h_mi1); // iv·iv = inv(tp·tp)
                                                                              // mul_inv (tp·tp) tp : inv((tp·tp)·tp) = inv(tp·tp)·inv tp.  symm.
            let h_mi2 = c.mul_inv(tptp.clone(), tp.clone(), hne_tptp, hne.clone());
            let inv_tptp_inv_tp = c.mul(c.inv(tptp.clone()), iv.clone());
            let h_step2 = c.symm(c.inv(cube_tp.clone()), inv_tptp_inv_tp.clone(), h_mi2);
            // inv(cube_tp) = inv(tp·tp)·inv tp  (h_step2 is that).
            // Now: cube_iv = (iv·iv)·iv. Rewrite iv·iv → inv(tp·tp) via h_iviv_eq:
            //   congr (· · iv) h_iviv_eq : (iv·iv)·iv = inv(tp·tp)·iv.
            let f_iv = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (w_id, w) = d.fresh_local(c.rat.clone());
                let body = c.mul(w, iv.clone());
                d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let s_cube = c.congr_arg(iviv.clone(), c.inv(tptp.clone()), f_iv, h_iviv_eq);
            // s_cube : cube_iv = inv(tp·tp)·iv = inv_tptp_inv_tp.
            // h_step2 : inv_tptp_inv_tp = inv(cube_tp)  (symm of h_mi2).
            // chain: cube_iv = inv_tptp_inv_tp = inv(cube_tp).
            let chain1 = c.trans(
                cube_iv.clone(),
                inv_tptp_inv_tp.clone(),
                c.inv(cube_tp.clone()),
                s_cube,
                h_step2,
            );
            // congrArg Rat.inv (bridge n) : inv(cube_tp) = inv(pow8 n).
            let pow8 = c.pow8(n.clone());
            let h_eq = Expr::app(bridge.clone(), n.clone());
            let h_congr = c.congr_arg(cube_tp.clone(), pow8.clone(), c.rat_inv.clone(), h_eq);
            let body = c.trans(
                cube_iv.clone(),
                c.inv(cube_tp.clone()),
                c.inv(pow8.clone()),
                chain1,
                h_congr,
            );
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.cbrtDyadicApprox_cube_eq : ∀ x n,
    ///   a_n³ = ((ofNat k_n · ofNat k_n)·ofNat k_n)·inv(8^n)`,
    /// where `a_n = ofNat k_n · inv(2^n)`.
    pub(crate) fn register_cbrt_dyadic_approx_cube_eq(
        &mut self,
        c: &CbrtSqueezeConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.cbrtDyadicApprox_cube_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let inv_cube_bridge = Expr::const_(
            Name::from_string("Rat.inv_two_pow_cube_eq_inv_pow8"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let a = c.approx(&x, n.clone());
            let kn = c.ofnat(c.cnum(&x, n.clone()));
            let rhs = c.mul(c.cube(kn), c.inv(c.pow8(n.clone())));
            let concl = c.eq(c.cube(a), rhs);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());

            let kn = c.ofnat(c.cnum(&x, n.clone()));
            let iv = c.inv_two_pow(n.clone());
            // a_n ≡ kn·iv defeq.
            let a_kn_iv = c.mul(kn.clone(), iv.clone());
            let cube_a = c.cube(a_kn_iv.clone()); // ((kn·iv)·(kn·iv))·(kn·iv)
            let cube_kn = c.cube(kn.clone()); // (kn·kn)·kn
            let cube_iv = c.cube(iv.clone()); // (iv·iv)·iv

            // regroup : cube_a = cube_kn · cube_iv  (cube_regroup kn iv).
            let regroup = c.cube_regroup(&b, &kn, &iv);
            let cube_kn_cube_iv = c.mul(cube_kn.clone(), cube_iv.clone());
            // step : congr (cube_kn · ·) (inv_cube_bridge n) :
            //   cube_kn·cube_iv = cube_kn·inv(8^n).
            let pow8_inv = c.inv(c.pow8(n.clone()));
            let h_invcube = Expr::app(inv_cube_bridge.clone(), n.clone());
            let f_left = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = d.fresh_local(c.rat.clone());
                let body = c.mul(cube_kn.clone(), t);
                d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let step = c.congr_arg(cube_iv.clone(), pow8_inv.clone(), f_left, h_invcube);
            let rhs = c.mul(cube_kn.clone(), pow8_inv.clone());
            let body = c.trans(cube_a, cube_kn_cube_iv, rhs, regroup, step);

            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body);
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

/// `fun n => Nat.rec motive base step n` for `ofNat_two_pow_cube_eq_pow8`.
fn build_cube_pow8_value(c: &CbrtSqueezeConsts, goal: &dyn Fn(&Expr) -> Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();

    // motive : fun n => ((tp·tp)·tp) = 8^n.
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = m.fresh_local(c.nat.clone());
        m.finish_child(m.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), goal(&n)))
    };

    // BASE n=0: ((1·1)·1) = 1.  ((tp0·tp0)·tp0) with tp0 ≡ 1, 8^0 ≡ 1.
    //   (1·1)·1 = (1·1) (mul_one) ; (1·1) = 1 (mul_one). chain.
    let base = {
        let tp0 = c.two_pow(c.nat_zero.clone()); // ≡ Rat.one
        let tp0_tp0 = c.mul(tp0.clone(), tp0.clone());
        let cube0 = c.mul(tp0_tp0.clone(), tp0.clone()); // ((1·1)·1)
                                                         // mul_one (tp0·tp0) : (tp0·tp0)·tp0 = tp0·tp0.
        let e1 = c.mul_one(tp0_tp0.clone());
        // mul_one tp0 : tp0·tp0 = tp0.  (defeq: 8^0 ≡ Rat.one ≡ tp0.)
        let e2 = c.mul_one(tp0.clone());
        c.trans(cube0, tp0_tp0.clone(), tp0.clone(), e1, e2)
    };

    // STEP.
    let step = {
        let mut s = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = s.fresh_local(c.nat.clone());
        let ih_ty = goal(&n);
        let (ih_id, ih) = s.fresh_local(ih_ty.clone());

        let tp = c.two_pow(n.clone()); // ofNat(2^n)
        let two = c.ofnat(c.nat_lit(2));
        let eight = c.ofnat(c.nat_lit(8));
        let pow8n = c.pow8(n.clone());

        let tp_succ = c.two_pow(c.succ(n.clone())); // ofNat(2^{n+1})
                                                    // e1 : ofNat(Nat.mul (2^n) 2) = tp·two  (ofNat_mul); LHS defeq tp_succ.
        let e1 = c.ofnat_mul(c.npow2(n.clone()), c.nat_lit(2));
        let tp_two = c.mul(tp.clone(), two.clone());

        // chain on ((tp·two)³): cube_regroup tp two : ((tp·two)·(tp·two))·(tp·two)
        //   = ((tp·tp)·tp)·((two·two)·two).
        let regroup = c.cube_regroup(&s, &tp, &two);
        let cube_tp = c.cube(tp.clone()); // (tp·tp)·tp
        let cube_two = c.cube(two.clone()); // (two·two)·two
        let cube_tp_cube_two = c.mul(cube_tp.clone(), cube_two.clone());

        // (two·two)·two = ofNat 8:  two·two = ofNat4 (symm ofNat_mul 2 2);
        //   ofNat4·two = ofNat8 (symm ofNat_mul 4 2).
        let four = c.ofnat(c.nat_lit(4));
        let two_two = c.mul(two.clone(), two.clone());
        let e_22 = c.ofnat_mul(c.nat_lit(2), c.nat_lit(2)); // ofNat4 = two·two
        let e_22_symm = c.symm(four.clone(), two_two.clone(), e_22); // two·two = ofNat4
        let f_r2 = c.s_f_right(&s, two.clone());
        let s_a = c.congr_arg(two_two.clone(), four.clone(), f_r2, e_22_symm); // (two·two)·two = ofNat4·two
        let four_two = c.mul(four.clone(), two.clone());
        let e_42 = c.ofnat_mul(c.nat_lit(4), c.nat_lit(2)); // ofNat8 = ofNat4·two
        let e_42_symm = c.symm(eight.clone(), four_two.clone(), e_42); // ofNat4·two = ofNat8
        let cube2_eq_8 = c.trans(
            cube_two.clone(),
            four_two.clone(),
            eight.clone(),
            s_a,
            e_42_symm,
        );
        // congr (cube_tp · ·) cube2_eq_8 : cube_tp·cube_two = cube_tp·ofNat8.
        let f_l = c.s_f_left(&s, cube_tp.clone());
        let step_b = c.congr_arg(cube_two.clone(), eight.clone(), f_l, cube2_eq_8);
        let cube_tp_8 = c.mul(cube_tp.clone(), eight.clone());
        // congr (· · ofNat8) ih : cube_tp·ofNat8 = 8^n·ofNat8.
        let f_ih = c.s_f_right(&s, eight.clone());
        let step_c = c.congr_arg(cube_tp.clone(), pow8n.clone(), f_ih, ih.clone());
        let pow8_8 = c.mul(pow8n.clone(), eight.clone());
        // mul_comm 8^n ofNat8 : 8^n·ofNat8 = ofNat8·8^n  (≡ 8^{n+1} defeq).
        let step_d = c.mul_comm(pow8n.clone(), eight.clone());
        let eight_pow8 = c.mul(eight.clone(), pow8n.clone());

        // assemble: (tp·two)³ = cube_tp·cube_two (regroup)
        //   = cube_tp·ofNat8 (step_b) = 8^n·ofNat8 (step_c) = ofNat8·8^n (step_d).
        let p0 = c.cube(tp_two.clone());
        let t1 = c.trans(
            p0.clone(),
            cube_tp_cube_two.clone(),
            cube_tp_8.clone(),
            regroup,
            step_b,
        );
        let t2 = c.trans(p0.clone(), cube_tp_8.clone(), pow8_8.clone(), t1, step_c);
        let chain = c.trans(p0.clone(), pow8_8.clone(), eight_pow8.clone(), t2, step_d);
        // chain : (tp·two)³ = ofNat8·8^n ≡ 8^{n+1}.

        // Transport to tp_succ³ via e1 (tp_succ ≡ ofNat(2^{n+1}) = tp·two).
        let ofnat_2sn = c.ofnat(c.npow2(c.succ(n.clone()))); // surface tp_succ
        let e1_symm = c.symm(ofnat_2sn.clone(), tp_two.clone(), e1); // tp·two = tp_succ
        let motive_t = {
            let mut d = EnvDeclBuilder::child_of(&s);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.eq(c.cube(t.clone()), c.pow8(c.succ(n.clone())));
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let goal_succ = c.subst(motive_t, tp_two.clone(), tp_succ.clone(), e1_symm, chain);

        let e = s.mk_lam(ih_id, BinderInfo::Default, ih_ty, goal_succ);
        s.finish_child(s.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
    };

    let (n_id, n) = b.fresh_local(c.nat.clone());
    let rec = Expr::apps(c.nat_rec_prop.clone(), [motive, base, step, n.clone()]);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec))
}
