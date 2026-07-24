// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rung 7b-upper — the UPPER squeeze
//! `x < a_n·a_n + (inv(2^n)+inv(2^n)+inv(2^n))` on `0 ≤ x < 1`, plus the small
//! `inv(2^n) ≤ 1` helper it consumes.

use super::SqueezeConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// `Rat.inv_two_pow_le_one : ∀ n, inv(ofNat 2^n) ≤ 1`.
    ///
    /// `inv_le_inv_of_le 1 (ofNat 2^n) (0<1)(1 ≤ ofNat 2^n) : inv(ofNat 2^n) ≤
    /// inv 1`; then `inv 1 = 1` (`1·inv 1 = 1` by `mul_inv_cancel`, `1·inv 1 =
    /// inv 1` by `one_mul`) transports the bound to `≤ 1`.
    pub(crate) fn register_inv_two_pow_le_one(
        &mut self,
        c: &SqueezeConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.inv_two_pow_le_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let inv_le_inv = Expr::const_(Name::from_string("Rat.inv_le_inv_of_le"), vec![]);
        let one_le_tp = Expr::const_(Name::from_string("Rat.one_le_ofNat_two_pow"), vec![]);
        let zero_lt_one = Expr::const_(Name::from_string("Rat.zero_lt_one"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let concl = c.le(c.inv_two_pow(n.clone()), c.rat_one.clone());
            b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let one = c.rat_one.clone();
            let tp = c.two_pow(n.clone());
            let inv_tp = c.inv(tp.clone());
            let inv_one = c.inv(one.clone());

            // h_le : inv(ofNat 2^n) ≤ inv 1.
            let h1le = Expr::app(one_le_tp.clone(), n.clone()); // 1 ≤ ofNat 2^n
            let h_le = Expr::apps(
                inv_le_inv.clone(),
                [one.clone(), tp.clone(), zero_lt_one.clone(), h1le],
            );

            // inv 1 = 1:  inv 1 = 1·inv 1 (symm one_mul) = 1 (mul_inv_cancel).
            let one_ne = Expr::apps(
                c.rat_ne_zero_of_pos.clone(),
                [one.clone(), zero_lt_one.clone()],
            );
            let one_mul_inv1 = c.mul(one.clone(), inv_one.clone());
            let e_om = c.one_mul(inv_one.clone()); // 1·inv 1 = inv 1
            let e_om_symm = c.symm(one_mul_inv1.clone(), inv_one.clone(), e_om); // inv 1 = 1·inv 1
            let e_cancel = c.mul_inv_cancel(one.clone(), one_ne); // 1·inv 1 = 1
            let e_inv1_eq_1 = c.trans(
                inv_one.clone(),
                one_mul_inv1.clone(),
                one.clone(),
                e_om_symm,
                e_cancel,
            ); // inv 1 = 1

            // transport h_le : inv_tp ≤ inv 1 along (inv 1 = 1) → inv_tp ≤ 1.
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = d.fresh_local(c.rat.clone());
                let body = c.le(inv_tp.clone(), t);
                d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let body = c.subst(motive, inv_one.clone(), one.clone(), e_inv1_eq_1, h_le);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.x_lt_dyadicApprox_sq_add_three_inv :
    ///   ∀ x, 0≤x → x<1 → ∀ n, x < a_n·a_n + (inv(2^n)+inv(2^n)+inv(2^n))`.
    pub(crate) fn register_x_lt_dyadic_approx_sq_add(
        &mut self,
        c: &SqueezeConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.x_lt_dyadicApprox_sq_add_three_inv");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
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
                let iv = c.inv_two_pow(n.clone());
                let three_iv = c.add(c.add(iv.clone(), iv.clone()), iv.clone());
                let concl = c.lt(x.clone(), c.add(c.mul(a.clone(), a), three_iv));
                ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
            };
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, inner);
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = build_upper_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// The proof term for `x_lt_dyadicApprox_sq_add_three_inv`.
fn build_upper_value(c: &SqueezeConsts) -> Expr {
    let dnum_sq_lt = Expr::const_(Name::from_string("Rat.dyadicNum_sq_lt_succ"), vec![]);
    let inv_sq_bridge = Expr::const_(Name::from_string("Rat.inv_two_pow_sq_eq_inv_pow4"), vec![]);
    let le_one = Expr::const_(Name::from_string("Rat.dyadicApprox_le_one"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let h0_ty = c.le(c.rat_zero.clone(), x.clone());
    let (h0_id, h0) = b.fresh_local(h0_ty.clone());
    let h1_ty = c.lt(x.clone(), c.rat_one.clone());
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());

    let inner = {
        let mut ib = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = ib.fresh_local(c.nat.clone());

        let one = c.rat_one.clone();
        let kn = c.ofnat(c.dnum(&x, n.clone()));
        let succ_kn_nat = c.succ(c.dnum(&x, n.clone())); // Nat: succ k_n
        let s_kn = c.ofnat(succ_kn_nat.clone()); // ofNat(succ k_n)
        let iv = c.inv_two_pow(n.clone());
        let pow4 = c.pow4(n.clone());
        let inv4 = c.inv(pow4.clone());
        // a_n surface form (defeq dyadicApprox): kn·iv.
        let a = c.mul(kn.clone(), iv.clone());
        let aa = c.mul(a.clone(), a.clone());
        // b_n := s_kn·iv ;  ss := s_kn·s_kn  (the invariant RHS).
        let bb = c.mul(s_kn.clone(), iv.clone());
        let ss = c.mul(s_kn.clone(), s_kn.clone());
        let x_pow4 = c.mul(x.clone(), pow4.clone());

        // ── Step A: x < b·b ──────────────────────────────────────────────
        // h_inv : x·4^n < ss   (dyadicNum_sq_lt_succ x h0 h1 n).
        let h_inv = Expr::apps(
            dnum_sq_lt.clone(),
            [x.clone(), h0.clone(), h1.clone(), n.clone()],
        );
        // multiply LEFT by inv4 > 0: inv4·(x·4^n) < inv4·ss.
        let inv4_pos = {
            let h_pos = Expr::app(
                Expr::const_(Name::from_string("Rat.zero_lt_dyadicPow4"), vec![]),
                n.clone(),
            );
            Expr::apps(
                Expr::const_(Name::from_string("Rat.inv_pos"), vec![]),
                [pow4.clone(), h_pos],
            )
        };
        let h_mul = c.mul_lt_pos_left(inv4.clone(), x_pow4.clone(), ss.clone(), h_inv, inv4_pos);
        // LHS: inv4·(x·4^n) = x.
        //   inv4·(x·4^n) = (inv4·x)·4^n (symm mul_assoc) = (x·inv4)·4^n (congr mul_comm)
        //     = x·(inv4·4^n) (mul_assoc) = x·(4^n·inv4) wait — cleaner:
        //   inv4·(x·4^n) = inv4·(4^n·x) (congr (inv4·_) (mul_comm x 4^n))
        //     = (inv4·4^n)·x (symm mul_assoc) = 1·x (congr (·x) cancel) = x (one_mul).
        let cancel4 = {
            // inv4·4^n = 1:  mul_comm + mul_inv_cancel give 4^n·inv4 = 1, so
            //   inv4·4^n = 4^n·inv4 (mul_comm) = 1.
            let pow4_ne = c.pow4_ne_zero(&n);
            let e_cancel = c.mul_inv_cancel(pow4.clone(), pow4_ne); // 4^n·inv4 = 1
            let e_comm = c.mul_comm(inv4.clone(), pow4.clone()); // inv4·4^n = 4^n·inv4
            let inv4_pow4 = c.mul(inv4.clone(), pow4.clone());
            let pow4_inv4 = c.mul(pow4.clone(), inv4.clone());
            c.trans(inv4_pow4, pow4_inv4, one.clone(), e_comm, e_cancel) // inv4·4^n = 1
        };
        // chain inv4·(x·4^n) = x:
        let inv4_x_pow4 = c.mul(inv4.clone(), x_pow4.clone()); // inv4·(x·4^n)
        let pow4_x = c.mul(pow4.clone(), x.clone()); // 4^n·x
        let inv4_pow4_x = c.mul(inv4.clone(), pow4_x.clone()); // inv4·(4^n·x)
                                                               // e_a1 : inv4·(x·4^n) = inv4·(4^n·x)  (congr (inv4·_) (mul_comm x 4^n)).
        let f_inv4 = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.mul(inv4.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let e_a1 = c.congr_arg(
            x_pow4.clone(),
            pow4_x.clone(),
            f_inv4,
            c.mul_comm(x.clone(), pow4.clone()),
        );
        // e_a2 : inv4·(4^n·x) = (inv4·4^n)·x  (symm mul_assoc inv4 4^n x).
        let inv4_pow4 = c.mul(inv4.clone(), pow4.clone());
        let inv4_pow4_times_x = c.mul(inv4_pow4.clone(), x.clone());
        let e_assoc = c.mul_assoc(inv4.clone(), pow4.clone(), x.clone()); // (inv4·4^n)·x = inv4·(4^n·x)
        let e_a2 = c.symm(inv4_pow4_times_x.clone(), inv4_pow4_x.clone(), e_assoc); // inv4·(4^n·x) = (inv4·4^n)·x
                                                                                    // e_a3 : (inv4·4^n)·x = 1·x  (congr (·x) cancel4).
        let f_x = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.mul(t, x.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let one_x = c.mul(one.clone(), x.clone());
        let e_a3 = c.congr_arg(inv4_pow4.clone(), one.clone(), f_x, cancel4);
        // e_a4 : 1·x = x  (one_mul x).
        let e_a4 = c.one_mul(x.clone());
        // assemble inv4·(x·4^n) = x.
        let t_a1 = c.trans(
            inv4_x_pow4.clone(),
            inv4_pow4_x.clone(),
            inv4_pow4_times_x.clone(),
            e_a1,
            e_a2,
        );
        let t_a2 = c.trans(
            inv4_x_pow4.clone(),
            inv4_pow4_times_x.clone(),
            one_x.clone(),
            t_a1,
            e_a3,
        );
        let lhs_eq_x = c.trans(inv4_x_pow4.clone(), one_x.clone(), x.clone(), t_a2, e_a4); // inv4·(x·4^n) = x

        // RHS: inv4·ss = b·b.
        //   b·b = (s_kn·iv)·(s_kn·iv) = (s_kn·s_kn)·(iv·iv)  (mmmc)
        //       = ss·inv4   (congr (ss·_) inv_sq_bridge)
        //       = inv4·ss   (mul_comm).  → so inv4·ss = b·b by symm of the chain.
        let ivsq = c.mul(iv.clone(), iv.clone());
        let mmmc_b = c.mmmc(s_kn.clone(), iv.clone(), s_kn.clone(), iv.clone()); // b·b = ss·(iv·iv)
        let h_invsq = Expr::app(inv_sq_bridge.clone(), n.clone()); // iv·iv = inv4
        let f_ss = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.mul(ss.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let ss_ivsq = c.mul(ss.clone(), ivsq.clone());
        let ss_inv4 = c.mul(ss.clone(), inv4.clone());
        let step_ss = c.congr_arg(ivsq.clone(), inv4.clone(), f_ss, h_invsq); // ss·(iv·iv) = ss·inv4
        let bb_eq_ss_inv4 = c.trans(
            c.mul(bb.clone(), bb.clone()),
            ss_ivsq.clone(),
            ss_inv4.clone(),
            mmmc_b,
            step_ss,
        ); // b·b = ss·inv4
        let e_comm_ss = c.mul_comm(ss.clone(), inv4.clone()); // ss·inv4 = inv4·ss
        let inv4_ss = c.mul(inv4.clone(), ss.clone());
        let bb_eq_inv4_ss = c.trans(
            c.mul(bb.clone(), bb.clone()),
            ss_inv4.clone(),
            inv4_ss.clone(),
            bb_eq_ss_inv4,
            e_comm_ss,
        ); // b·b = inv4·ss
        let inv4_ss_eq_bb = c.symm(
            c.mul(bb.clone(), bb.clone()),
            inv4_ss.clone(),
            bb_eq_inv4_ss,
        ); // inv4·ss = b·b

        // transport h_mul : inv4·(x·4^n) < inv4·ss  along lhs_eq_x (left) and
        //   inv4_ss_eq_bb (right) to get x < b·b.
        let bbm = c.mul(bb.clone(), bb.clone());
        // left transport: motive (fun t => t < inv4·ss).
        let motive_l = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.lt(t, inv4_ss.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_x_lt_inv4ss = c.subst(motive_l, inv4_x_pow4.clone(), x.clone(), lhs_eq_x, h_mul); // x < inv4·ss
                                                                                                // right transport: motive (fun t => x < t).
        let motive_r = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.lt(x.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_x_lt_bb = c.subst(
            motive_r,
            inv4_ss.clone(),
            bbm.clone(),
            inv4_ss_eq_bb,
            h_x_lt_inv4ss,
        ); // x < b·b

        // ── Step B: b = a + iv ───────────────────────────────────────────
        // s_kn = ofNat k_n + 1  (symm add_natCast_one k_n).
        let kn_plus_1 = c.add(kn.clone(), one.clone());
        let e_skn = c.add_natcast_one(c.dnum(&x, n.clone())); // ofNat k_n + 1 = ofNat(succ k_n)
                                                              // (kn+1)·iv = kn·iv + 1·iv  (right_distrib kn 1 iv).
        let rd = c.right_distrib(kn.clone(), one.clone(), iv.clone()); // (kn+1)·iv = kn·iv + 1·iv
                                                                       // 1·iv = iv (one_mul iv); congr (kn·iv + _) → kn·iv + 1·iv = kn·iv + iv = a + iv.
        let one_iv = c.mul(one.clone(), iv.clone());
        let e_oneiv = c.one_mul(iv.clone()); // 1·iv = iv
        let f_add_a = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.add(a.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let a_plus_oneiv = c.add(a.clone(), one_iv.clone());
        let a_plus_iv = c.add(a.clone(), iv.clone());
        let e_fix = c.congr_arg(one_iv.clone(), iv.clone(), f_add_a, e_oneiv); // a + 1·iv = a + iv
                                                                               // (kn+1)·iv = a + iv:  rd : (kn+1)·iv = a + 1·iv (note kn·iv ≡ a defeq),
                                                                               //   then e_fix.
        let kn1_iv = c.mul(kn_plus_1.clone(), iv.clone());
        let rd_chain = c.trans(
            kn1_iv.clone(),
            a_plus_oneiv.clone(),
            a_plus_iv.clone(),
            rd,
            e_fix,
        ); // (kn+1)·iv = a+iv
           // b = s_kn·iv. Transport along e_skn: s_kn = kn+1, so b = (kn+1)·iv.
           //   We want b = a+iv. Build via: congr (·iv) (symm e_skn) : (kn+1)·iv? No.
           //   e_skn : (kn+1) = s_kn. congr (fun t => t·iv) e_skn : (kn+1)·iv = s_kn·iv = b.
        let f_iv = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.mul(t, iv.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let e_kn1iv_eq_b = c.congr_arg(kn_plus_1.clone(), s_kn.clone(), f_iv, e_skn); // (kn+1)·iv = b
        let e_b_eq_kn1iv = c.symm(kn1_iv.clone(), bb.clone(), e_kn1iv_eq_b); // b = (kn+1)·iv
        let b_eq_a_iv = c.trans(
            bb.clone(),
            kn1_iv.clone(),
            a_plus_iv.clone(),
            e_b_eq_kn1iv,
            rd_chain,
        ); // b = a+iv

        // ── Step C: b·b = a·a + (1+1)·(a·iv) + iv·iv ─────────────────────
        // add_sq a iv : (a+iv)·(a+iv) = (a·a + (1+1)·(a·iv)) + iv·iv.
        let cross_coeff = c.add(one.clone(), one.clone()); // 1+1
        let a_iv = c.mul(a.clone(), iv.clone());
        let cross = c.mul(cross_coeff.clone(), a_iv.clone()); // (1+1)·(a·iv)
        let bracket = c.add(cross.clone(), ivsq.clone()); // (1+1)(a·iv) + iv·iv
        let aa_plus_cross = c.add(aa.clone(), cross.clone());
        let expand_rhs = c.add(aa_plus_cross.clone(), ivsq.clone()); // (a·a + cross) + iv·iv
        let h_add_sq = c.add_sq(a.clone(), iv.clone()); // (a+iv)·(a+iv) = expand_rhs
                                                        // b·b = (a+iv)·(a+iv): congr (fun t=>t·t) b_eq_a_iv via subst.
                                                        //   motive (fun t => t·t = expand_rhs); h_add_sq has type
                                                        //   (a+iv)·(a+iv) = expand_rhs ; subst from (a+iv) to b along symm b_eq_a_iv.
        let motive_sq = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.eq(c.mul(t.clone(), t), expand_rhs.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        // symm b_eq_a_iv : (a+iv) = b.
        let e_aiv_eq_b = c.symm(bb.clone(), a_plus_iv.clone(), b_eq_a_iv); // (a+iv) = b
        let h_bb_eq_expand = c.subst(
            motive_sq,
            a_plus_iv.clone(),
            bb.clone(),
            e_aiv_eq_b,
            h_add_sq,
        ); // b·b = expand_rhs

        // ── Step D: bracket ≤ iv+iv+iv ───────────────────────────────────
        // h_a_le_1 : a ≤ 1  (dyadicApprox_le_one x h0 h1 n).
        let h_a_le_1 = Expr::apps(
            le_one.clone(),
            [x.clone(), h0.clone(), h1.clone(), n.clone()],
        );
        // h_iv_le_1 : iv ≤ 1.
        let h_iv_le_1 = c.inv_two_pow_le_one(n.clone());
        // 0 ≤ iv.
        let h0_iv = c.le_of_lt(iv.clone(), c.zero_lt_inv_two_pow(n.clone()));
        // a·iv ≤ 1·iv : mul_le_right iv a 1 (a≤1)(0≤iv).
        let h_aiv_le_1iv =
            c.mul_le_right(iv.clone(), a.clone(), one.clone(), h_a_le_1, h0_iv.clone());
        // 1·iv = iv (one_mul); transport h_aiv_le_1iv RHS → a·iv ≤ iv.
        let motive_aiv = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.le(a_iv.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_aiv_le_iv = c.subst(
            motive_aiv,
            one_iv.clone(),
            iv.clone(),
            c.one_mul(iv.clone()),
            h_aiv_le_1iv,
        ); // a·iv ≤ iv
           // 0 ≤ 1+1 :  add_le_add? Simpler: 0 ≤ 1+1 via le_of_lt of 0 < 1+1.
           //   We just need 0 ≤ (1+1). Use mul_le_left with this nonneg. Build it
           //   as add_le_add 0 1 0 1 (0≤1)(0≤1) : (0+0) ≤ (1+1), and 0+0 ≡ 0? Not
           //   defeq necessarily. Instead: 0 ≤ 1 (zero_le_one) gives 0 ≤ 1+1 via
           //   le_trans 0 1 (1+1) (0≤1)(1 ≤ 1+1). 1 ≤ 1+1: le_add_of... use
           //   add_le_add_right? Simplest: 1 = 0+1 (symm? ) ... Use le_of_lt of
           //   0 < 1+1 = mul? Too much. Build 0 ≤ 1+1 directly:
           //     add_le_add 0 1 0 1 (0≤1)(0≤1) : 0+0 ≤ 1+1, then 0+0 = 0 (add_zero 0)
           //     transports left to 0 ≤ 1+1.
        let zle1 = c.zero_le_one();
        let h_00_le_11 = c.add_le_add(
            c.rat_zero.clone(),
            one.clone(),
            c.rat_zero.clone(),
            one.clone(),
            zle1.clone(),
            zle1.clone(),
        ); // (0+0) ≤ (1+1)
        let zero_zero = c.add(c.rat_zero.clone(), c.rat_zero.clone());
        // 0+0 = 0 : add_zero 0 (a+0 = a).  Use mul_one? No — use Rat.add_zero.
        let e_00_eq_0 = Expr::app(
            Expr::const_(Name::from_string("Rat.add_zero"), vec![]),
            c.rat_zero.clone(),
        ); // 0+0 = 0
        let motive_z = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.le(t, cross_coeff.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h0_11 = c.subst(
            motive_z,
            zero_zero.clone(),
            c.rat_zero.clone(),
            e_00_eq_0,
            h_00_le_11,
        ); // 0 ≤ 1+1
           // cross = (1+1)·(a·iv) ≤ (1+1)·iv : mul_le_left (1+1) (a·iv) iv (a·iv≤iv)(0≤1+1).
        let cc_iv = c.mul(cross_coeff.clone(), iv.clone());
        let h_cross_le = c.mul_le_left(
            cross_coeff.clone(),
            a_iv.clone(),
            iv.clone(),
            h_aiv_le_iv,
            h0_11,
        ); // cross ≤ (1+1)·iv
           // (1+1)·iv = iv + iv : right_distrib 1 1 iv → (1+1)·iv = 1·iv + 1·iv,
           //   then one_mul twice.
        let rd2 = c.right_distrib(one.clone(), one.clone(), iv.clone()); // (1+1)·iv = 1·iv + 1·iv
        let oneiv_plus_oneiv = c.add(one_iv.clone(), one_iv.clone());
        // congr both 1·iv → iv: first left then right.
        let f_left_iv = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.add(t, one_iv.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let iv_plus_oneiv = c.add(iv.clone(), one_iv.clone());
        let e_l = c.congr_arg(one_iv.clone(), iv.clone(), f_left_iv, c.one_mul(iv.clone())); // 1·iv+1·iv = iv+1·iv
        let f_right_iv = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.add(iv.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let iv_plus_iv = c.add(iv.clone(), iv.clone());
        let e_r = c.congr_arg(
            one_iv.clone(),
            iv.clone(),
            f_right_iv,
            c.one_mul(iv.clone()),
        ); // iv+1·iv = iv+iv
        let e_ll = c.trans(
            oneiv_plus_oneiv.clone(),
            iv_plus_oneiv.clone(),
            iv_plus_iv.clone(),
            e_l,
            e_r,
        ); // 1·iv+1·iv = iv+iv
        let e_cc_iv = c.trans(
            cc_iv.clone(),
            oneiv_plus_oneiv.clone(),
            iv_plus_iv.clone(),
            rd2,
            e_ll,
        ); // (1+1)·iv = iv+iv
           // transport h_cross_le RHS along e_cc_iv → cross ≤ iv+iv.
        let motive_cc = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.le(cross.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_cross_le_iviv = c.subst(
            motive_cc,
            cc_iv.clone(),
            iv_plus_iv.clone(),
            e_cc_iv,
            h_cross_le,
        ); // cross ≤ iv+iv

        // iv·iv ≤ iv : iv·iv ≤ 1·iv (mul_le_right iv iv 1 (iv≤1)(0≤iv)), then 1·iv=iv.
        let h_ivsq_le_1iv = c.mul_le_right(
            iv.clone(),
            iv.clone(),
            one.clone(),
            h_iv_le_1,
            h0_iv.clone(),
        );
        let motive_ivsq = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.le(ivsq.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_ivsq_le_iv = c.subst(
            motive_ivsq,
            one_iv.clone(),
            iv.clone(),
            c.one_mul(iv.clone()),
            h_ivsq_le_1iv,
        ); // iv·iv ≤ iv

        // bracket = cross + iv·iv ≤ (iv+iv) + iv = iv+iv+iv  (add_le_add).
        let three_iv = c.add(iv_plus_iv.clone(), iv.clone()); // (iv+iv)+iv
        let h_bracket_le = c.add_le_add(
            cross.clone(),
            iv_plus_iv.clone(),
            ivsq.clone(),
            iv.clone(),
            h_cross_le_iviv,
            h_ivsq_le_iv,
        ); // (cross + iv·iv) ≤ ((iv+iv)+iv)

        // ── Step E: combine ──────────────────────────────────────────────
        // x < b·b = (a·a + cross) + iv·iv = a·a + bracket?  add_sq gives RHS as
        //   ((a·a + cross) + iv·iv), which is NOT syntactically a·a + bracket.
        //   We instead bound expand_rhs directly: x < expand_rhs and
        //   expand_rhs ≤ a·a + (iv+iv+iv) so x < a·a + (iv+iv+iv).
        // x < expand_rhs: transport h_x_lt_bb along h_bb_eq_expand.
        let motive_xbb = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.lt(x.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_x_lt_expand = c.subst(
            motive_xbb,
            bbm.clone(),
            expand_rhs.clone(),
            h_bb_eq_expand,
            h_x_lt_bb,
        ); // x < (a·a+cross)+iv·iv

        // expand_rhs ≤ a·a + (iv+iv+iv):
        //   expand_rhs = (a·a + cross) + iv·iv. We want ≤ a·a + ((iv+iv)+iv).
        //   Reassociate: (a·a + cross) + iv·iv = a·a + (cross + iv·iv)  (mul/add_assoc).
        //   then add_le_add_left of bracket ≤ three_iv (via add_le_add with refl).
        let e_assoc_add = Expr::apps(
            Expr::const_(Name::from_string("Rat.add_assoc"), vec![]),
            [aa.clone(), cross.clone(), ivsq.clone()],
        ); // (a·a+cross)+iv·iv = a·a+(cross+iv·iv)
        let aa_plus_bracket = c.add(aa.clone(), bracket.clone());
        // transport h_x_lt_expand along e_assoc_add (RHS) → x < a·a + (cross+iv·iv).
        let motive_xe = {
            let mut d = EnvDeclBuilder::child_of(&ib);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.lt(x.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_x_lt_aabr = c.subst(
            motive_xe,
            expand_rhs.clone(),
            aa_plus_bracket.clone(),
            e_assoc_add,
            h_x_lt_expand,
        ); // x < a·a + bracket
           // a·a + bracket ≤ a·a + three_iv  (add_le_add (a·a)(a·a) bracket three_iv (le_refl)(h_bracket_le)).
        let aa_plus_three = c.add(aa.clone(), three_iv.clone());
        let h_aabr_le = c.add_le_add(
            aa.clone(),
            aa.clone(),
            bracket.clone(),
            three_iv.clone(),
            c.le_refl(aa.clone()),
            h_bracket_le,
        ); // a·a+bracket ≤ a·a+three_iv
           // x < a·a + three_iv  (lt_of_lt_of_le x (a·a+bracket)(a·a+three_iv)).
        let body = c.lt_of_lt_of_le(
            x.clone(),
            aa_plus_bracket.clone(),
            aa_plus_three.clone(),
            h_x_lt_aabr,
            h_aabr_le,
        );
        // NOTE: the stated goal RHS is `a_n·a_n + ((iv+iv)+iv)` where a_n is
        // `dyadicApprox x n` (defeq to a = kn·iv) and three_iv = (iv+iv)+iv.
        ib.finish_child(ib.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
    };

    let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, inner);
    let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
    b.finish(b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e))
}
