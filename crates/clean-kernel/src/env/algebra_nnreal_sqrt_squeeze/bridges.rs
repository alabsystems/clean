// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rung 7a — the scale bridges that turn `a_n·a_n` (a product of two
//! `inv(2^n)`-scaled numerators) into `(ofNat k_n · ofNat k_n)·inv(4^n)`, the
//! form the landed squeeze invariants speak in.

use super::SqueezeConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    /// `Rat.ofNat_two_pow_sq_eq_pow4 : ∀ n, ofNat(2^n)·ofNat(2^n) = dyadicPow4 n`.
    ///
    /// `Nat.rec` over `n`. BASE `n=0`: `ofNat(2^0)·ofNat(2^0) ≡ 1·1`,
    /// `dyadicPow4 0 ≡ 1` (`powNat _ 0 ≡ Rat.one`); `Rat.mul_one (ofNat 2^0)`
    /// (its `1` arg is defeq the second `ofNat 2^0`). STEP: with
    /// `2^{n+1} ≡ Nat.mul (2^n) 2` (Nat.pow ι) and `4^{n+1} ≡ ofNat 4·4^n`
    /// (powNat ι), rewrite `ofNat(2^{n+1}) = ofNat(2^n)·ofNat 2` (`ofNat_mul`),
    /// fold `(ofNat(2^n)·ofNat 2)·(ofNat(2^n)·ofNat 2) = (ofNat(2^n)·ofNat(2^n))·
    /// (ofNat 2·ofNat 2)` (`mul_mul_mul_comm`), `ofNat 2·ofNat 2 = ofNat 4`
    /// (`ofNat_mul` symm), `= 4^n·ofNat 4` (`congr` IH) `= ofNat 4·4^n`
    /// (`mul_comm`) `≡ 4^{n+1}` (defeq).
    pub(crate) fn register_ofnat_two_pow_sq_eq_pow4(
        &mut self,
        c: &SqueezeConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.ofNat_two_pow_sq_eq_pow4");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let goal = |n: &Expr| {
            c.eq(
                c.mul(c.two_pow(n.clone()), c.two_pow(n.clone())),
                c.pow4(n.clone()),
            )
        };
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), goal(&n)))
        };
        let value = build_two_pow_sq_value(c, &goal);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.zero_lt_dyadicPow4 : ∀ n, 0 < dyadicPow4 n`.
    ///
    /// `mul_pos (ofNat 2^n)(ofNat 2^n)(0<·)(0<·) : 0 < ofNat(2^n)·ofNat(2^n)`,
    /// transported along `ofNat_two_pow_sq_eq_pow4 n` (motive `fun t => 0 < t`).
    pub(crate) fn register_zero_lt_dyadic_pow4(
        &mut self,
        c: &SqueezeConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.zero_lt_dyadicPow4");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let bridge = Expr::const_(Name::from_string("Rat.ofNat_two_pow_sq_eq_pow4"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let concl = c.lt(c.rat_zero.clone(), c.pow4(n.clone()));
            b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let tp = c.two_pow(n.clone());
            let sq = c.mul(tp.clone(), tp.clone());
            let h_sq = c.mul_pos(
                tp.clone(),
                tp.clone(),
                c.zero_lt_two_pow(n.clone()),
                c.zero_lt_two_pow(n.clone()),
            );
            // motive fun t => 0 < t.
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = d.fresh_local(c.rat.clone());
                let body = c.lt(c.rat_zero.clone(), t);
                d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            // We must transport 0 < sq along (sq = pow4) to get 0 < pow4.
            // Eq.subst motive sq pow4 (bridge n) h_sq.
            let h_eq = Expr::app(bridge.clone(), n.clone());
            let pow4 = c.pow4(n.clone());
            let body = c.subst(motive, sq, pow4, h_eq, h_sq);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.inv_two_pow_sq_eq_inv_pow4 : ∀ n, inv(2^n)·inv(2^n) = inv(dyadicPow4 n)`.
    ///
    /// `mul_inv (ofNat 2^n)(ofNat 2^n) hne hne : inv(ofNat(2^n)·ofNat(2^n)) =
    /// inv(2^n)·inv(2^n)` symm, transported along `ofNat_two_pow_sq_eq_pow4 n`
    /// inside the `Rat.inv` (`congrArg Rat.inv`).
    pub(crate) fn register_inv_two_pow_sq_eq_inv_pow4(
        &mut self,
        c: &SqueezeConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.inv_two_pow_sq_eq_inv_pow4");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let bridge = Expr::const_(Name::from_string("Rat.ofNat_two_pow_sq_eq_pow4"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let lhs = c.mul(c.inv_two_pow(n.clone()), c.inv_two_pow(n.clone()));
            let rhs = c.inv(c.pow4(n.clone()));
            b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), c.eq(lhs, rhs)))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let tp = c.two_pow(n.clone());
            let sq = c.mul(tp.clone(), tp.clone());
            let inv_inv = c.mul(c.inv_two_pow(n.clone()), c.inv_two_pow(n.clone()));
            let hne = c.two_pow_ne_zero(n.clone());
            // mul_inv tp tp hne hne : inv(tp·tp) = inv tp · inv tp.
            let h_mul_inv = c.mul_inv(tp.clone(), tp.clone(), hne.clone(), hne);
            // symm : inv tp · inv tp = inv (tp·tp).
            let h_sym = c.symm(c.inv(sq.clone()), inv_inv.clone(), h_mul_inv);
            // congrArg Rat.inv (bridge n) : inv (tp·tp) = inv (pow4 n).
            let pow4 = c.pow4(n.clone());
            let h_eq = Expr::app(bridge.clone(), n.clone());
            let h_congr = c.congr_arg(sq.clone(), pow4.clone(), c.rat_inv.clone(), h_eq);
            // trans : inv tp · inv tp = inv (pow4 n).
            let body = c.trans(inv_inv, c.inv(sq), c.inv(pow4), h_sym, h_congr);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
        };
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `Rat.dyadicApprox_sq_eq : ∀ x n,
    ///     a_n·a_n = (ofNat k_n · ofNat k_n)·inv(dyadicPow4 n)`,
    /// where `a_n = ofNat k_n · inv(2^n)`.
    ///
    /// `a_n·a_n = (ofNat k_n · inv 2^n)·(ofNat k_n · inv 2^n)
    ///         = (ofNat k_n · ofNat k_n)·(inv 2^n · inv 2^n)`   (`mmmc`)
    ///         `= (ofNat k_n · ofNat k_n)·inv(4^n)`              (`congr` rung 7a).
    pub(crate) fn register_dyadic_approx_sq_eq(
        &mut self,
        c: &SqueezeConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.dyadicApprox_sq_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let inv_sq_bridge =
            Expr::const_(Name::from_string("Rat.inv_two_pow_sq_eq_inv_pow4"), vec![]);
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let a = c.approx(&x, n.clone());
            let kn = c.ofnat(c.dnum(&x, n.clone()));
            let rhs = c.mul(c.mul(kn.clone(), kn), c.inv(c.pow4(n.clone())));
            let concl = c.eq(c.mul(a.clone(), a), rhs);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (n_id, n) = b.fresh_local(c.nat.clone());

            let kn = c.ofnat(c.dnum(&x, n.clone()));
            let iv = c.inv_two_pow(n.clone());
            // a_n ≡ kn · iv (defeq via dyadicApprox unfold).
            let a = c.approx(&x, n.clone());
            let a_kn_iv = c.mul(kn.clone(), iv.clone()); // surface form of a_n
            let kk = c.mul(kn.clone(), kn.clone());
            let ivsq = c.mul(iv.clone(), iv.clone());

            // step1 : (kn·iv)·(kn·iv) = (kn·kn)·(iv·iv)  via mmmc kn iv kn iv.
            let mmmc = c.mmmc(kn.clone(), iv.clone(), kn.clone(), iv.clone());
            // step2 : congr (fun t => (kn·kn)·t) (inv_sq_bridge n) :
            //         (kn·kn)·(iv·iv) = (kn·kn)·inv(4^n).
            let pow4_inv = c.inv(c.pow4(n.clone()));
            let h_invsq = Expr::app(inv_sq_bridge.clone(), n.clone());
            let f_left = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = d.fresh_local(c.rat.clone());
                let body = c.mul(kk.clone(), t);
                d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let step2 = c.congr_arg(ivsq.clone(), pow4_inv.clone(), f_left, h_invsq);
            // trans : (kn·iv)·(kn·iv) = (kn·kn)·inv(4^n).
            let lhs = c.mul(a_kn_iv.clone(), a_kn_iv.clone());
            let mid = c.mul(kk.clone(), ivsq.clone());
            let rhs = c.mul(kk.clone(), pow4_inv.clone());
            let body = c.trans(lhs, mid, rhs, mmmc, step2);
            // Note: `a_n·a_n` is defeq `(kn·iv)·(kn·iv)`; the kernel reconciles.
            let _ = a;
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

/// `fun n => Nat.rec motive base step n` for `ofNat_two_pow_sq_eq_pow4`.
fn build_two_pow_sq_value(c: &SqueezeConsts, goal: &dyn Fn(&Expr) -> Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();

    // motive : fun n => ofNat(2^n)·ofNat(2^n) = 4^n.
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = m.fresh_local(c.nat.clone());
        m.finish_child(m.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), goal(&n)))
    };

    // BASE n=0: goal ≡ ofNat(2^0)·ofNat(2^0) = 4^0 ≡ (1)·(1) = 1.
    //   mul_one (ofNat 2^0) : ofNat(2^0)·1 = ofNat(2^0); both `1` and RHS are
    //   defeq to ofNat(2^0) (≡ Rat.one), and 4^0 ≡ Rat.one.
    let base = c.mul_one(c.two_pow(c.nat_zero.clone()));

    // STEP: fun (n:Nat)(ih : ofNat(2^n)·ofNat(2^n)=4^n) =>
    //   goal (n+1) : ofNat(2^{n+1})·ofNat(2^{n+1}) = 4^{n+1}.
    let step = {
        let mut s = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = s.fresh_local(c.nat.clone());
        let ih_ty = goal(&n);
        let (ih_id, ih) = s.fresh_local(ih_ty.clone());

        let tp = c.two_pow(n.clone()); // ofNat(2^n)
        let two = c.ofnat(c.nat_lit(2)); // ofNat 2
        let four = c.ofnat(c.nat_lit(4)); // ofNat 4
        let pow4n = c.pow4(n.clone());

        // tp_succ := ofNat(2^{n+1}); defeq ofNat(Nat.mul (2^n) 2).
        let tp_succ = c.two_pow(c.succ(n.clone()));
        // e1 : ofNat(Nat.mul (2^n) 2) = ofNat(2^n)·ofNat 2  (ofNat_mul (2^n) 2).
        //   LHS defeq tp_succ.
        let e1 = c.ofnat_mul(c.npow2(n.clone()), c.nat_lit(2));
        // So tp_succ = tp·two (by e1, since tp_succ ≡ ofNat(Nat.mul (2^n) 2)).
        let tp_two = c.mul(tp.clone(), two.clone());

        // goal_succ LHS = tp_succ·tp_succ. Rewrite both factors to tp·two.
        // Strategy: prove (tp·two)·(tp·two) = 4^{n+1}, then transport along
        // e1 (twice) — but cleaner: build the chain on (tp·two)·(tp·two) and
        // wrap with a single congr that replaces tp_succ by tp·two on BOTH
        // sides via congrArg of (fun t => t·t)? congrArg only changes one
        // function arg. Use Eq.subst with motive (fun t => t·t = 4^{n+1}).

        // chain on (tp·two)·(tp·two):
        //  mmmc tp two tp two : (tp·two)·(tp·two) = (tp·tp)·(two·two).
        let mmmc = c.mmmc(tp.clone(), two.clone(), tp.clone(), two.clone());
        //  two·two = ofNat 4 : symm (ofNat_mul 2 2) (ofNat_mul 2 2 : ofNat 4 = ofNat 2·ofNat 2);
        //    ofNat(Nat.mul 2 2) ≡ ofNat 4 defeq.
        let two_two = c.mul(two.clone(), two.clone());
        let ofnat_2_2 = c.ofnat_mul(c.nat_lit(2), c.nat_lit(2)); // ofNat(Nat.mul 2 2) = ofNat2·ofNat2
                                                                 // ofNat(Nat.mul 2 2) defeq ofNat 4, so ofnat_2_2 : ofNat 4 = two·two.
        let h_22_eq_4 = c.symm(four.clone(), two_two.clone(), ofnat_2_2); // two·two = ofNat 4
                                                                          //  congr (fun t => (tp·tp)·t) h_22_eq_4 : (tp·tp)·(two·two) = (tp·tp)·ofNat4.
        let tptp = c.mul(tp.clone(), tp.clone());
        let f_22 = {
            let mut d = EnvDeclBuilder::child_of(&s);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.mul(tptp.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let step_b = c.congr_arg(two_two.clone(), four.clone(), f_22, h_22_eq_4);
        //  congr (fun t => t·ofNat4) ih : (tp·tp)·ofNat4 = 4^n·ofNat4.
        let f_ih = {
            let mut d = EnvDeclBuilder::child_of(&s);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.mul(t, four.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let step_c = c.congr_arg(tptp.clone(), pow4n.clone(), f_ih, ih.clone());
        //  mul_comm 4^n ofNat4 : 4^n·ofNat4 = ofNat4·4^n  (≡ 4^{n+1} defeq).
        let step_d = c.mul_comm(pow4n.clone(), four.clone());

        // assemble: (tp·two)·(tp·two) = (tp·tp)·(two·two)   (mmmc)
        //   = (tp·tp)·ofNat4   (step_b)
        //   = 4^n·ofNat4       (step_c)
        //   = ofNat4·4^n       (step_d)   ≡ 4^{n+1}.
        let p0 = c.mul(tp_two.clone(), tp_two.clone());
        let p1 = c.mul(tptp.clone(), two_two.clone());
        let p2 = c.mul(tptp.clone(), four.clone());
        let p3 = c.mul(pow4n.clone(), four.clone());
        let p4 = c.mul(four.clone(), pow4n.clone());
        let t1 = c.trans(p0.clone(), p1.clone(), p2.clone(), mmmc, step_b);
        let t2 = c.trans(p0.clone(), p2.clone(), p3.clone(), t1, step_c);
        let chain_tp_two = c.trans(p0.clone(), p3.clone(), p4.clone(), t2, step_d);
        // chain_tp_two : (tp·two)·(tp·two) = ofNat4·4^n  ≡ 4^{n+1}.

        // Now transport to tp_succ·tp_succ via e1 : ofNat(Nat.mul(2^n)2) = tp·two,
        //   i.e. (defeq) tp_succ = tp·two. motive (fun t => t·t = 4^{n+1}).
        // We want goal_succ : tp_succ·tp_succ = 4^{n+1}.
        // Use Eq.subst with motive over the variable factor: subst motive
        //   (tp·two) tp_succ (symm e1) chain_tp_two.
        // e1 : tp_succ(≡LHS) = tp·two; symm e1 : tp·two = tp_succ.
        let ofnat_mul_2n_2_lhs = c.ofnat(c.npow2(c.succ(n.clone()))); // surface tp_succ ≡ ofNat(2^{n+1})
        let e1_symm = c.symm(ofnat_mul_2n_2_lhs.clone(), tp_two.clone(), e1); // tp·two = tp_succ
        let motive_t = {
            let mut d = EnvDeclBuilder::child_of(&s);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.eq(c.mul(t.clone(), t), c.pow4(c.succ(n.clone())));
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        // chain_tp_two has type (tp·two)·(tp·two) = ofNat4·4^n.
        // We need it as motive (tp·two) = ((tp·two)·(tp·two) = 4^{n+1}); since
        // ofNat4·4^n ≡ 4^{n+1} defeq, chain_tp_two : motive (tp·two).
        let goal_succ = c.subst(
            motive_t,
            tp_two.clone(),
            tp_succ.clone(),
            e1_symm,
            chain_tp_two,
        );

        let e = s.mk_lam(ih_id, BinderInfo::Default, ih_ty, goal_succ);
        s.finish_child(s.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
    };

    let (n_id, n) = b.fresh_local(c.nat.clone());
    let rec = Expr::apps(c.nat_rec_prop.clone(), [motive, base, step, n.clone()]);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), rec))
}
