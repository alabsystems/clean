// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rung 7c — the squeeze `Equiv` between the squared dyadic sequence and the
//! constant `x` sequence.

use super::IdentityConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl IdentityConsts {
    /// The LOWER conjunct `a_m·a_m < x+ε` (all m): `a_m·a_m ≤ x < x+ε`.
    /// `h_x_lt_xeps : x < x+ε` is supplied by the caller (it is m-independent).
    fn lower_conjunct(&self, x: &Expr, eps: &Expr, m: &Expr, h0: &Expr, h_x_lt_xeps: Expr) -> Expr {
        let a = self.approx(x, m.clone());
        let aa = self.mul(a.clone(), a.clone());
        let x_eps = self.add(x.clone(), eps.clone());
        // h_aa_le_x : a_m·a_m ≤ x.
        let h_aa_le_x = Expr::apps(self.sq_le.clone(), [x.clone(), h0.clone(), m.clone()]);
        self.lt_of_le_of_lt(aa, x.clone(), x_eps, h_aa_le_x, h_x_lt_xeps)
    }

    /// The UPPER conjunct `x < a_m·a_m + ε` for `m ≥ N := M+2`.
    /// `h_3iv_lt_eps : 3·inv(2^m) < ε` is supplied (m/N-dependent).
    fn upper_conjunct(
        &self,
        x: &Expr,
        eps: &Expr,
        m: &Expr,
        h0: &Expr,
        h1: &Expr,
        h_3iv_lt_eps: Expr,
    ) -> Expr {
        let a = self.approx(x, m.clone());
        let aa = self.mul(a.clone(), a.clone());
        let iv = self.inv_two_pow(m.clone());
        let three_iv = self.add(self.add(iv.clone(), iv.clone()), iv.clone());
        let aa_three = self.add(aa.clone(), three_iv.clone());
        let aa_eps = self.add(aa.clone(), eps.clone());
        // h_x_lt : x < a_m·a_m + 3·inv(2^m).
        let h_x_lt = Expr::apps(
            self.x_lt_sq_add.clone(),
            [x.clone(), h0.clone(), h1.clone(), m.clone()],
        );
        // a_m·a_m + 3·inv(2^m) < a_m·a_m + ε  (add_lt_add_left 3iv ε aa h_3iv_lt_eps).
        let h_add = self.add_lt_add_left(three_iv.clone(), eps.clone(), aa.clone(), h_3iv_lt_eps);
        // lt_trans x (aa+3iv) (aa+ε).
        self.lt_trans(x.clone(), aa_three, aa_eps, h_x_lt, h_add)
    }

    /// `x < x + ε` from `0 < ε`: `add_lt_add_left 0 ε x (0<ε) : x+0 < x+ε`,
    /// transported along `x+0 = x` (`add_zero x`).
    pub(super) fn x_lt_x_add_eps(
        &self,
        parent: &EnvDeclBuilder,
        x: &Expr,
        eps: &Expr,
        hpos: Expr,
    ) -> Expr {
        // add_lt_add_left 0 ε x hpos : (x+0) < (x+ε).
        let h = self.add_lt_add_left(self.rat_zero.clone(), eps.clone(), x.clone(), hpos);
        // transport (x+0) → x along add_zero x.
        let x_zero = self.add(x.clone(), self.rat_zero.clone());
        let x_eps = self.add(x.clone(), eps.clone());
        let e_az = self.add_zero(x.clone()); // x+0 = x
                                             // motive (fun t => t < x+ε).
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(self.rat.clone());
            let body = self.lt(t, x_eps.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.subst(motive, x_zero, x.clone(), e_az, h)
    }

    /// `3·inv(2^m) < ε` for `m ≥ N := succ(succ M)`, given `hN : N ≤ m` and
    /// `hM : inv(2^M) < ε`. Telescopes:
    ///   `3·inv(2^m) ≤ 3·inv(2^N)` (antitone)
    ///   `3·inv(2^N) ≤ inv(2^M)` (two `succ_add_self` + one antitone), so
    ///   `3·inv(2^m) < ε` via `lt_of_le_of_lt`.
    /// `N = succ(succ M)`, so `2^N = 2^{M+2}`.
    #[allow(clippy::too_many_arguments)]
    fn three_iv_lt_eps(
        &self,
        parent: &EnvDeclBuilder,
        eps: &Expr,
        m: &Expr,
        big_m: &Expr,
        hn: Expr,
        hm: Expr,
    ) -> Expr {
        let big_n = self.succ(self.succ(big_m.clone())); // M+2
        let iv_m = self.inv_two_pow(m.clone());
        let iv_n = self.inv_two_pow(big_n.clone()); // inv(2^{M+2})
        let iv_m1 = self.inv_two_pow(self.succ(big_m.clone())); // inv(2^{M+1})
        let iv_big_m = self.inv_two_pow(big_m.clone()); // inv(2^M)

        // hle : inv(2^m) ≤ inv(2^N).
        let hle = self.inv_le_of_le(big_n.clone(), m.clone(), hn);

        // 3·inv(2^m) ≤ 3·inv(2^N):  add_le_add ((iv_m+iv_m), iv_m) ≤ ((iv_n+iv_n), iv_n).
        let three_iv_m = self.add(self.add(iv_m.clone(), iv_m.clone()), iv_m.clone());
        let three_iv_n = self.add(self.add(iv_n.clone(), iv_n.clone()), iv_n.clone());
        let two_iv_m = self.add(iv_m.clone(), iv_m.clone());
        let two_iv_n = self.add(iv_n.clone(), iv_n.clone());
        let h_2iv = self.add_le_add(
            iv_m.clone(),
            iv_n.clone(),
            iv_m.clone(),
            iv_n.clone(),
            hle.clone(),
            hle.clone(),
        ); // (iv_m+iv_m) ≤ (iv_n+iv_n)
        let h_3iv_le = self.add_le_add(
            two_iv_m.clone(),
            two_iv_n.clone(),
            iv_m.clone(),
            iv_n.clone(),
            h_2iv,
            hle,
        ); // 3·iv_m ≤ 3·iv_n

        // 3·inv(2^N) ≤ inv(2^M):
        //   3·iv_n = (iv_n+iv_n)+iv_n.
        //   iv_n+iv_n = inv(2^{M+1})  (succ_add_self (M+1) : inv(2^{(M+1)+1})+...=inv(2^{M+1}));
        //     note (M+1)+1 = M+2 = N defeq.
        //   so 3·iv_n = inv(2^{M+1}) + iv_n.
        //   iv_n ≤ inv(2^{M+1})  (antitone, M+1 ≤ M+2).
        //   so 3·iv_n ≤ inv(2^{M+1}) + inv(2^{M+1}) = inv(2^M)  (succ_add_self M).
        // First rewrite (iv_n+iv_n) → inv(2^{M+1}) inside 3·iv_n via subst.
        let e_2ivn = self.succ_add_self(self.succ(big_m.clone())); // iv_n+iv_n = inv(2^{M+1})
                                                                   // motive (fun t => (t + iv_n) ≤ inv(2^M))  — we will prove the bound on
                                                                   // the rewritten form and transport BACK. Cleaner: prove bound on
                                                                   // inv(2^{M+1}) + iv_n, then subst (symm e_2ivn) to (iv_n+iv_n)+iv_n.
        let m1_plus_ivn = self.add(iv_m1.clone(), iv_n.clone());
        //   h_ivn_le_m1 : iv_n ≤ inv(2^{M+1})  (inv_le_of_le (M+1) N (M+1≤N)).
        let hle_m1n = self.nat_le_succ_self(self.succ(big_m.clone())); // (M+1) ≤ (M+2)
        let h_ivn_le_m1 = self.inv_le_of_le(self.succ(big_m.clone()), big_n.clone(), hle_m1n);
        //   m1 + iv_n ≤ m1 + m1  (add_le_add m1 m1 iv_n m1 (le_refl m1)(h_ivn_le_m1)).
        let m1_plus_m1 = self.add(iv_m1.clone(), iv_m1.clone());
        let h_m1ivn_le = self.add_le_add(
            iv_m1.clone(),
            iv_m1.clone(),
            iv_n.clone(),
            iv_m1.clone(),
            self.le_refl(iv_m1.clone()),
            h_ivn_le_m1,
        ); // (m1+iv_n) ≤ (m1+m1)
           //   m1+m1 = inv(2^M)  (succ_add_self M).
        let e_m1m1 = self.succ_add_self(big_m.clone()); // inv(2^{M+1})+inv(2^{M+1}) = inv(2^M)
                                                        //   transport h_m1ivn_le RHS along e_m1m1 → (m1+iv_n) ≤ inv(2^M).
        let motive_r = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(self.rat.clone());
            let body = self.le(m1_plus_ivn.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let h_m1ivn_le_big_m = self.subst(
            motive_r,
            m1_plus_m1.clone(),
            iv_big_m.clone(),
            e_m1m1,
            h_m1ivn_le,
        ); // (m1+iv_n) ≤ inv(2^M)
           //   transport BACK along (symm e_2ivn) : inv(2^{M+1}) = iv_n+iv_n, to
           //   turn (m1+iv_n) into ((iv_n+iv_n)+iv_n) = 3·iv_n. motive
           //   (fun t => (t + iv_n) ≤ inv(2^M)).
        let e_2ivn_symm = self.symm(two_iv_n.clone(), iv_m1.clone(), e_2ivn); // inv(2^{M+1}) = iv_n+iv_n
        let motive_l = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(self.rat.clone());
            let body = self.le(self.add(t, iv_n.clone()), iv_big_m.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let h_3ivn_le_big_m = self.subst(
            motive_l,
            iv_m1.clone(),
            two_iv_n.clone(),
            e_2ivn_symm,
            h_m1ivn_le_big_m,
        ); // 3·iv_n ≤ inv(2^M)

        // 3·iv_m ≤ 3·iv_n ≤ inv(2^M):  le_trans.
        let h_3ivm_le_big_m = self.le_trans(
            three_iv_m.clone(),
            three_iv_n.clone(),
            iv_big_m.clone(),
            h_3iv_le,
            h_3ivn_le_big_m,
        ); // 3·iv_m ≤ inv(2^M)
           // 3·iv_m < ε  (lt_of_le_of_lt with hm : inv(2^M) < ε).
        self.lt_of_le_of_lt(
            three_iv_m,
            iv_big_m.clone(),
            eps.clone(),
            h_3ivm_le_big_m,
            hm,
        )
    }

    /// `(M+1) ≤ (M+2)` i.e. `Nat.le (succ k)(succ(succ k))` for `k := M`,
    /// here phrased as `Nat.le a (succ a)` for `a := succ M`:
    /// `Nat.le.step a a (Nat.le.refl a)`.
    fn nat_le_succ_self(&self, a: Expr) -> Expr {
        let refl = Expr::app(self.nat_le_refl.clone(), a.clone());
        Expr::apps(self.nat_le_step.clone(), [a.clone(), a, refl])
    }
}

impl Environment {
    /// Rung 7c — `NNReal.dyadicApprox_sq_equiv_const`.
    pub(crate) fn register_dyadic_approx_sq_equiv_const(
        &mut self,
        c: &IdentityConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.dyadicApprox_sq_equiv_const");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let h0_ty = c.le(c.rat_zero.clone(), x.clone());
            let (h0_id, h0) = b.fresh_local(h0_ty.clone());
            let h1_ty = c.lt(x.clone(), c.rat_one.clone());
            let (h1_id, _h1) = b.fresh_local(h1_ty.clone());
            let concl = c.equiv(c.cmul(&x), c.cconst(&x, &h0));
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, concl);
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = build_equiv_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `fun x h0 h1 ε hpos => Exists.elim (exists_inv_two_pow_lt ε hpos) elim_fn`.
fn build_equiv_value(c: &IdentityConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let h0_ty = c.le(c.rat_zero.clone(), x.clone());
    let (h0_id, h0) = b.fresh_local(h0_ty.clone());
    let h1_ty = c.lt(x.clone(), c.rat_one.clone());
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    // The target ∃-predicate over N:
    //   fun N => ∀ m, N≤m → And (val(seq cmul m) < val(seq cconst m)+ε)
    //                          (val(seq cconst m) < val(seq cmul m)+ε)
    // which is defeq to: ∀ m, N≤m → And (a_m·a_m < x+ε)(x < a_m·a_m+ε).
    let tgt_pred = |bb: &EnvDeclBuilder| -> Expr {
        let mut bn = EnvDeclBuilder::child_of(bb);
        let (cap_id, cap) = bn.fresh_local(c.nat.clone());
        let inner = {
            let mut bi = EnvDeclBuilder::child_of(&bn);
            let (m_id, m) = bi.fresh_local(c.nat.clone());
            let hle_ty = c.nat_le(cap.clone(), m.clone());
            let (hle_id, _hle) = bi.fresh_local(hle_ty.clone());
            let a = c.approx(&x, m.clone());
            let aa = c.mul(a.clone(), a.clone());
            let left = c.lt(aa.clone(), c.add(x.clone(), eps.clone()));
            let right = c.lt(x.clone(), c.add(aa.clone(), eps.clone()));
            let concl = c.and_ty(left, right);
            let e = bi.mk_pi(hle_id, BinderInfo::Default, hle_ty, concl);
            let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };
        bn.finish_child(bn.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), inner))
    };

    // source: ∃ M, inv(2^M) < ε  (exists_inv_two_pow_lt ε hpos).
    let ex_mod = Expr::apps(c.exists_inv_two_pow_lt.clone(), [eps.clone(), hpos.clone()]);
    let src_pred = {
        let mut sp = EnvDeclBuilder::child_of(&b);
        let (sm_id, sm) = sp.fresh_local(c.nat.clone());
        let body = c.lt(c.inv_two_pow(sm.clone()), eps.clone());
        sp.finish_child(sp.mk_lam(sm_id, BinderInfo::Default, c.nat.clone(), body))
    };
    // target goal: ∃ N, tgt_pred N.
    let tgt_goal = Expr::apps(c.exists_c.clone(), [c.nat.clone(), tgt_pred(&b)]);

    // x < x+ε (m-independent).
    let h_x_lt_xeps = c.x_lt_x_add_eps(&b, &x, &eps, hpos.clone());

    // elim_fn : (M:Nat) → (hM : inv(2^M) < ε) → ∃ N, tgt_pred N.
    let elim_fn = {
        let mut eb = EnvDeclBuilder::child_of(&b);
        let (bigm_id, big_m) = eb.fresh_local(c.nat.clone());
        let hm_ty = c.lt(c.inv_two_pow(big_m.clone()), eps.clone());
        let (hm_id, hm) = eb.fresh_local(hm_ty.clone());

        // witness N := succ(succ M).
        let big_n = c.succ(c.succ(big_m.clone()));

        // proof of tgt_pred N : ∀ m, N≤m → And(...).
        let witness = {
            let mut wb = EnvDeclBuilder::child_of(&eb);
            let (m_id, m) = wb.fresh_local(c.nat.clone());
            let hle_ty = c.nat_le(big_n.clone(), m.clone());
            let (hle_id, hle) = wb.fresh_local(hle_ty.clone());

            let a = c.approx(&x, m.clone());
            let aa = c.mul(a.clone(), a.clone());
            let left_ty = c.lt(aa.clone(), c.add(x.clone(), eps.clone()));
            let right_ty = c.lt(x.clone(), c.add(aa.clone(), eps.clone()));

            // LOWER conjunct.
            let left = c.lower_conjunct(&x, &eps, &m, &h0, h_x_lt_xeps.clone());
            // 3·inv(2^m) < ε.
            let h_3iv = c.three_iv_lt_eps(&wb, &eps, &m, &big_m, hle, hm.clone());
            // UPPER conjunct.
            let right = c.upper_conjunct(&x, &eps, &m, &h0, &h1, h_3iv);
            let proof = c.and_intro(left_ty, right_ty, left, right);

            let e = wb.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
            let e = wb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
            wb.finish_child(e)
        };

        let intro = Expr::apps(
            c.exists_intro.clone(),
            [c.nat.clone(), tgt_pred(&eb), big_n, witness],
        );
        let e = eb.mk_lam(hm_id, BinderInfo::Default, hm_ty, intro);
        let e = eb.mk_lam(bigm_id, BinderInfo::Default, c.nat.clone(), e);
        eb.finish_child(e)
    };

    // @Exists.elim Nat src_pred tgt_goal ex_mod elim_fn : tgt_goal.
    let elim = Expr::apps(
        c.exists_elim.clone(),
        [c.nat.clone(), src_pred, tgt_goal, ex_mod, elim_fn],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, elim);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
    let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
    b.finish(b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e))
}
