// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rung 4a — the cube squeeze `Equiv` between the TRIPLE pointwise-product
//! dyadic sequence (`n ↦ a_n³`) and the constant `x` sequence.

use super::CbrtIdentityConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl CbrtIdentityConsts {
    /// LOWER conjunct `a_m³ < x+ε` (all m): `a_m³ ≤ x` (`cube_le`) `< x+ε`.
    fn lower_conjunct(&self, x: &Expr, m: &Expr, h0: &Expr, h_x_lt_xeps: Expr, eps: &Expr) -> Expr {
        let a = self.approx(x, m.clone());
        let a3 = self.cube(a);
        let x_eps = self.add(x.clone(), eps.clone());
        let h_a3_le_x = Expr::apps(self.cube_le.clone(), [x.clone(), h0.clone(), m.clone()]);
        self.lt_of_le_of_lt(a3, x.clone(), x_eps, h_a3_le_x, h_x_lt_xeps)
    }

    /// UPPER conjunct `x < a_m³ + ε` for `m ≥ N`. `h_7iv_lt_eps : 7iv < ε`
    /// supplied; `7iv := 3iv+(3iv+iv)` (matching the rung-3 bracketing).
    fn upper_conjunct(
        &self,
        x: &Expr,
        eps: &Expr,
        m: &Expr,
        h0: &Expr,
        h1: &Expr,
        h_7iv_lt_eps: Expr,
    ) -> Expr {
        let a = self.approx(x, m.clone());
        let a3 = self.cube(a);
        let iv = self.inv_two_pow(m.clone());
        let three_iv = self.add(self.add(iv.clone(), iv.clone()), iv.clone());
        let seven_iv = self.add(three_iv.clone(), self.add(three_iv.clone(), iv.clone()));
        let a3_seven = self.add(a3.clone(), seven_iv.clone());
        let a3_eps = self.add(a3.clone(), eps.clone());
        // x < a_m³ + 7iv  (rung 3).
        let h_x_lt = Expr::apps(
            self.x_lt_cube_add.clone(),
            [x.clone(), h0.clone(), h1.clone(), m.clone()],
        );
        // a_m³ + 7iv < a_m³ + ε  (add_lt_add_left 7iv ε a_m³).
        let h_add = self.add_lt_add_left(seven_iv.clone(), eps.clone(), a3.clone(), h_7iv_lt_eps);
        self.lt_trans(x.clone(), a3_seven, a3_eps, h_x_lt, h_add)
    }

    /// `x < x + ε` from `0 < ε`.
    pub(super) fn x_lt_x_add_eps(
        &self,
        parent: &EnvDeclBuilder,
        x: &Expr,
        eps: &Expr,
        hpos: Expr,
    ) -> Expr {
        let h = self.add_lt_add_left(self.rat_zero.clone(), eps.clone(), x.clone(), hpos);
        let x_zero = self.add(x.clone(), self.rat_zero.clone());
        let x_eps = self.add(x.clone(), eps.clone());
        let e_az = self.add_zero(x.clone());
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(self.rat.clone());
            let body = self.lt(t, x_eps.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.subst(motive, x_zero, x.clone(), e_az, h)
    }

    /// `(M+1) ≤ (M+2)` phrased as `Nat.le a (succ a)` for `a := succ M`.
    #[cfg(test)]
    fn nat_le_succ_self(&self, a: Expr) -> Expr {
        let refl = Expr::app(self.nat_le_refl.clone(), a.clone());
        Expr::apps(self.nat_le_step.clone(), [a.clone(), a, refl])
    }

    /// `3iv := (iv+iv)+iv` for `iv := inv(2^k)`.
    fn three_iv(&self, k: &Expr) -> Expr {
        let iv = self.inv_two_pow(k.clone());
        self.add(self.add(iv.clone(), iv.clone()), iv.clone())
    }
    /// `7iv := 3iv + (3iv + iv)`.
    fn seven_iv(&self, k: &Expr) -> Expr {
        let iv = self.inv_two_pow(k.clone());
        let three = self.three_iv(k);
        self.add(three.clone(), self.add(three, iv))
    }

    /// `iv ≤ iv+iv` from `0 ≤ iv`. `add_le_add_left 0 iv iv (0≤iv) : iv+0 ≤ iv+iv`,
    /// transported along `iv+0 = iv`.
    fn iv_le_double(&self, parent: &EnvDeclBuilder, k: &Expr) -> Expr {
        let iv = self.inv_two_pow(k.clone());
        let h0iv = self.zero_le_inv_two_pow(k.clone());
        let h = self.add_le_add_left(self.rat_zero.clone(), iv.clone(), iv.clone(), h0iv); // iv+0 ≤ iv+iv
        let iv_zero = self.add(iv.clone(), self.rat_zero.clone());
        let iv_iv = self.add(iv.clone(), iv.clone());
        let e_az = self.add_zero(iv.clone()); // iv+0 = iv
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(self.rat.clone());
            let body = self.le(t, iv_iv.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.subst(motive, iv_zero, iv.clone(), e_az, h) // iv ≤ iv+iv
    }

    /// `7·inv(2^m) < ε` for `m ≥ N := succ(succ(succ M))`, given `hN : N ≤ m`
    /// and `hM : inv(2^M) < ε`. Telescopes:
    ///   `7iv_m ≤ 7iv_N`  (antitone, add_le_add of `iv_m ≤ iv_N`)
    ///   `7iv_N ≤ inv(2^M)`  (the 8-fold halving telescope, see body)
    /// so `7iv_m < ε` via `lt_of_le_of_lt`.
    fn seven_iv_lt_eps(
        &self,
        parent: &EnvDeclBuilder,
        eps: &Expr,
        m: &Expr,
        big_m: &Expr,
        hn: Expr,
        hm: Expr,
    ) -> Expr {
        let big_n = self.succ(self.succ(self.succ(big_m.clone()))); // M+3
        let iv_m = self.inv_two_pow(m.clone());
        let iv_n = self.inv_two_pow(big_n.clone()); // inv(2^{M+3})
        let iv_big_m = self.inv_two_pow(big_m.clone()); // inv(2^M)

        // hle : iv_m ≤ iv_N.
        let hle = self.inv_le_of_le(big_n.clone(), m.clone(), hn);

        // 7iv_m ≤ 7iv_N:  add_le_add over the 3iv+(3iv+iv) tree.
        let three_iv_m = self.three_iv(m);
        let three_iv_n = self.three_iv(&big_n);
        let two_iv_m = self.add(iv_m.clone(), iv_m.clone());
        let two_iv_n = self.add(iv_n.clone(), iv_n.clone());
        // 2iv_m ≤ 2iv_N
        let h_2iv = self.add_le_add(
            iv_m.clone(),
            iv_n.clone(),
            iv_m.clone(),
            iv_n.clone(),
            hle.clone(),
            hle.clone(),
        );
        // 3iv_m ≤ 3iv_N
        let h_3iv = self.add_le_add(
            two_iv_m.clone(),
            two_iv_n.clone(),
            iv_m.clone(),
            iv_n.clone(),
            h_2iv,
            hle.clone(),
        );
        // (3iv_m+iv_m) ≤ (3iv_N+iv_N)
        let tail_m = self.add(three_iv_m.clone(), iv_m.clone());
        let tail_n = self.add(three_iv_n.clone(), iv_n.clone());
        let h_tail = self.add_le_add(
            three_iv_m.clone(),
            three_iv_n.clone(),
            iv_m.clone(),
            iv_n.clone(),
            h_3iv.clone(),
            hle,
        );
        // 7iv_m = 3iv_m+(3iv_m+iv_m) ≤ 3iv_N+(3iv_N+iv_N) = 7iv_N
        let seven_m = self.seven_iv(m);
        let seven_n = self.seven_iv(&big_n);
        let h_7iv_le = self.add_le_add(
            three_iv_m.clone(),
            three_iv_n.clone(),
            tail_m.clone(),
            tail_n.clone(),
            h_3iv,
            h_tail,
        ); // 7iv_m ≤ 7iv_N

        // 7iv_N ≤ inv(2^M).  Let A := inv(2^{M+1}), B := inv(2^{M+2}).
        //   B = iv_N + iv_N    (succ_add_self (M+2): (M+2)+1 = M+3 = N)
        //   A = B + B          (succ_add_self (M+1))
        //   inv(2^M) = A + A   (succ_add_self M)
        // Set FOUR_N := (iv_N+iv_N)+(iv_N+iv_N). Then A = FOUR_N (transport B = iv_N+iv_N
        //   into A = B+B). We bound:
        //   3iv_N ≤ FOUR_N           [add_le_add_left iv_N (iv_N+iv_N) (iv_N+iv_N) (iv_N ≤ iv_N+iv_N)]
        //   3iv_N + iv_N = FOUR_N    [add_assoc (iv_N+iv_N) iv_N iv_N]
        // Hence 7iv_N = 3iv_N+(3iv_N+iv_N) ≤ FOUR_N + FOUR_N = A + A = inv(2^M).
        let big_m1 = self.succ(big_m.clone()); // M+1
        let big_m2 = self.succ(self.succ(big_m.clone())); // M+2
        let a_inv = self.inv_two_pow(big_m1.clone()); // inv(2^{M+1})
        let b_inv = self.inv_two_pow(big_m2.clone()); // inv(2^{M+2})
        let four_n = self.add(two_iv_n.clone(), two_iv_n.clone()); // (iv_N+iv_N)+(iv_N+iv_N)

        // e_b : iv_N+iv_N = inv(2^{M+2})   (succ_add_self (M+2); note (M+2)+1 = N).
        let e_b = self.succ_add_self(big_m2.clone()); // inv(2^{(M+2)+1})+... = inv(2^{M+2})
                                                      // i.e. iv_N + iv_N = B  (since 2^{(M+2)+1} ≡ 2^{M+3} = 2^N defeq).

        // A = B + B  (succ_add_self (M+1)).
        let e_a = self.succ_add_self(big_m1.clone()); // inv(2^{(M+1)+1})+... = inv(2^{M+1}); (M+1)+1 = M+2.
        let b_plus_b = self.add(b_inv.clone(), b_inv.clone());

        // FOUR_N = A:  FOUR_N = (iv_N+iv_N)+(iv_N+iv_N) = B+B (congr both via e_b) = A (symm e_a).
        // congr (·+(iv_N+iv_N)) e_b : (iv_N+iv_N)+(iv_N+iv_N) = B+(iv_N+iv_N)
        let f_l = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(self.rat.clone());
            let body = self.add(w, two_iv_n.clone());
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let cong_l = self.congr_arg_rat(two_iv_n.clone(), b_inv.clone(), f_l, e_b.clone());
        let b_plus_2ivn = self.add(b_inv.clone(), two_iv_n.clone());
        // congr (B+·) e_b : B+(iv_N+iv_N) = B+B
        let f_r = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(self.rat.clone());
            let body = self.add(b_inv.clone(), w);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let cong_r = self.congr_arg_rat(two_iv_n.clone(), b_inv.clone(), f_r, e_b.clone());
        let four_eq_bb = self.trans_rat(
            four_n.clone(),
            b_plus_2ivn.clone(),
            b_plus_b.clone(),
            cong_l,
            cong_r,
        ); // FOUR_N = B+B
        let four_eq_a = self.trans_rat(
            four_n.clone(),
            b_plus_b.clone(),
            a_inv.clone(),
            four_eq_bb,
            e_a.clone(),
        ); // FOUR_N = A

        // inv(2^M) = A + A  (succ_add_self M).
        let e_m = self.succ_add_self(big_m.clone()); // inv(2^{M+1})+inv(2^{M+1}) = inv(2^M)
        let a_plus_a = self.add(a_inv.clone(), a_inv.clone());

        // 3iv_N ≤ FOUR_N:  3iv_N = (iv_N+iv_N)+iv_N.
        //   add_le_add (iv_N+iv_N)(iv_N+iv_N) iv_N (iv_N+iv_N) (le_refl)(iv_N ≤ iv_N+iv_N).
        let h_ivn_le_double = self.iv_le_double(parent, &big_n); // iv_N ≤ iv_N+iv_N
        let h_3ivn_le_four = self.add_le_add(
            two_iv_n.clone(),
            two_iv_n.clone(),
            iv_n.clone(),
            two_iv_n.clone(),
            self.le_refl(two_iv_n.clone()),
            h_ivn_le_double,
        ); // (iv_N+iv_N)+iv_N ≤ (iv_N+iv_N)+(iv_N+iv_N) = FOUR_N

        // 3iv_N + iv_N = FOUR_N:  add_assoc (iv_N+iv_N) iv_N iv_N.
        let e_tail_eq_four = self.add_assoc(two_iv_n.clone(), iv_n.clone(), iv_n.clone()); // ((iv_N+iv_N)+iv_N)+iv_N = (iv_N+iv_N)+(iv_N+iv_N)

        // 3iv_N ≤ A  (transport h_3ivn_le_four RHS FOUR_N → A via four_eq_a).
        let motive_3 = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(self.rat.clone());
            let body = self.le(three_iv_n.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let h_3ivn_le_a = self.subst(
            motive_3,
            four_n.clone(),
            a_inv.clone(),
            four_eq_a.clone(),
            h_3ivn_le_four,
        ); // 3iv_N ≤ A

        // 3iv_N + iv_N ≤ A  (from equality e_tail_eq_four then four_eq_a; build via le_refl transport).
        //   tail_n = 3iv_N + iv_N ; e_tail_eq_four : tail_n = FOUR_N ; four_eq_a : FOUR_N = A.
        //   so tail_n = A; le_refl A transported back: A ≤ A, transport LHS A → tail_n.
        let tail_eq_a = self.trans_rat(
            tail_n.clone(),
            four_n.clone(),
            a_inv.clone(),
            e_tail_eq_four,
            four_eq_a,
        ); // tail_n = A
        let motive_tail = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(self.rat.clone());
            let body = self.le(t, a_inv.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let tail_eq_a_symm = self.symm(tail_n.clone(), a_inv.clone(), tail_eq_a); // A = tail_n
        let h_tail_le_a = self.subst(
            motive_tail,
            a_inv.clone(),
            tail_n.clone(),
            tail_eq_a_symm,
            self.le_refl(a_inv.clone()),
        ); // tail_n ≤ A

        // 7iv_N = 3iv_N + tail_n ≤ A + A  (add_le_add 3iv_N A tail_n A).
        let h_7ivn_le_aa = self.add_le_add(
            three_iv_n.clone(),
            a_inv.clone(),
            tail_n.clone(),
            a_inv.clone(),
            h_3ivn_le_a,
            h_tail_le_a,
        ); // 7iv_N ≤ A+A
           // transport RHS A+A → inv(2^M) via e_m.
        let motive_aa = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(self.rat.clone());
            let body = self.le(seven_n.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let h_7ivn_le_bigm = self.subst(
            motive_aa,
            a_plus_a.clone(),
            iv_big_m.clone(),
            e_m,
            h_7ivn_le_aa,
        ); // 7iv_N ≤ inv(2^M)

        // 7iv_m ≤ 7iv_N ≤ inv(2^M)  (le_trans).
        let h_7ivm_le_bigm = self.le_trans(
            seven_m.clone(),
            seven_n.clone(),
            iv_big_m.clone(),
            h_7iv_le,
            h_7ivn_le_bigm,
        ); // 7iv_m ≤ inv(2^M)
           // 7iv_m < ε  (lt_of_le_of_lt with hm).
        self.lt_of_le_of_lt(seven_m, iv_big_m.clone(), eps.clone(), h_7ivm_le_bigm, hm)
    }

    /// `@congrArg Rat Rat a b f h : f a = f b`.
    fn congr_arg_rat(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        let l1 = crate::level::Level::succ(crate::level::Level::zero());
        Expr::apps(
            Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `@Eq.trans Rat a b c h1 h2 : a = c`.
    fn trans_rat(&self, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
        let l1 = crate::level::Level::succ(crate::level::Level::zero());
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![l1]),
            [self.rat.clone(), a, b, c, h1, h2],
        )
    }
}

impl Environment {
    /// Rung 4a — `NNReal.cbrtDyadicApprox_cube_equiv_const`.
    pub(crate) fn register_cbrt_cube_equiv_const(
        &mut self,
        c: &CbrtIdentityConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNReal.cbrtDyadicApprox_cube_equiv_const");
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
            let concl = c.equiv(c.cmul3(&x), c.cconst(&x, &h0));
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, concl);
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
            b.finish(b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e))
        };
        let value = build_cube_equiv_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `fun x h0 h1 ε hpos => Exists.elim (exists_inv_two_pow_lt ε hpos) elim_fn`.
fn build_cube_equiv_value(c: &CbrtIdentityConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let h0_ty = c.le(c.rat_zero.clone(), x.clone());
    let (h0_id, h0) = b.fresh_local(h0_ty.clone());
    let h1_ty = c.lt(x.clone(), c.rat_one.clone());
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.lt(c.rat_zero.clone(), eps.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    // target ∃-pred over N (defeq to the cube conjuncts via the carrier defeqs):
    //   fun N => ∀ m, N≤m → And (a_m³ < x+ε)(x < a_m³+ε).
    let tgt_pred = |bb: &EnvDeclBuilder| -> Expr {
        let mut bn = EnvDeclBuilder::child_of(bb);
        let (cap_id, cap) = bn.fresh_local(c.nat.clone());
        let inner = {
            let mut bi = EnvDeclBuilder::child_of(&bn);
            let (m_id, m) = bi.fresh_local(c.nat.clone());
            let hle_ty = c.nat_le(cap.clone(), m.clone());
            let (hle_id, _hle) = bi.fresh_local(hle_ty.clone());
            let a3 = c.cube(c.approx(&x, m.clone()));
            let left = c.lt(a3.clone(), c.add(x.clone(), eps.clone()));
            let right = c.lt(x.clone(), c.add(a3.clone(), eps.clone()));
            let concl = c.and_ty(left, right);
            let e = bi.mk_pi(hle_id, BinderInfo::Default, hle_ty, concl);
            let e = bi.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
            bi.finish_child(e)
        };
        bn.finish_child(bn.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), inner))
    };

    // source: ∃ M, inv(2^M) < ε.
    let ex_mod = Expr::apps(c.exists_inv_two_pow_lt.clone(), [eps.clone(), hpos.clone()]);
    let src_pred = {
        let mut sp = EnvDeclBuilder::child_of(&b);
        let (sm_id, sm) = sp.fresh_local(c.nat.clone());
        let body = c.lt(c.inv_two_pow(sm.clone()), eps.clone());
        sp.finish_child(sp.mk_lam(sm_id, BinderInfo::Default, c.nat.clone(), body))
    };
    let tgt_goal = Expr::apps(c.exists_c.clone(), [c.nat.clone(), tgt_pred(&b)]);

    // x < x+ε (m-independent).
    let h_x_lt_xeps = c.x_lt_x_add_eps(&b, &x, &eps, hpos.clone());

    // elim_fn : (M:Nat) → (hM : inv(2^M) < ε) → ∃ N, tgt_pred N.
    let elim_fn = {
        let mut eb = EnvDeclBuilder::child_of(&b);
        let (bigm_id, big_m) = eb.fresh_local(c.nat.clone());
        let hm_ty = c.lt(c.inv_two_pow(big_m.clone()), eps.clone());
        let (hm_id, hm) = eb.fresh_local(hm_ty.clone());

        // witness N := succ(succ(succ M)) = M+3.
        let big_n = c.succ(c.succ(c.succ(big_m.clone())));

        let witness = {
            let mut wb = EnvDeclBuilder::child_of(&eb);
            let (m_id, m) = wb.fresh_local(c.nat.clone());
            let hle_ty = c.nat_le(big_n.clone(), m.clone());
            let (hle_id, hle) = wb.fresh_local(hle_ty.clone());

            let a3 = c.cube(c.approx(&x, m.clone()));
            let left_ty = c.lt(a3.clone(), c.add(x.clone(), eps.clone()));
            let right_ty = c.lt(x.clone(), c.add(a3.clone(), eps.clone()));

            let left = c.lower_conjunct(&x, &m, &h0, h_x_lt_xeps.clone(), &eps);
            let h_7iv = c.seven_iv_lt_eps(&wb, &eps, &m, &big_m, hle, hm.clone());
            let right = c.upper_conjunct(&x, &eps, &m, &h0, &h1, h_7iv);
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
