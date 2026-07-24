// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// RUNG-B per-S core: `BoolAnalysis.lowband_term_le`. Included from
// `boolean_analysis_kkl_rungb.rs` (shares `RungBConsts`).
//
//   ∀ (size c : Rat) (b1 b2 : Bool),
//     0 ≤ c → 0 ≤ size → (b1 = true → Rat.one ≤ size)
//       → four · (ind (and b1 b2) · c) ≤ size · (ind b2 · (four · c))
//
// Proof: `Bool.rec` on `b1` (the FIRST `and`-argument, so `and b1 b2`
// δ-reduces), then `Bool.rec` on `b2`:
//   * b1=false: `and false b2 ≡ false`, `ind false ≡ 0`, LHS ≡ four·(0·c) → 0;
//     RHS ≥ 0 by `mul_nonneg` twice (size≥0, ind b2·(four·c)≥0). The
//     `b1=true→1≤size` hypothesis is NOT used here.
//   * b1=true: `and true b2 ≡ b2`. Sub-`Bool.rec` on b2:
//       - b2=false: both sides reduce to 0 (ind false ≡ 0); 0 ≤ 0 by le_refl.
//       - b2=true: `ind true ≡ 1`. Goal ≡ four·(1·c) ≤ size·(1·(four·c)).
//         `one_mul` rewrites collapse to `(four·c) ≤ size·(four·c)`, closed by
//         `mul_le_mul_of_nonneg_right` with `1≤size` (from the hypothesis) and
//         `0≤four·c` (`mul_nonneg`, `0≤four` by le_refl-of-defeq).

impl RungBConsts {
    /// `0 ≤ a` as `@LE.le Rat instLERat Rat.zero a`.
    fn nonneg(&self, a: Expr) -> Expr {
        self.rat_le(self.rat_zero.clone(), a)
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]),
            [a, b, ha, hb],
        )
    }
    /// `Rat.mul_le_mul_of_nonneg_right a bv cv h_bc h_a : bv·a ≤ cv·a`.
    fn mul_le_right(&self, a: Expr, bv: Expr, cv: Expr, h_bc: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_right"), vec![]),
            [a, bv, cv, h_bc, h_a],
        )
    }
    /// `Rat.le_refl a : a ≤ a`.
    fn le_refl(&self, a: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Rat.le_refl"), vec![]), a)
    }
    /// `Rat.one_mul a : Rat.one · a = a`.
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Rat.one_mul"), vec![]), a)
    }
    /// `Rat.zero_mul a : Rat.zero · a = Rat.zero`.
    fn zero_mul(&self, a: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Rat.zero_mul"), vec![]), a)
    }
    /// `Rat.mul_zero a : a · Rat.zero = Rat.zero`.
    fn mul_zero(&self, a: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Rat.mul_zero"), vec![]), a)
    }
}

/// `∀ (size c : Rat) (b1 b2 : Bool), 0≤c → 0≤size → (b1=true → 1≤size)
///    → four·(ind (and b1 b2)·c) ≤ size·(ind b2·(four·c))`.
fn lowband_term_type(c: &RungBConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (size_id, size) = b.fresh_local(c.rat());
    let (cv_id, cv) = b.fresh_local(c.rat());
    let (b1_id, b1) = b.fresh_local(c.bool_.clone());
    let (b2_id, b2) = b.fresh_local(c.bool_.clone());

    let h_c_ty = c.nonneg(cv.clone());
    let h_size_ty = c.nonneg(size.clone());
    let h_thr_ty = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let ante = c.eq_bool(b1.clone(), c.bool_true.clone());
        let (a_id, _) = ch.fresh_local(ante.clone());
        let cons = c.rat_le(c.rat_one.clone(), size.clone());
        ch.finish_child(ch.mk_pi(a_id, BinderInfo::Default, ante, cons))
    };

    let concl = lowband_goal(c, &size, &cv, &b1, &b2);

    let (hc_id, _) = b.fresh_local(h_c_ty.clone());
    let (hsize_id, _) = b.fresh_local(h_size_ty.clone());
    let (hthr_id, _) = b.fresh_local(h_thr_ty.clone());
    let e = b.mk_pi(hthr_id, BinderInfo::Default, h_thr_ty, concl);
    let e = b.mk_pi(hsize_id, BinderInfo::Default, h_size_ty, e);
    let e = b.mk_pi(hc_id, BinderInfo::Default, h_c_ty, e);
    let e = b.mk_pi(b2_id, BinderInfo::Default, c.bool_.clone(), e);
    let e = b.mk_pi(b1_id, BinderInfo::Default, c.bool_.clone(), e);
    let e = b.mk_pi(cv_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_pi(size_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// `four·(ind (and b1 b2)·c) ≤ size·(ind b2·(four·c))` for given b1,b2.
fn lowband_goal(c: &RungBConsts, size: &Expr, cv: &Expr, b1: &Expr, b2: &Expr) -> Expr {
    let lhs = c.mul(
        c.four(),
        c.mul(c.ind_of(c.band(b1.clone(), b2.clone())), cv.clone()),
    );
    let rhs = c.mul(
        size.clone(),
        c.mul(c.ind_of(b2.clone()), c.mul(c.four(), cv.clone())),
    );
    c.rat_le(lhs, rhs)
}

fn build_lowband_term_proof(c: &RungBConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (size_id, size) = b.fresh_local(c.rat());
    let (cv_id, cv) = b.fresh_local(c.rat());
    let (b1_id, b1) = b.fresh_local(c.bool_.clone());
    let (b2_id, b2) = b.fresh_local(c.bool_.clone());

    let h_c_ty = c.nonneg(cv.clone());
    let h_size_ty = c.nonneg(size.clone());
    let h_thr_ty = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let ante = c.eq_bool(b1.clone(), c.bool_true.clone());
        let (a_id, _) = ch.fresh_local(ante.clone());
        let cons = c.rat_le(c.rat_one.clone(), size.clone());
        ch.finish_child(ch.mk_pi(a_id, BinderInfo::Default, ante, cons))
    };
    let (hc_id, h_c) = b.fresh_local(h_c_ty.clone());
    let (hsize_id, h_size) = b.fresh_local(h_size_ty.clone());
    let (hthr_id, h_thr) = b.fresh_local(h_thr_ty.clone());

    let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let bool_true = c.bool_true.clone();
    let four = c.four();
    let four_c = c.mul(four.clone(), cv.clone());
    let zero = c.rat_zero.clone();
    let one = c.rat_one.clone();

    // motive (outer, on b1) : fun (b1' : Bool) =>
    //   (b1' = true → 1 ≤ size) → goal(size, c, b1', b2)
    // (the threshold hypothesis is carried INTO the motive so the true-branch
    // can apply it at b1' := true; the false branch ignores it.)
    let thr_ty_of_b1 = |b1p: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let ante = c.eq_bool(b1p.clone(), bool_true.clone());
        let (a_id, _) = ch.fresh_local(ante.clone());
        let cons = c.rat_le(one.clone(), size.clone());
        ch.finish_child(ch.mk_pi(a_id, BinderInfo::Default, ante, cons))
    };
    let outer_motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (b1p_id, b1p) = m.fresh_local(c.bool_.clone());
        let thr = thr_ty_of_b1(&b1p, &m);
        let (h_id, _) = m.fresh_local(thr.clone());
        let imp = m.mk_pi(
            h_id,
            BinderInfo::Default,
            thr,
            lowband_goal(c, &size, &cv, &b1p, &b2),
        );
        m.finish_child(m.mk_lam(b1p_id, BinderInfo::Default, c.bool_.clone(), imp))
    };

    // ── b1 = false branch: ignore the hypothesis; goal(false, b2).
    //   and false b2 ≡ false, ind false ≡ 0 ⇒ LHS ≡ four·(0·c).
    //   RHS = size·(ind b2·(four·c)) ≥ 0.
    let b1_false_case = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let thr_false = thr_ty_of_b1(&bool_false, &m);
        let (h_id, _) = m.fresh_local(thr_false.clone());

        // ind b2 · (four·c)
        let ind_b2 = c.ind_of(b2.clone());
        let inner = c.mul(ind_b2.clone(), four_c.clone());
        let rhs = c.mul(size.clone(), inner.clone());

        // h_fourc_nn : 0 ≤ four·c   [mul_nonneg four c (le_refl-of-defeq 0≤four) h_c]
        //   0 ≤ four is `le_refl`-provable only at four; instead build via
        //   `mul_nonneg` needs 0≤four. We get 0≤four from `four = mk(ofNat 4) 1`
        //   being a nonneg literal: use the dedicated `four_nonneg` term.
        let h_four_nn = four_nonneg(c);
        let h_fourc_nn = c.mul_nonneg(four.clone(), cv.clone(), h_four_nn, h_c.clone());
        // h_inner_nn : 0 ≤ ind b2·(four·c)   [mul_nonneg (ind b2) (four·c) (ind_nonneg b2) h_fourc_nn]
        let h_indb2_nn = ind_nonneg(c, &b2);
        let h_inner_nn = c.mul_nonneg(ind_b2.clone(), four_c.clone(), h_indb2_nn, h_fourc_nn);
        // h_rhs_nn : 0 ≤ size·(ind b2·(four·c))  [mul_nonneg size inner h_size h_inner_nn]
        let h_rhs_nn = c.mul_nonneg(size.clone(), inner.clone(), h_size.clone(), h_inner_nn);

        // Transport 0 ≤ rhs along 0 = four·(0·c) to get four·(0·c) ≤ rhs.
        //   The goal (after δ) LHS is four·(ind false · c) ≡ four·(0·c).
        //   e0 : 0·c = 0   [zero_mul c]
        //   e1 : four·(0·c) = four·0   via subst (motive t => four·(0·c) = four·t)
        //   e2 : four·0 = 0   [mul_zero four]
        //   e_lhs0 : four·(0·c) = 0 (trans e1 e2); symm → 0 = four·(0·c);
        //   subst h_rhs_nn (0 ≤ rhs) along that.
        let zero_mul_c = c.mul(zero.clone(), cv.clone()); // 0·c
        let four_zero_mul_c = c.mul(four.clone(), zero_mul_c.clone()); // four·(0·c)
        let four_zero = c.mul(four.clone(), zero.clone()); // four·0

        let e0 = c.zero_mul(cv.clone());
        let motive1 = {
            let mut mm = EnvDeclBuilder::child_of(&m);
            let (t_id, t) = mm.fresh_local(c.rat());
            let body = c.eq_rat(four_zero_mul_c.clone(), c.mul(four.clone(), t));
            mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        let refl_base = c.refl_rat(four_zero_mul_c.clone());
        let e1 = c.subst_rat(motive1, zero_mul_c.clone(), zero.clone(), e0, refl_base);
        let e2 = c.mul_zero(four.clone());
        let e_lhs0 = c.trans_rat(four_zero_mul_c.clone(), four_zero, zero.clone(), e1, e2);
        let e_sym = c.symm_rat(four_zero_mul_c.clone(), zero.clone(), e_lhs0);
        let motive2 = {
            let mut mm = EnvDeclBuilder::child_of(&m);
            let (t_id, t) = mm.fresh_local(c.rat());
            let body = c.rat_le(t, rhs.clone());
            mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        let proof = c.subst_rat(motive2, zero.clone(), four_zero_mul_c, e_sym, h_rhs_nn);
        m.finish_child(m.mk_lam(h_id, BinderInfo::Default, thr_false, proof))
    };

    // ── b1 = true branch: and true b2 ≡ b2. Sub-Bool.rec on b2.
    let b1_true_case = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let thr_true = thr_ty_of_b1(&bool_true, &m);
        let (ht_id, ht) = m.fresh_local(thr_true.clone());

        // h1size : 1 ≤ size   [ht (refl true)]
        let h1size = Expr::app(ht, c.refl_bool(bool_true.clone()));

        // Goal at b1=true is `goal(size, c, true, b2)` whose LHS `and true b2 ≡ b2`.
        // We prove `four·(ind b2·c) ≤ size·(ind b2·(four·c))` by Bool.rec on b2.

        // inner motive (on b2') : fun (b2' : Bool) =>
        //   four·(ind b2'·c) ≤ size·(ind b2'·(four·c))
        let inner_goal = |b2p: &Expr| -> Expr {
            let lhs = c.mul(four.clone(), c.mul(c.ind_of(b2p.clone()), cv.clone()));
            let rhs = c.mul(size.clone(), c.mul(c.ind_of(b2p.clone()), four_c.clone()));
            c.rat_le(lhs, rhs)
        };
        let inner_motive = {
            let mut mm = EnvDeclBuilder::child_of(&m);
            let (b2p_id, b2p) = mm.fresh_local(c.bool_.clone());
            let body = inner_goal(&b2p);
            mm.finish_child(mm.mk_lam(b2p_id, BinderInfo::Default, c.bool_.clone(), body))
        };

        // b2=false: ind false ≡ 0. LHS ≡ four·(0·c), RHS ≡ size·(0·(four·c)).
        //   Both reduce to 0 via the same algebra; prove 0 ≤ 0 (le_refl 0) and
        //   transport both ends.
        let b2_false_proof = {
            // LHS chain: four·(0·c) = 0  (as in the b1=false branch)
            let zero_mul_c = c.mul(zero.clone(), cv.clone());
            let four_zero_mul_c = c.mul(four.clone(), zero_mul_c.clone());
            let four_zero = c.mul(four.clone(), zero.clone());
            let e0 = c.zero_mul(cv.clone());
            let motive_l = {
                let mut mm = EnvDeclBuilder::child_of(&m);
                let (t_id, t) = mm.fresh_local(c.rat());
                let body = c.eq_rat(four_zero_mul_c.clone(), c.mul(four.clone(), t));
                mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };
            let e1 = c.subst_rat(
                motive_l,
                zero_mul_c.clone(),
                zero.clone(),
                e0,
                c.refl_rat(four_zero_mul_c.clone()),
            );
            let e2 = c.mul_zero(four.clone());
            let e_lhs0 = c.trans_rat(four_zero_mul_c.clone(), four_zero, zero.clone(), e1, e2);
            // 0 = four·(0·c)
            let e_lhs_sym = c.symm_rat(four_zero_mul_c.clone(), zero.clone(), e_lhs0);

            // RHS chain: size·(0·(four·c)) = 0
            let zero_fourc = c.mul(zero.clone(), four_c.clone()); // 0·(four·c)
            let size_zero_fourc = c.mul(size.clone(), zero_fourc.clone());
            let size_zero = c.mul(size.clone(), zero.clone());
            let er0 = c.zero_mul(four_c.clone()); // 0·(four·c) = 0
            let motive_r = {
                let mut mm = EnvDeclBuilder::child_of(&m);
                let (t_id, t) = mm.fresh_local(c.rat());
                let body = c.eq_rat(size_zero_fourc.clone(), c.mul(size.clone(), t));
                mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };
            let er1 = c.subst_rat(
                motive_r,
                zero_fourc.clone(),
                zero.clone(),
                er0,
                c.refl_rat(size_zero_fourc.clone()),
            );
            let er2 = c.mul_zero(size.clone());
            let e_rhs0 = c.trans_rat(size_zero_fourc.clone(), size_zero, zero.clone(), er1, er2);

            // Build 0 ≤ 0 then transport: first LHS 0→four·(0·c), then RHS 0→size·(0·(four·c)).
            // start: le_refl 0 : 0 ≤ 0
            let h00 = c.le_refl(zero.clone());
            // transport RHS: motive t => 0 ≤ t along (0 = size·(0·(four·c))) i.e. symm e_rhs0
            let e_rhs_sym = c.symm_rat(size_zero_fourc.clone(), zero.clone(), e_rhs0);
            let motive_rr = {
                let mut mm = EnvDeclBuilder::child_of(&m);
                let (t_id, t) = mm.fresh_local(c.rat());
                let body = c.rat_le(zero.clone(), t);
                mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };
            // h_0_le_rhs : 0 ≤ size·(0·(four·c))
            let h_0_le_rhs = c.subst_rat(
                motive_rr,
                zero.clone(),
                size_zero_fourc.clone(),
                e_rhs_sym,
                h00,
            );
            // transport LHS: motive t => t ≤ size·(0·(four·c)) along (0 = four·(0·c))
            let motive_ll = {
                let mut mm = EnvDeclBuilder::child_of(&m);
                let (t_id, t) = mm.fresh_local(c.rat());
                let body = c.rat_le(t, size_zero_fourc.clone());
                mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };
            c.subst_rat(
                motive_ll,
                zero.clone(),
                four_zero_mul_c.clone(),
                e_lhs_sym,
                h_0_le_rhs,
            )
        };

        // b2=true: ind true ≡ 1. LHS ≡ four·(1·c), RHS ≡ size·(1·(four·c)).
        //   base : (four·c) ≤ size·(four·c)   [mul_le_right (four·c) 1 size h1size h_fourc_nn]
        //     ≡ 1·(four·c) ≤ size·(four·c) after one_mul; then transport.
        let b2_true_proof = {
            let h_four_nn = four_nonneg(c);
            let h_fourc_nn = c.mul_nonneg(four.clone(), cv.clone(), h_four_nn, h_c.clone());
            // base0 : 1·(four·c) ≤ size·(four·c)
            //   mul_le_mul_of_nonneg_right (four·c) 1 size h1size h_fourc_nn
            let base0 = c.mul_le_right(
                four_c.clone(),
                one.clone(),
                size.clone(),
                h1size.clone(),
                h_fourc_nn.clone(),
            );
            // Goal at b2=true: four·(1·c) ≤ size·(1·(four·c)).
            //   We have base0 : 1·(four·c) ≤ size·(four·c).
            //   RHS: size·(four·c) = size·(1·(four·c))?  one_mul (four·c): 1·(four·c)=four·c;
            //     symm → four·c = 1·(four·c); subst into RHS of base0.
            //   LHS: 1·(four·c) vs four·(1·c). We need to rewrite base0's LHS
            //     `1·(four·c)` to `four·(1·c)`. Both equal four·c:
            //       1·(four·c) = four·c   [one_mul (four·c)]
            //       four·(1·c) = four·c   [congr four · (one_mul c)] → four·c
            //     so chain `four·(1·c) = four·c = 1·(four·c)` and subst.
            let one_fourc = c.mul(one.clone(), four_c.clone()); // 1·(four·c)
            let size_one_fourc = c.mul(size.clone(), one_fourc.clone()); // size·(1·(four·c))
            let one_c = c.mul(one.clone(), cv.clone()); // 1·c
            let four_one_c = c.mul(four.clone(), one_c.clone()); // four·(1·c)

            // RHS transport: base0 RHS size·(four·c) → size·(1·(four·c)).
            //   e_rhs : four·c = 1·(four·c)   [symm (one_mul (four·c))]
            let e_rhs = c.symm_rat(one_fourc.clone(), four_c.clone(), c.one_mul(four_c.clone()));
            //   subst motive t => 1·(four·c) ≤ size·t  (transport RHS of base0)
            let motive_rhs = {
                let mut mm = EnvDeclBuilder::child_of(&m);
                let (t_id, t) = mm.fresh_local(c.rat());
                let body = c.rat_le(one_fourc.clone(), c.mul(size.clone(), t));
                mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };
            // step1 : 1·(four·c) ≤ size·(1·(four·c))
            let step1 = c.subst_rat(motive_rhs, four_c.clone(), one_fourc.clone(), e_rhs, base0);

            // LHS transport: 1·(four·c) → four·(1·c).
            //   eL1 : 1·(four·c) = four·c   [one_mul (four·c)]
            //   eL2 : four·c = four·(1·c)   [symm (congrArg (four · ·) (one_mul c))]
            //         one_mul c : 1·c = c ; symm → c = 1·c ; congrArg (four·) : four·c = four·(1·c)
            //   eL : 1·(four·c) = four·(1·c)  [trans eL1 eL2]
            let e_l1 = c.one_mul(four_c.clone()); // 1·(four·c) = four·c
            let c_eq_onec = c.symm_rat(one_c.clone(), cv.clone(), c.one_mul(cv.clone())); // c = 1·c
            let e_l2 = congr_arg_mul_left(c, &four, cv.clone(), one_c.clone(), c_eq_onec); // four·c = four·(1·c)
            let e_l = c.trans_rat(
                one_fourc.clone(),
                four_c.clone(),
                four_one_c.clone(),
                e_l1,
                e_l2,
            );
            //   subst motive t => t ≤ size·(1·(four·c))  along (1·(four·c) = four·(1·c))
            let motive_lhs = {
                let mut mm = EnvDeclBuilder::child_of(&m);
                let (t_id, t) = mm.fresh_local(c.rat());
                let body = c.rat_le(t, size_one_fourc.clone());
                mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };
            c.subst_rat(motive_lhs, one_fourc.clone(), four_one_c, e_l, step1)
        };

        // inner Bool.rec on b2.
        let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![c.u0.clone()]);
        let inner = Expr::apps(
            bool_rec,
            [inner_motive, b2_false_proof, b2_true_proof, b2.clone()],
        );
        m.finish_child(m.mk_lam(ht_id, BinderInfo::Default, thr_true, inner))
    };

    // outer Bool.rec on b1 : (b1=true → 1≤size) → goal(b1), applied to h_thr.
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![c.u0.clone()]);
    let rec = Expr::apps(
        bool_rec,
        [outer_motive, b1_false_case, b1_true_case, b1.clone()],
    );
    let body = Expr::app(rec, h_thr);

    let e = b.mk_lam(hthr_id, BinderInfo::Default, h_thr_ty, body);
    let e = b.mk_lam(hsize_id, BinderInfo::Default, h_size_ty, e);
    let e = b.mk_lam(hc_id, BinderInfo::Default, h_c_ty, e);
    let e = b.mk_lam(b2_id, BinderInfo::Default, c.bool_.clone(), e);
    let e = b.mk_lam(b1_id, BinderInfo::Default, c.bool_.clone(), e);
    let e = b.mk_lam(cv_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_lam(size_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// `0 ≤ four` — `four = mk (ofNat 4) 1` is a nonneg literal; `Rat.le_refl`
/// does not give this, so build it from `Rat.zero_le_natCast`-style nonnegativity.
/// We use the landed `BoolAnalysis.natCast_nonneg` at `k := 4`: it proves
/// `0 ≤ mk (ofNat 4) 1`, which is exactly `0 ≤ four`.
fn four_nonneg(c: &RungBConsts) -> Expr {
    let four_nat = c.succ(c.succ(c.succ(c.succ(c.nat_zero.clone()))));
    Expr::app(
        Expr::const_(Name::from_string("BoolAnalysis.natCast_nonneg"), vec![]),
        four_nat,
    )
}

/// `0 ≤ ind b` for any `b : Bool` — `BoolAnalysis.ind_nonneg b`.
fn ind_nonneg(c: &RungBConsts, b: &Expr) -> Expr {
    let _ = c;
    Expr::app(
        Expr::const_(Name::from_string("BoolAnalysis.ind_nonneg"), vec![]),
        b.clone(),
    )
}

/// `congrArg (fun t => a·t) (h : x = y) : a·x = a·y`.
fn congr_arg_mul_left(c: &RungBConsts, a: &Expr, x: Expr, y: Expr, h: Expr) -> Expr {
    let g = {
        let mut d = EnvDeclBuilder::new();
        let (t_id, t) = d.fresh_local(c.rat());
        let body = c.mul(a.clone(), t);
        d.finish(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
    };
    Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![c.u1.clone(), c.u1.clone()],
        ),
        [c.rat(), c.rat(), x, y, g, h],
    )
}
