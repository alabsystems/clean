// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Friedgut junta-theorem roadmap — STEP (c): the i∉J-MASKED dual-HC aggregate.
// `include!`d into `boolean_analysis_kkl_dualhc_percoord.rs` so it shares
// `PerCoordConsts` and the per-coordinate `W_norm` / nonneg witnesses
// byte-for-byte with the (unmasked) aggregate + reflect. (Regular `//` comments
// only — inner doc `//!` is not allowed at an `include!` site.)
//
// ## Why a MASKED aggregate (and why the landed unmasked one is not enough)
//
// The landed `BoolAnalysis.kkl_wnorm_sum_le_rat` sums `W_norm_i` over ALL
// coordinates under the UNIFORM hypothesis `∀ i, Inf_i ≤ d·d`. Friedgut needs
// the OUTSIDE-`J`-masked version: the witness junta `J := {i : Inf_i ≥ τ}` makes
// the inside-`J` influences LARGE (`≥ τ`, possibly `≥ 1`), so the uniform
// hypothesis FAILS and the per-coordinate dual-HC brick (which needs `Inf_i < 1`)
// cannot even be stated there. The masked aggregate restricts the sum and the
// hypothesis to the outside-`J` coordinates `m i := (Inf_i < τ)`.
//
// ## What this proves
//
//   (2a) BoolAnalysis.kkl_wnorm_le_d_inf_masked :    -- per-coordinate Rat bound
//     ∀ (n : Nat) (f : BoolFn n) (d : Rat) (i : Fin n)
//       (hd : 0 ≤ d) (hdd0 : 0 ≤ d·d) (hdd1 : d·d < 1)
//       (h0i : 0 ≤ Influence n f i) (h1i : Influence n f i ≤ d·d),
//       Rat.le W_norm_i (Rat.mul (Rat.ofNat 4) (Rat.mul d (Influence n f i)))
//
//   (2b) BoolAnalysis.kkl_wnorm_sum_le_rat_masked :  -- the masked aggregate
//     ∀ (n : Nat) (f : BoolFn n) (m : Fin n → Bool) (d : Rat)
//       (hd : 0 ≤ d) (hdd0 : 0 ≤ d·d) (hdd1 : d·d < 1)
//       (h0 : ∀ i, 0 ≤ Influence n f i)
//       (h1m : ∀ i, m i = Bool.true → Influence n f i ≤ d·d),
//       Rat.le (Fin.sum n (fun i => Rat.mul (ind (m i)) W_norm_i))
//              (Rat.mul (Rat.ofNat 4) (Rat.mul d (TotalInfluence n f)))
//
// i.e. `Σ_{i: m i} ‖T_{1/3} D_i f‖₂² ≤ 4·(d·I[f])` with `d` the Rat stand-in for
// `√τ` (`Inf_i ≤ d·d = τ` on the mask). N-FREE.
//
// ## Proof (constructive, EMPTY admitted-axiom closure)
//
// (2a) per-coordinate, all in NNReal then reflect to Rat:
//   1. `dualhc_per_coord_uncond n f i h0i (Inf_i<1)` :
//        ofRat W_norm_i ≤ 4·pow32 Inf_i    (Inf_i<1 := lt_of_le_of_lt Inf_i (d·d) 1 h1i hdd1).
//   2. `pow32_le_sqrt_eps_mul Inf_i (d·d) h0i h1i hdd1` :
//        pow32 Inf_i ≤ sqrtRat(d·d)·ofRat Inf_i.
//   3. `sqrtRat_sq_le_ofRat d hd hdd0 hdd1` : sqrtRat(d·d) ≤ ofRat d, scaled on the
//      RIGHT by ofRat Inf_i (`mul_le_mul_left` after `mul_comm` twice — the
//      left-factor-monotonicity idiom borrowed from `aggregate_reflect`):
//        sqrtRat(d·d)·ofRat Inf_i ≤ ofRat d · ofRat Inf_i.
//   4. `ofRat_mul d Inf_i hd h0i h_dInf` : ofRat d · ofRat Inf_i = ofRat(d·Inf_i).
//   chain (2)+(3)+eq(4): pow32 Inf_i ≤ ofRat(d·Inf_i); scale by 4 (mul_le_mul_left)
//   and ofRat_mul 4 (d·Inf_i): 4·pow32 Inf_i ≤ ofRat(4·(d·Inf_i)); chain with (1):
//   ofRat W_norm_i ≤ ofRat(4·(d·Inf_i)); reflect via `ofRat_le_ofRat_rev`.
//
// (2b) Rat masked-sum assembly over (2a) + STEP (b) masked finSum lemmas:
//   1. per_i_cond : ∀ i, m i = true → W_norm_i ≤ 4·(d·Inf_i)
//        := fun i he => kkl_wnorm_le_d_inf_masked n f d i hd hdd0 hdd1 (h0 i)(h1m i he).
//   2. mono : Σ ind(m i)·W_norm_i ≤ Σ ind(m i)·(4·(d·Inf_i))
//        := masked_finSum_le_cond n m (fun i => W_norm_i)(fun i => 4·(d·Inf_i)) per_i_cond.
//   3. smul₁ : Σ ind(m i)·(4·(d·Inf_i)) = 4·Σ ind(m i)·(d·Inf_i)
//        := masked_finSum_smul n m 4 (fun i => d·Inf_i).
//   4. smul₂ : Σ ind(m i)·(d·Inf_i) = d·Σ ind(m i)·Inf_i
//        := masked_finSum_smul n m d (fun i => Inf_i).
//   5. full : Σ ind(m i)·Inf_i ≤ Σ Inf_i = I[f]
//        := masked_finSum_le_full n m (fun i => Inf_i) h0   (Fin.sum n Inf ≡ TotalInfluence).
//   chain: Σ ind(m)·W_norm ≤[2] 4·(d·Σ ind(m)·Inf) ≤[mul_le_mul_left, full×2] 4·(d·I[f]),
//   transporting the two `smul` equalities through `Eq.subst`.
//
// Every leaf (`dualhc_per_coord_uncond`, `pow32_le_sqrt_eps_mul`,
// `sqrtRat_sq_le_ofRat`, `NNReal.ofRat_mul`, `NNReal.ofRat_le_ofRat_rev`,
// `NNReal.mul_le_mul_left`, `NNReal.mul_comm`, `NNReal.le.trans`,
// `masked_finSum_le_cond`/`_smul`/`_le_full`, `Rat.mul_le_mul_of_nonneg_left`,
// `Rat.lt_of_le_of_lt`, `Rat.mul_nonneg`, `Eq.*`) is a landed `Constructive`
// empty-closure Theorem, so both lemmas here are too. No axiom added or removed.

impl PerCoordConsts {
    // ── extra NNReal leaves the masked per-coord bound needs (lazily built) ──
    fn nn_sqrtrat(&self, x: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("NNReal.sqrtRat"), vec![]),
            x.clone(),
        )
    }
    /// `NNReal.pow32_le_sqrt_eps_mul x eps h0 hxe he1 :
    ///   le (pow32 x h0)(mul (sqrtRat eps)(ofRat x h0))`.
    fn nn_pow32_bound(&self, x: &Expr, eps: &Expr, h0: Expr, hxe: Expr, he1: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.pow32_le_sqrt_eps_mul"), vec![]),
            [x.clone(), eps.clone(), h0, hxe, he1],
        )
    }
    /// `NNReal.sqrtRat_sq_le_ofRat d hd hdd0 hdd1 : le (sqrtRat (d·d))(ofRat d hd)`.
    fn nn_sqrt_sq_le(&self, d: &Expr, hd: Expr, hdd0: Expr, hdd1: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.sqrtRat_sq_le_ofRat"), vec![]),
            [d.clone(), hd, hdd0, hdd1],
        )
    }
    /// `NNReal.ofRat_mul a b ha hb hab : Eq (mul (ofRat a ha)(ofRat b hb))(ofRat (a·b) hab)`.
    fn nn_ofrat_mul(&self, a: &Expr, b: &Expr, ha: Expr, hb: Expr, hab: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.ofRat_mul"), vec![]),
            [a.clone(), b.clone(), ha, hb, hab],
        )
    }
    /// `NNReal.ofRat_le_ofRat_rev a b ha hb (h : le (ofRat a ha)(ofRat b hb)) : Rat.le a b`.
    fn nn_ofrat_le_rev(&self, a: &Expr, b: &Expr, ha: Expr, hb: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.ofRat_le_ofRat_rev"), vec![]),
            [a.clone(), b.clone(), ha, hb, h],
        )
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn rat_mul_nonneg(&self, a: &Expr, b: &Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]),
            [a.clone(), b.clone(), ha, hb],
        )
    }
    /// `Rat.lt_of_le_of_lt a b c (a≤b)(b<c) : a < c`.
    fn rat_lt_of_le_of_lt(&self, a: &Expr, b: &Expr, cc: &Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.lt_of_le_of_lt"), vec![]),
            [a.clone(), b.clone(), cc.clone(), hab, hbc],
        )
    }
    /// `Eq.subst.{1} Rat motive a b h_eq h`.
    fn rat_subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `Eq.symm.{1} Rat a b h`.
    fn rat_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            bit,
        )
    }
}

// ── (2a) the per-coordinate masked Rat bound `W_norm_i ≤ 4·(d·Inf_i)`. ──
fn build_wnorm_le_d_inf_masked(c: &PerCoordConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.bool_fn_of(&n));
    let (d_id, d) = b.fresh_local(c.rat.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));
    let dd = c.mul(d.clone(), d.clone());

    let hd_ty = c.le(c.rat_zero.clone(), d.clone());
    let (hd_id, hd) = b.fresh_local(hd_ty.clone());
    let hdd0_ty = c.le(c.rat_zero.clone(), dd.clone());
    let (hdd0_id, hdd0) = b.fresh_local(hdd0_ty.clone());
    let hdd1_ty = c.lt(dd.clone(), c.rat_one.clone());
    let (hdd1_id, hdd1) = b.fresh_local(hdd1_ty.clone());
    let inf = c.influence_of(&n, &f, &i);
    let h0i_ty = c.le(c.rat_zero.clone(), inf.clone());
    let (h0i_id, h0i) = b.fresh_local(h0i_ty.clone());
    let h1i_ty = c.le(inf.clone(), dd.clone());
    let (h1i_id, h1i) = b.fresh_local(h1i_ty.clone());

    let (w_norm, h_wnorm) = c.w_norm_and_nonneg(&b, &n, &f, &i);
    let four = c.ofnat(4);
    let d_inf = c.mul(d.clone(), inf.clone()); // d·Inf_i
    let four_d_inf = c.mul(four.clone(), d_inf.clone()); // 4·(d·Inf_i)
    let concl = c.le(w_norm.clone(), four_d_inf.clone());

    let body = if for_value {
        // NNReal carriers.
        let of_wnorm = c.nn_of_rat(w_norm.clone(), h_wnorm.clone()); // ofRat W_norm_i
        let of_inf = c.nn_of_rat(inf.clone(), h0i.clone()); // ofRat Inf_i
        let four_nn = c.nn_of_rat(four.clone(), c.h_four_nonneg()); // ofRat 4
        let z = c.nn_of_rat(d.clone(), hd.clone()); // ofRat d
        let sqrt_dd = c.nn_sqrtrat(&dd); // sqrtRat(d·d)
        let pow32_inf = c.nn_pow32(inf.clone(), h0i.clone()); // pow32 Inf_i
        let four_pow32 = c.nn_mul(four_nn.clone(), pow32_inf.clone()); // 4·pow32 Inf_i

        // (1) hbase : ofRat W_norm_i ≤ 4·pow32 Inf_i.
        //   Inf_i < 1 := lt_of_le_of_lt Inf_i (d·d) 1 h1i hdd1.
        let hinf_lt1 =
            c.rat_lt_of_le_of_lt(&inf, &dd, &c.rat_one.clone(), h1i.clone(), hdd1.clone());
        let hbase = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.dualhc_per_coord_uncond"),
                vec![],
            ),
            [n.clone(), f.clone(), i.clone(), h0i.clone(), hinf_lt1],
        );

        // (2) hp : pow32 Inf_i ≤ sqrtRat(d·d)·ofRat Inf_i.
        let sqrt_of_inf = c.nn_mul(sqrt_dd.clone(), of_inf.clone());
        let hp = c.nn_pow32_bound(&inf, &dd, h0i.clone(), h1i.clone(), hdd1.clone());

        // (3) sqrtRat(d·d)·ofRat Inf_i ≤ ofRat d · ofRat Inf_i.
        //   Left-factor monotonicity: build via mul_comm twice + mul_le_mul_left.
        //   hsq : sqrtRat(d·d) ≤ ofRat d.
        let hsq = c.nn_sqrt_sq_le(&d, hd.clone(), hdd0.clone(), hdd1.clone());
        //   e1 : sqrtRat·ofRat Inf = ofRat Inf · sqrtRat  (mul_comm).
        let inf_sqrt = c.nn_mul(of_inf.clone(), sqrt_dd.clone());
        let e1 = c.nn_mul_comm(sqrt_dd.clone(), of_inf.clone());
        //   hbm : ofRat Inf · sqrtRat ≤ ofRat Inf · ofRat d  (mul_le_mul_left of_inf … hsq).
        let inf_z = c.nn_mul(of_inf.clone(), z.clone());
        let hbm = c.nn_mul_le_mul_left(of_inf.clone(), sqrt_dd.clone(), z.clone(), hsq);
        //   step_a : sqrtRat·ofRat Inf ≤ ofRat Inf · ofRat d  (subst (symm e1) hbm on LHS).
        let e1_symm = c.rat_symm_nn(sqrt_of_inf.clone(), inf_sqrt.clone(), e1);
        let motive_a = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = m.fresh_local(c.nnreal.clone());
            let body = c.nn_le(t, inf_z.clone());
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
        };
        let step_a = c.eq_subst_nn(
            motive_a,
            inf_sqrt.clone(),
            sqrt_of_inf.clone(),
            e1_symm,
            hbm,
        );
        //   e2 : ofRat Inf · ofRat d = ofRat d · ofRat Inf  (mul_comm).
        let z_inf = c.nn_mul(z.clone(), of_inf.clone());
        let e2 = c.nn_mul_comm(of_inf.clone(), z.clone());
        //   h3 : sqrtRat·ofRat Inf ≤ ofRat d · ofRat Inf  (subst e2 step_a on RHS).
        let motive_b = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = m.fresh_local(c.nnreal.clone());
            let body = c.nn_le(sqrt_of_inf.clone(), t);
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
        };
        let h3 = c.eq_subst_nn(motive_b, inf_z.clone(), z_inf.clone(), e2, step_a);

        // (4) e4 : ofRat d · ofRat Inf = ofRat(d·Inf_i)  (ofRat_mul d Inf hd h0i h_dInf).
        let h_d_inf = c.rat_mul_nonneg(&d, &inf, hd.clone(), h0i.clone()); // 0 ≤ d·Inf_i
        let of_d_inf = c.nn_of_rat(d_inf.clone(), h_d_inf.clone()); // ofRat(d·Inf_i)
        let e4 = c.nn_ofrat_mul(&d, &inf, hd.clone(), h0i.clone(), h_d_inf.clone());
        //   h5 : sqrtRat·ofRat Inf ≤ ofRat(d·Inf_i)  (subst e4 h3 on RHS).
        let motive_c = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = m.fresh_local(c.nnreal.clone());
            let body = c.nn_le(sqrt_of_inf.clone(), t);
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
        };
        let h5 = c.eq_subst_nn(motive_c, z_inf.clone(), of_d_inf.clone(), e4, h3);

        // (6) hp' : pow32 Inf_i ≤ ofRat(d·Inf_i)  (le.trans hp h5).
        let hp_prime = c.nn_le_trans(
            pow32_inf.clone(),
            sqrt_of_inf.clone(),
            of_d_inf.clone(),
            hp,
            h5,
        );
        // (7) h4 : 4·pow32 Inf_i ≤ 4·ofRat(d·Inf_i)  (mul_le_mul_left four_nn … hp').
        let four_of_dinf = c.nn_mul(four_nn.clone(), of_d_inf.clone());
        let h4 = c.nn_mul_le_mul_left(
            four_nn.clone(),
            pow32_inf.clone(),
            of_d_inf.clone(),
            hp_prime,
        );
        // (8) e8 : 4·ofRat(d·Inf_i) = ofRat(4·(d·Inf_i))  (ofRat_mul 4 (d·Inf) h4nn h_dInf hr).
        let hr = c.rat_mul_nonneg(&four, &d_inf, c.h_four_nonneg(), h_d_inf.clone()); // 0 ≤ 4·(d·Inf)
        let of_4dinf = c.nn_of_rat(four_d_inf.clone(), hr.clone()); // ofRat(4·(d·Inf))
        let e8 = c.nn_ofrat_mul(
            &four,
            &d_inf,
            c.h_four_nonneg(),
            h_d_inf.clone(),
            hr.clone(),
        );
        //   h4' : 4·pow32 Inf_i ≤ ofRat(4·(d·Inf_i))  (subst e8 h4 on RHS).
        let motive_d = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = m.fresh_local(c.nnreal.clone());
            let body = c.nn_le(four_pow32.clone(), t);
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
        };
        let h4_prime = c.eq_subst_nn(motive_d, four_of_dinf.clone(), of_4dinf.clone(), e8, h4);

        // (9) hfinal_nn : ofRat W_norm_i ≤ ofRat(4·(d·Inf_i))  (le.trans hbase h4').
        let hfinal_nn = c.nn_le_trans(
            of_wnorm.clone(),
            four_pow32.clone(),
            of_4dinf.clone(),
            hbase,
            h4_prime,
        );
        // (10) reflect : W_norm_i ≤ 4·(d·Inf_i)  (ofRat_le_ofRat_rev W_norm (4·(d·Inf)) h_wnorm hr hfinal_nn).
        c.nn_ofrat_le_rev(&w_norm, &four_d_inf, h_wnorm.clone(), hr.clone(), hfinal_nn)
    } else {
        concl
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, h1i_id, h1i_ty, body);
    let e = bind(&b, h0i_id, h0i_ty, e);
    let e = bind(&b, hdd1_id, hdd1_ty, e);
    let e = bind(&b, hdd0_id, hdd0_ty, e);
    let e = bind(&b, hd_id, hd_ty, e);
    let e = bind(&b, i_id, c.fin_of(&n), e);
    let e = bind(&b, d_id, c.rat.clone(), e);
    let e = bind(&b, f_id, c.bool_fn_of(&n), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}

impl PerCoordConsts {
    /// `Eq.symm.{1} NNReal a b h` (the reflect file's helper is private to its
    /// own scope; provide the NNReal symm we need here).
    fn rat_symm_nn(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            ),
            [self.nnreal.clone(), a, b, h],
        )
    }
    /// `fun (i : Fin n) => Rat.mul (ind (m i)) W_norm_i` — the masked summand.
    fn masked_wn_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, m: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let (w_norm, _h) = self.w_norm_and_nonneg(&b, n, f, &i);
        let body = self.mul(self.ind_of(Expr::app(m.clone(), i.clone())), w_norm);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `fun (i : Fin n) => Rat.mul (d) (Influence n f i)`.
    fn d_inf_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, d: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.mul(d.clone(), self.influence_of(n, f, &i));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `fun (i : Fin n) => Influence n f i`.
    fn inf_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.influence_of(n, f, &i);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c (h:b≤c)(h0:0≤a) : a·b ≤ a·c`.
    fn rat_mul_le_left(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, h0: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]),
            [a, b, cc, hbc, h0],
        )
    }
}

// ── (2b) the masked aggregate `Σ ind(m)·W_norm ≤ 4·(d·I[f])`. ──
fn build_wnorm_sum_le_rat_masked(c: &PerCoordConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.bool_fn_of(&n));
    let mask_ty = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (j_id, _j) = d.fresh_local(fin_n.clone());
        d.finish_child(d.mk_pi(
            j_id,
            BinderInfo::Default,
            fin_n,
            Expr::const_(Name::from_string("Bool"), vec![]),
        ))
    };
    let (m_id, m) = b.fresh_local(mask_ty.clone());
    let (d_id, d) = b.fresh_local(c.rat.clone());
    let dd = c.mul(d.clone(), d.clone());

    let hd_ty = c.le(c.rat_zero.clone(), d.clone());
    let (hd_id, hd) = b.fresh_local(hd_ty.clone());
    let hdd0_ty = c.le(c.rat_zero.clone(), dd.clone());
    let (hdd0_id, hdd0) = b.fresh_local(hdd0_ty.clone());
    let hdd1_ty = c.lt(dd.clone(), c.rat_one.clone());
    let (hdd1_id, hdd1) = b.fresh_local(hdd1_ty.clone());

    // h0 : ∀ i, 0 ≤ Inf_i.
    let h0_ty = {
        let mut bb = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = bb.fresh_local(fin_n.clone());
        let body = c.le(c.rat_zero.clone(), c.influence_of(&n, &f, &i));
        bb.finish_child(bb.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    };
    let (h0_id, h0) = b.fresh_local(h0_ty.clone());
    // h1m : ∀ i, m i = true → Inf_i ≤ d·d.
    let h1m_ty = {
        let mut bb = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = bb.fresh_local(fin_n.clone());
        let prem = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [
                Expr::const_(Name::from_string("Bool"), vec![]),
                Expr::app(m.clone(), i.clone()),
                Expr::const_(Name::from_string("Bool.true"), vec![]),
            ],
        );
        let concl = c.le(c.influence_of(&n, &f, &i), dd.clone());
        let body = Expr::pi(BinderInfo::Default, prem, concl);
        bb.finish_child(bb.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    };
    let (h1m_id, h1m) = b.fresh_local(h1m_ty.clone());

    let masked_wn = c.masked_wn_fn(&b, &n, &f, &m);
    let sigma = c.fin_sum_of(&n, masked_wn.clone());
    let four = c.ofnat(4);
    let tot = c.total_influence_of(&n, &f);
    let four_d_tot = c.mul(four.clone(), c.mul(d.clone(), tot.clone())); // 4·(d·I)
    let concl = c.le(sigma.clone(), four_d_tot.clone());

    let body = if for_value {
        let d_inf = c.d_inf_fn(&b, &n, &f, &d); // fun i => d·Inf_i
        let inf = c.inf_fn(&b, &n, &f); // fun i => Inf_i
                                        // masked summands' Fin.sum carriers.
        let masked_d_inf = {
            // fun i => ind(m i)·(d·Inf_i)
            let mut bb = EnvDeclBuilder::child_of(&b);
            let fin_n = c.fin_of(&n);
            let (i_id, i) = bb.fresh_local(fin_n.clone());
            let body = c.mul(
                c.ind_of(Expr::app(m.clone(), i.clone())),
                c.mul(d.clone(), c.influence_of(&n, &f, &i)),
            );
            bb.finish_child(bb.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        let masked_4_d_inf = {
            // fun i => ind(m i)·(4·(d·Inf_i))
            let mut bb = EnvDeclBuilder::child_of(&b);
            let fin_n = c.fin_of(&n);
            let (i_id, i) = bb.fresh_local(fin_n.clone());
            let body = c.mul(
                c.ind_of(Expr::app(m.clone(), i.clone())),
                c.mul(four.clone(), c.mul(d.clone(), c.influence_of(&n, &f, &i))),
            );
            bb.finish_child(bb.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        let masked_inf = {
            // fun i => ind(m i)·Inf_i
            let mut bb = EnvDeclBuilder::child_of(&b);
            let fin_n = c.fin_of(&n);
            let (i_id, i) = bb.fresh_local(fin_n.clone());
            let body = c.mul(
                c.ind_of(Expr::app(m.clone(), i.clone())),
                c.influence_of(&n, &f, &i),
            );
            bb.finish_child(bb.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };

        let sum_4_d_inf = c.fin_sum_of(&n, masked_4_d_inf.clone()); // Σ ind·(4·(d·Inf))
        let sum_d_inf = c.fin_sum_of(&n, masked_d_inf.clone()); // Σ ind·(d·Inf)
        let sum_inf = c.fin_sum_of(&n, masked_inf.clone()); // Σ ind·Inf
        let d_sum_inf = c.mul(d.clone(), sum_inf.clone()); // d·Σ ind·Inf
        let four_d_sum_inf = c.mul(four.clone(), d_sum_inf.clone()); // 4·(d·Σ ind·Inf)

        // (1) per_i_cond : ∀ i, m i = true → W_norm_i ≤ 4·(d·Inf_i).
        let per_i_cond = {
            let mut pb = EnvDeclBuilder::child_of(&b);
            let fin_n = c.fin_of(&n);
            let (i_id, i) = pb.fresh_local(fin_n.clone());
            let mi = Expr::app(m.clone(), i.clone());
            let prem = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [
                    Expr::const_(Name::from_string("Bool"), vec![]),
                    mi.clone(),
                    Expr::const_(Name::from_string("Bool.true"), vec![]),
                ],
            );
            let (he_id, he) = pb.fresh_local(prem.clone());
            let h0i = Expr::app(h0.clone(), i.clone());
            let h1mi = Expr::app(Expr::app(h1m.clone(), i.clone()), he); // Inf_i ≤ d·d
            let body = Expr::apps(
                Expr::const_(
                    Name::from_string("BoolAnalysis.kkl_wnorm_le_d_inf_masked"),
                    vec![],
                ),
                [
                    n.clone(),
                    f.clone(),
                    d.clone(),
                    i.clone(),
                    hd.clone(),
                    hdd0.clone(),
                    hdd1.clone(),
                    h0i,
                    h1mi,
                ],
            );
            let inner = pb.mk_lam(he_id, BinderInfo::Default, prem, body);
            pb.finish_child(pb.mk_lam(i_id, BinderInfo::Default, fin_n, inner))
        };

        // (2) mono : Σ ind·W_norm ≤ Σ ind·(4·(d·Inf))
        //     := masked_finSum_le_cond n m wn_fn (fun i => 4·(d·Inf_i)) per_i_cond.
        let wn_fn = {
            // fun i => W_norm_i  (the unmasked payload; matches masked_finSum_le_cond's `g`).
            let mut bb = EnvDeclBuilder::child_of(&b);
            let fin_n = c.fin_of(&n);
            let (i_id, i) = bb.fresh_local(fin_n.clone());
            let (w_norm, _h) = c.w_norm_and_nonneg(&bb, &n, &f, &i);
            bb.finish_child(bb.mk_lam(i_id, BinderInfo::Default, fin_n, w_norm))
        };
        let four_d_inf_fn = {
            // fun i => 4·(d·Inf_i)
            let mut bb = EnvDeclBuilder::child_of(&b);
            let fin_n = c.fin_of(&n);
            let (i_id, i) = bb.fresh_local(fin_n.clone());
            let body = c.mul(four.clone(), c.mul(d.clone(), c.influence_of(&n, &f, &i)));
            bb.finish_child(bb.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        let mono = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.masked_finSum_le_cond"),
                vec![],
            ),
            [
                n.clone(),
                m.clone(),
                wn_fn.clone(),
                four_d_inf_fn.clone(),
                per_i_cond,
            ],
        );

        // (3) smul1 : Σ ind·(4·(d·Inf)) = 4·Σ ind·(d·Inf)
        //     := masked_finSum_smul n m 4 (fun i => d·Inf_i).
        let smul1 = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.masked_finSum_smul"), vec![]),
            [n.clone(), m.clone(), four.clone(), d_inf.clone()],
        );
        let four_sum_d_inf = c.mul(four.clone(), sum_d_inf.clone()); // 4·Σ ind·(d·Inf)

        // (4) smul2 : Σ ind·(d·Inf) = d·Σ ind·Inf
        //     := masked_finSum_smul n m d (fun i => Inf_i).
        let smul2 = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.masked_finSum_smul"), vec![]),
            [n.clone(), m.clone(), d.clone(), inf.clone()],
        );

        // (5) full : Σ ind·Inf ≤ Σ Inf = I[f]
        //     := masked_finSum_le_full n m (fun i => Inf_i) h0.
        let full = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.masked_finSum_le_full"),
                vec![],
            ),
            [n.clone(), m.clone(), inf.clone(), h0.clone()],
        );

        // ── chain in Rat ──
        // step1 : Σ ind·W_norm ≤ 4·Σ ind·(d·Inf)
        //   transport mono's RHS Σ ind·(4·(d·Inf)) ↦ 4·Σ ind·(d·Inf) along smul1.
        let motive_s1 = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.le(sigma.clone(), t);
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let step1 = c.rat_subst(
            motive_s1,
            sum_4_d_inf.clone(),
            four_sum_d_inf.clone(),
            smul1,
            mono,
        );

        // step2 : Σ ind·W_norm ≤ 4·(d·Σ ind·Inf)
        //   transport step1's RHS 4·Σ ind·(d·Inf) ↦ 4·(d·Σ ind·Inf) along
        //   congrArg (4·) smul2.
        let congr_4 = {
            // congrArg (fun t => 4·t) smul2 : 4·Σ ind·(d·Inf) = 4·(d·Σ ind·Inf).
            let f4 = {
                let mut mb = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.mul(four.clone(), t);
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            Expr::apps(
                c.congr_arg1.clone(),
                [
                    c.rat.clone(),
                    c.rat.clone(),
                    sum_d_inf.clone(),
                    d_sum_inf.clone(),
                    f4,
                    smul2,
                ],
            )
        };
        let motive_s2 = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.le(sigma.clone(), t);
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let step2 = c.rat_subst(
            motive_s2,
            four_sum_d_inf.clone(),
            four_d_sum_inf.clone(),
            congr_4,
            step1,
        );

        // hmono_final : 4·(d·Σ ind·Inf) ≤ 4·(d·I[f]).
        //   d·Σ ind·Inf ≤ d·I[f]  via mul_le_left d (Σ ind·Inf)(I[f]) full hd.
        let d_tot = c.mul(d.clone(), tot.clone());
        let hd_step = c.rat_mul_le_left(d.clone(), sum_inf.clone(), tot.clone(), full, hd.clone());
        //   4·(d·Σ ind·Inf) ≤ 4·(d·I[f])  via mul_le_left 4 (d·Σ ind·Inf)(d·I[f]) hd_step (0≤4).
        let h4_step = c.rat_mul_le_left(
            four.clone(),
            d_sum_inf.clone(),
            d_tot.clone(),
            hd_step,
            c.h_four_nonneg(),
        );

        // close : Σ ind·W_norm ≤ 4·(d·I[f])  via le.trans step2 h4_step.
        c.rat_le_trans(
            sigma.clone(),
            four_d_sum_inf.clone(),
            four_d_tot.clone(),
            step2,
            h4_step,
        )
    } else {
        concl
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, h1m_id, h1m_ty, body);
    let e = bind(&b, h0_id, h0_ty, e);
    let e = bind(&b, hdd1_id, hdd1_ty, e);
    let e = bind(&b, hdd0_id, hdd0_ty, e);
    let e = bind(&b, hd_id, hd_ty, e);
    let e = bind(&b, d_id, c.rat.clone(), e);
    let e = bind(&b, m_id, mask_ty, e);
    let e = bind(&b, f_id, c.bool_fn_of(&n), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}

impl PerCoordConsts {
    /// `Rat.le_trans a b c (a≤b)(b≤c) : a ≤ c`.
    fn rat_le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            [a, b, cc, h1, h2],
        )
    }
}

impl Environment {
    /// Register the masked dual-HC aggregate (STEP c): the per-coordinate Rat
    /// bound `kkl_wnorm_le_d_inf_masked` and the masked aggregate
    /// `kkl_wnorm_sum_le_rat_masked`. Idempotent; kernel-checked, `Constructive`,
    /// EMPTY admitted-axiom closure. No axiom added or removed.
    pub fn init_boolean_analysis_kkl_dualhc_masked(&mut self) -> Result<(), EnvError> {
        self.init_eq()?;
        self.init_boolean_analysis_kkl_dualhc_percoord_uncond()?; // dualhc_per_coord_uncond
        self.init_boolean_analysis_kkl_dualhc_aggregate()?; // PerCoordConsts NNReal helpers chain
        self.init_algebra_nnreal_pow32_bound()?; // pow32_le_sqrt_eps_mul, pow32, sqrtRat, ofRat, mul
        self.register_kkl_sqrtrat_sq_le_ofrat()?; // NNReal.sqrtRat_sq_le_ofRat
        self.init_algebra_nnreal_reverse_square_algebra()?; // NNReal.ofRat_mul, NNReal.mul_comm
        self.init_algebra_nnreal_reverse_square_mono()?; // NNReal.mul_le_mul_left
        self.init_algebra_nnreal_le()?; // NNReal.le.trans, NNReal.ofRat_le_ofRat
        self.register_kkl_nnreal_to_rat_reflection()?; // NNReal.ofRat_le_ofRat_rev
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_left
        self.init_boolean_analysis_order_toolkit_b1c()?; // Rat.lt_of_le_of_lt
        self.init_rat_field_inst()?; // Rat.mul_nonneg, Rat.le_trans (via field tower)
        self.init_boolean_analysis_friedgut_masked_finsum()?; // masked finSum lemmas (STEP b)

        let name_a = Name::from_string("BoolAnalysis.kkl_wnorm_le_d_inf_masked");
        if self.get_const(&name_a).is_none() {
            let c = PerCoordConsts::new();
            self.add_decl(Declaration::Theorem {
                name: name_a,
                level_params: vec![],
                type_: build_wnorm_le_d_inf_masked(&c, false),
                value: build_wnorm_le_d_inf_masked(&c, true),
            })?;
        }
        let name_b = Name::from_string("BoolAnalysis.kkl_wnorm_sum_le_rat_masked");
        if self.get_const(&name_b).is_none() {
            let c = PerCoordConsts::new();
            self.add_decl(Declaration::Theorem {
                name: name_b,
                level_params: vec![],
                type_: build_wnorm_sum_le_rat_masked(&c, false),
                value: build_wnorm_sum_le_rat_masked(&c, true),
            })?;
        }
        Ok(())
    }
}
