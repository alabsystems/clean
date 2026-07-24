// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// KKL finish — RUNG 4c: REFLECT the NNReal dual-HC aggregate into Rat.
// `include!`d into `boolean_analysis_kkl_dualhc_percoord.rs` so it shares
// `PerCoordConsts` and the per-coordinate `W_norm`/nonneg witnesses
// byte-for-byte with the aggregate. (Regular `//` comments only — inner doc
// `//!` is not allowed at an `include!` site.)
//
// ## What this proves
//
//   BoolAnalysis.kkl_wnorm_sum_le_rat :
//     ∀ (n : Nat) (f : BoolFn n) (d : Rat)
//       (hd  : Rat.le Rat.zero d)
//       (hdd0 : Rat.le Rat.zero (Rat.mul d d))
//       (hdd1 : Rat.lt (Rat.mul d d) Rat.one)
//       (h0 : ∀ i, Rat.le Rat.zero (Influence n f i))
//       (h1 : ∀ i, Rat.le (Influence n f i) (Rat.mul d d)),
//       Rat.le (Fin.sum n (fun i => W_norm_i))
//              (Rat.mul (Rat.ofNat 4) (Rat.mul d (TotalInfluence n f)))
//
// i.e. `Σ_i ‖T_{1/3} D_i f‖₂² ≤ 4·(δ·I[f])` over Rat, where `W_norm_i` is the
// SAME normalized two-norm summand the aggregate sums (BYTE-IDENTICAL to rung 2's
// `kkl_lowband_le_wnorm_sum` RHS summand).
//
// ## Proof (constructive, EMPTY admitted-axiom closure)
//
// Write `Σwn := Fin.sum n W_norm`, `c := sqrtRat (d·d)`, `Z := ofRat d hd`,
// `I := ofRat (TotalInfluence n f) hTot`, `four := ofRat 4 h4`.
//
// 1. agg : finSum n Lfn ≤ four·(c·I)
//      := kkl_deriv_two_norm_sum_le n f (d·d) h0 h1 hdd1
//    (its eps := d·d; √(d·d) is `c`).
// 2. heq_l : finSum n Lfn = ofRat Σwn hsum   (finSum_ofRat n W_norm hwn hsum;
//    Lfn ≡ fun i => ofRat (W_norm i)(hwn i) by β).
// 3. agg' : ofRat Σwn ≤ four·(c·I)   (Eq.subst heq_l into agg).
// 4. h_cz : c·I ≤ Z·I   (mul_comm c I; mul_le_mul_left I c Z (sqrtRat_sq_le_ofRat
//    d hd hdd0 hdd1); mul_comm I Z; two Eq.substs — the LEFT-factor monotonicity).
// 5. h_4 : four·(c·I) ≤ four·(Z·I)   (mul_le_mul_left four (c·I)(Z·I) h_cz).
// 6. heq_r : four·(Z·I) = ofRat (4·(d·I)) hr
//      := Eq.trans (congrArg (four·) (ofRat_mul d Tot hd hTot h_dI))
//                  (ofRat_mul 4 (d·Tot) h4 h_dI hr)
//    (Z·I = ofRat(d·Tot); four·ofRat(d·Tot) = ofRat(4·(d·Tot))).
// 7. agg'' : ofRat Σwn ≤ ofRat (4·(d·I)) hr   (le.trans agg' (subst heq_r h_4)).
// 8. reflect : Σwn ≤ 4·(d·I)
//      := ofRat_le_ofRat_rev Σwn (4·(d·Tot)) hsum hr agg''.
//
// Every leaf (`kkl_deriv_two_norm_sum_le`, `NNReal.finSum_ofRat`,
// `NNReal.sqrtRat_sq_le_ofRat`, `NNReal.mul_comm`, `NNReal.mul_le_mul_left`,
// `NNReal.ofRat_mul`, `NNReal.le.trans`, `NNReal.ofRat_le_ofRat_rev`,
// `Fin.sum_nonneg`, `Rat.mul_nonneg`, `Eq.*`) is a landed `Constructive`
// empty-closure Theorem, so this reflection is too. No axiom added or removed.

impl PerCoordConsts {
    fn fin_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum"), vec![]),
            [n.clone(), g],
        )
    }
    /// `0 ≤ 4` witness — byte-match the aggregate's `h_four_nonneg`.
    fn h4_nonneg(&self) -> Expr {
        self.h_four_nonneg()
    }
    /// `4·(d·Tot)` — the Rat RHS `4·(δ·I[f])`.
    fn four_d_tot(&self, n: &Expr, f: &Expr, d: &Expr) -> Expr {
        let tot = self.total_influence_of(n, f);
        let d_tot = self.mul(d.clone(), tot);
        self.mul(self.ofnat(4), d_tot)
    }

    /// `Wn := fun (i : Fin n) => W_norm_i` (the Rat summand, byte-identical to the
    /// aggregate's `Lfn`-payload and rung 2's `wn_fn`).
    fn wn_rat_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let (w_norm, _h) = self.w_norm_and_nonneg(&b, n, f, &i);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, w_norm))
    }
    /// `Hwn := fun (i : Fin n) => h_wnorm_nonneg_i`.
    fn wn_nonneg_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let (_w, h) = self.w_norm_and_nonneg(&b, n, f, &i);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, h))
    }
    /// `0 ≤ Fin.sum n Wn` via `Fin.sum_nonneg n Wn Hwn`.
    fn h_sum_nonneg(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let wn = self.wn_rat_fn(parent, n, f);
        let hwn = self.wn_nonneg_fn(parent, n, f);
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_nonneg"), vec![]),
            [n.clone(), wn, hwn],
        )
    }

    fn eq_subst_nn(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.subst"),
                vec![Level::succ(Level::zero())],
            ),
            [self.nnreal.clone(), motive, a, b, h_eq, h],
        )
    }
    fn eq_trans_nn(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.trans"),
                vec![Level::succ(Level::zero())],
            ),
            [self.nnreal.clone(), a, b, cc, h1, h2],
        )
    }
    /// `congrArg (fun t => NNReal.mul L t) h : mul L a = mul L b`.
    fn congr_nn_mul_left(
        &self,
        parent: &EnvDeclBuilder,
        l: &Expr,
        a: Expr,
        b: Expr,
        h: Expr,
    ) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(self.nnreal.clone());
            let body = Expr::apps(self.nnreal_mul.clone(), [l.clone(), t]);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.nnreal.clone(), body))
        };
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
            ),
            [self.nnreal.clone(), self.nnreal.clone(), a, b, f, h],
        )
    }
    fn nn_mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.mul_comm"), vec![]),
            [a, b],
        )
    }
    fn nn_mul_le_mul_left(&self, a: Expr, cc: Expr, d: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.mul_le_mul_left"), vec![]),
            [a, cc, d, h],
        )
    }
    fn nn_le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.le.trans"), vec![]),
            [a, b, cc, h1, h2],
        )
    }
}

/// Build the type (`for_value=false`) / proof (`for_value=true`) of
/// `BoolAnalysis.kkl_wnorm_sum_le_rat`.
fn build_wnorm_reflect(c: &PerCoordConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.bool_fn_of(&n));
    let (d_id, d) = b.fresh_local(c.rat.clone());
    let dd = c.mul(d.clone(), d.clone());

    let hd_ty = c.le(c.rat_zero.clone(), d.clone());
    let (hd_id, hd) = b.fresh_local(hd_ty.clone());
    let hdd0_ty = c.le(c.rat_zero.clone(), dd.clone());
    let (hdd0_id, hdd0) = b.fresh_local(hdd0_ty.clone());
    let hdd1_ty = c.lt(dd.clone(), c.rat_one.clone());
    let (hdd1_id, hdd1) = b.fresh_local(hdd1_ty.clone());
    let h0_ty = c.nn_hyp(&b, &n, &f); // ∀ i, 0 ≤ Inf_i
    let (h0_id, h0) = b.fresh_local(h0_ty.clone());
    let h1_ty = c.le_hyp(&b, &n, &f, &dd); // ∀ i, Inf_i ≤ d·d
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());

    let wn = c.wn_rat_fn(&b, &n, &f);
    let sigma = c.fin_sum_of(&n, wn.clone());
    let four_d_tot = c.four_d_tot(&n, &f, &d);
    let concl = c.le(sigma.clone(), four_d_tot.clone());

    let body = if for_value {
        // ── proof term ───────────────────────────────────────────────────────
        let tot = c.total_influence_of(&n, &f);
        let h_tot = c.h_total_nonneg(&b, &n, &f, &h0); // 0 ≤ Tot
        let hsum = c.h_sum_nonneg(&b, &n, &f); // 0 ≤ Σwn
        let hwn = c.wn_nonneg_fn(&b, &n, &f);

        // NNReal carriers.
        let four_nn = c.nn_of_rat(c.ofnat(4), c.h4_nonneg());
        let sqrt_dd = c.nn_sqrt(&dd); // c := sqrtRat (d·d)
        let z = c.nn_of_rat(d.clone(), hd.clone()); // Z := ofRat d hd
        let i_nn = c.nn_of_rat(tot.clone(), h_tot.clone()); // I := ofRat Tot hTot
        let lfn = c.lfn(&b, &n, &f);
        let finsum_l = c.nn_finsum(&n, lfn.clone());
        let of_sigma = c.nn_of_rat(sigma.clone(), hsum.clone()); // ofRat Σwn hsum

        // (1) agg : finSum n Lfn ≤ four·(c·I).
        let c_i = c.nn_mul(sqrt_dd.clone(), i_nn.clone()); // c·I
        let final_rhs = c.nn_mul(four_nn.clone(), c_i.clone()); // four·(c·I)
        let agg = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.kkl_deriv_two_norm_sum_le"),
                vec![],
            ),
            [
                n.clone(),
                f.clone(),
                dd.clone(),
                h0.clone(),
                h1.clone(),
                hdd1.clone(),
            ],
        );

        // (2) heq_l : finSum n Lfn = ofRat Σwn hsum.
        let heq_l = Expr::apps(
            Expr::const_(Name::from_string("NNReal.finSum_ofRat"), vec![]),
            [n.clone(), wn.clone(), hwn.clone(), hsum.clone()],
        );

        // (3) agg' : ofRat Σwn ≤ four·(c·I)   subst (fun t => le t (four·(c·I))) heq_l agg.
        let motive_l = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = m.fresh_local(c.nnreal.clone());
            let body = c.nn_le(t, final_rhs.clone());
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
        };
        let agg_p = c.eq_subst_nn(motive_l, finsum_l.clone(), of_sigma.clone(), heq_l, agg);

        // (4) h_cz : c·I ≤ Z·I (left-factor monotonicity via mul_comm twice).
        //   e1 : c·I = I·c   (mul_comm c I).
        let i_c = c.nn_mul(i_nn.clone(), sqrt_dd.clone());
        let e1 = c.nn_mul_comm(sqrt_dd.clone(), i_nn.clone());
        //   hbase : I·c ≤ I·Z   (mul_le_mul_left I c Z (sqrtRat_sq_le_ofRat …)).
        let h_sqrt = Expr::apps(
            Expr::const_(Name::from_string("NNReal.sqrtRat_sq_le_ofRat"), vec![]),
            [d.clone(), hd.clone(), hdd0.clone(), hdd1.clone()],
        );
        let i_z = c.nn_mul(i_nn.clone(), z.clone());
        let hbase = c.nn_mul_le_mul_left(i_nn.clone(), sqrt_dd.clone(), z.clone(), h_sqrt);
        //   transport hbase's LHS I·c back to c·I along (symm e1): subst.
        //   We instead transport the GOAL: build `c·I ≤ Z·I` from `I·c ≤ I·Z`
        //   via two rewrites e1 (c·I = I·c) and e2 (I·Z = Z·I).
        //   step_a : c·I ≤ I·Z   subst (fun t => le t (I·Z)) (symm e1) hbase.
        let z_i = c.nn_mul(z.clone(), i_nn.clone());
        let e1_symm = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.symm"),
                vec![Level::succ(Level::zero())],
            ),
            [c.nnreal.clone(), c_i.clone(), i_c.clone(), e1],
        );
        let motive_a = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = m.fresh_local(c.nnreal.clone());
            let body = c.nn_le(t, i_z.clone());
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
        };
        let step_a = c.eq_subst_nn(motive_a, i_c.clone(), c_i.clone(), e1_symm, hbase);
        //   e2 : I·Z = Z·I   (mul_comm I Z).
        let e2 = c.nn_mul_comm(i_nn.clone(), z.clone());
        //   h_cz : c·I ≤ Z·I   subst (fun t => le (c·I) t) e2 step_a.
        let motive_b = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = m.fresh_local(c.nnreal.clone());
            let body = c.nn_le(c_i.clone(), t);
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
        };
        let h_cz = c.eq_subst_nn(motive_b, i_z.clone(), z_i.clone(), e2, step_a);

        // (5) h_4 : four·(c·I) ≤ four·(Z·I).
        let four_zi = c.nn_mul(four_nn.clone(), z_i.clone());
        let h_4 = c.nn_mul_le_mul_left(four_nn.clone(), c_i.clone(), z_i.clone(), h_cz);

        // (6) heq_r : four·(Z·I) = ofRat (4·(d·Tot)) hr.
        //   Z·I = ofRat (d·Tot) h_dTot   (ofRat_mul d Tot hd hTot h_dTot).
        let mul_nonneg = Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]);
        let h_d_tot = Expr::apps(
            mul_nonneg.clone(),
            [d.clone(), tot.clone(), hd.clone(), h_tot.clone()],
        ); // 0 ≤ d·Tot
        let d_tot = c.mul(d.clone(), tot.clone());
        let of_d_tot = c.nn_of_rat(d_tot.clone(), h_d_tot.clone());
        let zi_eq = Expr::apps(
            Expr::const_(Name::from_string("NNReal.ofRat_mul"), vec![]),
            [
                d.clone(),
                tot.clone(),
                hd.clone(),
                h_tot.clone(),
                h_d_tot.clone(),
            ],
        ); // Z·I = ofRat(d·Tot)
           //   congr : four·(Z·I) = four·ofRat(d·Tot).
        let congr_zi = c.congr_nn_mul_left(&b, &four_nn, z_i.clone(), of_d_tot.clone(), zi_eq);
        //   hr : 0 ≤ 4·(d·Tot).
        let hr = Expr::apps(
            mul_nonneg,
            [c.ofnat(4), d_tot.clone(), c.h4_nonneg(), h_d_tot.clone()],
        );
        //   four·ofRat(d·Tot) = ofRat(4·(d·Tot)) hr   (ofRat_mul 4 (d·Tot) h4 h_dTot hr).
        let four_of_dtot = c.nn_mul(four_nn.clone(), of_d_tot.clone());
        let of_4dtot = c.nn_of_rat(four_d_tot.clone(), hr.clone()); // ofRat(4·(d·Tot)) hr
        let outer_eq = Expr::apps(
            Expr::const_(Name::from_string("NNReal.ofRat_mul"), vec![]),
            [
                c.ofnat(4),
                d_tot.clone(),
                c.h4_nonneg(),
                h_d_tot.clone(),
                hr.clone(),
            ],
        );
        let heq_r = c.eq_trans_nn(
            four_zi.clone(),
            four_of_dtot.clone(),
            of_4dtot.clone(),
            congr_zi,
            outer_eq,
        );

        // (7) transport h_4 RHS four·(Z·I) ↦ ofRat(4·(d·Tot)) along heq_r:
        //   h_4' : four·(c·I) ≤ ofRat(4·(d·Tot)).
        let motive_r = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = m.fresh_local(c.nnreal.clone());
            let body = c.nn_le(final_rhs.clone(), t);
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
        };
        let h_4p = c.eq_subst_nn(motive_r, four_zi.clone(), of_4dtot.clone(), heq_r, h_4);

        // (7b) agg'' : ofRat Σwn ≤ ofRat(4·(d·Tot))   le.trans agg' h_4'.
        let agg_pp = c.nn_le_trans(
            of_sigma.clone(),
            final_rhs.clone(),
            of_4dtot.clone(),
            agg_p,
            h_4p,
        );

        // (8) reflect : Σwn ≤ 4·(d·Tot).
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.ofRat_le_ofRat_rev"), vec![]),
            [
                sigma.clone(),
                four_d_tot.clone(),
                hsum.clone(),
                hr.clone(),
                agg_pp,
            ],
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
    let e = bind(&b, h1_id, h1_ty, body);
    let e = bind(&b, h0_id, h0_ty, e);
    let e = bind(&b, hdd1_id, hdd1_ty, e);
    let e = bind(&b, hdd0_id, hdd0_ty, e);
    let e = bind(&b, hd_id, hd_ty, e);
    let e = bind(&b, d_id, c.rat.clone(), e);
    let e = bind(&b, f_id, c.bool_fn_of(&n), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Register `BoolAnalysis.kkl_wnorm_sum_le_rat` — RUNG 4c: the NNReal dual-HC
    /// aggregate reflected into Rat (`Σ_i W_norm_i ≤ 4·(δ·I[f])`). Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent; no axiom
    /// added/removed.
    pub fn register_kkl_wnorm_sum_le_rat(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_wnorm_sum_le_rat");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_kkl_dualhc_aggregate()?; // kkl_deriv_two_norm_sum_le
        self.init_algebra_nnreal_finsum_ofrat()?; // NNReal.finSum_ofRat (+ ofRat_add)
        self.register_kkl_sqrtrat_sq_le_ofrat()?; // NNReal.sqrtRat_sq_le_ofRat
        self.init_algebra_nnreal_reverse_square_algebra()?; // NNReal.mul_comm, ofRat_mul
        self.init_algebra_nnreal_reverse_square_mono()?; // NNReal.mul_le_mul_left
        self.register_kkl_nnreal_to_rat_reflection()?; // NNReal.ofRat_le_ofRat_rev
        self.init_fin_sum()?; // Fin.sum_nonneg
        self.register_rat_order_proofs()?; // Rat.mul_nonneg
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = PerCoordConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_wnorm_reflect(&c, false),
            value: build_wnorm_reflect(&c, true),
        })
    }
}
