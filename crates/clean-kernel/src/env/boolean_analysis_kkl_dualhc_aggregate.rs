// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// KKL dual-HC — the AGGREGATE (sum-over-coordinates) of the per-coordinate
// dual-HC bound. `include!`d into `boolean_analysis_kkl_dualhc_percoord.rs`;
// shares its `PerCoordConsts` and the `build_w_nonneg` / `build_dinv_nonneg`
// witnesses so the summand is byte-for-byte the per-coordinate conclusion's LHS.
// (Regular `//` comments only — inner doc `//!` is not allowed at an `include!`
// site.)
//
// ## What this proves
//
//   BoolAnalysis.kkl_deriv_two_norm_sum_le :
//     ∀ (n : Nat) (f : BoolFn n) (eps : Rat),
//       (∀ i, Rat.le Rat.zero (Influence n f i)) →
//       (∀ i, Rat.le (Influence n f i) eps) →
//       Rat.lt eps Rat.one →
//         NNReal.le
//           (NNReal.finSum n (fun i => NNReal.ofRat W_norm_i hWn_i))
//           (NNReal.mul (NNReal.ofRat 4 h4)
//                       (NNReal.mul (NNReal.sqrtRat eps)
//                                   (NNReal.ofRat (TotalInfluence n f) hTot)))
//
// i.e. `Σ_i ‖T_{1/3} D_i f‖₂² ≤ 4·(√ε·I[f])`, where the per-coordinate summand
// `W_norm_i := W_i·inv(8^n)` with `W_i := subsetSum n (fun y => (noiseOp(1/3) D_i f)(y)²)`
// is BYTE-IDENTICAL to the LHS of `dualhc_per_coord_uncond`.
//
// ## Proof (constructive, EMPTY admitted-axiom closure) — pure NNReal composition
//
// Let `Lfn i := ofRat W_norm_i hWn_i`, `Pfn i := pow32 (Inf_i) (h0 i)`,
// `Gfn i := mul (ofRat 4 h4)(Pfn i)`, `four := ofRat 4 h4`, `c := sqrtRat eps`.
//
//   1. per-coord : ∀ i, NNReal.le (Lfn i)(Gfn i)
//        := fun i => dualhc_per_coord_uncond n f i (h0 i)(h1 i)
//      (its conclusion `le (ofRat W_norm_i hWn_i)(mul (ofRat 4 h4)(pow32 Inf_i (h0 i)))`
//       is byte-for-byte `le (Lfn i)(Gfn i)`).
//   2. h_sum_le : le (finSum n Lfn)(finSum n Gfn)
//        := NNReal.finSum_le n Lfn Gfn (per-coord).
//   3. h_smul : finSum n Gfn = mul four (finSum n Pfn)
//        := NNReal.finSum_smul n four Pfn   (Gfn ≡ fun i => mul four (Pfn i) by β).
//   4. h_charge : le (finSum n Pfn)(mul c (ofRat I[f] hTot))
//        := kkl_sum_pow32_influence_le n f eps h0 h1 he1
//      (its LHS `finSum n (fun i => pow32 Inf_i (h0 i))` is `finSum n Pfn`; passing
//       OUR `h0` as the consumer's `hnn` makes the proof fields agree byte-for-byte).
//   5. h_mul_le : le (mul four (finSum n Pfn))(mul four (mul c (ofRat I[f] hTot)))
//        := NNReal.mul_le_mul_left four (finSum n Pfn)(mul c (ofRat I[f] hTot)) h_charge.
//   6. transport (2) along (3): le (finSum n Lfn)(mul four (finSum n Pfn))
//        := Eq.subst (motive t => le (finSum n Lfn) t) h_smul h_sum_le.
//   7. close by NNReal.le.trans of (6) and (5):
//        le (finSum n Lfn)(mul four (mul c (ofRat I[f] hTot))).
//
// Every leaf (`dualhc_per_coord_uncond`, `NNReal.finSum_le`, `NNReal.finSum_smul`,
// `kkl_sum_pow32_influence_le`, `NNReal.mul_le_mul_left`, `NNReal.le.trans`,
// `Eq.subst`) is a landed `Constructive` empty-closure Theorem, so this aggregate
// is `Constructive` with EMPTY admitted-axiom closure. No axiom added or removed.

impl PerCoordConsts {
    // ── NNReal / consumer atoms (lazily constructed, no extra struct field) ──
    fn nn(&self) -> Expr {
        self.nnreal.clone()
    }
    fn nn_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a, b])
    }
    fn nn_mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a, b])
    }
    fn nn_of_rat(&self, x: Expr, h: Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [x, h])
    }
    fn nn_pow32(&self, x: Expr, h: Expr) -> Expr {
        Expr::apps(self.nnreal_pow32.clone(), [x, h])
    }
    fn nn_finsum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("NNReal.finSum"), vec![]),
            [n.clone(), g],
        )
    }
    fn nn_sqrt(&self, eps: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("NNReal.sqrtRat"), vec![]),
            eps.clone(),
        )
    }
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.TotalInfluence"), vec![]),
            [n.clone(), f.clone()],
        )
    }
    /// `0 ≤ 4` — byte-match `build_per_coord_uncond`'s `h4_nonneg` witness.
    fn h_four_nonneg(&self) -> Expr {
        let four_of = self.ofnat(4);
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let refl = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [bool_c, btrue],
        );
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]),
            [self.rat_zero.clone(), four_of, refl],
        )
    }
    /// `W_norm_i` and its nonneg witness — byte-for-byte `build_per_coord_uncond`.
    fn w_norm_and_nonneg(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        f: &Expr,
        i: &Expr,
    ) -> (Expr, Expr) {
        let big_d = self.pow_of(8, n); // 8^n
        let d_inv = self.inv(big_d.clone());
        let g = self.deriv_lam(parent, n, f, i);
        let tg = self.op(n, &g);
        let w = self.ssum(
            n,
            self.lam_hcp(parent, n, |y| {
                let tgy = Expr::app(tg.clone(), y.clone());
                self.mul(tgy.clone(), tgy)
            }),
        );
        let w_norm = self.mul(w.clone(), d_inv.clone());
        let hw_nonneg = build_w_nonneg(self, parent, n, &tg);
        let h_dinv_nonneg = build_dinv_nonneg(self, &big_d, n);
        let mul_nonneg = Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]);
        let h_wnorm_nonneg = Expr::apps(mul_nonneg, [w, d_inv, hw_nonneg, h_dinv_nonneg]);
        (w_norm, h_wnorm_nonneg)
    }
    /// `Lfn := fun (i : Fin n) => NNReal.ofRat W_norm_i hWn_i`.
    fn lfn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let (w_norm, h_wnorm) = self.w_norm_and_nonneg(&b, n, f, &i);
        let body = self.nn_of_rat(w_norm, h_wnorm);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `Pfn := fun (i : Fin n) => NNReal.pow32 (Influence n f i)(h0 i)`.
    fn pfn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, h0: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let inf = self.influence_of(n, f, &i);
        let h0i = Expr::app(h0.clone(), i.clone());
        let body = self.nn_pow32(inf, h0i);
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `Gfn := fun (i : Fin n) => NNReal.mul (ofRat 4 h4)(pow32 Inf_i (h0 i))`.
    fn gfn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, h0: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let inf = self.influence_of(n, f, &i);
        let h0i = Expr::app(h0.clone(), i.clone());
        let four_nn = self.nn_of_rat(self.ofnat(4), self.h_four_nonneg());
        let body = self.nn_mul(four_nn, self.nn_pow32(inf, h0i));
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `∀ (i : Fin n), Rat.le Rat.zero (Influence n f i)`.
    fn nn_hyp(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.le(self.rat_zero.clone(), self.influence_of(n, f, &i));
        b.finish_child(b.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `∀ (i : Fin n), Rat.le (Influence n f i) eps`.
    fn le_hyp(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, eps: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = self.le(self.influence_of(n, f, &i), eps.clone());
        b.finish_child(b.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `0 ≤ TotalInfluence n f` := `Fin.sum_nonneg n (fun i => Influence n f i) h0`
    /// (`TotalInfluence ≡ Fin.sum n (fun i => Influence n f i)` reducible δ).
    fn h_total_nonneg(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, h0: &Expr) -> Expr {
        let infl = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let fin_n = self.fin_of(n);
            let (i_id, i) = b.fresh_local(fin_n.clone());
            let body = self.influence_of(n, f, &i);
            b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_nonneg"), vec![]),
            [n.clone(), infl, h0.clone()],
        )
    }
}

/// Build the type (`for_value = false`) or proof value (`for_value = true`) of
/// `kkl_deriv_two_norm_sum_le`.
fn build_aggregate(c: &PerCoordConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.bool_fn_of(&n));
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let h_nn_ty = c.nn_hyp(&b, &n, &f);
    let (h0_id, h0) = b.fresh_local(h_nn_ty.clone());
    let h_le_ty = c.le_hyp(&b, &n, &f, &eps);
    let (h1_id, h1) = b.fresh_local(h_le_ty.clone());
    let he1_ty = c.lt(eps.clone(), c.rat_one.clone());
    let (he1_id, he1) = b.fresh_local(he1_ty.clone());

    let lfn = c.lfn(&b, &n, &f);
    let four_nn = c.nn_of_rat(c.ofnat(4), c.h_four_nonneg());
    let sqrt_eps = c.nn_sqrt(&eps);
    let h_tot = c.h_total_nonneg(&b, &n, &f, &h0);
    let of_total = c.nn_of_rat(c.total_influence_of(&n, &f), h_tot.clone());
    let charge_rhs = c.nn_mul(sqrt_eps.clone(), of_total.clone()); // √ε·I[f]
    let final_rhs = c.nn_mul(four_nn.clone(), charge_rhs.clone()); // 4·(√ε·I[f])

    let lhs = c.nn_finsum(&n, lfn.clone());
    let concl = c.nn_le(lhs.clone(), final_rhs.clone());

    let body = if for_value {
        let pfn = c.pfn(&b, &n, &f, &h0);
        let gfn = c.gfn(&b, &n, &f, &h0);
        let finsum_l = c.nn_finsum(&n, lfn.clone());
        let finsum_p = c.nn_finsum(&n, pfn.clone());
        let finsum_g = c.nn_finsum(&n, gfn.clone());

        // (1) per-coord : ∀ i, le (Lfn i)(Gfn i)
        //       := fun i => dualhc_per_coord_uncond n f i (h0 i)(hlt1 i),
        //   where hlt1 i : Inf_i < 1 is DERIVED from `h1 i : Inf_i ≤ eps` and
        //   `he1 : eps < 1` via `Rat.lt_of_le_of_lt Inf_i eps 1 (h1 i) he1`.
        let per_coord = {
            let mut pb = EnvDeclBuilder::child_of(&b);
            let fin_n = c.fin_of(&n);
            let (i_id, i) = pb.fresh_local(fin_n.clone());
            let inf = c.influence_of(&n, &f, &i);
            let h0i = Expr::app(h0.clone(), i.clone());
            let h1i = Expr::app(h1.clone(), i.clone());
            // hlt1i : Rat.lt Inf_i Rat.one
            //   := Rat.lt_of_le_of_lt Inf_i eps Rat.one (h1 i) he1
            //   (`Rat.lt_of_le_of_lt a b c : le a b → lt b c → lt a c`, so b := eps, c := 1).
            let lt_of_le_of_lt = Expr::const_(Name::from_string("Rat.lt_of_le_of_lt"), vec![]);
            let hlt1i = Expr::apps(
                lt_of_le_of_lt,
                [inf, eps.clone(), c.rat_one.clone(), h1i, he1.clone()],
            );
            let uncond = Expr::const_(
                Name::from_string("BoolAnalysis.dualhc_per_coord_uncond"),
                vec![],
            );
            let body = Expr::apps(uncond, [n.clone(), f.clone(), i.clone(), h0i, hlt1i]);
            pb.finish_child(pb.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };

        // (2) h_sum_le : le (finSum n Lfn)(finSum n Gfn).
        let h_sum_le = Expr::apps(
            Expr::const_(Name::from_string("NNReal.finSum_le"), vec![]),
            [n.clone(), lfn.clone(), gfn.clone(), per_coord],
        );

        // (3) h_smul : finSum n Gfn = mul four (finSum n Pfn).
        //   NNReal.finSum_smul n four Pfn : finSum n (fun i => mul four (Pfn i)) = mul four (finSum n Pfn).
        //   LHS `fun i => mul four (Pfn i)` is defeq to `Gfn` (β).
        let h_smul = Expr::apps(
            Expr::const_(Name::from_string("NNReal.finSum_smul"), vec![]),
            [n.clone(), four_nn.clone(), pfn.clone()],
        );
        let mul_four_finsum_p = c.nn_mul(four_nn.clone(), finsum_p.clone());

        // (4) h_charge : le (finSum n Pfn)(mul (sqrtRat eps)(ofRat I[f] hTot)).
        //   kkl_sum_pow32_influence_le n f eps h0 h1 he1 — its LHS is `finSum n Pfn`
        //   (same `h0` ⟹ byte-identical proof fields) and RHS is `charge_rhs`.
        let h_charge = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.kkl_sum_pow32_influence_le"),
                vec![],
            ),
            [
                n.clone(),
                f.clone(),
                eps.clone(),
                h0.clone(),
                h1.clone(),
                he1.clone(),
            ],
        );

        // (5) h_mul_le : le (mul four (finSum n Pfn))(mul four charge_rhs).
        //   NNReal.mul_le_mul_left four (finSum n Pfn) charge_rhs h_charge.
        let h_mul_le = Expr::apps(
            Expr::const_(Name::from_string("NNReal.mul_le_mul_left"), vec![]),
            [
                four_nn.clone(),
                finsum_p.clone(),
                charge_rhs.clone(),
                h_charge,
            ],
        );

        // (6) transport (2) along (3): le (finSum n Lfn)(mul four (finSum n Pfn)).
        //   Eq.subst.{1} NNReal (motive t => le (finSum n Lfn) t)
        //                (finSum n Gfn)(mul four (finSum n Pfn)) h_smul h_sum_le.
        let motive = {
            let mut mb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = mb.fresh_local(c.nn());
            let mbody = c.nn_le(finsum_l.clone(), t);
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.nn(), mbody))
        };
        let eq_subst = Expr::const_(
            Name::from_string("Eq.subst"),
            vec![Level::succ(Level::zero())],
        );
        let h_step6 = Expr::apps(
            eq_subst,
            [
                c.nn(),
                motive,
                finsum_g.clone(),
                mul_four_finsum_p.clone(),
                h_smul,
                h_sum_le,
            ],
        );

        // (7) close : NNReal.le.trans (finSum n Lfn)(mul four (finSum n Pfn))(mul four charge_rhs) h_step6 h_mul_le.
        let le_trans = Expr::const_(Name::from_string("NNReal.le.trans"), vec![]);
        Expr::apps(
            le_trans,
            [
                finsum_l,
                mul_four_finsum_p,
                final_rhs.clone(),
                h_step6,
                h_mul_le,
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
    let e = bind(&b, he1_id, he1_ty, body);
    let e = bind(&b, h1_id, h_le_ty, e);
    let e = bind(&b, h0_id, h_nn_ty, e);
    let e = bind(&b, eps_id, c.rat.clone(), e);
    let e = bind(&b, f_id, c.bool_fn_of(&n), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}
