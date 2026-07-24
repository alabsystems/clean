// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by `boolean_analysis_noise_fn_succ.rs` — the per-index leaf proof that
// the merged half-split integrand `LOWᵢ + HIGHᵢ` equals the keystone RHS
// `gPart·d + ρ·(liftH·d)` (LOW) / `gPart·d + (−ρ)·(liftH·d)` (HIGH).

impl NoiseFnSuccConsts {
    /// `noiseDensityW_point_peel_<b><c> ρ n x y` — the density coordinate peel.
    fn peel(&self, b_true: bool, c_true: bool, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let suffix = match (b_true, c_true) {
            (false, false) => "ff",
            (false, true) => "ft",
            (true, false) => "tf",
            (true, true) => "tt",
        };
        Expr::apps(
            Expr::const_(
                Name::from_string(&format!("BoolAnalysis.noiseDensityW_point_peel_{suffix}")),
                vec![],
            ),
            [rho.clone(), n.clone(), x.clone(), y.clone()],
        )
    }

    /// The decode↔extend bridge for the outer point of this half:
    /// `hcDecode (n+1) (castP (idx_map k)) = extend_b n (hcDecode n k)`.
    fn outer_bridge(&self, half: Half, n: &Expr, k: &Expr) -> Expr {
        let name = match half {
            Half::Low => "BoolAnalysis.hcDecode_castP_castAdd_extendF",
            Half::High => "BoolAnalysis.hcDecode_castP_addNat_extendT",
        };
        Expr::apps(
            Expr::const_(Name::from_string(name), vec![]),
            [n.clone(), k.clone()],
        )
    }

    /// The closed-bit factor cleanup `1 + ρ·(pm b · pm c) = factor`, where
    /// `factor = 1+ρ` (b == c, product ≡ +1) or `Rat.sub 1 ρ` (b ≠ c, product ≡ −1).
    ///
    /// `pm b · pm c` ground-reduces to `1` / `neg 1` (defeq), so `Rat.mul_one ρ`
    /// proves `ρ·(pm b·pm c) = ρ` (+1 case) and `Rat.mul_neg ρ 1` + `congrArg neg
    /// (mul_one ρ)` proves `ρ·(pm b·pm c) = neg ρ` (−1 case), then `congrArg (1+·)`
    /// lifts. The −1 cleanup's `Rat.add 1 (neg ρ)` is defeq to `Rat.sub 1 ρ`.
    fn factor_cleanup(
        &self,
        parent: &EnvDeclBuilder,
        b_true: bool,
        c_true: bool,
        rho: &Expr,
    ) -> Expr {
        let pm_b = self.pm_of(self.bit(b_true));
        let pm_c = self.pm_of(self.bit(c_true));
        let pm_prod = self.mul(pm_b, pm_c); // pm b · pm c
        let rho_prod = self.mul(rho.clone(), pm_prod); // ρ·(pm b·pm c)
        let same = b_true == c_true;

        // h_mul : ρ·(pm b·pm c) = (ρ  or  neg ρ).
        let (rhs_inner, h_mul) = if same {
            // Rat.mul_one ρ : ρ·1 = ρ  (LHS defeq ρ·(pm·pm)).
            (rho.clone(), self.mul_one(rho.clone()))
        } else {
            // Rat.mul_neg ρ 1 : ρ·(−1) = −(ρ·1)  (LHS defeq ρ·(pm·pm)).
            let neg_rho1 = Expr::app(self.rat_neg().clone(), self.mul(rho.clone(), self.one()));
            let mneg = self.mul_neg(rho.clone(), self.one());
            // congrArg neg (mul_one ρ) : −(ρ·1) = −ρ.
            let neg_rho = Expr::app(self.rat_neg().clone(), rho.clone());
            let cong_neg = self.congr_neg(
                self.mul(rho.clone(), self.one()),
                rho.clone(),
                self.mul_one(rho.clone()),
            );
            // trans : ρ·(−1) = −(ρ·1) = −ρ.
            let chain = self.trans(rho_prod.clone(), neg_rho1, neg_rho.clone(), mneg, cong_neg);
            (neg_rho, chain)
        };

        // congrArg (fun s => 1+s) h_mul : 1+ρ·(pm·pm) = 1+rhs_inner.
        let add_one_fn = {
            let mut dd = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = dd.fresh_local(self.rat());
            let body = self.add(self.one(), s);
            dd.finish_child(dd.mk_lam(s_id, BinderInfo::Default, self.rat(), body))
        };
        self.congr_to_rat(self.rat(), rho_prod, rhs_inner, add_one_fn, h_mul)
    }

    fn rat_neg(&self) -> &Expr {
        &self.rat_neg_const
    }
    /// `congrArg Rat.neg h : −a = −b`  from `h : a = b`.
    fn congr_neg(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.congr_to_rat(self.rat(), a, b, self.rat_neg().clone(), h)
    }

    /// One half-leg rewrite `F(ext_c y)·D = F(ext_c y)·(d·factor)`, where `D` is
    /// the split density `noiseDensityW ρ (n+1) (hcDecode (n+1) (split_idx))
    /// (ext_c n y)`, `d := noiseDensityW ρ n x' y`, and `factor` the closed-bit
    /// `(1+ρ)`/`(1−ρ)`. `x' := hcDecode n k`, `y := hcDecode n i`.
    #[allow(clippy::too_many_arguments)]
    fn half_leg(
        &self,
        parent: &EnvDeclBuilder,
        half: Half,
        c_true: bool,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        k: &Expr,
        i: &Expr,
    ) -> Expr {
        let b_true = matches!(half, Half::High); // outer top bit
        let sn = self.succ(n);
        let x_prime = self.decode(n, k); // x' = hcDecode n k
        let y = self.decode(n, i); // y  = hcDecode n i
        let ext_outer = self.extend(b_true, n, &x_prime); // extend_b n x'
        let ext_c_y = self.extend(c_true, n, &y); // ext_c n y
        let split_idx = self.split_index(parent, half, n, k);
        let outer_pt = self.decode(&sn, &split_idx); // hcDecode (n+1) (split_idx)

        // F(ext_c y).
        let f_ext = Expr::app(f.clone(), ext_c_y.clone());

        // D = noiseDensityW ρ (n+1) outer_pt (ext_c y).
        let dens_raw = self.density(rho, &sn, &outer_pt, &ext_c_y);
        // ── bridge the outer point: D = noiseDensityW ρ (n+1) (extend_b x') (ext_c y).
        let bridge = self.outer_bridge(half, n, k); // outer_pt = extend_b x'
        let dens_bridged = self.density(rho, &sn, &ext_outer, &ext_c_y);
        let bridge_fn = {
            let mut dd = EnvDeclBuilder::child_of(parent);
            let (pt_id, pt) = dd.fresh_local(self.hcpoint_of(&sn));
            let body = self.density(rho, &sn, &pt, &ext_c_y);
            dd.finish_child(dd.mk_lam(pt_id, BinderInfo::Default, self.hcpoint_of(&sn), body))
        };
        let cong_bridge = self.congr_to_rat(
            self.hcpoint_of(&sn),
            outer_pt.clone(),
            ext_outer.clone(),
            bridge_fn,
            bridge,
        );

        // ── peel: noiseDensityW ρ (n+1) (extend_b x') (ext_c y)
        //           = d·(1+ρ·(pm b·pm c)).
        let d_small = self.density(rho, n, &x_prime, &y); // d
        let pm_prod = self.mul(self.pm_of(self.bit(b_true)), self.pm_of(self.bit(c_true)));
        let raw_factor = self.add(self.one(), self.mul(rho.clone(), pm_prod)); // 1+ρ·(pm·pm)
        let dens_peeled = self.mul(d_small.clone(), raw_factor.clone());
        let peel = self.peel(b_true, c_true, rho, n, &x_prime, &y);

        // ── factor cleanup: d·(1+ρ·(pm·pm)) = d·factor.
        let factor = if b_true == c_true {
            self.add(self.one(), rho.clone()) // 1+ρ
        } else {
            self.sub(self.one(), rho.clone()) // 1−ρ
        };
        let dens_clean = self.mul(d_small.clone(), factor.clone());
        let factor_eq = self.factor_cleanup(parent, b_true, c_true, rho);
        let mul_d_fn = {
            let mut dd = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = dd.fresh_local(self.rat());
            let body = self.mul(d_small.clone(), s);
            dd.finish_child(dd.mk_lam(s_id, BinderInfo::Default, self.rat(), body))
        };
        let cong_factor = self.congr_to_rat(
            self.rat(),
            raw_factor.clone(),
            factor.clone(),
            mul_d_fn,
            factor_eq,
        );

        // chain the density: dens_raw = dens_bridged = dens_peeled = dens_clean.
        let dens_chain = self.trans(
            dens_raw.clone(),
            dens_bridged.clone(),
            dens_peeled.clone(),
            cong_bridge,
            peel,
        );
        let dens_chain = self.trans(
            dens_raw.clone(),
            dens_peeled,
            dens_clean.clone(),
            dens_chain,
            cong_factor,
        );

        // ── lift through F(ext_c y)·(·): F(ext_c y)·D = F(ext_c y)·(d·factor).
        let mul_f_fn = {
            let mut dd = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = dd.fresh_local(self.rat());
            let body = self.mul(f_ext.clone(), s);
            dd.finish_child(dd.mk_lam(s_id, BinderInfo::Default, self.rat(), body))
        };
        self.congr_to_rat(self.rat(), dens_raw, dens_clean, mul_f_fn, dens_chain)
    }

    /// The per-index leaf `LOWᵢ + HIGHᵢ = gPart·d + (±ρ)·(liftH·d)`, used (defeq)
    /// as a proof of `raw_combined i = target i` for `Fin.sum_congr`.
    fn combined_leaf(
        &self,
        parent: &EnvDeclBuilder,
        half: Half,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        k: &Expr,
        i: &Expr,
    ) -> Expr {
        let sn = self.succ(n);
        let x_prime = self.decode(n, k);
        let y = self.decode(n, i);
        let split_idx = self.split_index(parent, half, n, k);
        let outer_pt = self.decode(&sn, &split_idx);
        let ext_f_y = self.extend(false, n, &y);
        let ext_t_y = self.extend(true, n, &y);

        // p = F(extendF y), q = F(extendT y), d = noiseDensityW ρ n x' y.
        let p = Expr::app(f.clone(), ext_f_y.clone());
        let q = Expr::app(f.clone(), ext_t_y.clone());
        let d_small = self.density(rho, n, &x_prime, &y);

        // raw LOWᵢ = p·D₊, HIGHᵢ = q·D₋  (D_b = noiseDensityW ρ (n+1) outer_pt (ext_b y)).
        let d_plus = self.density(rho, &sn, &outer_pt, &ext_f_y);
        let d_minus = self.density(rho, &sn, &outer_pt, &ext_t_y);
        let low_i = self.mul(p.clone(), d_plus);
        let high_i = self.mul(q.clone(), d_minus);
        let raw_i = self.add(low_i.clone(), high_i.clone());

        // half-leg rewrites.
        let hp_low = self.half_leg(parent, half, false, rho, n, f, k, i); // p·D₊ = p·(d·factor_p)
        let hp_high = self.half_leg(parent, half, true, rho, n, f, k, i); // q·D₋ = q·(d·factor_q)

        // factor_p / factor_q per half.
        let (fac_p, fac_q) = match half {
            Half::Low => (
                self.add(self.one(), rho.clone()),
                self.sub(self.one(), rho.clone()),
            ),
            Half::High => (
                self.sub(self.one(), rho.clone()),
                self.add(self.one(), rho.clone()),
            ),
        };
        let leg_p_clean = self.mul(p.clone(), self.mul(d_small.clone(), fac_p)); // p·(d·factor_p)
        let leg_q_clean = self.mul(q.clone(), self.mul(d_small.clone(), fac_q)); // q·(d·factor_q)

        // cong on the add: raw_i = leg_p_clean + leg_q_clean.
        let mid1 = self.add(leg_p_clean.clone(), high_i.clone());
        let cong_left = {
            let mut dd = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = dd.fresh_local(self.rat());
            let body = self.add(s, high_i.clone());
            let f_lam = dd.finish_child(dd.mk_lam(s_id, BinderInfo::Default, self.rat(), body));
            self.congr_to_rat(
                self.rat(),
                low_i.clone(),
                leg_p_clean.clone(),
                f_lam,
                hp_low,
            )
        };
        let cleaned_sum = self.add(leg_p_clean.clone(), leg_q_clean.clone());
        let cong_right = {
            let mut dd = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = dd.fresh_local(self.rat());
            let body = self.add(leg_p_clean.clone(), s);
            let f_lam = dd.finish_child(dd.mk_lam(s_id, BinderInfo::Default, self.rat(), body));
            self.congr_to_rat(
                self.rat(),
                high_i.clone(),
                leg_q_clean.clone(),
                f_lam,
                hp_high,
            )
        };
        let cong_add = self.trans(
            raw_i.clone(),
            mid1,
            cleaned_sum.clone(),
            cong_left,
            cong_right,
        );

        // keystone: cleaned_sum = keystone RHS (defeq to target_i).
        let keystone = match half {
            Half::Low => self.keystone(&p, &q, &d_small, rho),
            Half::High => self.keystone_high(&p, &q, &d_small, rho),
        };
        let target_i = self.target_integrand(half, rho, n, f, k, i);
        // cleaned_sum is defeq to the keystone LHS; keystone RHS is defeq to target_i.
        self.trans(raw_i, cleaned_sum, target_i, cong_add, keystone)
    }

    /// `peel_pointwise_keystone_high p q d ρ`.
    fn keystone_high(&self, p: &Expr, q: &Expr, d: &Expr, rho: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.peel_pointwise_keystone_high"),
                vec![],
            ),
            [p.clone(), q.clone(), d.clone(), rho.clone()],
        )
    }
}
