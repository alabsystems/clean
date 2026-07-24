// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by `boolean_analysis_noise_fn_succ.rs` — the type + full assembly of
// `noiseFn_succ_low` / `_high` from the split, the per-index leaf, and the
// `Fin.sum_{add,smul}` linearity steps.

impl NoiseFnSuccConsts {
    /// `noiseFn_succ_split ρ n F split_idx`.
    fn split_lemma(&self, rho: &Expr, n: &Expr, f: &Expr, split_idx: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.noiseFn_succ_split"), vec![]),
            [rho.clone(), n.clone(), f.clone(), split_idx.clone()],
        )
    }

    /// One split half-function, byte-for-byte the `noiseFn_succ_split` form:
    /// `fun (i : Fin (2^n)) => F(extend_c n (decode n i)) ·
    ///   noiseDensityW ρ (n+1) (decode (n+1) split_idx) (extend_c n (decode n i))`.
    fn split_half_fn(
        &self,
        parent: &EnvDeclBuilder,
        c_true: bool,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        outer_pt: &Expr,
    ) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let p2n = self.pow2(n);
        let (i_id, i) = d.fresh_local(self.fin_of(&p2n));
        let ext = self.extend(c_true, n, &self.decode(n, &i));
        let body = self.mul(
            Expr::app(f.clone(), ext.clone()),
            self.density(rho, &self.succ(n), outer_pt, &ext),
        );
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, self.fin_of(&p2n), body))
    }

    /// `fun (i : Fin (2^n)) => LOWᵢ + HIGHᵢ` — the merged split integrand.
    fn raw_combined_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        outer_pt: &Expr,
    ) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let p2n = self.pow2(n);
        let (i_id, i) = d.fresh_local(self.fin_of(&p2n));
        let low = self.split_body(&d, false, rho, n, f, outer_pt, &i);
        let high = self.split_body(&d, true, rho, n, f, outer_pt, &i);
        let body = self.add(low, high);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, self.fin_of(&p2n), body))
    }

    /// The split half-body at a concrete index `i` (the inlined integrand).
    #[allow(clippy::too_many_arguments)]
    fn split_body(
        &self,
        _parent: &EnvDeclBuilder,
        c_true: bool,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        outer_pt: &Expr,
        i: &Expr,
    ) -> Expr {
        let ext = self.extend(c_true, n, &self.decode(n, i));
        self.mul(
            Expr::app(f.clone(), ext.clone()),
            self.density(rho, &self.succ(n), outer_pt, &ext),
        )
    }

    /// The `n`-level `noiseFn`-integrand of `lift n F` at outer point `x' = decode
    /// n k`: `fun (i : Fin (2^n)) => (lift n F)(decode n i) · noiseDensityW ρ n x' (decode n i)`.
    /// `lift` is `gPart` (g-leg) or `liftH` (cross leg). Byte-identical to `noiseFn`'s
    /// inner sum body, so `Fin.sum (2^n) (this) ≡ noiseFn ρ n (lift n F) k` (defeq).
    fn integrand_fn(
        &self,
        parent: &EnvDeclBuilder,
        is_g: bool,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        k: &Expr,
    ) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let p2n = self.pow2(n);
        let (i_id, i) = d.fresh_local(self.fin_of(&p2n));
        let body = self.integrand_body(is_g, rho, n, f, k, &i);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, self.fin_of(&p2n), body))
    }

    /// `(lift n F)(decode n i) · noiseDensityW ρ n (decode n k) (decode n i)`.
    fn integrand_body(
        &self,
        is_g: bool,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        k: &Expr,
        i: &Expr,
    ) -> Expr {
        let x_prime = self.decode(n, k);
        let y = self.decode(n, i);
        let lift = if is_g {
            Expr::app(self.g_part_of(n, f), y.clone())
        } else {
            Expr::app(self.lift_h_of(n, f), y.clone())
        };
        self.mul(lift, self.density(rho, n, &x_prime, &y))
    }

    /// `fun (i : Fin (2^n)) => (±ρ)·(hInteg i)` — the cross integrand (the
    /// argument to `Fin.sum_smul`). Sign `+ρ` (LOW) / `−ρ` (HIGH).
    fn cross_fn(
        &self,
        parent: &EnvDeclBuilder,
        half: Half,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        k: &Expr,
    ) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let p2n = self.pow2(n);
        let (i_id, i) = d.fresh_local(self.fin_of(&p2n));
        let coeff = self.cross_coeff(half, rho);
        let body = self.mul(coeff, self.integrand_body(false, rho, n, f, k, &i));
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, self.fin_of(&p2n), body))
    }

    /// The cross coefficient: `ρ` (LOW), `Rat.neg ρ` (HIGH).
    fn cross_coeff(&self, half: Half, rho: &Expr) -> Expr {
        match half {
            Half::Low => rho.clone(),
            Half::High => Expr::app(self.rat_neg_const.clone(), rho.clone()),
        }
    }

    /// `fun (i : Fin (2^n)) => gInteg i + (±ρ)·hInteg i` — the target integrand.
    fn target_fn(
        &self,
        parent: &EnvDeclBuilder,
        half: Half,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        k: &Expr,
    ) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let p2n = self.pow2(n);
        let (i_id, i) = d.fresh_local(self.fin_of(&p2n));
        let body = self.target_integrand(half, rho, n, f, k, &i);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, self.fin_of(&p2n), body))
    }

    /// `gInteg i + (±ρ)·hInteg i` at a concrete index (the leaf's RHS shape).
    fn target_integrand(
        &self,
        half: Half,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        k: &Expr,
        i: &Expr,
    ) -> Expr {
        let g = self.integrand_body(true, rho, n, f, k, i);
        let coeff = self.cross_coeff(half, rho);
        let cross = self.mul(coeff, self.integrand_body(false, rho, n, f, k, i));
        self.add(g, cross)
    }

    /// `fun (i : Fin (2^n)) => <combined_leaf>` — the per-index proof for sum_congr.
    fn leaf_fn(
        &self,
        parent: &EnvDeclBuilder,
        half: Half,
        rho: &Expr,
        n: &Expr,
        f: &Expr,
        k: &Expr,
    ) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let p2n = self.pow2(n);
        let (i_id, i) = d.fresh_local(self.fin_of(&p2n));
        let body = self.combined_leaf(&d, half, rho, n, f, k, &i);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, self.fin_of(&p2n), body))
    }

    /// `(neg ρ)·X = neg(ρ·X)` via `mul_comm` + `mul_neg` (avoids unregistered
    /// `Rat.neg_mul`).
    fn neg_mul(&self, rho: &Expr, x: &Expr) -> Expr {
        let neg_rho = Expr::app(self.rat_neg_const.clone(), rho.clone());
        let neg_rho_x = self.mul(neg_rho.clone(), x.clone()); // (−ρ)·X
        let x_neg_rho = self.mul(x.clone(), neg_rho.clone()); // X·(−ρ)
        let comm1 = self.mul_comm(neg_rho.clone(), x.clone()); // (−ρ)·X = X·(−ρ)
        let x_rho = self.mul(x.clone(), rho.clone()); // X·ρ
        let neg_x_rho = Expr::app(self.rat_neg_const.clone(), x_rho.clone()); // −(X·ρ)
        let mneg = self.mul_neg(x.clone(), rho.clone()); // X·(−ρ) = −(X·ρ)
        let rho_x = self.mul(rho.clone(), x.clone()); // ρ·X
        let neg_rho_x_out = Expr::app(self.rat_neg_const.clone(), rho_x.clone()); // −(ρ·X)
        let comm2 = self.mul_comm(x.clone(), rho.clone()); // X·ρ = ρ·X
        let cong = self.congr_to_rat(
            self.rat(),
            x_rho.clone(),
            rho_x.clone(),
            self.rat_neg_const.clone(),
            comm2,
        );
        let s = self.trans(neg_rho_x.clone(), x_neg_rho, neg_x_rho.clone(), comm1, mneg);
        self.trans(neg_rho_x, neg_x_rho, neg_rho_x_out, s, cong)
    }

    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            [a, b],
        )
    }
}

/// Build the type of `noiseFn_succ_<half>`.
fn build_noise_fn_succ_type(c: &NoiseFnSuccConsts, half: Half) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let (f_id, f) = b.fresh_local(c.f_type(&n));
    let p2n = c.pow2(&n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));

    let split_idx = c.split_index(&b, half, &n, &k);
    let lhs = c.noise_fn(&rho, &sn, &f, &split_idx);
    let g_leg = c.noise_fn(&rho, &n, &c.g_part_of(&n, &f), &k);
    let h_leg = c.mul(rho.clone(), c.noise_fn(&rho, &n, &c.lift_h_of(&n, &f), &k));
    let rhs = match half {
        Half::Low => c.add(g_leg, h_leg),
        Half::High => c.sub(g_leg, h_leg),
    };
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(k_id, BinderInfo::Default, c.fin_of(&p2n), concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, c.f_type(&n), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// Build the proof of `noiseFn_succ_<half>`.
fn build_noise_fn_succ_value(c: &NoiseFnSuccConsts, half: Half) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let sn = c.succ(&n);
    let (f_id, f) = b.fresh_local(c.f_type(&n));
    let p2n = c.pow2(&n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));

    let split_idx = c.split_index(&b, half, &n, &k);
    let outer_pt = c.decode(&sn, &split_idx);

    // ── step 1 : split.  lhs = (Σ LOWsplit) + (Σ HIGHsplit).
    let lhs = c.noise_fn(&rho, &sn, &f, &split_idx);
    let low_fn = c.split_half_fn(&b, false, &rho, &n, &f, &outer_pt);
    let high_fn = c.split_half_fn(&b, true, &rho, &n, &f, &outer_pt);
    let sum_low = c.sum(&p2n, low_fn.clone());
    let sum_high = c.sum(&p2n, high_fn.clone());
    let split_rhs = c.add(sum_low.clone(), sum_high.clone());
    let split = c.split_lemma(&rho, &n, &f, &split_idx);

    // ── step 2 : merge.  (Σ LOW)+(Σ HIGH) = Σ (LOW+HIGH)   [Eq.symm Fin.sum_add].
    let raw_fn = c.raw_combined_fn(&b, &rho, &n, &f, &outer_pt);
    let sum_raw = c.sum(&p2n, raw_fn.clone());
    let sum_add_split = c.sum_add(&p2n, low_fn, high_fn);
    let merge = c.symm(sum_raw.clone(), split_rhs.clone(), sum_add_split);

    // ── step 3 : per-index leaf.  Σ raw = Σ target   [Fin.sum_congr].
    let target_fn = c.target_fn(&b, half, &rho, &n, &f, &k);
    let sum_target = c.sum(&p2n, target_fn.clone());
    let leaf_fn = c.leaf_fn(&b, half, &rho, &n, &f, &k);
    let congr = c.sum_congr(&p2n, raw_fn, target_fn, leaf_fn);

    // ── step 4 : split target.  Σ target = (Σ gInteg) + (Σ cross)   [Fin.sum_add].
    let g_fn = c.integrand_fn(&b, true, &rho, &n, &f, &k);
    let cross_fn = c.cross_fn(&b, half, &rho, &n, &f, &k);
    let sum_g = c.sum(&p2n, g_fn.clone());
    let sum_cross = c.sum(&p2n, cross_fn.clone());
    let split_target = c.sum_add(&p2n, g_fn, cross_fn.clone());
    let g_plus_cross = c.add(sum_g.clone(), sum_cross.clone());

    // ── step 5 : pull ±ρ out of the cross.  Σ cross = (±ρ)·(Σ hInteg)   [Fin.sum_smul].
    let h_fn = c.integrand_fn(&b, false, &rho, &n, &f, &k);
    let sum_h = c.sum(&p2n, h_fn.clone());
    let coeff = c.cross_coeff(half, &rho);
    let smul = c.sum_smul(&p2n, coeff.clone(), h_fn);
    let coeff_sum_h = c.mul(coeff.clone(), sum_h.clone());
    // congr on the 2nd add slot: (Σg + Σcross) = (Σg + (±ρ)·Σh).
    let cross_to_smul = {
        let mut dd = EnvDeclBuilder::child_of(&b);
        let (s_id, s) = dd.fresh_local(c.rat());
        let body = c.add(sum_g.clone(), s);
        let f_lam = dd.finish_child(dd.mk_lam(s_id, BinderInfo::Default, c.rat(), body));
        c.congr_to_rat(c.rat(), sum_cross.clone(), coeff_sum_h.clone(), f_lam, smul)
    };
    let g_plus_coeff_h = c.add(sum_g.clone(), coeff_sum_h.clone());

    // ── step 6 : assemble the RHS (Σg ≡ noiseFn gPart, Σh ≡ noiseFn liftH defeq).
    let g_leg = c.noise_fn(&rho, &n, &c.g_part_of(&n, &f), &k);
    let h_leg_inner = c.noise_fn(&rho, &n, &c.lift_h_of(&n, &f), &k);
    let rho_h_leg = c.mul(rho.clone(), h_leg_inner.clone());
    let rhs = match half {
        Half::Low => c.add(g_leg.clone(), rho_h_leg.clone()),
        Half::High => c.sub(g_leg.clone(), rho_h_leg.clone()),
    };

    // chain so far: lhs = split_rhs = sum_raw = sum_target = g_plus_cross = g_plus_coeff_h.
    let t = c.trans(lhs.clone(), split_rhs, sum_raw.clone(), split, merge);
    let t = c.trans(lhs.clone(), sum_raw, sum_target.clone(), t, congr);
    let t = c.trans(
        lhs.clone(),
        sum_target,
        g_plus_cross.clone(),
        t,
        split_target,
    );
    let t = c.trans(
        lhs.clone(),
        g_plus_cross,
        g_plus_coeff_h.clone(),
        t,
        cross_to_smul,
    );

    // For HIGH, the final coeff is (−ρ): rewrite (−ρ)·Σh → −(ρ·Σh) and let
    // `Rat.sub` defeq fold; `g_plus_coeff_h` is then defeq to the stated `rhs`.
    let proof = match half {
        Half::Low => {
            // g_plus_coeff_h = Σg + ρ·Σh, defeq to rhs (Σg ≡ noiseFn gPart, Σh ≡ noiseFn liftH).
            t
        }
        Half::High => {
            // g_plus_coeff_h = Σg + (−ρ)·Σh.  neg_mul : (−ρ)·Σh = −(ρ·Σh).
            let neg_mul = c.neg_mul(&rho, &sum_h);
            let neg_rho_sum_h = c.mul(c.cross_coeff(Half::High, &rho), sum_h.clone());
            let neg_of_rho_sum_h =
                Expr::app(c.rat_neg_const.clone(), c.mul(rho.clone(), sum_h.clone()));
            let cong_neg_mul = {
                let mut dd = EnvDeclBuilder::child_of(&b);
                let (s_id, s) = dd.fresh_local(c.rat());
                let body = c.add(sum_g.clone(), s);
                let f_lam = dd.finish_child(dd.mk_lam(s_id, BinderInfo::Default, c.rat(), body));
                c.congr_to_rat(
                    c.rat(),
                    neg_rho_sum_h,
                    neg_of_rho_sum_h.clone(),
                    f_lam,
                    neg_mul,
                )
            };
            let g_plus_neg = c.add(sum_g.clone(), neg_of_rho_sum_h);
            // g_plus_neg = Σg + −(ρ·Σh), defeq to Rat.sub (noiseFn gPart) (ρ·noiseFn liftH).
            c.trans(lhs.clone(), g_plus_coeff_h, g_plus_neg, t, cong_neg_mul)
        }
    };
    // The final term's RHS is defeq to `rhs`; bind and return.
    let _ = rhs;

    let e = b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), proof);
    let e = b.mk_lam(f_id, BinderInfo::Default, c.f_type(&n), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// Build the type + proof of `noiseFn_succ_<half>`.
fn build_noise_fn_succ(c: &NoiseFnSuccConsts, half: Half) -> (Expr, Expr) {
    (
        build_noise_fn_succ_type(c, half),
        build_noise_fn_succ_value(c, half),
    )
}
