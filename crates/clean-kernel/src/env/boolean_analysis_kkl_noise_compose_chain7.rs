// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_kkl_noise_compose_chain6.rs — the RUNG-1 leg
// proofs and top-level `two_norm_spectral_value` for
// `noise_two_norm_spectral_third`. Split out only for the 500-line-per-file
// convention; not a standalone module.

impl ComposeConsts {
    /// Rung1-leg2 (G1 → G2): per x, substitute the operator semigroup
    /// `g x·(T_{1/3}² g x) = g x·(cube·T_{1/9}g x)` via
    /// `congr (g x·_) (noiseOp_compose_third n g x)`. `subsetSum_congr`.
    fn rung1_leg2(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let hyp = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let gx = Expr::app(g.clone(), x.clone());
            let inner_op = Expr::apps(self.noise_op.clone(), [self.third(), n.clone(), g.clone()]);
            let ttg = self.op_apply(&self.third(), n, &inner_op, &x);
            let scaled = self.mul(self.cube(n), self.op_apply(&self.ninth(), n, g, &x));
            let motive = self.mul_left_motive(&xb, &gx);
            let body = self.congr_rat(ttg, scaled, motive, self.op_compose_at(n, g, &x));
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
        };
        let g1 = self.g1_x_fn(parent, n, g);
        let g2 = self.g2_x_fn(parent, n, g);
        self.ss_congr(n, &g1, &g2, hyp)
    }

    /// Per-x leg-3 leaf: `g x·(cube·op) = cube·(g x·op)` (i.e. `a·(c·b) = c·(a·b)`).
    ///   `a·(c·b) →[symm assoc a c b] (a·c)·b →[congr (_·b) comm a c] (c·a)·b
    ///          →[assoc c a b] c·(a·b)`.
    fn rung1_leg3_leaf(&self, parent: &EnvDeclBuilder, a: &Expr, cc: &Expr, b: &Expr) -> Expr {
        let acb = self.mul(a.clone(), self.mul(cc.clone(), b.clone())); // a·(c·b)
        let ac_b = self.mul(self.mul(a.clone(), cc.clone()), b.clone()); // (a·c)·b
        let ca_b = self.mul(self.mul(cc.clone(), a.clone()), b.clone()); // (c·a)·b
        let c_ab = self.mul(cc.clone(), self.mul(a.clone(), b.clone())); // c·(a·b)
                                                                         // s1 : a·(c·b) = (a·c)·b   symm (assoc a c b)
        let s1 = self.symm(
            ac_b.clone(),
            acb.clone(),
            self.mul_assoc(a.clone(), cc.clone(), b.clone()),
        );
        // s2 : (a·c)·b = (c·a)·b   congr (_·b) (comm a c)
        let motive = self.mul_right_motive(parent, b);
        let s2 = self.congr_rat(
            self.mul(a.clone(), cc.clone()),
            self.mul(cc.clone(), a.clone()),
            motive,
            self.mul_comm(a.clone(), cc.clone()),
        );
        // s3 : (c·a)·b = c·(a·b)   assoc c a b
        let s3 = self.mul_assoc(cc.clone(), a.clone(), b.clone());
        let t1 = self.trans(acb.clone(), ac_b.clone(), ca_b.clone(), s1, s2);
        self.trans(acb, ca_b, c_ab, t1, s3)
    }

    /// Rung1-leg3 (G2 → G3 = `cube·Σ_x(g x·op)`): per x reassoc
    /// `g x·(cube·op) = cube·(g x·op)` (`ss_congr` over `rung1_leg3_leaf`), then
    /// `subsetSum_smul` to pull `cube` out.
    fn rung1_leg3(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let cube = self.cube(n);
        // scaled_fn x := cube·(g x·op)   (subsetSum_smul's scaled form)
        let scaled_fn = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let gx_op = self.mul(
                Expr::app(g.clone(), x.clone()),
                self.op_apply(&self.ninth(), n, g, &x),
            );
            let body = self.mul(cube.clone(), gx_op);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
        };
        let inner_fn = self.g3_inner_x_fn(parent, n, g);
        // leg A: G2 = Σ_x cube·(g x·op)   (ss_congr over leaf).
        let g2 = self.g2_x_fn(parent, n, g);
        let leaf_hyp = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let gx = Expr::app(g.clone(), x.clone());
            let op = self.op_apply(&self.ninth(), n, g, &x);
            let body = self.rung1_leg3_leaf(&xb, &gx, &cube, &op);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
        };
        let sum_g2 = self.ssum(n, g2.clone());
        let sum_scaled = self.ssum(n, scaled_fn.clone());
        let step_a = self.ss_congr(n, &g2, &scaled_fn, leaf_hyp);
        // leg B: Σ_x cube·(g x·op) = cube·Σ_x(g x·op)   (ss_smul).
        let step_b = self.ss_smul(n, &cube, &inner_fn);
        let g3 = self.mul(cube.clone(), self.ssum(n, inner_fn));
        self.trans(sum_g2, sum_scaled, g3, step_a, step_b)
    }

    /// Per-y leg-4 inner leaf: `g x·(W·g y) = (g x·g y)·W`.
    ///   `g x·(W·g y) →[congr (g x·_) comm W (g y)] g x·(g y·W)
    ///             →[symm assoc (g x)(g y) W] (g x·g y)·W`.
    fn rung1_leg4_leaf(&self, parent: &EnvDeclBuilder, gx: &Expr, gy: &Expr, w: &Expr) -> Expr {
        let gx_wgy = self.mul(gx.clone(), self.mul(w.clone(), gy.clone())); // g x·(W·g y)
        let gx_gyw = self.mul(gx.clone(), self.mul(gy.clone(), w.clone())); // g x·(g y·W)
        let gxgy_w = self.mul(self.mul(gx.clone(), gy.clone()), w.clone()); // (g x·g y)·W
                                                                            // s1 : g x·(W·g y) = g x·(g y·W)   congr (g x·_) (comm W (g y))
        let motive = self.mul_left_motive(parent, gx);
        let s1 = self.congr_rat(
            self.mul(w.clone(), gy.clone()),
            self.mul(gy.clone(), w.clone()),
            motive,
            self.mul_comm(w.clone(), gy.clone()),
        );
        // s2 : g x·(g y·W) = (g x·g y)·W   symm (assoc (g x)(g y) W)
        let s2 = self.symm(
            gxgy_w.clone(),
            gx_gyw.clone(),
            self.mul_assoc(gx.clone(), gy.clone(), w.clone()),
        );
        self.trans(gx_wgy, gx_gyw, gxgy_w, s1, s2)
    }

    /// Per-x leg-4 slice: `g x·noiseOp(1/9)g x = Σ_y (g x·g y)·W_{1/9}(x,y)`.
    /// `noiseOp(1/9)g x ≡ Σ_y W_{1/9}(x,y)·g y` (reducible); smul-in then per-y
    /// reassoc (`rung1_leg4_leaf`).
    fn rung1_leg4_xslice(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let gx = Expr::app(g.clone(), x.clone());
        // h_fn y := W_{1/9}(x,y)·g y   (the noiseOp(1/9)g x reducible body)
        let h_fn = {
            let mut yb = EnvDeclBuilder::child_of(parent);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let body = self.mul(
                self.dens(&self.ninth(), n, x, &y),
                Expr::app(g.clone(), y.clone()),
            );
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };
        // gh_fn y := g x·(W·g y)
        let gh_fn = {
            let mut yb = EnvDeclBuilder::child_of(parent);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let hw = self.mul(
                self.dens(&self.ninth(), n, x, &y),
                Expr::app(g.clone(), y.clone()),
            );
            let body = self.mul(gx.clone(), hw);
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };
        // final_fn y := (g x·g y)·W   (B3a inner integrand at this x)
        let final_fn = {
            let mut yb = EnvDeclBuilder::child_of(parent);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let gxgy = self.mul(gx.clone(), Expr::app(g.clone(), y.clone()));
            let body = self.mul(gxgy, self.dens(&self.ninth(), n, x, &y));
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };

        let sum_h = self.ssum(n, h_fn.clone());
        let gx_sumh = self.mul(gx.clone(), sum_h.clone()); // g x·(Σ_y W·g y)
        let sum_gh = self.ssum(n, gh_fn.clone());
        let sum_final = self.ssum(n, final_fn.clone());
        // s1 : g x·Σ_y(W·g y) = Σ_y g x·(W·g y)   symm (ss_smul n (g x) h_fn)
        let smul = self.ss_smul(n, &gx, &h_fn);
        let s1 = self.symm(sum_gh.clone(), gx_sumh.clone(), smul);
        // s2 : Σ_y g x·(W·g y) = Σ_y (g x·g y)·W   ss_congr over leaf
        let leaf_hyp = {
            let mut yb = EnvDeclBuilder::child_of(parent);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let gy = Expr::app(g.clone(), y.clone());
            let w = self.dens(&self.ninth(), n, x, &y);
            let body = self.rung1_leg4_leaf(&yb, &gx, &gy, &w);
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };
        let s2 = self.ss_congr(n, &gh_fn, &final_fn, leaf_hyp);
        self.trans(gx_sumh, sum_gh, sum_final, s1, s2)
    }

    /// Rung1-leg4 (G3-inner → G4-inner, under `congr (cube·_)`): per x the
    /// `rung1_leg4_xslice`, lifted by `subsetSum_congr`, then `congr (cube·_)`.
    fn rung1_leg4(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let cube = self.cube(n);
        let inner3 = self.g3_inner_x_fn(parent, n, g);
        let inner4 = self.g4_inner_x_fn(parent, n, g);
        let hyp = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let body = self.rung1_leg4_xslice(&xb, n, g, &x);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
        };
        let inner_congr = self.ss_congr(n, &inner3, &inner4, hyp);
        let sum3 = self.ssum(n, inner3);
        let sum4 = self.ssum(n, inner4);
        let motive = self.mul_left_motive(parent, &cube);
        self.congr_rat(sum3, sum4, motive, inner_congr)
    }

    /// Rung1-leg5 (G4 → RHS spectral, under `congr (cube·_)`): the spectral Fubini
    /// `Σ_x Σ_y (g x·g y)·W_{1/9} = Σ_S ((1/3)^{|S|})²·(A·A)` via
    /// `Eq.symm (noise_two_norm_eq_pairing n g)` (B3a), lifted by `congr (cube·_)`.
    fn rung1_leg5(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let cube = self.cube(n);
        let pairing = self.ssum(n, self.g4_inner_x_fn(parent, n, g)); // ⟨T_{1/9}g,g⟩
        let spectral = self.ssum(n, self.spectral_s_fn(parent, n, g)); // Σ_S w²·A²
                                                                       // B3a : spectral = pairing ; symm(spectral, pairing, b3a) gives
                                                                       // pairing = spectral (Eq.symm l r h : r = l from h : l = r).
        let b3a = self.two_norm_pairing_at(n, g);
        let inner = self.symm(spectral.clone(), pairing.clone(), b3a);
        let motive = self.mul_left_motive(parent, &cube);
        self.congr_rat(pairing, spectral, motive, inner)
    }
}

/// `λ n g => Eq.trans … (G0 = G1 = G2 = G3 = G4 = RHS)`.
fn two_norm_spectral_value(c: &ComposeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let cube = c.cube(&n);

    // G0 (LHS): Σ_y (T_{1/3}g y)·(T_{1/3}g y).
    let g0 = {
        let yfn = {
            let mut yb = EnvDeclBuilder::child_of(&b);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let tgy = c.op_apply(&c.third(), &n, &g, &y);
            let body = c.mul(tgy.clone(), tgy);
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };
        c.ssum(&n, yfn)
    };
    let g1 = c.ssum(&n, c.g1_x_fn(&b, &n, &g));
    let g2 = c.ssum(&n, c.g2_x_fn(&b, &n, &g));
    let g3 = c.mul(cube.clone(), c.ssum(&n, c.g3_inner_x_fn(&b, &n, &g)));
    let g4 = c.mul(cube.clone(), c.ssum(&n, c.g4_inner_x_fn(&b, &n, &g)));
    let rhs = c.mul(cube.clone(), c.ssum(&n, c.spectral_s_fn(&b, &n, &g)));

    // G0 = G1 : noise_self_adjoint_sq (1/3) n g.
    let l1 = c.self_adjoint_sq_at(&c.third(), &n, &g);
    let l2 = c.rung1_leg2(&b, &n, &g);
    let l3 = c.rung1_leg3(&b, &n, &g);
    let l4 = c.rung1_leg4(&b, &n, &g);
    let l5 = c.rung1_leg5(&b, &n, &g);

    let t1 = c.trans(g0.clone(), g1.clone(), g2.clone(), l1, l2);
    let t2 = c.trans(g0.clone(), g2.clone(), g3.clone(), t1, l3);
    let t3 = c.trans(g0.clone(), g3.clone(), g4.clone(), t2, l4);
    let proof = c.trans(g0, g4, rhs, t3, l5);

    let val = b.mk_lam(g_id, BinderInfo::Default, g_ty, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}
