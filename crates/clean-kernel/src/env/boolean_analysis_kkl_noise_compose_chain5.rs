// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_kkl_noise_compose_chain4.rs — the leg proofs and
// top-level `op_compose_type` / `op_compose_value` for `noiseOp_compose_third`.
// Split out only for the 500-line-per-file convention; not a standalone module.

impl ComposeConsts {
    /// Op-leg-1 (F0 → F1): per z, smul-in `W_{1/3}(x,z)·(Σ_w h_w) = Σ_w
    /// W_{1/3}(x,z)·h_w` (`symm (ss_smul n (W x z) h_fn)`); lifted over z by
    /// `subsetSum_congr`.
    fn op_leg1(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        // F0 z-integrand `fun z => W_{1/3}(x,z)·(noiseOp(1/3)g z)` — the LHS with the
        // OUTER noiseOp folded but the inner noiseOp written as its subsetSum body.
        let f0_fn = {
            let mut zb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = zb.fresh_local(hcp.clone());
            let inner = {
                let mut wb = EnvDeclBuilder::child_of(&zb);
                let (w_id, w) = wb.fresh_local(hcp.clone());
                let body = self.mul(
                    self.dens(&self.third(), n, &z, &w),
                    Expr::app(g.clone(), w.clone()),
                );
                wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), body))
            };
            let inner_sum = self.ssum(n, inner);
            let body = self.mul(self.dens(&self.third(), n, x, &z), inner_sum);
            zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
        };
        let hyp = {
            let mut zb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = zb.fresh_local(hcp.clone());
            // h_fn w := W_{1/3}(z,w)·g w
            let h_fn = {
                let mut wb = EnvDeclBuilder::child_of(&zb);
                let (w_id, w) = wb.fresh_local(hcp.clone());
                let body = self.mul(
                    self.dens(&self.third(), n, &z, &w),
                    Expr::app(g.clone(), w.clone()),
                );
                wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), body))
            };
            let wxz = self.dens(&self.third(), n, x, &z);
            let sum_h = self.ssum(n, h_fn.clone());
            let lhs = self.mul(wxz.clone(), sum_h.clone()); // W·(Σ_w h)
                                                            // smul : Σ_w (W·h) = W·Σ_w h ; symm gives W·Σ_w h = Σ_w (W·h).
            let smul = self.ss_smul(n, &wxz, &h_fn);
            // Σ_w (W·h) integrand
            let wh_fn = {
                let mut wb = EnvDeclBuilder::child_of(&zb);
                let (w_id, w) = wb.fresh_local(hcp.clone());
                let hw = self.mul(
                    self.dens(&self.third(), n, &z, &w),
                    Expr::app(g.clone(), w.clone()),
                );
                let body = self.mul(wxz.clone(), hw);
                wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), body))
            };
            let sum_wh = self.ssum(n, wh_fn);
            let body = self.symm(sum_wh, lhs, smul);
            zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
        };
        let f1_fn = self.f1_z_fn(parent, n, g, x);
        self.ss_congr(n, &f0_fn, &f1_fn, hyp)
    }

    /// Op-leg-2 (F1 → F2): `subsetSum_swap n op_swap_kernel`
    /// (`Σ_z Σ_w K = Σ_w Σ_z K`).
    fn op_leg2(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        let k = self.op_swap_kernel(parent, n, g, x);
        self.ss_swap(n, &k)
    }

    /// Op-leg-3 (F2 → F3): per w, reassoc each z-summand `W·(W·g) = (W·W)·g`
    /// (`ss_congr` over `symm assoc`), then pull `g w` out of the z-sum
    /// (`symm (ss_smul)`-style right-out). Lifted over w by `subsetSum_congr`.
    fn op_leg3(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let hyp = {
            let mut wb = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = wb.fresh_local(hcp.clone());
            let gw = Expr::app(g.clone(), w.clone());

            // pre_fn z := W(x,z)·(W(z,w)·g w)   (F2 inner z-integrand at this w)
            let pre_fn = {
                let mut zb = EnvDeclBuilder::child_of(&wb);
                let (z_id, z) = zb.fresh_local(hcp.clone());
                let inner = self.mul(self.dens(&self.third(), n, &z, &w), gw.clone());
                let body = self.mul(self.dens(&self.third(), n, x, &z), inner);
                zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
            };
            // mid_fn z := (W(x,z)·W(z,w))·g w
            let mid_fn = {
                let mut zb = EnvDeclBuilder::child_of(&wb);
                let (z_id, z) = zb.fresh_local(hcp.clone());
                let pp = self.mul(
                    self.dens(&self.third(), n, x, &z),
                    self.dens(&self.third(), n, &z, &w),
                );
                let body = self.mul(pp, gw.clone());
                zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
            };
            // P_fn z := W(x,z)·W(z,w)   (the convolution summand)
            let p_fn = {
                let mut zb = EnvDeclBuilder::child_of(&wb);
                let (z_id, z) = zb.fresh_local(hcp.clone());
                let body = self.mul(
                    self.dens(&self.third(), n, x, &z),
                    self.dens(&self.third(), n, &z, &w),
                );
                zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
            };
            // step A: Σ_z W·(W·g) = Σ_z (W·W)·g   (ss_congr over symm assoc).
            let assoc_hyp = {
                let mut zb = EnvDeclBuilder::child_of(&wb);
                let (z_id, z) = zb.fresh_local(hcp.clone());
                let wxz = self.dens(&self.third(), n, x, &z);
                let wzw = self.dens(&self.third(), n, &z, &w);
                let lhs = self.mul(wxz.clone(), self.mul(wzw.clone(), gw.clone())); // W·(W·g)
                let rhs = self.mul(self.mul(wxz.clone(), wzw.clone()), gw.clone()); // (W·W)·g
                                                                                    // assoc wxz wzw gw : (W·W)·g = W·(W·g);  symm gives W·(W·g) = (W·W)·g.
                let assoc = self.mul_assoc(wxz, wzw, gw.clone());
                let body = self.symm(rhs, lhs, assoc);
                zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
            };
            let sum_pre = self.ssum(n, pre_fn.clone());
            let sum_mid = self.ssum(n, mid_fn.clone());
            let step_a = self.ss_congr(n, &pre_fn, &mid_fn, assoc_hyp);
            // step B: Σ_z (P·g w) = (Σ_z P)·g w   (right-smul-out = symm of right-in).
            let sum_p = self.ssum(n, p_fn.clone());
            let conv_times_g = self.mul(sum_p.clone(), gw.clone());
            let step_b = self.right_smul_out(&wb, n, &p_fn, &gw, &sum_p);
            // chain: sum_pre = sum_mid = (Σ_z P)·g w  = F3 body at this w.
            let body = self.trans(sum_pre, sum_mid, conv_times_g, step_a, step_b);
            wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), body))
        };
        let f2 = self.f2_w_fn(parent, n, g, x);
        let f3 = self.f3_w_fn(parent, n, g, x);
        self.ss_congr(n, &f2, &f3, hyp)
    }

    /// `Σ_z (P_z·c) = (Σ_z P_z)·c` — the right-smul pull-OUT (`c := g w`). Chain:
    ///   `Σ_z (P·c) →[ss_congr·comm] Σ_z (c·P) →[ss_smul] c·Σ_z P
    ///            →[comm] (Σ_z P)·c`.
    fn right_smul_out(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        p_fn: &Expr,
        c: &Expr,
        sum_p: &Expr,
    ) -> Expr {
        let hcp = self.hcpoint_of(n);
        // pc_fn z := P_z·c
        let pc_fn = {
            let mut zb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = zb.fresh_local(hcp.clone());
            let body = self.mul(Expr::app(p_fn.clone(), z.clone()), c.clone());
            zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
        };
        // cp_fn z := c·P_z
        let cp_fn = {
            let mut zb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = zb.fresh_local(hcp.clone());
            let body = self.mul(c.clone(), Expr::app(p_fn.clone(), z.clone()));
            zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
        };
        let sum_pc = self.ssum(n, pc_fn.clone());
        let sum_cp = self.ssum(n, cp_fn.clone());
        let c_sum = self.mul(c.clone(), sum_p.clone());
        let out = self.mul(sum_p.clone(), c.clone());
        // s1 : Σ(P·c) = Σ(c·P)  ss_congr over per-z comm P c
        let comm_hyp = {
            let mut zb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = zb.fresh_local(hcp.clone());
            let body = self.mul_comm(Expr::app(p_fn.clone(), z.clone()), c.clone());
            zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
        };
        let s1 = self.ss_congr(n, &pc_fn, &cp_fn, comm_hyp);
        // s2 : Σ(c·P) = c·Σ P   (ss_smul)
        let s2 = self.ss_smul(n, c, p_fn);
        // s3 : c·Σ P = (Σ P)·c   (mul_comm)
        let s3 = self.mul_comm(c.clone(), sum_p.clone());
        let t1 = self.trans(sum_pc.clone(), sum_cp, c_sum.clone(), s1, s2);
        self.trans(sum_pc, c_sum, out, t1, s3)
    }

    /// Op-leg-4 (F3 → F4): per w, the convolution `(Σ_z W·W)·g = (cube·W_{1/9})·g`
    /// via `congr (_·g w) (noiseDensityW_compose_third n x w)`. `subsetSum_congr`.
    fn op_leg4(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let hyp = {
            let mut wb = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = wb.fresh_local(hcp.clone());
            let gw = Expr::app(g.clone(), w.clone());
            let conv = self.conv_zsum(&wb, n, x, &w);
            let conv_rhs = self.mul(self.cube(n), self.dens(&self.ninth(), n, x, &w));
            let motive = self.mul_right_motive(&wb, &gw);
            let body = self.congr_rat(conv, conv_rhs, motive, self.conv_at(n, x, &w));
            wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), body))
        };
        let f3 = self.f3_w_fn(parent, n, g, x);
        let f4 = self.f4_w_fn(parent, n, g, x);
        self.ss_congr(n, &f3, &f4, hyp)
    }

    /// Op-leg-5 (F4 → F5): per w, reassoc `(cube·W_{1/9})·g = cube·(W_{1/9}·g)`
    /// (`mul_assoc`). `subsetSum_congr`.
    fn op_leg5(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let hyp = {
            let mut wb = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = wb.fresh_local(hcp.clone());
            let gw = Expr::app(g.clone(), w.clone());
            let cube = self.cube(n);
            let w9 = self.dens(&self.ninth(), n, x, &w);
            let body = self.mul_assoc(cube, w9, gw);
            wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), body))
        };
        let f4 = self.f4_w_fn(parent, n, g, x);
        let f5 = self.f5_w_fn(parent, n, g, x);
        self.ss_congr(n, &f4, &f5, hyp)
    }

    /// Op-leg-6 (F5 → F6): `subsetSum_smul n cube f6_inner_w_fn`
    /// (`Σ_w cube·(…) = cube·Σ_w(…)`); the folded RHS `cube·subsetSum n
    /// (f6_inner) ≡ cube·noiseOp(1/9) n g x`.
    fn op_leg6(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        let cube = self.cube(n);
        let inner = self.f6_inner_w_fn(parent, n, g, x);
        self.ss_smul(n, &cube, &inner)
    }
}

/// `∀ (n : Nat) (g : HCPoint n → Rat) (x : HCPoint n),
///    noiseOp (1/3) n (noiseOp (1/3) n g) x = cube n · noiseOp (1/9) n g x`.
fn op_compose_type(c: &ComposeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());

    let third = c.third();
    let ninth = c.ninth();
    // LHS: noiseOp(1/3) n (noiseOp(1/3) n g) x.
    let inner = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.noiseOp"), vec![]),
        [third.clone(), n.clone(), g.clone()],
    );
    let lhs = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.noiseOp"), vec![]),
        [third.clone(), n.clone(), inner, x.clone()],
    );
    // RHS: cube · noiseOp(1/9) n g x.
    let rhs = c.mul(c.cube(&n), c.op(&ninth, &n, &g, &x));
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(x_id, BinderInfo::Default, hcp, concl);
    let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `λ n g x => Eq.trans … (F0 = F1 = … = F6 ≡ cube·noiseOp(1/9)g x)`.
fn op_compose_value(c: &ComposeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());

    let third = c.third();
    let ninth = c.ninth();
    let cube = c.cube(&n);

    // F0 (LHS, folded outer noiseOp; the proof runs over the subsetSum body, which
    // is def-eq to noiseOp(1/3) n (noiseOp(1/3) n g) x by reducibility).
    let f0 = {
        let f0_fn = {
            let mut zb = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = zb.fresh_local(hcp.clone());
            let inner = {
                let mut wb = EnvDeclBuilder::child_of(&zb);
                let (w_id, w) = wb.fresh_local(hcp.clone());
                let body = c.mul(c.dens(&third, &n, &z, &w), Expr::app(g.clone(), w.clone()));
                wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), body))
            };
            let inner_sum = c.ssum(&n, inner);
            let body = c.mul(c.dens(&third, &n, &x, &z), inner_sum);
            zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
        };
        c.ssum(&n, f0_fn)
    };
    let f1 = c.ssum(&n, c.f1_z_fn(&b, &n, &g, &x));
    let f2 = c.ssum(&n, c.f2_w_fn(&b, &n, &g, &x));
    let f3 = c.ssum(&n, c.f3_w_fn(&b, &n, &g, &x));
    let f4 = c.ssum(&n, c.f4_w_fn(&b, &n, &g, &x));
    let f5 = c.ssum(&n, c.f5_w_fn(&b, &n, &g, &x));
    let f6 = c.mul(cube.clone(), c.ssum(&n, c.f6_inner_w_fn(&b, &n, &g, &x)));
    // RHS = cube · noiseOp(1/9) n g x  (def-eq to f6).
    let rhs = c.mul(cube.clone(), c.op(&ninth, &n, &g, &x));

    let l1 = c.op_leg1(&b, &n, &g, &x);
    let l2 = c.op_leg2(&b, &n, &g, &x);
    let l3 = c.op_leg3(&b, &n, &g, &x);
    let l4 = c.op_leg4(&b, &n, &g, &x);
    let l5 = c.op_leg5(&b, &n, &g, &x);
    let l6 = c.op_leg6(&b, &n, &g, &x);

    let t1 = c.trans(f0.clone(), f1.clone(), f2.clone(), l1, l2);
    let t2 = c.trans(f0.clone(), f2.clone(), f3.clone(), t1, l3);
    let t3 = c.trans(f0.clone(), f3.clone(), f4.clone(), t2, l4);
    let t4 = c.trans(f0.clone(), f4.clone(), f5.clone(), t3, l5);
    let t5 = c.trans(f0.clone(), f5.clone(), f6.clone(), t4, l6);
    // f6 = rhs is def-eq (noiseOp(1/9) reducible); close with the final smul leg's
    // RHS endpoint already being f6, and f6 ≡ rhs, so use `t5` retyped via the RHS
    // spelling: the `trans` to `rhs` needs an explicit `f6 = rhs` proof.
    let f6_eq_rhs = {
        // f6 := cube·subsetSum n (f6_inner) ; rhs := cube·noiseOp(1/9) n g x.
        // subsetSum n (f6_inner) ≡ noiseOp(1/9) n g x (reducible), so Eq.refl on f6.
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(eq_refl, [c.rat.clone(), f6.clone()])
    };
    let proof = c.trans(f0, f6, rhs, t5, f6_eq_rhs);

    let val = b.mk_lam(x_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(g_id, BinderInfo::Default, g_ty, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}
