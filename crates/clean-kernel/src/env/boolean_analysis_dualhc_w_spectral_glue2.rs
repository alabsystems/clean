// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_dualhc_w_spectral_glue.rs — the `glue_value`
// (semigroup glue) multi-leg Fubini proof. Split out for the 500-line convention.

impl WSpectralConsts {
    /// `fun (v : HCPoint n) => dens(ρ,w,v)·g v` — the inner `(Tg)(w)` v-integrand.
    fn dens_g_v_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        g: &Expr,
        w: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (v_id, v) = b.fresh_local(hcp.clone());
        let body = self.mul(self.dens(rho, n, w, &v), Expr::app(g.clone(), v.clone()));
        b.finish_child(b.mk_lam(v_id, BinderInfo::Default, hcp, body))
    }

    /// `fun w => dens(ρ,x,w)·dens(ρ,w,v)` — the semigroup w-kernel at fixed x,v.
    fn compose_w_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        v: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (w_id, w) = b.fresh_local(hcp.clone());
        let body = self.mul(self.dens(rho, n, x, &w), self.dens(rho, n, &w, v));
        b.finish_child(b.mk_lam(w_id, BinderInfo::Default, hcp, body))
    }

    /// `Σ_v dens(ρ²,x,v)·g v` — the `cube·(·)` factor of `inner_x`'s RHS.
    fn rhosq_dens_g_sum(
        &self,
        parent: &EnvDeclBuilder,
        rho_sq: &Expr,
        n: &Expr,
        g: &Expr,
        x: &Expr,
    ) -> Expr {
        self.ssum(n, self.dens_g_v_fn(parent, rho_sq, n, g, x))
    }

    /// `inner_x : Σ_w dens(ρ,x,w)·(Σ_v dens(ρ,w,v)·g v) = cube·(Σ_v dens(ρ²,x,v)·g v)`.
    /// The per-`x` operator-composition collapse (the heart of the glue).
    fn inner_x(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let rho_sq = self.mul(rho.clone(), rho.clone());

        // i0 := Σ_w dens(ρ,x,w)·(Σ_v dens(ρ,w,v)·g v).
        let i0_fn = self.ttg_w_fn(parent, rho, n, g, x); // fun w => dens(x,w)·(Σ_v dens(w,v)·g v)
        let i0 = self.ssum(n, i0_fn.clone());

        // i1 := Σ_w Σ_v dens(ρ,x,w)·(dens(ρ,w,v)·g v)   [per-w symm smul].
        let i1_w_fn = {
            let mut wb = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = wb.fresh_local(hcp.clone());
            let v_fn = {
                let mut vb = EnvDeclBuilder::child_of(&wb);
                let (v_id, v) = vb.fresh_local(hcp.clone());
                let body = self.mul(
                    self.dens(rho, n, x, &w),
                    self.mul(self.dens(rho, n, &w, &v), Expr::app(g.clone(), v.clone())),
                );
                vb.finish_child(vb.mk_lam(v_id, BinderInfo::Default, hcp.clone(), body))
            };
            wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), self.ssum(n, v_fn)))
        };
        let i1 = self.ssum(n, i1_w_fn.clone());
        // legA (i0=i1): subsetSum_congr over w of symm(smul n dens(x,w) dens_g_v_fn).
        let leg_a = {
            let h = {
                let mut wb = EnvDeclBuilder::child_of(parent);
                let (w_id, w) = wb.fresh_local(hcp.clone());
                let dxw = self.dens(rho, n, x, &w);
                let dg = self.dens_g_v_fn(&wb, rho, n, g, &w); // fun v => dens(w,v)·g v
                let dg_sum = self.ssum(n, dg.clone());
                // smul : Σ_v dxw·(dg v) = dxw·Σ_v dg v ; symm : dxw·Σ = Σ_v dxw·(dg v)
                let smul = self.ss_smul(n, &dxw, &dg);
                let lhs_w = self.mul(dxw.clone(), dg_sum.clone()); // dxw·(Σ_v dg v) = i0 body
                let pulled_fn = {
                    let mut vb = EnvDeclBuilder::child_of(&wb);
                    let (v_id, v) = vb.fresh_local(hcp.clone());
                    let body = self.mul(
                        dxw.clone(),
                        self.mul(self.dens(rho, n, &w, &v), Expr::app(g.clone(), v.clone())),
                    );
                    vb.finish_child(vb.mk_lam(v_id, BinderInfo::Default, hcp.clone(), body))
                };
                let rhs_w = self.ssum(n, pulled_fn);
                let pf = self.symm(rhs_w, lhs_w, smul);
                wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), pf))
            };
            self.ss_congr(n, &i0_fn, &i1_w_fn, h)
        };

        // i2 := Σ_v Σ_w dens(ρ,x,w)·(dens(ρ,w,v)·g v)   [swap w↔v].
        let swap_kernel = {
            let mut wb = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = wb.fresh_local(hcp.clone());
            let v_lam = {
                let mut vb = EnvDeclBuilder::child_of(&wb);
                let (v_id, v) = vb.fresh_local(hcp.clone());
                let body = self.mul(
                    self.dens(rho, n, x, &w),
                    self.mul(self.dens(rho, n, &w, &v), Expr::app(g.clone(), v.clone())),
                );
                vb.finish_child(vb.mk_lam(v_id, BinderInfo::Default, hcp.clone(), body))
            };
            wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), v_lam))
        };
        // subsetSum_swap n swap_kernel : Σ_w Σ_v K w v = Σ_v Σ_w K w v.
        let leg_b = self.ss_swap(n, &swap_kernel);
        let i2_v_fn = {
            let mut vb = EnvDeclBuilder::child_of(parent);
            let (v_id, v) = vb.fresh_local(hcp.clone());
            let w_fn = {
                let mut wb = EnvDeclBuilder::child_of(&vb);
                let (w_id, w) = wb.fresh_local(hcp.clone());
                let body = self.mul(
                    self.dens(rho, n, x, &w),
                    self.mul(self.dens(rho, n, &w, &v), Expr::app(g.clone(), v.clone())),
                );
                wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), body))
            };
            vb.finish_child(vb.mk_lam(v_id, BinderInfo::Default, hcp.clone(), self.ssum(n, w_fn)))
        };
        let i2 = self.ssum(n, i2_v_fn.clone());

        // i3 := Σ_v (Σ_w dens(x,w)·dens(w,v))·g v   [per-v iC: pull g v out, regroup].
        let i3_v_fn = {
            let mut vb = EnvDeclBuilder::child_of(parent);
            let (v_id, v) = vb.fresh_local(hcp.clone());
            let dd_sum = self.ssum(n, self.compose_w_fn(&vb, rho, n, x, &v));
            let body = self.mul(dd_sum, Expr::app(g.clone(), v.clone()));
            vb.finish_child(vb.mk_lam(v_id, BinderInfo::Default, hcp.clone(), body))
        };
        let i3 = self.ssum(n, i3_v_fn.clone());
        let leg_c = self.ss_congr(n, &i2_v_fn, &i3_v_fn, self.ic_per_v(parent, rho, n, g, x));

        // i4 := Σ_v (cube·dens(ρ²,x,v))·g v   [per-v iD: compose collapse].
        let i4_v_fn = {
            let mut vb = EnvDeclBuilder::child_of(parent);
            let (v_id, v) = vb.fresh_local(hcp.clone());
            let cd = self.mul(self.cube(n), self.dens(&rho_sq, n, x, &v));
            let body = self.mul(cd, Expr::app(g.clone(), v.clone()));
            vb.finish_child(vb.mk_lam(v_id, BinderInfo::Default, hcp.clone(), body))
        };
        let i4 = self.ssum(n, i4_v_fn.clone());
        let leg_d = {
            let h = {
                let mut vb = EnvDeclBuilder::child_of(parent);
                let (v_id, v) = vb.fresh_local(hcp.clone());
                let dd_sum = self.ssum(n, self.compose_w_fn(&vb, rho, n, x, &v));
                let cd = self.mul(self.cube(n), self.dens(&rho_sq, n, x, &v));
                let gv = Expr::app(g.clone(), v.clone());
                // compose : Σ_w dens(x,w)·dens(w,v) = cube·dens(ρ²,x,v).
                let comp = self.compose(rho, n, x, &v);
                let m = self.mul_left_motive(&vb, &gv); // fun z => z·g v
                let pf = self.congr(dd_sum, cd, m, comp);
                vb.finish_child(vb.mk_lam(v_id, BinderInfo::Default, hcp.clone(), pf))
            };
            self.ss_congr(n, &i3_v_fn, &i4_v_fn, h)
        };

        // i5 := Σ_v cube·(dens(ρ²,x,v)·g v)   [per-v iE step1: assoc].
        let i5_v_fn = {
            let mut vb = EnvDeclBuilder::child_of(parent);
            let (v_id, v) = vb.fresh_local(hcp.clone());
            let dg = self.mul(
                self.dens(&rho_sq, n, x, &v),
                Expr::app(g.clone(), v.clone()),
            );
            let body = self.mul(self.cube(n), dg);
            vb.finish_child(vb.mk_lam(v_id, BinderInfo::Default, hcp.clone(), body))
        };
        let i5 = self.ssum(n, i5_v_fn.clone());
        let leg_e = {
            let h = {
                let mut vb = EnvDeclBuilder::child_of(parent);
                let (v_id, v) = vb.fresh_local(hcp.clone());
                let cube = self.cube(n);
                let d = self.dens(&rho_sq, n, x, &v);
                let gv = Expr::app(g.clone(), v.clone());
                // mul_assoc cube d gv : (cube·d)·gv = cube·(d·gv).
                let pf = self.mul_assoc(&cube, &d, &gv);
                vb.finish_child(vb.mk_lam(v_id, BinderInfo::Default, hcp.clone(), pf))
            };
            self.ss_congr(n, &i4_v_fn, &i5_v_fn, h)
        };

        // i6 := cube·Σ_v dens(ρ²,x,v)·g v   [smul].
        let dg_sum_fn = self.dens_g_v_fn(parent, &rho_sq, n, g, x); // fun v => dens(ρ²,x,v)·g v
        let leg_f = self.ss_smul(n, &self.cube(n), &dg_sum_fn);
        let i6 = self.mul(
            self.cube(n),
            self.rhosq_dens_g_sum(parent, &rho_sq, n, g, x),
        );

        // chain i0 = i1 = i2 = i3 = i4 = i5 = i6.
        let t1 = self.trans(i0.clone(), i1.clone(), i2.clone(), leg_a, leg_b);
        let t2 = self.trans(i0.clone(), i2.clone(), i3.clone(), t1, leg_c);
        let t3 = self.trans(i0.clone(), i3.clone(), i4.clone(), t2, leg_d);
        let t4 = self.trans(i0.clone(), i4.clone(), i5.clone(), t3, leg_e);
        self.trans(i0, i5, i6, t4, leg_f)
    }

    /// The per-`v` hypothesis of `inner_x`'s legC:
    /// `Σ_w dens(ρ,x,w)·(dens(ρ,w,v)·g v) = (Σ_w dens(ρ,x,w)·dens(ρ,w,v))·g v`.
    fn ic_per_v(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let mut vb = EnvDeclBuilder::child_of(parent);
        let (v_id, v) = vb.fresh_local(hcp.clone());
        let gv = Expr::app(g.clone(), v.clone());

        // l0 := Σ_w dens(x,w)·(dens(w,v)·g v).
        let l0_fn = {
            let mut wb = EnvDeclBuilder::child_of(&vb);
            let (w_id, w) = wb.fresh_local(hcp.clone());
            let body = self.mul(
                self.dens(rho, n, x, &w),
                self.mul(self.dens(rho, n, &w, &v), gv.clone()),
            );
            wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), body))
        };
        let l0 = self.ssum(n, l0_fn.clone());

        // l1 := Σ_w (dens(x,w)·dens(w,v))·g v   [per-w symm(mul_assoc)].
        let l1_fn = {
            let mut wb = EnvDeclBuilder::child_of(&vb);
            let (w_id, w) = wb.fresh_local(hcp.clone());
            let dd = self.mul(self.dens(rho, n, x, &w), self.dens(rho, n, &w, &v));
            let body = self.mul(dd, gv.clone());
            wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), body))
        };
        let l1 = self.ssum(n, l1_fn.clone());
        let leg1 = {
            let h = {
                let mut wb = EnvDeclBuilder::child_of(&vb);
                let (w_id, w) = wb.fresh_local(hcp.clone());
                let dxw = self.dens(rho, n, x, &w);
                let dwv = self.dens(rho, n, &w, &v);
                // mul_assoc dxw dwv gv : (dxw·dwv)·gv = dxw·(dwv·gv) ; symm reverses.
                let assoc = self.mul_assoc(&dxw, &dwv, &gv);
                let lhs_w = self.mul(dxw.clone(), self.mul(dwv.clone(), gv.clone()));
                let rhs_w = self.mul(self.mul(dxw.clone(), dwv.clone()), gv.clone());
                let pf = self.symm(rhs_w, lhs_w, assoc);
                wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), pf))
            };
            self.ss_congr(n, &l0_fn, &l1_fn, h)
        };

        // l2 := Σ_w g v·(dens(x,w)·dens(w,v))   [per-w mul_comm].
        let l2_fn = {
            let mut wb = EnvDeclBuilder::child_of(&vb);
            let (w_id, w) = wb.fresh_local(hcp.clone());
            let dd = self.mul(self.dens(rho, n, x, &w), self.dens(rho, n, &w, &v));
            let body = self.mul(gv.clone(), dd);
            wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), body))
        };
        let l2 = self.ssum(n, l2_fn.clone());
        let leg2 = {
            let h = {
                let mut wb = EnvDeclBuilder::child_of(&vb);
                let (w_id, w) = wb.fresh_local(hcp.clone());
                let dd = self.mul(self.dens(rho, n, x, &w), self.dens(rho, n, &w, &v));
                let pf = self.mul_comm(&dd, &gv);
                wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), pf))
            };
            self.ss_congr(n, &l1_fn, &l2_fn, h)
        };

        // l3 := g v·(Σ_w dens(x,w)·dens(w,v))   [smul].
        let dd_fn = self.compose_w_fn(&vb, rho, n, x, &v);
        let leg3 = self.ss_smul(n, &gv, &dd_fn);
        let dd_sum = self.ssum(n, dd_fn.clone());
        let l3 = self.mul(gv.clone(), dd_sum.clone());

        // l4 := (Σ_w dens(x,w)·dens(w,v))·g v   [mul_comm].
        let l4 = self.mul(dd_sum.clone(), gv.clone());
        let leg4 = self.mul_comm(&gv, &dd_sum);

        let t1 = self.trans(l0.clone(), l1.clone(), l2.clone(), leg1, leg2);
        let t2 = self.trans(l0.clone(), l2.clone(), l3.clone(), t1, leg3);
        let pf = self.trans(l0, l3, l4, t2, leg4);

        vb.finish_child(vb.mk_lam(v_id, BinderInfo::Default, hcp, pf))
    }
}

/// `glue_value` — the proof of `W_self_adjoint_glue`.
/// `Σ_x g x·(T²g)(x) = cube·Σ_x Σ_v (g x·g v)·dens(ρ²,x,v)`.
fn glue_value(c: &WSpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fn_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(fn_ty.clone());
    let rho = c.third();
    let rho_sq = c.mul(rho.clone(), rho.clone());
    let hcp = c.hcpoint_of(&n);

    // E0 := Σ_x g x·(T²g)(x).
    let e0_fn = c.glue_lhs_x_fn(&b, &rho, &n, &g);
    let e0 = c.ssum(&n, e0_fn.clone());

    // E1 := Σ_x cube·(Σ_v (g x·g v)·dens(ρ²,x,v))   [per-x gMain].
    let e1_x_fn = {
        let mut xb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let inner_sum = c.ssum(&n, c.spec_v_fn(&xb, &rho_sq, &n, &g, &x));
        let body = c.mul(c.cube(&n), inner_sum);
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    let e1 = c.ssum(&n, e1_x_fn.clone());
    let leg_main = {
        let h = {
            let mut xb = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let pf = c.gmain_per_x(&xb, &rho, &n, &g, &x);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), pf))
        };
        c.ss_congr(&n, &e0_fn, &e1_x_fn, h)
    };

    // E2 := cube·Σ_x (Σ_v (g x·g v)·dens(ρ²,x,v))   [symm smul].
    // The inner x-sum integrand fun x => Σ_v (g x·g v)·dens(ρ²,x,v) is byte-for-byte
    // spec_lhs_x_fn, so cube·(Σ_x spec_lhs_x_fn) is def-eq to the target RHS.
    let spec_fn = c.spec_lhs_x_fn(&b, &rho_sq, &n, &g);
    let spec_sum = c.ssum(&n, spec_fn.clone());
    let e2 = c.mul(c.cube(&n), spec_sum.clone());
    // smul n cube spec_fn : Σ_x cube·(spec_fn x) = cube·Σ_x spec_fn x ; the LHS = E1.
    let leg_smul = c.ss_smul(&n, &c.cube(&n), &spec_fn);

    let proof = c.trans(e0, e1, e2, leg_main, leg_smul);
    let r = b.mk_lam(g_id, BinderInfo::Default, fn_ty, proof);
    let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

impl WSpectralConsts {
    /// `fun (v : HCPoint n) => (g x·g v)·dens(ρ²,x,v)` — the spec v-integrand at
    /// fixed x (byte-for-byte `spec_lhs_x_fn`'s inner body).
    fn spec_v_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho_sq: &Expr,
        n: &Expr,
        g: &Expr,
        x: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (v_id, v) = b.fresh_local(hcp.clone());
        let gx_gv = self.mul(
            Expr::app(g.clone(), x.clone()),
            Expr::app(g.clone(), v.clone()),
        );
        let body = self.mul(gx_gv, self.dens(rho_sq, n, x, &v));
        b.finish_child(b.mk_lam(v_id, BinderInfo::Default, hcp, body))
    }

    /// gMain per-`x`: `g x·(T²g)(x) = cube·Σ_v (g x·g v)·dens(ρ²,x,v)`.
    fn gmain_per_x(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        g: &Expr,
        x: &Expr,
    ) -> Expr {
        let rho_sq = self.mul(rho.clone(), rho.clone());
        let gx = Expr::app(g.clone(), x.clone());
        let cube = self.cube(n);

        // m0 := g x·(Σ_w dens(x,w)·(Σ_v dens(w,v)·g v))   [the T² body].
        let ttg = self.ssum(n, self.ttg_w_fn(parent, rho, n, g, x));
        let m0 = self.mul(gx.clone(), ttg.clone());

        // inner_x : ttg = cube·(Σ_v dens(ρ²,x,v)·g v).
        let dg_sum = self.rhosq_dens_g_sum(parent, &rho_sq, n, g, x); // Σ_v dens(ρ²,x,v)·g v
        let cube_dg = self.mul(cube.clone(), dg_sum.clone());
        let inner = self.inner_x(parent, rho, n, g, x);
        // m1 := g x·(cube·Σ_v dens(ρ²,x,v)·g v)   [congr (g x·) inner].
        let m_gx = self.mul_right_motive(parent, &gx);
        let leg_inner = self.congr(ttg, cube_dg.clone(), m_gx, inner);
        let m1 = self.mul(gx.clone(), cube_dg.clone());

        // m2 := (g x·cube)·Σ_v ...   [symm mul_assoc gx cube dg_sum].
        let assoc1 = self.mul_assoc(&gx, &cube, &dg_sum); // (gx·cube)·S = gx·(cube·S)
        let gx_cube = self.mul(gx.clone(), cube.clone());
        let m2 = self.mul(gx_cube.clone(), dg_sum.clone());
        let leg_a = self.symm(m2.clone(), m1.clone(), assoc1);

        // m3 := (cube·g x)·Σ_v ...   [congr-left mul_comm gx cube].
        let comm1 = self.mul_comm(&gx, &cube);
        let cube_gx = self.mul(cube.clone(), gx.clone());
        let m_left = self.mul_left_motive(parent, &dg_sum);
        let leg_b = self.congr(gx_cube.clone(), cube_gx.clone(), m_left, comm1);
        let m3 = self.mul(cube_gx.clone(), dg_sum.clone());

        // m4 := cube·(g x·Σ_v ...)   [mul_assoc cube gx dg_sum].
        let assoc2 = self.mul_assoc(&cube, &gx, &dg_sum);
        let gx_dg = self.mul(gx.clone(), dg_sum.clone());
        let m4 = self.mul(cube.clone(), gx_dg.clone());
        let leg_c = assoc2; // (cube·gx)·S = cube·(gx·S)

        // m5 := cube·(Σ_v g x·(dens(ρ²,x,v)·g v))   [congr (cube·) symm(smul gx dens_g)].
        let dens_g_fn = self.dens_g_v_fn(parent, &rho_sq, n, g, x); // fun v => dens(ρ²,x,v)·g v
        let smul_gx = self.ss_smul(n, &gx, &dens_g_fn); // Σ_v gx·(dg v) = gx·Σ_v dg v
        let pulled_fn = {
            let mut vb = EnvDeclBuilder::child_of(parent);
            let hcp = self.hcpoint_of(n);
            let (v_id, v) = vb.fresh_local(hcp.clone());
            let body = self.mul(
                gx.clone(),
                self.mul(
                    self.dens(&rho_sq, n, x, &v),
                    Expr::app(g.clone(), v.clone()),
                ),
            );
            vb.finish_child(vb.mk_lam(v_id, BinderInfo::Default, hcp, body))
        };
        let pulled_sum = self.ssum(n, pulled_fn.clone());
        let smul_sym = self.symm(pulled_sum.clone(), gx_dg.clone(), smul_gx);
        let m_cube = self.mul_right_motive(parent, &cube);
        let leg_d = self.congr(gx_dg.clone(), pulled_sum.clone(), m_cube, smul_sym);
        let m5 = self.mul(cube.clone(), pulled_sum.clone());

        // m6 := cube·(Σ_v (g x·g v)·dens(ρ²,x,v))   [congr (cube·) subsetSum_congr per-v].
        let spec_fn = self.spec_v_fn(parent, &rho_sq, n, g, x);
        let spec_sum = self.ssum(n, spec_fn.clone());
        let per_v = {
            let mut vb = EnvDeclBuilder::child_of(parent);
            let hcp = self.hcpoint_of(n);
            let (v_id, v) = vb.fresh_local(hcp.clone());
            let d = self.dens(&rho_sq, n, x, &v);
            let gv = Expr::app(g.clone(), v.clone());
            // gx·(d·gv) →[congr-right comm d gv] gx·(gv·d) →[symm assoc] (gx·gv)·d
            let comm_dgv = self.mul_comm(&d, &gv);
            let m_in = self.mul_right_motive(&vb, &gx);
            let s1 = self.congr(
                self.mul(d.clone(), gv.clone()),
                self.mul(gv.clone(), d.clone()),
                m_in,
                comm_dgv,
            );
            let mid = self.mul(gx.clone(), self.mul(gv.clone(), d.clone()));
            let assoc3 = self.mul_assoc(&gx, &gv, &d); // (gx·gv)·d = gx·(gv·d)
            let s2 = self.symm(
                self.mul(self.mul(gx.clone(), gv.clone()), d.clone()),
                mid.clone(),
                assoc3,
            );
            let from = self.mul(gx.clone(), self.mul(d.clone(), gv.clone()));
            let to = self.mul(self.mul(gx.clone(), gv.clone()), d.clone());
            let pf = self.trans(from, mid, to, s1, s2);
            vb.finish_child(vb.mk_lam(v_id, BinderInfo::Default, hcp, pf))
        };
        let ssc = self.ss_congr(n, &pulled_fn, &spec_fn, per_v);
        let m_cube2 = self.mul_right_motive(parent, &cube);
        let leg_e = self.congr(pulled_sum.clone(), spec_sum.clone(), m_cube2, ssc);
        let m6 = self.mul(cube.clone(), spec_sum.clone());

        // chain m0 = m1 = m2 = m3 = m4 = m5 = m6.
        let t1 = self.trans(m0.clone(), m1.clone(), m2.clone(), leg_inner, leg_a);
        let t2 = self.trans(m0.clone(), m2.clone(), m3.clone(), t1, leg_b);
        let t3 = self.trans(m0.clone(), m3.clone(), m4.clone(), t2, leg_c);
        let t4 = self.trans(m0.clone(), m4.clone(), m5.clone(), t3, leg_d);
        self.trans(m0, m5, m6, t4, leg_e)
    }
}
