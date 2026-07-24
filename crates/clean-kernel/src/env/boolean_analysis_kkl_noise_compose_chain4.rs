// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_kkl_noise_compose.rs — the OPERATOR semigroup
// `noiseOp_compose_third` (`T_{1/3} ∘ T_{1/3} = 2^n·T_{1/9}` applied to g), a
// Fubini wrapper around the kernel convolution `noiseDensityW_compose_third`.
// Split out only for the 500-line-per-file convention; not a standalone module.

impl ComposeConsts {
    /// `noiseOp ρ n g a` — the un-normalized noise operator applied to `g` at `a`,
    /// folded (`is_reducible`): `≡ subsetSum n (fun w => W_ρ(a,w)·g w)`.
    fn op(&self, rho: &Expr, n: &Expr, g: &Expr, a: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.noiseOp"), vec![]),
            [rho.clone(), n.clone(), g.clone(), a.clone()],
        )
    }

    /// F1 z-integrand `fun z => Σ_w W_{1/3}(x,z)·(W_{1/3}(z,w)·g w)` — after the
    /// per-z smul-in of `W_{1/3}(x,z)` into the inner `noiseOp(1/3)g` sum.
    fn f1_z_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        let mut zb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (z_id, z) = zb.fresh_local(hcp.clone());
        let inner = {
            let mut wb = EnvDeclBuilder::child_of(&zb);
            let (w_id, w) = wb.fresh_local(hcp.clone());
            let wzw_gw = self.mul(
                self.dens(&self.third(), n, &z, &w),
                Expr::app(g.clone(), w.clone()),
            );
            let body = self.mul(self.dens(&self.third(), n, x, &z), wzw_gw);
            wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), body))
        };
        let body = self.ssum(n, inner);
        zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp, body))
    }

    /// The op-swap kernel `fun z w => W_{1/3}(x,z)·(W_{1/3}(z,w)·g w)`.
    fn op_swap_kernel(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        let mut zb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (z_id, z) = zb.fresh_local(hcp.clone());
        let inner = {
            let mut wb = EnvDeclBuilder::child_of(&zb);
            let (w_id, w) = wb.fresh_local(hcp.clone());
            let wzw_gw = self.mul(
                self.dens(&self.third(), n, &z, &w),
                Expr::app(g.clone(), w.clone()),
            );
            let body = self.mul(self.dens(&self.third(), n, x, &z), wzw_gw);
            wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp.clone(), body))
        };
        zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp, inner))
    }

    /// F2 w-integrand `fun w => Σ_z W_{1/3}(x,z)·(W_{1/3}(z,w)·g w)` — swap kernel's
    /// outer slice (`subsetSum n (fun z => K z w)` at fixed w).
    fn f2_w_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        let mut wb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (w_id, w) = wb.fresh_local(hcp.clone());
        let inner = {
            let mut zb = EnvDeclBuilder::child_of(&wb);
            let (z_id, z) = zb.fresh_local(hcp.clone());
            let wzw_gw = self.mul(
                self.dens(&self.third(), n, &z, &w),
                Expr::app(g.clone(), w.clone()),
            );
            let body = self.mul(self.dens(&self.third(), n, x, &z), wzw_gw);
            zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
        };
        let body = self.ssum(n, inner);
        wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp, body))
    }

    /// `Σ_z W_{1/3}(x,z)·W_{1/3}(z,w)` — the convolution LHS at fixed `x,w` (the
    /// `noiseDensityW_compose_third` LHS integrand-sum).
    fn conv_zsum(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, w: &Expr) -> Expr {
        let mut zb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (z_id, z) = zb.fresh_local(hcp.clone());
        let body = self.mul(
            self.dens(&self.third(), n, x, &z),
            self.dens(&self.third(), n, &z, w),
        );
        let f = zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }

    /// F3 w-integrand `fun w => (Σ_z W_{1/3}(x,z)·W_{1/3}(z,w))·g w` — after the
    /// per-w reassoc + pull-out of `g w` from the z-sum.
    fn f3_w_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        let mut wb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (w_id, w) = wb.fresh_local(hcp.clone());
        let conv = self.conv_zsum(&wb, n, x, &w);
        let body = self.mul(conv, Expr::app(g.clone(), w.clone()));
        wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp, body))
    }

    /// F4 w-integrand `fun w => (cube·W_{1/9}(x,w))·g w` — after the convolution.
    fn f4_w_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        let mut wb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (w_id, w) = wb.fresh_local(hcp.clone());
        let conv = self.mul(self.cube(n), self.dens(&self.ninth(), n, x, &w));
        let body = self.mul(conv, Expr::app(g.clone(), w.clone()));
        wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp, body))
    }

    /// F5 w-integrand `fun w => cube·(W_{1/9}(x,w)·g w)` — after the per-w reassoc
    /// `(cube·W)·g = cube·(W·g)`.
    fn f5_w_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        let mut wb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (w_id, w) = wb.fresh_local(hcp.clone());
        let wg = self.mul(
            self.dens(&self.ninth(), n, x, &w),
            Expr::app(g.clone(), w.clone()),
        );
        let body = self.mul(self.cube(n), wg);
        wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp, body))
    }

    /// The inner integrand of F6's `cube·Σ_w(…)`: `fun w => W_{1/9}(x,w)·g w`
    /// (def-eq to `noiseOp(1/9) n g x`'s reducible body).
    fn f6_inner_w_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        let mut wb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (w_id, w) = wb.fresh_local(hcp.clone());
        let body = self.mul(
            self.dens(&self.ninth(), n, x, &w),
            Expr::app(g.clone(), w.clone()),
        );
        wb.finish_child(wb.mk_lam(w_id, BinderInfo::Default, hcp, body))
    }

    /// `noiseDensityW_compose_third n x w : Σ_z W_{1/3}(x,z)·W_{1/3}(z,w) =
    /// cube·W_{1/9}(x,w)` — the landed kernel convolution.
    fn conv_at(&self, n: &Expr, x: &Expr, w: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.noiseDensityW_compose_third"),
                vec![],
            ),
            [n.clone(), x.clone(), w.clone()],
        )
    }
}

include!("boolean_analysis_kkl_noise_compose_chain5.rs");
