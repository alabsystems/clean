// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_noise_spectral_legs.rs — the leg proofs and the
// top-level `spectral_chain` for `noise_spectral_core`.

impl SpectralConsts {
    // ── intermediate endpoint integrands (subsetSum n of these) ──────────────

    /// E0u x-integrand `fun x => Σ_y (a x·a y)·(Σ_S w_S·(χ_Sx·χ_Sy))`.
    fn e0_x_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, a: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.e0_y_sum(&xb, rho, n, a, &x);
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `Σ_y (a x·a y)·(Σ_S w_S·(χ_Sx·χ_Sy))` at fixed x.
    fn e0_y_sum(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, a: &Expr, x: &Expr) -> Expr {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let ax_ay = self.mul(
            Expr::app(a.clone(), x.clone()),
            Expr::app(a.clone(), y.clone()),
        );
        let chi_sum = self.ssum(n, self.wchi_fn(&yb, rho, n, x, &y));
        let body = self.mul(ax_ay, chi_sum);
        let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }
    /// `fun S => w_S·(χ_Sx·χ_Sy)` — the noiseDensityW summand at fixed x,y.
    fn wchi_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let w = self.weight(&sb, rho, n, &s);
        let body = self.mul(w, self.mul(self.chi_(n, &s, x), self.chi_(n, &s, y)));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun S => w_S·(g_Sx·g_Sy)` — the weighted Fourier-product summand at x,y.
    fn wg_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        a: &Expr,
        x: &Expr,
        y: &Expr,
    ) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let w = self.weight(&sb, rho, n, &s);
        let body = self.mul(w, self.mul(self.g(n, a, &s, x), self.g(n, a, &s, y)));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// E1 x-integrand `fun x => Σ_y Σ_S w_S·(g_Sx·g_Sy)`.
    fn e1_x_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, a: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let y_sum = {
            let mut yb = EnvDeclBuilder::child_of(&xb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let s_sum = self.ssum(n, self.wg_fn(&yb, rho, n, a, &x, &y));
            let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), s_sum));
            self.ssum(n, f)
        };
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, y_sum))
    }
    /// E2 x-integrand `fun x => Σ_S Σ_y w_S·(g_Sx·g_Sy)`.
    fn e2_x_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, a: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let s_sum = {
            let mut sb = EnvDeclBuilder::child_of(&xb);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let y_sum = self.wg_ysum_fixed_sx(&sb, rho, n, a, &s, &x);
            let f = sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), y_sum));
            self.ssum(n, f)
        };
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, s_sum))
    }
    /// `Σ_y w_S·(g_Sx·g_Sy)` at fixed S,x (the swap kernel inner sum).
    fn wg_ysum_fixed_sx(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        a: &Expr,
        s: &Expr,
        x: &Expr,
    ) -> Expr {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let w = self.weight(&yb, rho, n, s);
        let body = self.mul(w, self.mul(self.g(n, a, s, x), self.g(n, a, s, &y)));
        let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }
    /// E3 S-integrand `fun S => Σ_x Σ_y w_S·(g_Sx·g_Sy)`.
    fn e3_s_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, a: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let x_sum = {
            let mut xb = EnvDeclBuilder::child_of(&sb);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let y_sum = self.wg_ysum_fixed_sx(&xb, rho, n, a, &s, &x);
            let f = xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), y_sum));
            self.ssum(n, f)
        };
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, x_sum))
    }
    /// E4 S-integrand `fun S => w_S·(Σ_x Σ_y g_Sx·g_Sy)`.
    fn e4_s_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, a: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let w = self.weight(&sb, rho, n, &s);
        let dbl = self.dbl_xy(&sb, n, a, &s);
        let body = self.mul(w, dbl);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `Σ_x Σ_y g_Sx·g_Sy` at fixed S.
    fn dbl_xy(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, s: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let y_sum = {
            let mut yb = EnvDeclBuilder::child_of(&xb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let body = self.mul(self.g(n, a, s, &x), self.g(n, a, s, &y));
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };
        let f = xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, self.ssum(n, y_sum)));
        self.ssum(n, f)
    }
    /// `Σ_y g_Sx·g_Sy` at fixed S,x — the inner sum of `dbl_xy`.
    fn inner_y_g(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, s: &Expr, x: &Expr) -> Expr {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let body = self.mul(self.g(n, a, s, x), self.g(n, a, s, &y));
        let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }

    /// The swap kernel `fun S x => Σ_y w_S·(g_Sx·g_Sy)` (HCPoint→HCPoint→Rat).
    fn swap_kernel(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, a: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let inner = {
            let mut xb = EnvDeclBuilder::child_of(&sb);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let y_sum = self.wg_ysum_fixed_sx(&xb, rho, n, a, &s, &x);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), y_sum))
        };
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, inner))
    }
}

include!("boolean_analysis_noise_spectral_chain2.rs");
