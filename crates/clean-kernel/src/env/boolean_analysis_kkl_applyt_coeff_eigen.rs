// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_kkl_applyt_coeff.rs — the `eigen_type` /
// `eigen_value` builders for `noiseDensity_apply_chi_eigen` (the diagonal action
// of the noise kernel on a single decoded character). Split out only for the
// 500-line-per-file convention; not a standalone module.

// ── statement ────────────────────────────────────────────────────────────────

impl CoeffConsts {
    /// `fun (x : HCPoint n) => noiseDensityW ρ n x y · χ_S(x)` — the eigen-action
    /// `x`-integrand (`S := hcDecode n jS`).
    fn eigen_x_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        s: &Expr,
        y: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(self.density(rho, n, &x, y), self.chi_(n, s, &x));
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
}

fn eigen_type(c: &CoeffConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fin_p = c.fin_of(&c.pow2(&n));
    let (js_id, js) = b.fresh_local(fin_p.clone());
    let hcp = c.hcpoint_of(&n);
    let (y_id, y) = b.fresh_local(hcp.clone());
    let s = c.hc_decode(&n, &js);

    let lhs = c.ssum(&n, c.eigen_x_fn(&b, &rho, &n, &s, &y));
    // (2^n · ρ^{|S|}) · χ_S(y)
    let coeff = c.mul(c.cube(&n), c.pow(&rho, &c.set_size(&n, &s)));
    let rhs = c.mul(coeff, c.chi_(&n, &s, &y));
    let concl = c.eq_rat(lhs, rhs);

    let r = b.mk_pi(y_id, BinderInfo::Default, hcp, concl);
    let r = b.mk_pi(js_id, BinderInfo::Default, fin_p, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), r);
    b.finish(r)
}

// ── proof ────────────────────────────────────────────────────────────────────

impl CoeffConsts {
    /// `fun (T : HCPoint n) => ρ^{|T|}·(χ_T(x)·χ_T(y))` — the spectral summand of
    /// `noiseDensityW ρ n x y` (byte-for-byte its reducible body).
    fn w_summand_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        y: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (t_id, t) = b.fresh_local(hcp.clone());
        let body = self.mul(
            self.pow(rho, &self.set_size(n, &t)),
            self.mul(self.chi_(n, &t, x), self.chi_(n, &t, y)),
        );
        b.finish_child(b.mk_lam(t_id, BinderInfo::Default, hcp, body))
    }

    /// `fun x => Σ_T χ_S(x)·(ρ^{|T|}·(χ_T x·χ_T y))` — after legA (per-x smul-in).
    fn m1_x_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, s: &Expr, y: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let chi_sx = self.chi_(n, s, &x);
        let t_sum = {
            let mut tb = EnvDeclBuilder::child_of(&xb);
            let (t_id, t) = tb.fresh_local(hcp.clone());
            let w = self.mul(
                self.pow(rho, &self.set_size(n, &t)),
                self.mul(self.chi_(n, &t, &x), self.chi_(n, &t, y)),
            );
            let body = self.mul(chi_sx.clone(), w);
            let f = tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, t_sum))
    }

    /// `fun T => Σ_x χ_S(x)·(ρ^{|T|}·(χ_T x·χ_T y))` — after legB (swap x↔T).
    fn m2_t_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, s: &Expr, y: &Expr) -> Expr {
        let mut tb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (t_id, t) = tb.fresh_local(hcp.clone());
        let x_sum = {
            let mut xb = EnvDeclBuilder::child_of(&tb);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let w = self.mul(
                self.pow(rho, &self.set_size(n, &t)),
                self.mul(self.chi_(n, &t, &x), self.chi_(n, &t, y)),
            );
            let body = self.mul(self.chi_(n, s, &x), w);
            let f = xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp, x_sum))
    }

    /// `fun T => (ρ^{|T|}·χ_T(y))·(Σ_x χ_T(x)·χ_S(x))` — after legC (per-T factor).
    fn m3_t_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, s: &Expr, y: &Expr) -> Expr {
        let mut tb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (t_id, t) = tb.fresh_local(hcp.clone());
        let coeff = self.mul(self.pow(rho, &self.set_size(n, &t)), self.chi_(n, &t, y));
        let chi_chi = {
            let mut xb = EnvDeclBuilder::child_of(&tb);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let body = self.mul(self.chi_(n, &t, &x), self.chi_(n, s, &x));
            let f = xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        let body = self.mul(coeff, chi_chi);
        tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp, body))
    }

    /// `fun (x : HCPoint n) => χ_T(x)·χ_S(x)` — the inner orthogonality integrand
    /// (`S, T` fixed).
    fn chi_chi_fn(&self, parent: &EnvDeclBuilder, n: &Expr, t: &Expr, s: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.mul(self.chi_(n, t, &x), self.chi_(n, s, &x));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
}

include!("boolean_analysis_kkl_applyt_coeff_eigen_chain.rs");
