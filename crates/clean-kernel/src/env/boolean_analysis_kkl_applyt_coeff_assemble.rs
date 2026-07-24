// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_kkl_applyt_coeff.rs — the `coeff_type` /
// `coeff_value` builders for `applyT_coeff_eq` (the applyT-coefficient
// orthogonality identity, assembled from the eigen-action).

// ── statement ────────────────────────────────────────────────────────────────

impl CoeffConsts {
    /// `fun (x : HCPoint n) => applyT ρ n g x · χ_S(x)` — the coefficient
    /// `A_{applyT(ρ)g}(S)` integrand (`S := hcDecode n jS`).
    fn coeff_x_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        g: &Expr,
        s: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(self.applyt(rho, n, g, &x), self.chi_(n, s, &x));
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (x : HCPoint n) => g x · χ_S(x)` — the coefficient `A_g(S)` integrand.
    fn ag_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(g.clone(), x.clone()), self.chi_(n, s, &x));
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
}

fn coeff_type(c: &CoeffConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let fin_p = c.fin_of(&c.pow2(&n));
    let (js_id, js) = b.fresh_local(fin_p.clone());
    let s = c.hc_decode(&n, &js);

    let lhs = c.ssum(&n, c.coeff_x_fn(&b, &rho, &n, &g, &s)); // A_{applyT(ρ)g}(S)
    let coeff = c.mul(c.cube(&n), c.pow(&rho, &c.set_size(&n, &s))); // 2^n·ρ^{|S|}
    let rhs = c.mul(coeff, c.ssum(&n, c.ag_fn(&b, &n, &g, &s))); // (2^n·ρ^{|S|})·A_g(S)
    let concl = c.eq_rat(lhs, rhs);

    let r = b.mk_pi(js_id, BinderInfo::Default, fin_p, concl);
    let r = b.mk_pi(g_id, BinderInfo::Default, g_ty, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), r);
    b.finish(r)
}

// ── proof ────────────────────────────────────────────────────────────────────

impl CoeffConsts {
    /// `fun x => (Σ_y g y·W(ρ,x,y))·χ_S(x)` — the coefficient integrand with
    /// `applyT` δ-unfolded (def-eq to `coeff_x_fn`).
    fn a0_x_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let y_sum = {
            let mut yb = EnvDeclBuilder::child_of(&xb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let body = self.mul(
                Expr::app(g.clone(), y.clone()),
                self.density(rho, n, &x, &y),
            );
            let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        let body = self.mul(y_sum, self.chi_(n, s, &x));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun x => Σ_y χ_S(x)·(g y·W(ρ,x,y))` — after legA (per-x smul-in).
    fn a1_x_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let chi_sx = self.chi_(n, s, &x);
        let y_sum = {
            let mut yb = EnvDeclBuilder::child_of(&xb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let gw = self.mul(
                Expr::app(g.clone(), y.clone()),
                self.density(rho, n, &x, &y),
            );
            let body = self.mul(chi_sx.clone(), gw);
            let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, y_sum))
    }
    /// `fun y => Σ_x χ_S(x)·(g y·W(ρ,x,y))` — after legB (swap x↔y).
    fn a2_y_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let x_sum = {
            let mut xb = EnvDeclBuilder::child_of(&yb);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let gw = self.mul(
                Expr::app(g.clone(), y.clone()),
                self.density(rho, n, &x, &y),
            );
            let body = self.mul(self.chi_(n, s, &x), gw);
            let f = xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, x_sum))
    }
    /// `fun y => g y·(Σ_x W(ρ,x,y)·χ_S(x))` — after legC (per-y factor).
    fn a3_y_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let inner = self.ssum(n, self.coeff_eigen_x_fn(&yb, rho, n, s, &y));
        let body = self.mul(Expr::app(g.clone(), y.clone()), inner);
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, body))
    }
    /// `fun x => W(ρ,x,y)·χ_S(x)` — the eigen-action LHS integrand (= `eigen_x_fn`).
    fn coeff_eigen_x_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        s: &Expr,
        y: &Expr,
    ) -> Expr {
        self.eigen_x_fn(parent, rho, n, s, y)
    }
    /// `fun y => g y·((2^n·ρ^{|S|})·χ_S(y))` — after legD (eigen-action per y).
    fn a4_y_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let coeff = self.mul(self.cube(n), self.pow(rho, &self.set_size(n, s)));
        let body = self.mul(
            Expr::app(g.clone(), y.clone()),
            self.mul(coeff, self.chi_(n, s, &y)),
        );
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, body))
    }
    /// `fun y => (2^n·ρ^{|S|})·(g y·χ_S(y))` — after legE (per-y reassoc).
    fn a5_y_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let coeff = self.mul(self.cube(n), self.pow(rho, &self.set_size(n, s)));
        let body = self.mul(
            coeff,
            self.mul(Expr::app(g.clone(), y.clone()), self.chi_(n, s, &y)),
        );
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, body))
    }
}

include!("boolean_analysis_kkl_applyt_coeff_assemble_chain.rs");
