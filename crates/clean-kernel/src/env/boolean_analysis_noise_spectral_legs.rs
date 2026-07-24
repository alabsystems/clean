// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_noise_spectral.rs — the `spectral_type` /
// `spectral_value` builders for `noise_spectral_core`. Split out only for the
// 500-line-per-file convention; not a standalone module.

// ── extra algebra combinators ────────────────────────────────────────────────

impl SpectralConsts {
    fn rat_mul_comm(&self) -> Expr {
        Expr::const_(Name::from_string("Rat.mul_comm"), vec![])
    }
    fn mul_comm(&self, a: Expr, bb: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm(), [a, bb])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        let eq_symm = Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        );
        Expr::apps(eq_symm, [self.rat.clone(), a, b, h])
    }
    /// `congrArg (fun z => left·z) h : left·a = left·bb` for `h : a = bb`.
    fn mul_left_congr(
        &self,
        parent: &EnvDeclBuilder,
        left: &Expr,
        a: Expr,
        bb: Expr,
        h: Expr,
    ) -> Expr {
        let g = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = b.fresh_local(self.rat.clone());
            let body = self.mul(left.clone(), z);
            b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr(a, bb, g, h)
    }
    /// `subsetSum_smul n cc f : subsetSum n (fun S => cc·(f S)) = cc·subsetSum n f`.
    fn ss_smul(&self, n: &Expr, cc: &Expr, f: &Expr) -> Expr {
        Expr::apps(
            self.subset_sum_smul.clone(),
            [n.clone(), cc.clone(), f.clone()],
        )
    }
    /// `subsetSum_congr n G H h : subsetSum n G = subsetSum n H`.
    fn ss_congr(&self, n: &Expr, g: &Expr, h: &Expr, hyp: Expr) -> Expr {
        Expr::apps(
            self.subset_sum_congr.clone(),
            [n.clone(), g.clone(), h.clone(), hyp],
        )
    }
    /// `subsetSum_swap n f : Σ_S Σ_x f S x = Σ_x Σ_S f S x` for
    /// `f : HCPoint n → HCPoint n → Rat`.
    fn ss_swap(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.subset_sum_swap.clone(), [n.clone(), f.clone()])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            [a, b, cc],
        )
    }
}

// ── statement endpoints (functions HCPoint→… for subsetSum) ──────────────────

impl SpectralConsts {
    /// `fun (x : HCPoint n) => a x · χ_S x` — inner integrand at fixed S.
    fn g_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.g(n, a, s, &x);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// RHS `S`-integrand `fun S => w_S·((Σ_x g_Sx)·(Σ_x g_Sx))`.
    fn rhs_s_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, a: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let inner = self.ssum(n, self.g_fn(&b, n, a, &s));
        let w = self.weight(&b, rho, n, &s);
        let body = self.mul(w, self.mul(inner.clone(), inner));
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// LHS `x`-integrand `fun x => Σ_y (a x·a y)·noiseDensityW ρ n x y`.
    fn lhs_x_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, a: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let y_sum = {
            let mut yb = EnvDeclBuilder::child_of(&xb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let ax_ay = self.mul(
                Expr::app(a.clone(), x.clone()),
                Expr::app(a.clone(), y.clone()),
            );
            let body = self.mul(ax_ay, self.noise_density(rho, n, &x, &y));
            let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, y_sum))
    }
}

fn spectral_type(c: &SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let a_ty = c.hcpoint_to_rat(&n);
    let (a_id, a) = b.fresh_local(a_ty.clone());
    let lhs = c.ssum(&n, c.lhs_x_fn(&b, &rho, &n, &a));
    let rhs = c.ssum(&n, c.rhs_s_fn(&b, &rho, &n, &a));
    let concl = c.eq_rat(lhs, rhs);
    let r = b.mk_pi(a_id, BinderInfo::Default, a_ty, concl);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), r);
    b.finish(r)
}

fn spectral_value(c: &SpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let a_ty = c.hcpoint_to_rat(&n);
    let (a_id, a) = b.fresh_local(a_ty.clone());
    let proof = spectral_chain(c, &b, &rho, &n, &a);
    let val = b.mk_lam(a_id, BinderInfo::Default, a_ty, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

include!("boolean_analysis_noise_spectral_chain.rs");
