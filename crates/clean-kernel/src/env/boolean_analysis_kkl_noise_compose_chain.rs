// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_kkl_noise_compose.rs — the endpoint integrands,
// leg proofs, and top-level `compose_type` / `compose_value` for
// `noiseDensityW_compose_third`. Split out only for the 500-line-per-file
// convention; not a standalone module.

// ── statement endpoints (the `fun … => …` integrands `subsetSum n` consumes) ──

impl ComposeConsts {
    /// `1/3` literal — the noise parameter throughout.
    fn third(&self) -> Expr {
        self.one_over(3)
    }
    /// `1/9` literal — the composed parameter.
    fn ninth(&self) -> Expr {
        self.one_over(9)
    }

    /// `fun (S : HCPoint n) => (1/3)^{|S|}·(χ_S a·χ_S b)` — the reducible body of
    /// `noiseDensityW (1/3) n a b` (byte-for-byte: weight `powNat (1/3) (setSizeNat
    /// n S)`, body `χ_S a·χ_S b`). `subsetSum n (this)` is def-eq to `W_{1/3}(a,b)`.
    fn w3_body_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, b: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let w = self.pow(&self.third(), &self.set_size(n, &s));
        let body = self.mul(w, self.mul(self.chi_(n, &s, a), self.chi_(n, &s, b)));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// `fun (S : HCPoint n) => (1/9)^{|S|}·(χ_S a·χ_S b)` — the reducible body of
    /// `noiseDensityW (1/9) n a b`.
    fn w9_body_fn(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, b: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let w = self.pow(&self.ninth(), &self.set_size(n, &s));
        let body = self.mul(w, self.mul(self.chi_(n, &s, a), self.chi_(n, &s, b)));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// `g3 S z := (1/3)^{|S|}·(χ_S x·χ_S z)` — the S-summand of `W_{1/3}(x,z)` at
    /// fixed pivot `x`, as a function of the spectral index `S` and vertex `z`.
    fn g3(&self, n: &Expr, x: &Expr, s: &Expr, z: &Expr) -> Expr {
        let w = self.pow(&self.third(), &self.set_size(n, s));
        self.mul(w, self.mul(self.chi_(n, s, x), self.chi_(n, s, z)))
    }

    /// E0 z-integrand `fun z => (Σ_S g3 S z)·W_{1/3}(z,y)` — the LHS with the FIRST
    /// density `noiseDensityW (1/3) n x z` δ-unfolded to its S-sum. Def-eq to the
    /// stated LHS integrand `fun z => W_{1/3}(x,z)·W_{1/3}(z,y)`.
    fn e0_z_fn(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let mut zb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (z_id, z) = zb.fresh_local(hcp.clone());
        let s_sum = self.ssum(n, self.w3_body_fn(&zb, n, x, &z));
        let body = self.mul(s_sum, self.dens(&self.third(), n, &z, y));
        zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp, body))
    }

    /// E1 z-integrand `fun z => Σ_S (g3 S z·W_{1/3}(z,y))` — after pulling the
    /// per-z factor `W_{1/3}(z,y)` into the S-sum.
    fn e1_z_fn(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let mut zb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (z_id, z) = zb.fresh_local(hcp.clone());
        let inner = {
            let mut sb = EnvDeclBuilder::child_of(&zb);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let body = self.mul(self.g3(n, x, &s, &z), self.dens(&self.third(), n, &z, y));
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };
        let body = self.ssum(n, inner);
        zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp, body))
    }

    /// The swap kernel `fun S z => g3 S z·W_{1/3}(z,y)` (HCPoint→HCPoint→Rat) —
    /// the body `subsetSum_swap` reorders. `subsetSum n (fun z => subsetSum n
    /// (fun S => K S z))` is the E1 endpoint; the swapped `subsetSum n (fun S =>
    /// subsetSum n (fun z => K S z))` is the E2 endpoint.
    fn swap_kernel(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let inner = {
            let mut zb = EnvDeclBuilder::child_of(&sb);
            let (z_id, z) = zb.fresh_local(hcp.clone());
            let body = self.mul(self.g3(n, x, &s, &z), self.dens(&self.third(), n, &z, y));
            zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
        };
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, inner))
    }

    /// E2 S-integrand `fun S => Σ_z (g3 S z·W_{1/3}(z,y))` — the swap kernel's
    /// outer slice (`subsetSum n (fun z => K S z)` at fixed S).
    fn e2_s_fn(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let inner = {
            let mut zb = EnvDeclBuilder::child_of(&sb);
            let (z_id, z) = zb.fresh_local(hcp.clone());
            let body = self.mul(self.g3(n, x, &s, &z), self.dens(&self.third(), n, &z, y));
            zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
        };
        let body = self.ssum(n, inner);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// E3 S-integrand `fun S => ((1/3)^{|S|}·χ_S x)·(Σ_z χ_S(z)·W_{1/3}(z,y))` —
    /// after factoring the z-constant `(1/3)^{|S|}·χ_S x` out of the z-sum so the
    /// residual z-sum is exactly the eigen lemma's LHS at base point `y`.
    fn e3_s_fn(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let coeff = self.mul(
            self.pow(&self.third(), &self.set_size(n, &s)),
            self.chi_(n, &s, x),
        );
        let body = self.mul(coeff, self.eigen_zsum(&sb, n, &s, y));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// `Σ_z χ_S(z)·W_{1/3}(z,y)` — the eigen lemma's LHS integrand-sum, with the
    /// product written `χ_S(z)·W_{1/3}(z,y)` (i.e. the residual after factoring out
    /// `(1/3)^{|S|}·χ_S x`).
    fn eigen_zsum(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, y: &Expr) -> Expr {
        let mut zb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (z_id, z) = zb.fresh_local(hcp.clone());
        let body = self.mul(self.chi_(n, s, &z), self.dens(&self.third(), n, &z, y));
        let f = zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }

    /// The eigen lemma's NATIVE z-integrand `fun z => W_{1/3}(z,y)·χ_S(z)` (the
    /// product in the order the landed `noiseDensity_apply_chi_eigen` spells it).
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn eigen_native_zsum(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, y: &Expr) -> Expr {
        let mut zb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (z_id, z) = zb.fresh_local(hcp.clone());
        let body = self.mul(self.dens(&self.third(), n, &z, y), self.chi_(n, s, &z));
        let f = zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }

    /// E4 S-integrand `fun S => ((1/3)^{|S|}·χ_S x)·((cube·(1/3)^{|S|})·χ_S y)` —
    /// after the eigen collapse of the z-sum.
    fn e4_s_fn(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let pw = self.pow(&self.third(), &self.set_size(n, &s));
        let coeff = self.mul(pw.clone(), self.chi_(n, &s, x));
        let eig = self.mul(self.mul(self.cube(n), pw), self.chi_(n, &s, y));
        let body = self.mul(coeff, eig);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// E5 S-integrand `fun S => cube·(((1/3)^{|S|}·(1/3)^{|S|})·(χ_S x·χ_S y))` —
    /// after regrouping E4's six factors into `cube·(w²·(χ·χ))` (the `subsetSum_smul`
    /// scaled form with the squared per-level weight).
    fn e5_s_fn(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let pw = self.pow(&self.third(), &self.set_size(n, &s));
        let wsq = self.mul(pw.clone(), pw);
        let chis = self.mul(self.chi_(n, &s, x), self.chi_(n, &s, y));
        let body = self.mul(self.cube(n), self.mul(wsq, chis));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// E6/E7 inner S-integrand for the `cube·(…)` factor: `fun S =>
    /// ((1/3)^{|S|}·(1/3)^{|S|})·(χ_S x·χ_S y)` — the body inside `cube·Σ_S(…)`
    /// after `subsetSum_smul`, BEFORE the per-S semigroup rewrite.
    fn e6_inner_s_fn(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let pw = self.pow(&self.third(), &self.set_size(n, &s));
        let wsq = self.mul(pw.clone(), pw);
        let chis = self.mul(self.chi_(n, &s, x), self.chi_(n, &s, y));
        let body = self.mul(wsq, chis);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

// ── top-level type ────────────────────────────────────────────────────────────

/// `∀ (n : Nat) (x y : HCPoint n),
///    subsetSum n (fun z => W_{1/3}(x,z)·W_{1/3}(z,y)) = cube n · W_{1/9}(x,y)`.
fn compose_type(c: &ComposeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (y_id, y) = b.fresh_local(hcp.clone());

    // LHS z-integrand: fun z => W_{1/3}(x,z)·W_{1/3}(z,y)  (FOLDED densities).
    let lhs_fn = {
        let mut zb = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = zb.fresh_local(hcp.clone());
        let body = c.mul(
            c.dens(&c.third(), &n, &x, &z),
            c.dens(&c.third(), &n, &z, &y),
        );
        zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
    };
    let lhs = c.ssum(&n, lhs_fn);
    let rhs = c.mul(c.cube(&n), c.dens(&c.ninth(), &n, &x, &y));
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(y_id, BinderInfo::Default, hcp.clone(), concl);
    let e = b.mk_pi(x_id, BinderInfo::Default, hcp, e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

include!("boolean_analysis_kkl_noise_compose_chain2.rs");
