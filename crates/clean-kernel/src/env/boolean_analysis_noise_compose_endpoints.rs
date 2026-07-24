// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_noise_compose.rs — the endpoint integrand
// builders + the top-level `compose_type` for `noiseDensityW_compose`.
// Split out only for the 500-line-per-file convention; not a standalone module.

impl ComposeConsts {
    /// `K_{S,T}(x,z) := (wS·χ_S x)·(wT·χ_T z)` — the per-`(S,T)` coefficient,
    /// the y-independent head pulled out of the `y`-sum (legD). `parent` must be
    /// the binder context in which `s,t` live.
    fn k_coeff(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        z: &Expr,
        s: &Expr,
        t: &Expr,
    ) -> Expr {
        let ws = self.weight(parent, rho, n, s);
        let wt = self.weight(parent, rho, n, t);
        let left = self.mul(ws, self.chi_(n, s, x));
        let right = self.mul(wt, self.chi_(n, t, z));
        self.mul(left, right)
    }

    /// `χ_S y · χ_T y` — the y-dependent character pair (keystone integrand).
    fn chi_pair(&self, n: &Expr, s: &Expr, t: &Expr, y: &Expr) -> Expr {
        self.mul(self.chi_(n, s, y), self.chi_(n, t, y))
    }

    /// `densint_x(S,y) := wS·(χ_S x · χ_S y)` — byte-for-byte the `noiseDensityW`
    /// integrand of `dens(ρ,x,y)` at subset `S` (so `subsetSum n (fun S => this)`
    /// is def-eq to `noiseDensityW ρ n x y`).
    fn dens_int(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        y: &Expr,
        s: &Expr,
    ) -> Expr {
        let w = self.weight(parent, rho, n, s);
        let chis = self.mul(self.chi_(n, s, x), self.chi_(n, s, y));
        self.mul(w, chis)
    }
    /// `fun (S : HCPoint n) => densint_x(S,y)` — the `dens(ρ,x,y)` integrand fn.
    fn dens_int_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        y: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let body = self.dens_int(&b, rho, n, x, y, &s);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// The NATURAL double-sum summand `densint_x(S,y)·densint_z(T,y)` —
    /// `(wS·(χ_S x·χ_S y))·(wT·(χ_T y·χ_T z))`, exactly what `Fin.sum_mul_sum`
    /// produces (legA).
    fn nat_summand(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        z: &Expr,
        s: &Expr,
        t: &Expr,
        y: &Expr,
    ) -> Expr {
        let dx = self.dens_int(parent, rho, n, x, y, s);
        let dz = self.dens_int(parent, rho, n, y, z, t);
        self.mul(dx, dz)
    }

    // ── E0: the LHS y-integrand ──────────────────────────────────────────────
    /// `fun (y : HCPoint n) => dens(ρ,x,y)·dens(ρ,y,z)`.
    fn e0_y_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, x: &Expr, z: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = b.fresh_local(hcp.clone());
        let body = self.mul(
            self.noise_density(rho, n, x, &y),
            self.noise_density(rho, n, &y, z),
        );
        b.finish_child(b.mk_lam(y_id, BinderInfo::Default, hcp, body))
    }

    // ── E1: per-y, the product expanded to a NATURAL double S,T sum ──────────
    /// E1 y-integrand `fun y => Σ_S Σ_T densint_x(S,y)·densint_z(T,y)`.
    fn e1_y_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, x: &Expr, z: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = b.fresh_local(hcp.clone());
        let s_fn = {
            let mut sb = EnvDeclBuilder::child_of(&b);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let t_fn = {
                let mut tb = EnvDeclBuilder::child_of(&sb);
                let (t_id, t) = tb.fresh_local(hcp.clone());
                let body = self.nat_summand(&tb, rho, n, x, z, &s, &t, &y);
                tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), body))
            };
            let body = self.ssum(n, t_fn);
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };
        let body = self.ssum(n, s_fn);
        b.finish_child(b.mk_lam(y_id, BinderInfo::Default, hcp, body))
    }

    // ── E2: S outer (swap y↔S): fun S => Σ_y Σ_T natural ─────────────────────
    /// E2 S-integrand `fun S => Σ_y Σ_T densint_x(S,y)·densint_z(T,y)`.
    fn e2_s_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, x: &Expr, z: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let y_fn = {
            let mut yb = EnvDeclBuilder::child_of(&b);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let t_fn = {
                let mut tb = EnvDeclBuilder::child_of(&yb);
                let (t_id, t) = tb.fresh_local(hcp.clone());
                let body = self.nat_summand(&tb, rho, n, x, z, &s, &t, &y);
                tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), body))
            };
            let body = self.ssum(n, t_fn);
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
        };
        let body = self.ssum(n, y_fn);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    // ── E3: per S, T outer (swap y↔T): fun S => Σ_T Σ_y natural ──────────────
    /// E3 S-integrand `fun S => Σ_T Σ_y densint_x(S,y)·densint_z(T,y)`.
    fn e3_s_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, x: &Expr, z: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let t_fn = {
            let mut tb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = tb.fresh_local(hcp.clone());
            let y_fn = {
                let mut yb = EnvDeclBuilder::child_of(&tb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let body = self.nat_summand(&yb, rho, n, x, z, &s, &t, &y);
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
            };
            let body = self.ssum(n, y_fn);
            tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), body))
        };
        let body = self.ssum(n, t_fn);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    // ── E4: per S, Σ_T K_{S,T}·(Σ_y χ_S y · χ_T y) ───────────────────────────
    /// `fun (y : HCPoint n) => χ_S y · χ_T y` — keystone y-sum integrand.
    fn chi_pair_y_fn(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = b.fresh_local(hcp.clone());
        let body = self.chi_pair(n, s, t, &y);
        b.finish_child(b.mk_lam(y_id, BinderInfo::Default, hcp, body))
    }
    /// E4 S-integrand `fun S => Σ_T K_{S,T}·(Σ_y χ_S y · χ_T y)`.
    fn e4_s_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, x: &Expr, z: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let t_fn = {
            let mut tb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = tb.fresh_local(hcp.clone());
            let kk = self.k_coeff(&tb, rho, n, x, z, &s, &t);
            let ysum = self.ssum(n, self.chi_pair_y_fn(&tb, n, &s, &t));
            let body = self.mul(kk, ysum);
            tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), body))
        };
        let body = self.ssum(n, t_fn);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    // ── E5: per S, Σ_T K_{S,T}·(cube·[SΔT=∅]) — keystone applied ─────────────
    /// `S Δ T` integrand `fun i => Bool.xor (S i) (T i)` (matches keystone).
    fn symm_diff_fn(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = Expr::apps(
            self.bool_xor.clone(),
            [Expr::app(s.clone(), i.clone()), Expr::app(t.clone(), i)],
        );
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `ind (Nat.beq (setSizeNat n (S Δ T)) 0)` — empty-set indicator.
    fn empty_ind(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        let sd = self.symm_diff_fn(parent, n, s, t);
        let ss = Expr::apps(self.set_size_nat.clone(), [n.clone(), sd]);
        let beq = Expr::apps(self.nat_beq.clone(), [ss, self.nat_zero.clone()]);
        Expr::app(self.ind.clone(), beq)
    }
    /// E5 S-integrand `fun S => Σ_T K_{S,T}·(cube·ind[SΔT=∅])`.
    fn e5_s_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, x: &Expr, z: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let body = self.ssum(n, self.e5_t_fn(&b, rho, n, x, z, &s));
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun T => K_{S,T}·(cube·ind[SΔT=∅])` — the E5 T-integrand at fixed `S`.
    fn e5_t_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        z: &Expr,
        s: &Expr,
    ) -> Expr {
        let mut tb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (t_id, t) = tb.fresh_local(hcp.clone());
        let kk = self.k_coeff(&tb, rho, n, x, z, s, &t);
        let diag = self.mul(self.cube(n), self.empty_ind(&tb, n, s, &t));
        let body = self.mul(kk, diag);
        tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp, body))
    }

    // ── E6: per S, cube·K_{S,S} — T-extraction done ──────────────────────────
    /// E6 S-integrand `fun S => cube · K_{S,S}(x,z)`.
    fn e6_s_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, x: &Expr, z: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let kk = self.k_coeff(&b, rho, n, x, z, &s, &s);
        let body = self.mul(self.cube(n), kk);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    // ── E7: per S, cube·((ρ·ρ)^{|S|}·(χ_S x·χ_S z)) — power folded ───────────
    /// The diagonal-folded summand `(ρ·ρ)^{|S|}·(χ_S x · χ_S z)` (the
    /// `noiseDensityW (ρ·ρ)` integrand byte-for-byte).
    fn rhosq_int(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        z: &Expr,
        s: &Expr,
    ) -> Expr {
        let rho_sq = self.mul(rho.clone(), rho.clone());
        let w = self.pow(&rho_sq, &self.popcount(parent, n, s));
        let chis = self.mul(self.chi_(n, s, x), self.chi_(n, s, z));
        self.mul(w, chis)
    }
    /// E7 S-integrand `fun S => cube · ((ρ·ρ)^{|S|}·(χ_S x · χ_S z))`.
    fn e7_s_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, x: &Expr, z: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let body = self.mul(self.cube(n), self.rhosq_int(&b, rho, n, x, z, &s));
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    /// The bare `noiseDensityW (ρ·ρ)` S-integrand `fun S => (ρ·ρ)^{|S|}·(χ_S x·χ_S z)`
    /// — `subsetSum n (this)` is def-eq (reducible δ) to `noiseDensityW (ρ·ρ) n x z`.
    fn rhosq_int_fn(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        x: &Expr,
        z: &Expr,
    ) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let body = self.rhosq_int(&b, rho, n, x, z, &s);
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

/// `∀ (ρ : Rat) (n : Nat) (x z : HCPoint n),
///   subsetSum n (fun y => dens(ρ,x,y)·dens(ρ,y,z)) = cube n · dens(ρ², n, x, z)`.
fn compose_type(c: &ComposeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (z_id, z) = b.fresh_local(hcp.clone());

    let lhs = c.ssum(&n, c.e0_y_fn(&b, &rho, &n, &x, &z));
    let rho_sq = c.mul(rho.clone(), rho.clone());
    let rhs = c.mul(c.cube(&n), c.noise_density(&rho_sq, &n, &x, &z));
    let concl = c.eq_rat(lhs, rhs);

    let r = b.mk_pi(z_id, BinderInfo::Default, hcp.clone(), concl);
    let r = b.mk_pi(x_id, BinderInfo::Default, hcp, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), r);
    b.finish(r)
}
