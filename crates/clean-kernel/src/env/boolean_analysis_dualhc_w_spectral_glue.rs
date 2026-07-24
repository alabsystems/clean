// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_dualhc_w_spectral.rs — the type/value builders
// for `W_self_adjoint_glue` and `dualhc_W_eq_spectral`. Split out only for the
// 500-line-per-file convention; not a standalone module.

impl WSpectralConsts {
    // ── shared endpoint integrands ───────────────────────────────────────────

    /// `noise_spectral_level` LHS x-integrand `fun x => Σ_y (g x·g y)·dens(ρ²,x,y)`
    /// — byte-for-byte `LevelSplitConsts::lhs_x_fn` at `ρ→ρ` (density `ρ·ρ`).
    fn spec_lhs_x_fn(&self, parent: &EnvDeclBuilder, rho_sq: &Expr, n: &Expr, g: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let y_sum = {
            let mut yb = EnvDeclBuilder::child_of(&xb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let gx_gy = self.mul(
                Expr::app(g.clone(), x.clone()),
                Expr::app(g.clone(), y.clone()),
            );
            let body = self.mul(gx_gy, self.dens(rho_sq, n, &x, &y));
            let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, y_sum))
    }

    /// `noise_spectral_level` RHS S-integrand `fun S => levelWt ρ n S · (A·A)` —
    /// byte-for-byte `LevelSplitConsts::rhs_lvl_fn`.
    fn spec_rhs_s_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let w = self.level_wt(rho, n, &s);
        let inner = self.a_coeff(&b, n, g, &s);
        let body = self.mul(w, self.mul(inner.clone(), inner));
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }

    // ── glue LHS: Σ_x g x · (T² g)(x) ───────────────────────────────────────
    // `(T² g)(x) = noiseOp ρ n (noiseOp ρ n g) x` (reducible noiseOp):
    //   = Σ_w dens(ρ,x,w)·(noiseOp ρ n g)(w)
    //   = Σ_w dens(ρ,x,w)·(Σ_v dens(ρ,w,v)·g v).

    /// `fun (w : HCPoint n) => dens(ρ,x,w)·(Σ_v dens(ρ,w,v)·g v)` — the `(T²g)(x)`
    /// w-integrand (def-eq to `noiseOp ρ n (noiseOp ρ n g) x`'s body).
    fn ttg_w_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, x: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (w_id, w) = b.fresh_local(hcp.clone());
        let tgw = self.tg_v_sum(&b, rho, n, g, &w);
        let body = self.mul(self.dens(rho, n, x, &w), tgw);
        b.finish_child(b.mk_lam(w_id, BinderInfo::Default, hcp, body))
    }

    /// `Σ_v dens(ρ,w,v)·g v` — `(noiseOp ρ n g)(w)` (def-eq, reducible).
    fn tg_v_sum(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr, w: &Expr) -> Expr {
        let v_fn = {
            let mut vb = EnvDeclBuilder::child_of(parent);
            let hcp = self.hcpoint_of(n);
            let (v_id, v) = vb.fresh_local(hcp.clone());
            let body = self.mul(self.dens(rho, n, w, &v), Expr::app(g.clone(), v.clone()));
            vb.finish_child(vb.mk_lam(v_id, BinderInfo::Default, hcp, body))
        };
        self.ssum(n, v_fn)
    }

    /// glue LHS x-integrand `fun x => g x · (Σ_w dens(ρ,x,w)·(Σ_v dens(ρ,w,v)·g v))`.
    fn glue_lhs_x_fn(&self, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let wsum = self.ssum(n, self.ttg_w_fn(&b, rho, n, g, &x));
        let body = self.mul(Expr::app(g.clone(), x.clone()), wsum);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
}

include!("boolean_analysis_dualhc_w_spectral_glue2.rs");

/// `∀ n g, Σ_x g x·(T²g)(x) = cube · Σ_x Σ_v (g x·g v)·dens(ρ²,x,v)`  (ρ = third).
fn glue_type(c: &WSpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fn_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(fn_ty.clone());
    let rho = c.third();
    let rho_sq = c.mul(rho.clone(), rho.clone());

    let lhs = c.ssum(&n, c.glue_lhs_x_fn(&b, &rho, &n, &g));
    let rhs = c.mul(c.cube(&n), c.ssum(&n, c.spec_lhs_x_fn(&b, &rho_sq, &n, &g)));
    let concl = c.eq_rat(lhs, rhs);

    let r = b.mk_pi(g_id, BinderInfo::Default, fn_ty, concl);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

/// `∀ n g, Σ_y (T third g y)² = cube · Σ_S levelWt third n S · (A·A)`.
fn w_spectral_type(c: &WSpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fn_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(fn_ty.clone());
    let rho = c.third();

    // lhs := Σ_y (noiseOp third n g y)².
    let tg = c.op(&rho, &n, &g);
    let lhs_fn = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (y_id, y) = d.fresh_local(hcp.clone());
        let tgy = Expr::app(tg.clone(), y.clone());
        let body = c.mul(tgy.clone(), tgy);
        d.finish_child(d.mk_lam(y_id, BinderInfo::Default, hcp, body))
    };
    let lhs = c.ssum(&n, lhs_fn);
    let rhs = c.mul(c.cube(&n), c.ssum(&n, c.spec_rhs_s_fn(&b, &rho, &n, &g)));
    let concl = c.eq_rat(lhs, rhs);

    let r = b.mk_pi(g_id, BinderInfo::Default, fn_ty, concl);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

/// `dualhc_W_eq_spectral` proof value: `Eq.trans (Eq.trans sa glue) (congr (cube·) spec)`.
fn w_spectral_value(c: &WSpectralConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let fn_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(fn_ty.clone());
    let rho = c.third();
    let rho_sq = c.mul(rho.clone(), rho.clone());

    // Endpoints.
    let tg = c.op(&rho, &n, &g);
    let e_lhs = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (y_id, y) = d.fresh_local(hcp.clone());
        let tgy = Expr::app(tg.clone(), y.clone());
        let body = c.mul(tgy.clone(), tgy);
        let f = d.finish_child(d.mk_lam(y_id, BinderInfo::Default, hcp, body));
        c.ssum(&n, f)
    };
    let e_mid1 = c.ssum(&n, c.glue_lhs_x_fn(&b, &rho, &n, &g)); // Σ_x g x·(T²g)(x)
    let spec_lhs = c.ssum(&n, c.spec_lhs_x_fn(&b, &rho_sq, &n, &g)); // Σ_x Σ_v ...·dens(ρ²)
    let e_mid2 = c.mul(c.cube(&n), spec_lhs.clone()); // cube · spec_lhs
    let spec_rhs = c.ssum(&n, c.spec_rhs_s_fn(&b, &rho, &n, &g)); // Σ_S levelWt·(A·A)
    let e_rhs = c.mul(c.cube(&n), spec_rhs.clone());

    // sa : e_lhs = e_mid1   (noise_self_adjoint_sq ρ n g ; RHS def-eq to e_mid1).
    let sa = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.noise_self_adjoint_sq"),
            vec![],
        ),
        [rho.clone(), n.clone(), g.clone()],
    );
    // glue : e_mid1 = e_mid2   (W_self_adjoint_glue n g).
    let glue = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.W_self_adjoint_glue"),
            vec![],
        ),
        [n.clone(), g.clone()],
    );
    // spec : spec_lhs = spec_rhs   (noise_spectral_level ρ n g).
    let spec = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.noise_spectral_level"),
            vec![],
        ),
        [rho.clone(), n.clone(), g.clone()],
    );
    // spec_lift : cube·spec_lhs = cube·spec_rhs   (congrArg (cube·) spec).
    let m_cube = c.mul_right_motive(&b, &c.cube(&n));
    let spec_lift = c.congr(spec_lhs.clone(), spec_rhs.clone(), m_cube, spec);

    // chain: e_lhs = e_mid1 = e_mid2 = e_rhs.
    let t1 = c.trans(e_lhs.clone(), e_mid1.clone(), e_mid2.clone(), sa, glue);
    let proof = c.trans(e_lhs, e_mid2, e_rhs, t1, spec_lift);

    let r = b.mk_lam(g_id, BinderInfo::Default, fn_ty, proof);
    let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}
