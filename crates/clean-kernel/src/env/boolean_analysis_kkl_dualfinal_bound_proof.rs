// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_kkl_dualfinal_bound.rs — the `bound_type` /
// `bound_value` builders for `applyT_two_norm_sq_spectral`.

// ── statement ────────────────────────────────────────────────────────────────

fn bound_type(c: &BoundConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());

    let lhs = c.mul(c.cube(&n), c.ssum(&n, c.applyt_sq_fn(&b, &rho, &n, &g)));
    let rhs = c.ssum(&n, c.rhs_s_fn(&b, &rho, &n, &g));
    let concl = c.eq_rat(lhs, rhs);

    let r = b.mk_pi(g_id, BinderInfo::Default, g_ty, concl);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    let r = b.mk_pi(rho_id, BinderInfo::Default, c.rat.clone(), r);
    b.finish(r)
}

// ── proof ────────────────────────────────────────────────────────────────────

impl BoundConsts {
    /// `fun (jS : Fin (2^n)) => G (hcDecode n jS)` — the `subsetSum`↔`Fin.sum`
    /// decoded integrand for an `HCPoint n → Rat` summand `G`.
    fn dec_index(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_p = self.fin_of(&self.pow2(n));
        let (j_id, j) = b.fresh_local(fin_p.clone());
        let body = Expr::app(g.clone(), self.hc_decode(n, &j));
        b.finish_child(b.mk_lam(j_id, BinderInfo::Default, fin_p, body))
    }

    /// `congrArg (fun z => z·z) h : a·a = bb·bb` for `h : a = bb`.
    fn square_congr(&self, parent: &EnvDeclBuilder, a: Expr, bb: Expr, h: Expr) -> Expr {
        let sq_fn = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = b.fresh_local(self.rat.clone());
            let body = self.mul(z.clone(), z);
            b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, bb, sq_fn, h],
        )
    }
}

fn bound_value(c: &BoundConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());

    let applyt_g = {
        // `applyT ρ n g : HCPoint n → Rat`  (the materialized operator value).
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = c.applyt(&rho, &n, &g, &x);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    };

    // lhs := 2^n · Σ_x sq(applyT ρ n g x).
    let lhs = c.mul(c.cube(&n), c.ssum(&n, c.applyt_sq_fn(&b, &rho, &n, &g)));
    // mid := Σ_S A_{applyT g}(S)²  (Parseval LHS at a := applyT ρ n g).
    let mid = c.ssum(&n, c.mid_s_fn(&b, &rho, &n, &g));
    // rhs := Σ_S (2^n·ρ^{|S|}·A_g(S))².
    let rhs = c.ssum(&n, c.rhs_s_fn(&b, &rho, &n, &g));

    // leg1 : lhs = mid.
    //   subsetSum_parseval_core n (applyT ρ n g) : Σ_S A_{applyT g}(S)² = 2^n·Σ_x sq(applyT g x),
    //   i.e. `mid = lhs`; `Eq.symm` flips it.
    let parseval = Expr::apps(c.parseval_core.clone(), [n.clone(), applyt_g.clone()]);
    let leg1 = c.symm(mid.clone(), lhs.clone(), parseval);

    // leg2 : mid = rhs   via Fin.sum_congr over the decoded jS.
    //   F jS := mid_s_fn (hcDecode jS) = A_{applyT g}(hcDec jS)²,
    //   G jS := rhs_s_fn (hcDecode jS) = (2^n·ρ^{|hcDec jS|}·A_g(hcDec jS))²,
    //   h jS := congrArg (·²) (applyT_coeff_eq ρ n g jS).
    let f_mid = c.dec_index(&b, &n, &c.mid_s_fn(&b, &rho, &n, &g));
    let g_rhs = c.dec_index(&b, &n, &c.rhs_s_fn(&b, &rho, &n, &g));
    let h_fn = {
        let mut jb = EnvDeclBuilder::child_of(&b);
        let fin_p = c.fin_of(&c.pow2(&n));
        let (js_id, js) = jb.fresh_local(fin_p.clone());
        let s = c.hc_decode(&n, &js);
        // applyT_coeff_eq ρ n g jS : A_{applyT g}(hcDec jS) = (2^n·ρ^{|S|})·A_g(S).
        let coeff_eq = Expr::apps(
            c.applyt_coeff_eq.clone(),
            [rho.clone(), n.clone(), g.clone(), js.clone()],
        );
        // a := A_{applyT g}(hcDec jS) = subsetSum n (fun x => applyT ρ n g x · χ_S x).
        let a = {
            let mut xb = EnvDeclBuilder::child_of(&jb);
            let hcp = c.hcpoint_of(&n);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let body = c.mul(c.applyt(&rho, &n, &g, &x), c.chi_(&n, &s, &x));
            let f = xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body));
            c.ssum(&n, f)
        };
        let bb = c.coeff(&jb, &rho, &n, &g, &s);
        let body = c.square_congr(&jb, a, bb, coeff_eq);
        jb.finish_child(jb.mk_lam(js_id, BinderInfo::Default, fin_p, body))
    };
    let leg2 = Expr::apps(c.fin_sum_congr.clone(), [c.pow2(&n), f_mid, g_rhs, h_fn]);

    // Assemble: lhs = mid = rhs.
    let proof = c.trans(lhs, mid, rhs, leg1, leg2);

    let val = b.mk_lam(g_id, BinderInfo::Default, g_ty, proof);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}
