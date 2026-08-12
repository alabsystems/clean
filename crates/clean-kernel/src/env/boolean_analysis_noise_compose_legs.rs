// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_noise_compose.rs — the `compose_value`
// multi-leg proof of `noiseDensityW_compose`. Split out for the
// 500-line-per-file convention; not a standalone module.

impl ComposeConsts {
    // ── extra named-lemma combinators ────────────────────────────────────────
    fn hc_decode(&self, n: &Expr, j: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
            [n.clone(), j.clone()],
        )
    }
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn fin_sum(&self, m: &Expr, g: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum"), vec![]),
            [m.clone(), g],
        )
    }
    /// `Fin.sum_congr m f g (pw : ∀ i, f i = g i) : Fin.sum m f = Fin.sum m g`.
    fn fin_sum_congr(&self, m: &Expr, f: &Expr, g: &Expr, pw: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            [m.clone(), f.clone(), g.clone(), pw],
        )
    }
    /// `Fin.sum_mul_sum m1 m2 F G : (Σ F)·(Σ G) = Σ_i Σ_j (F i · G j)`.
    fn fin_sum_mul_sum(&self, m1: &Expr, m2: &Expr, f: &Expr, g: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_mul_sum"), vec![]),
            [m1.clone(), m2.clone(), f.clone(), g.clone()],
        )
    }
    /// `subsetSum_subset_diag_extract_scaled n jS f`.
    fn diag_scaled(&self, n: &Expr, js: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.diag_scaled.clone(), [n.clone(), js.clone(), f.clone()])
    }
    /// `subsetSum_chi_pair_diag n S T`.
    fn keystone(&self, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        self.chi_pair_diag(n, s, t)
    }
}

/// The proof of `noiseDensityW_compose` at fixed `ρ, n, x, z`.
///
/// Builds the chain `E0 = E1 = E2 = E3 = E4 = E5 = E6 = E7 = E_rhs`. The first
/// and last endpoints are def-eq to the stated LHS / RHS (`noiseDensityW`
/// reducible), so the closing `Eq.trans` typechecks against the goal.
fn compose_value(c: &ComposeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (x_id, x) = b.fresh_local(hcp.clone());
    let (z_id, z) = b.fresh_local(hcp.clone());

    let proof = compose_chain(c, &b, &rho, &n, &x, &z);

    let val = b.mk_lam(z_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(x_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}

fn compose_chain(
    c: &ComposeConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    x: &Expr,
    z: &Expr,
) -> Expr {
    // endpoint expressions (all `subsetSum n (·)`).
    let e0 = c.ssum(n, c.e0_y_fn(parent, rho, n, x, z));
    let e1 = c.ssum(n, c.e1_y_fn(parent, rho, n, x, z));
    let e2 = c.ssum(n, c.e2_s_fn(parent, rho, n, x, z));
    let e3 = c.ssum(n, c.e3_s_fn(parent, rho, n, x, z));
    let e4 = c.ssum(n, c.e4_s_fn(parent, rho, n, x, z));
    let e5 = c.ssum(n, c.e5_s_fn(parent, rho, n, x, z));
    let e6 = c.ssum(n, c.e6_s_fn(parent, rho, n, x, z));
    let e7 = c.ssum(n, c.e7_s_fn(parent, rho, n, x, z));
    let rho_sq = c.mul(rho.clone(), rho.clone());
    let e_rhs = c.mul(c.cube(n), c.noise_density(&rho_sq, n, x, z));

    let leg_a = leg_a(c, parent, rho, n, x, z);
    let leg_b = leg_b(c, parent, rho, n, x, z);
    let leg_c = leg_c(c, parent, rho, n, x, z);
    let leg_d = leg_d(c, parent, rho, n, x, z);
    let leg_e = leg_e(c, parent, rho, n, x, z);
    let leg_f = leg_f(c, parent, rho, n, x, z);
    let leg_g = leg_g(c, parent, rho, n, x, z);
    let leg_h = leg_h(c, parent, rho, n, x, z);

    let t1 = c.trans(e0.clone(), e1.clone(), e2.clone(), leg_a, leg_b);
    let t2 = c.trans(e0.clone(), e2.clone(), e3.clone(), t1, leg_c);
    let t3 = c.trans(e0.clone(), e3.clone(), e4.clone(), t2, leg_d);
    let t4 = c.trans(e0.clone(), e4.clone(), e5.clone(), t3, leg_e);
    let t5 = c.trans(e0.clone(), e5.clone(), e6.clone(), t4, leg_f);
    let t6 = c.trans(e0.clone(), e6.clone(), e7.clone(), t5, leg_g);
    c.trans(e0, e7, e_rhs, t6, leg_h)
}

// ── legA : E0 = E1  (per-y product → natural double sum, Fin.sum_mul_sum) ────
//
// Per y: dens(ρ,x,y)·dens(ρ,y,z) = Σ_S Σ_T densint_x(S,y)·densint_z(T,y).
// Both `dens` δ-unfold to subsetSum forms, which δ-unfold to Fin.sum (2^n) of the
// DECODED integrands; `Fin.sum_mul_sum (2^n) (2^n) Fx Fz` (Fx/Fz the decoded
// density integrands) is exactly that, up to def-eq. So the per-y proof is the
// `Fin.sum_mul_sum` term, and `subsetSum_congr` over y lifts it.
fn leg_a(
    c: &ComposeConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    x: &Expr,
    z: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);
    let pp = c.pow2(n);
    let fin_p = c.fin_of(&pp);
    let h = {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        // Fx := fun (jS : Fin 2^n) => densint_x(hcDecode jS, y)
        let fx = {
            let mut jb = EnvDeclBuilder::child_of(&yb);
            let (j_id, j) = jb.fresh_local(fin_p.clone());
            let s = c.hc_decode(n, &j);
            let body = c.dens_int(&jb, rho, n, x, &y, &s);
            jb.finish_child(jb.mk_lam(j_id, BinderInfo::Default, fin_p.clone(), body))
        };
        // Fz := fun (jT : Fin 2^n) => densint_z(hcDecode jT, y) = wT·(χ_T y·χ_T z)
        let fz = {
            let mut jb = EnvDeclBuilder::child_of(&yb);
            let (j_id, j) = jb.fresh_local(fin_p.clone());
            let t = c.hc_decode(n, &j);
            let body = c.dens_int(&jb, rho, n, &y, z, &t);
            jb.finish_child(jb.mk_lam(j_id, BinderInfo::Default, fin_p.clone(), body))
        };
        let pf = c.fin_sum_mul_sum(&pp, &pp, &fx, &fz);
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), pf))
    };
    c.ss_congr(
        n,
        &c.e0_y_fn(parent, rho, n, x, z),
        &c.e1_y_fn(parent, rho, n, x, z),
        h,
    )
}

// ── legB : E1 = E2  (swap y↔S; the Σ_T body is carried as f's value) ─────────
//
// E1 = Σ_y Σ_S F(y,S),  F(y,S) := Σ_T natural(S,T,y).
// subsetSum_swap n (fun y S => F(y,S)) : Σ_y Σ_S F = Σ_S Σ_y F = E2.
fn leg_b(
    c: &ComposeConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    x: &Expr,
    z: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);
    // f : HCPoint→HCPoint→Rat := fun y S => Σ_T natural(S,T,y).
    let f = {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let s_body = {
            let mut sb = EnvDeclBuilder::child_of(&yb);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let t_fn = {
                let mut tb = EnvDeclBuilder::child_of(&sb);
                let (t_id, t) = tb.fresh_local(hcp.clone());
                let body = c.nat_summand(&tb, rho, n, x, z, &s, &t, &y);
                tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), body))
            };
            let body = c.ssum(n, t_fn);
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), s_body))
    };
    c.ss_swap(n, &f)
}

// ── legC : E2 = E3  (per S, swap y↔T) ────────────────────────────────────────
//
// E2 = Σ_S Σ_y Σ_T natural,  E3 = Σ_S Σ_T Σ_y natural.
// Per S: subsetSum_swap n (fun y T => natural(S,T,y)) : Σ_y Σ_T = Σ_T Σ_y.
fn leg_c(
    c: &ComposeConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    x: &Expr,
    z: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);
    let h = {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        // f : HCPoint→HCPoint→Rat := fun y T => natural(S,T,y).
        let f = {
            let mut yb = EnvDeclBuilder::child_of(&sb);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let t_body = {
                let mut tb = EnvDeclBuilder::child_of(&yb);
                let (t_id, t) = tb.fresh_local(hcp.clone());
                let body = c.nat_summand(&tb, rho, n, x, z, &s, &t, &y);
                tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), body))
            };
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), t_body))
        };
        let pf = c.ss_swap(n, &f);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), pf))
    };
    c.ss_congr(
        n,
        &c.e2_s_fn(parent, rho, n, x, z),
        &c.e3_s_fn(parent, rho, n, x, z),
        h,
    )
}

include!("boolean_analysis_noise_compose_legs2.rs");

// ── legG : E6 = E7  (per S, mmmc + powNat_mul_base) ──────────────────────────
//
// Per S: cube·K_{S,S} = cube·((ρ·ρ)^|S|·(χ_S x·χ_S z)).
//   K_{S,S} = (wS·χ_S x)·(wS·χ_S z)
//     →[mmmc wS (χ_S x) wS (χ_S z)]   (wS·wS)·(χ_S x·χ_S z)
//     →[congr-left (·(χ_S x·χ_S z)) (symm powNat_mul_base ρ ρ |S|)]
//        ((ρ·ρ)^|S|)·(χ_S x·χ_S z)
//   then congr (cube·) lifts; subsetSum_congr over S.
fn leg_g(
    c: &ComposeConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    x: &Expr,
    z: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);
    let h = {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let cube = c.cube(n);
        let ws = c.weight(&sb, rho, n, &s);
        let chi_x = c.chi_(n, &s, x);
        let chi_z = c.chi_(n, &s, z);
        let chis = c.mul(chi_x.clone(), chi_z.clone());
        let kss = c.mul(
            c.mul(ws.clone(), chi_x.clone()),
            c.mul(ws.clone(), chi_z.clone()),
        );
        // step1 : (wS·χx)·(wS·χz) = (wS·wS)·(χx·χz)
        let mm = c.mmmc(&ws, &chi_x, &ws, &chi_z);
        let ws_sq = c.mul(ws.clone(), ws.clone());
        let mid = c.mul(ws_sq.clone(), chis.clone());
        // step2 : (wS·wS)·(χx·χz) = ((ρ·ρ)^|S|)·(χx·χz)
        //   powNat_mul_base ρ ρ |S| : (ρ·ρ)^|S| = ρ^|S|·ρ^|S|  ; symm → ws·ws = (ρ·ρ)^|S|
        let pc_s = c.popcount(&sb, n, &s);
        let rho_sq = c.mul(rho.clone(), rho.clone());
        let rhosq_pow = c.pow(&rho_sq, &pc_s);
        let pmb = c.pownat_mul_base(rho, rho, &pc_s); // (ρ·ρ)^|S| = ρ^|S|·ρ^|S|
        let pmb_sym = c.symm(rhosq_pow.clone(), ws_sq.clone(), pmb); // ws·ws = (ρ·ρ)^|S|
        let motive = c.mul_left_motive(&sb, &chis); // fun w => w·(χx·χz)
        let step2 = c.congr(ws_sq.clone(), rhosq_pow.clone(), motive, pmb_sym);
        let target_kss = c.mul(rhosq_pow.clone(), chis.clone()); // = rhosq_int(S)
        let kss_eq = c.trans(kss.clone(), mid, target_kss.clone(), mm, step2);
        // lift under (cube·) : cube·K_{S,S} = cube·target
        let cube_motive = c.mul_right_motive(&sb, &cube);
        let body = c.congr(kss, target_kss, cube_motive, kss_eq);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };
    c.ss_congr(
        n,
        &c.e6_s_fn(parent, rho, n, x, z),
        &c.e7_s_fn(parent, rho, n, x, z),
        h,
    )
}

// ── legH : E7 = E_rhs  (pull cube out via subsetSum_smul) ────────────────────
//
// E7 = Σ_S cube·rhosq_int(S)  →[subsetSum_smul n cube rhosq_int_fn]
//   cube·(Σ_S rhosq_int(S)) ≡ cube·noiseDensityW(ρ·ρ) n x z  (δ-eq, density reducible).
fn leg_h(
    c: &ComposeConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    x: &Expr,
    z: &Expr,
) -> Expr {
    let cube = c.cube(n);
    let f = c.rhosq_int_fn(parent, rho, n, x, z);
    c.ss_smul(n, &cube, &f)
}
