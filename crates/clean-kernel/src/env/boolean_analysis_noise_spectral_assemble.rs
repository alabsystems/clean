// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_noise_spectral_chain2.rs — the top-level
// `spectral_chain` assembling the Fubini legs for `noise_spectral_core`.

/// The proof of `noise_spectral_core` at fixed `ρ, n, a`.
///
/// Builds the chain `E0u = E1 = E2 = E3 = E4 = E_rhs`, where `E0u` is the
/// noiseDensityW-unfolded LHS (def-eq to the stated `Σ_x Σ_y a_x a_y·noiseDensityW`
/// because `noiseDensityW` is reducible). All endpoints are `subsetSum n (·)`.
fn spectral_chain(
    c: &SpectralConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    a: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);

    // endpoint expressions.
    let e0 = c.ssum(n, c.e0_x_fn(parent, rho, n, a));
    let e1 = c.ssum(n, c.e1_x_fn(parent, rho, n, a));
    let e2 = c.ssum(n, c.e2_x_fn(parent, rho, n, a));
    let e3 = c.ssum(n, c.e3_s_fn(parent, rho, n, a));
    let e4 = c.ssum(n, c.e4_s_fn(parent, rho, n, a));
    let e_rhs = c.ssum(n, c.rhs_s_fn(parent, rho, n, a));

    // legA : e0 = e1   (subsetSum_congr over x of subsetSum_congr over y of leg1_xy).
    let leg_a = {
        let h = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            // before_y : fun y => (a x·a y)·(Σ_S w_S·(χ_Sx·χ_Sy))
            let before_y = {
                let mut yb = EnvDeclBuilder::child_of(&xb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let ax_ay = c.mul(
                    Expr::app(a.clone(), x.clone()),
                    Expr::app(a.clone(), y.clone()),
                );
                let chi_sum = c.ssum(n, c.wchi_fn(&yb, rho, n, &x, &y));
                let body = c.mul(ax_ay, chi_sum);
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
            };
            // after_y : fun y => Σ_S w_S·(g_Sx·g_Sy)
            let after_y = {
                let mut yb = EnvDeclBuilder::child_of(&xb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let body = c.ssum(n, c.wg_fn(&yb, rho, n, a, &x, &y));
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
            };
            let h_y = {
                let mut yb = EnvDeclBuilder::child_of(&xb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let pf = c.leg1_xy(&yb, rho, n, a, &x, &y);
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), pf))
            };
            let inner = c.ss_congr(n, &before_y, &after_y, h_y);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), inner))
        };
        c.ss_congr(
            n,
            &c.e0_x_fn(parent, rho, n, a),
            &c.e1_x_fn(parent, rho, n, a),
            h,
        )
    };

    // legB : e1 = e2   (subsetSum_congr over x of per-x swap y↔S).
    let leg_b = {
        let h = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            // F y S = w_S·(g_Sx·g_Sy) — swap kernel for the per-x y↔S Fubini.
            let f = {
                let mut yb = EnvDeclBuilder::child_of(&xb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let inner = {
                    let mut sb = EnvDeclBuilder::child_of(&yb);
                    let (s_id, s) = sb.fresh_local(hcp.clone());
                    let w = c.weight(&sb, rho, n, &s);
                    let body = c.mul(w, c.mul(c.g(n, a, &s, &x), c.g(n, a, &s, &y)));
                    sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
                };
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), inner))
            };
            // subsetSum_swap n f : Σ_y Σ_S F y S = Σ_S Σ_y F y S.
            let swap = c.ss_swap(n, &f);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), swap))
        };
        c.ss_congr(
            n,
            &c.e1_x_fn(parent, rho, n, a),
            &c.e2_x_fn(parent, rho, n, a),
            h,
        )
    };

    // legC : e2 = e3   (symm of subsetSum_swap n swap_kernel, the global S↔x swap).
    let leg_c = {
        let kernel = c.swap_kernel(parent, rho, n, a);
        let swap = c.ss_swap(n, &kernel); // : Σ_S Σ_x kernel (=e3) = Σ_x Σ_S kernel (=e2)
        c.symm(e3.clone(), e2.clone(), swap)
    };

    // legD : e3 = e4   (subsetSum_congr over S of pullout_per_s).
    let leg_d = {
        let h = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let pf = c.pullout_per_s(&sb, rho, n, a, &s);
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), pf))
        };
        c.ss_congr(
            n,
            &c.e3_s_fn(parent, rho, n, a),
            &c.e4_s_fn(parent, rho, n, a),
            h,
        )
    };

    // legE : e4 = e_rhs   (subsetSum_congr over S of congrArg (w_S·) (symm sq_expand)).
    let leg_e = {
        let h = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let w = c.weight(&sb, rho, n, &s);
            let g_fn = c.g_fn(&sb, n, a, &s);
            let g_sum = c.ssum(n, g_fn);
            let gg = c.mul(g_sum.clone(), g_sum);
            let dbl = c.dbl_xy(&sb, n, a, &s);
            // sq_expand : G·G = Σ_x Σ_y g_Sx·g_Sy ; symm : dbl = G·G.
            let sq = c.sq_expand_per_s(&sb, n, a, &s);
            let sq_sym = c.symm(gg.clone(), dbl.clone(), sq);
            // congr (w_S·) sq_sym : w_S·dbl = w_S·(G·G).
            let pf = c.mul_left_congr(&sb, &w, dbl, gg, sq_sym);
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), pf))
        };
        c.ss_congr(
            n,
            &c.e4_s_fn(parent, rho, n, a),
            &c.rhs_s_fn(parent, rho, n, a),
            h,
        )
    };

    // Assemble: e0 = e1 = e2 = e3 = e4 = e_rhs.
    let t1 = c.trans(e0.clone(), e1.clone(), e2.clone(), leg_a, leg_b);
    let t2 = c.trans(e0.clone(), e2.clone(), e3.clone(), t1, leg_c);
    let t3 = c.trans(e0.clone(), e3.clone(), e4.clone(), t2, leg_d);
    c.trans(e0, e4, e_rhs, t3, leg_e)
}
