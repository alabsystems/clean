// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_noise_spectral_chain.rs — the leg proofs and the
// top-level `spectral_chain` for `noise_spectral_core`.

impl SpectralConsts {
    /// `p·(w·q) = w·(p·q)` (a left-commute, via assoc + comm + assoc):
    ///   p·(w·q) =[symm assoc] (p·w)·q =[congr(·q)(comm p w)] (w·p)·q
    ///           =[assoc]      w·(p·q).
    fn mul_left_comm(&self, parent: &EnvDeclBuilder, p: &Expr, w: &Expr, q: &Expr) -> Expr {
        let p_wq = self.mul(p.clone(), self.mul(w.clone(), q.clone()));
        let pw_q = self.mul(self.mul(p.clone(), w.clone()), q.clone());
        let wp_q = self.mul(self.mul(w.clone(), p.clone()), q.clone());
        let w_pq = self.mul(w.clone(), self.mul(p.clone(), q.clone()));
        // leg1 : p·(w·q) = (p·w)·q   (symm of mul_assoc p w q : (p·w)·q = p·(w·q)).
        let assoc1 = self.mul_assoc(p.clone(), w.clone(), q.clone());
        let leg1 = self.symm(pw_q.clone(), p_wq.clone(), assoc1);
        // leg2 : (p·w)·q = (w·p)·q   (congr (·q) (mul_comm p w)).
        let g_rq = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = b.fresh_local(self.rat.clone());
            let body = self.mul(z, q.clone());
            b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        let comm = self.mul_comm(p.clone(), w.clone());
        let leg2 = self.congr(
            self.mul(p.clone(), w.clone()),
            self.mul(w.clone(), p.clone()),
            g_rq,
            comm,
        );
        // leg3 : (w·p)·q = w·(p·q)   (mul_assoc w p q).
        let leg3 = self.mul_assoc(w.clone(), p.clone(), q.clone());
        let t1 = self.trans(p_wq.clone(), pw_q, wp_q.clone(), leg1, leg2);
        self.trans(p_wq, wp_q, w_pq, t1, leg3)
    }

    /// Leg1 per (x,y): `(a x·a y)·(Σ_S w_S·(χ_Sx·χ_Sy)) = Σ_S w_S·(g_Sx·g_Sy)`.
    ///   • `Eq.symm (subsetSum_smul n (a x·a y) wchi_fn)` :
    ///       (a x·a y)·Σ_S w_S·(χ_Sx·χ_Sy) = Σ_S (a x·a y)·(w_S·(χ_Sx·χ_Sy));
    ///   • `subsetSum_congr` over S of the per-S regroup
    ///       (a x·a y)·(w_S·(χ_Sx·χ_Sy)) = w_S·(g_Sx·g_Sy).
    fn leg1_xy(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        a: &Expr,
        x: &Expr,
        y: &Expr,
    ) -> Expr {
        let hcp = self.hcpoint_of(n);
        let ax_ay = self.mul(
            Expr::app(a.clone(), x.clone()),
            Expr::app(a.clone(), y.clone()),
        );
        let wchi = self.wchi_fn(parent, rho, n, x, y);
        let ss_wchi = self.ssum(n, wchi.clone());
        // pre : (a x·a y)·Σ_S wchi = Σ_S (a x·a y)·wchi_S.
        let smul = self.ss_smul(n, &ax_ay, &wchi);
        let lhs_pre = self.mul(ax_ay.clone(), ss_wchi);
        // scaled integrand: fun S => (a x·a y)·(w_S·(χ_Sx·χ_Sy)).
        let scaled_fn = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let w = self.weight(&sb, rho, n, &s);
            let body = self.mul(
                ax_ay.clone(),
                self.mul(w, self.mul(self.chi_(n, &s, x), self.chi_(n, &s, y))),
            );
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };
        let ss_scaled = self.ssum(n, scaled_fn.clone());
        let pre = self.symm(ss_scaled.clone(), lhs_pre.clone(), smul);
        // per-S regroup hypothesis: (a x·a y)·(w_S·(χχ)) = w_S·(g_Sx·g_Sy).
        let wg = self.wg_fn(parent, rho, n, a, x, y);
        let h_regroup = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let pf = self.regroup_per_s(&sb, rho, n, a, &s, x, y);
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), pf))
        };
        let congr = self.ss_congr(n, &scaled_fn, &wg, h_regroup);
        let ss_wg = self.ssum(n, wg);
        self.trans(lhs_pre, ss_scaled, ss_wg, pre, congr)
    }

    /// Per-S regroup: `(a x·a y)·(w_S·(χ_Sx·χ_Sy)) = w_S·(g_Sx·g_Sy)`.
    ///   • mul_left_comm (a x·a y) w_S (χ_Sx·χ_Sy) :
    ///       (axay)·(w·(χχ)) = w·((axay)·(χχ));
    ///   • congrArg (w·) (Eq.symm (mmmc (a x) χ_Sx (a y) χ_Sy)) :
    ///       w·((axay)·(χχ)) = w·((ax·χx)·(ay·χy)) = w·(g_Sx·g_Sy).
    fn regroup_per_s(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        a: &Expr,
        s: &Expr,
        x: &Expr,
        y: &Expr,
    ) -> Expr {
        let ax = Expr::app(a.clone(), x.clone());
        let ay = Expr::app(a.clone(), y.clone());
        let ax_ay = self.mul(ax.clone(), ay.clone());
        let chi_x = self.chi_(n, s, x);
        let chi_y = self.chi_(n, s, y);
        let chi_chi = self.mul(chi_x.clone(), chi_y.clone());
        let w = self.weight(parent, rho, n, s);
        // leg1 : (axay)·(w·(χχ)) = w·((axay)·(χχ)).
        let leg1 = self.mul_left_comm(parent, &ax_ay, &w, &chi_chi);
        // mmmc (a x) χx (a y) χy : (ax·χx)·(ay·χy) = (ax·ay)·(χx·χy).
        let mmmc = self.mmmc(ax.clone(), chi_x.clone(), ay.clone(), chi_y.clone());
        let gx_gy = self.mul(self.mul(ax.clone(), chi_x), self.mul(ay.clone(), chi_y));
        // symm mmmc : (ax·ay)·(χx·χy) = (ax·χx)·(ay·χy).
        let mmmc_sym = self.symm(
            gx_gy.clone(),
            self.mul(ax_ay.clone(), chi_chi.clone()),
            mmmc,
        );
        // congr (w·) mmmc_sym : w·((axay)·(χχ)) = w·(gx·gy).
        let leg2 = self.mul_left_congr(
            parent,
            &w,
            self.mul(ax_ay.clone(), chi_chi.clone()),
            gx_gy.clone(),
            mmmc_sym,
        );
        let lhs = self.mul(ax_ay.clone(), self.mul(w.clone(), chi_chi.clone()));
        let mid = self.mul(w.clone(), self.mul(ax_ay, chi_chi));
        let rhs = self.mul(w, gx_gy);
        self.trans(lhs, mid, rhs, leg1, leg2)
    }

    /// Per-S square expansion: `(Σ_x g_Sx)·(Σ_x g_Sx) = Σ_x Σ_y g_Sx·g_Sy`.
    ///   • Eq.symm (subsetSum_smul n G g_fn) : G·G = Σ_x G·g_Sx;
    ///   • subsetSum_congr over x of: G·g_Sx = g_Sx·G = Σ_y g_Sx·g_Sy.
    fn sq_expand_per_s(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, s: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let g_fn = self.g_fn(parent, n, a, s);
        let g_sum = self.ssum(n, g_fn.clone()); // G
                                                // pre : G·G = Σ_x G·g_Sx   (symm of subsetSum_smul n G g_fn).
        let smul = self.ss_smul(n, &g_sum, &g_fn);
        let gg = self.mul(g_sum.clone(), g_sum.clone());
        // scaled : fun x => G·g_Sx.
        let scaled_fn = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let body = self.mul(g_sum.clone(), self.g(n, a, s, &x));
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
        };
        let ss_scaled = self.ssum(n, scaled_fn.clone());
        let pre = self.symm(ss_scaled.clone(), gg.clone(), smul);
        // per-x hypothesis : G·g_Sx = Σ_y g_Sx·g_Sy.
        let inner_fn = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let body = self.inner_y_g(&xb, n, a, s, &x);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
        };
        let h_x = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let pf = self.sq_expand_per_sx(&xb, n, a, s, &x, &g_sum);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), pf))
        };
        let congr = self.ss_congr(n, &scaled_fn, &inner_fn, h_x);
        let dbl = self.dbl_xy(parent, n, a, s);
        self.trans(gg, ss_scaled, dbl, pre, congr)
    }

    /// Per-(S,x): `G·g_Sx = Σ_y g_Sx·g_Sy`  (G := Σ_x g_Sx).
    ///   • mul_comm G g_Sx : G·g_Sx = g_Sx·G;
    ///   • Eq.symm (subsetSum_smul n g_Sx g_fn) : g_Sx·G = Σ_y g_Sx·g_Sy.
    fn sq_expand_per_sx(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        a: &Expr,
        s: &Expr,
        x: &Expr,
        g_sum: &Expr,
    ) -> Expr {
        let g_sx = self.g(n, a, s, x);
        let g_fn = self.g_fn(parent, n, a, s);
        // leg1 : G·g_Sx = g_Sx·G  (mul_comm G g_Sx).
        let comm = self.mul_comm(g_sum.clone(), g_sx.clone());
        // smul n g_Sx g_fn : Σ_y g_Sx·g_Sy = g_Sx·Σ_y g_Sy = g_Sx·G.
        let smul = self.ss_smul(n, &g_sx, &g_fn);
        let inner = self.inner_y_g(parent, n, a, s, x);
        let gsx_g = self.mul(g_sx.clone(), g_sum.clone());
        // leg2 : g_Sx·G = Σ_y g_Sx·g_Sy  (symm smul).
        let leg2 = self.symm(inner.clone(), gsx_g.clone(), smul);
        let gg_gsx = self.mul(g_sum.clone(), g_sx.clone());
        self.trans(gg_gsx, gsx_g, inner, comm, leg2)
    }

    /// Per-S pull-out: `Σ_x Σ_y w_S·(g_Sx·g_Sy) = w_S·(Σ_x Σ_y g_Sx·g_Sy)`.
    ///   • subsetSum_congr over x of: Σ_y w_S·(g_Sx·g_Sy) = w_S·Σ_y g_Sx·g_Sy
    ///       (subsetSum_smul n w_S inner_y_g);
    ///   • subsetSum_smul n w_S (fun x => Σ_y g_Sx·g_Sy) :
    ///       Σ_x w_S·(Σ_y …) = w_S·(Σ_x Σ_y …).
    fn pullout_per_s(
        &self,
        parent: &EnvDeclBuilder,
        rho: &Expr,
        n: &Expr,
        a: &Expr,
        s: &Expr,
    ) -> Expr {
        let hcp = self.hcpoint_of(n);
        let w = self.weight(parent, rho, n, s);
        // before x-integrand : fun x => Σ_y w_S·(g_Sx·g_Sy).
        let before_x = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let body = self.wg_ysum_fixed_sx(&xb, rho, n, a, s, &x);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
        };
        // after x-integrand : fun x => w_S·(Σ_y g_Sx·g_Sy).
        let after_x = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let inner = self.inner_y_g(&xb, n, a, s, &x);
            let body = self.mul(w.clone(), inner);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
        };
        // per-x hyp : Σ_y w_S·(g_Sx·g_Sy) = w_S·Σ_y g_Sx·g_Sy  (subsetSum_smul).
        let h_x = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            // inner integrand fun y => g_Sx·g_Sy
            let inner_fn = {
                let mut yb = EnvDeclBuilder::child_of(&xb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let body = self.mul(self.g(n, a, s, &x), self.g(n, a, s, &y));
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
            };
            let pf = self.ss_smul(n, &w, &inner_fn);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), pf))
        };
        let congr = self.ss_congr(n, &before_x, &after_x, h_x);
        // legB : Σ_x w_S·(Σ_y …) = w_S·(Σ_x Σ_y …)  (subsetSum_smul n w_S inner_x).
        let inner_x = {
            let mut xb = EnvDeclBuilder::child_of(parent);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let body = self.inner_y_g(&xb, n, a, s, &x);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
        };
        let leg_b = self.ss_smul(n, &w, &inner_x);
        let before = self.ssum(n, before_x);
        let mid = self.ssum(n, after_x);
        let dbl = self.dbl_xy(parent, n, a, s);
        let rhs = self.mul(w, dbl);
        self.trans(before, mid, rhs, congr, leg_b)
    }
}

include!("boolean_analysis_noise_spectral_assemble.rs");
