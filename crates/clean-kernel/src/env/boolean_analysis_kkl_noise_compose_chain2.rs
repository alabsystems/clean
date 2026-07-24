// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_kkl_noise_compose_chain.rs — the seven leg proofs
// and the top-level `compose_value` for `noiseDensityW_compose_third`. Split out
// only for the 500-line-per-file convention; not a standalone module.

impl ComposeConsts {
    /// Per-z leg-1 leaf: `(Σ_S g3 S z)·w = Σ_S (g3 S z·w)` (right-smul-in),
    /// where `w := W_{1/3}(z,y)`. Chain:
    ///   `(Σ_S g)·w →[mul_comm] w·(Σ_S g) →[symm ss_smul] Σ_S w·g
    ///             →[ss_congr·mul_comm] Σ_S g·w`.
    fn leg1_leaf(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr, z: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let w = self.dens(&self.third(), n, z, y);
        // g_fn S := g3 S z
        let g_fn = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let body = self.g3(n, x, &s, z);
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };
        // w·g_fn S := w·(g3 S z)
        let wg_fn = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let body = self.mul(w.clone(), self.g3(n, x, &s, z));
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };
        // g·w_fn S := (g3 S z)·w
        let gw_fn = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let body = self.mul(self.g3(n, x, &s, z), w.clone());
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };

        let sum_g = self.ssum(n, g_fn.clone());
        let sum_wg = self.ssum(n, wg_fn.clone());
        let sum_gw = self.ssum(n, gw_fn.clone());
        let a0 = self.mul(sum_g.clone(), w.clone()); // (Σ_S g)·w
        let a1 = self.mul(w.clone(), sum_g.clone()); // w·(Σ_S g)

        // s1 : (Σ_S g)·w = w·(Σ_S g)
        let s1 = self.mul_comm(sum_g.clone(), w.clone());
        // s2 : w·(Σ_S g) = Σ_S (w·g)   =  symm (ss_smul n w g_fn)
        let smul = self.ss_smul(n, &w, &g_fn); // Σ_S (w·g) = w·Σ_S g
        let s2 = self.symm(sum_wg.clone(), a1.clone(), smul);
        // s3 : Σ_S (w·g) = Σ_S (g·w)  via ss_congr over per-S mul_comm w (g3 S z)
        let hyp3 = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let body = self.mul_comm(w.clone(), self.g3(n, x, &s, z));
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };
        let s3 = self.ss_congr(n, &wg_fn, &gw_fn, hyp3);

        // chain: a0 = a1 = sum_wg = sum_gw
        let t1 = self.trans(a0.clone(), a1.clone(), sum_wg.clone(), s1, s2);
        self.trans(a0, sum_wg, sum_gw, t1, s3)
    }

    /// Leg 1 (E0 → E1): `subsetSum_congr` over `leg1_leaf` per z.
    fn leg1(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let hyp = {
            let mut zb = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = zb.fresh_local(hcp.clone());
            let body = self.leg1_leaf(&zb, n, x, y, &z);
            zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
        };
        let e0 = self.e0_z_fn(parent, n, x, y);
        let e1 = self.e1_z_fn(parent, n, x, y);
        self.ss_congr(n, &e0, &e1, hyp)
    }

    /// Leg 2 (E1 → E2): `Eq.symm (subsetSum_swap n swap_kernel)`.
    /// `subsetSum_swap` is `Σ_S Σ_z K = Σ_z Σ_S K`; E1 is `Σ_z Σ_S K`, E2 is
    /// `Σ_S Σ_z K`, so the symm gives `E1 = E2`.
    fn leg2(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let k = self.swap_kernel(parent, n, x, y);
        let swap = self.ss_swap(n, &k); // Σ_S Σ_z K = Σ_z Σ_S K
        let e1 = self.ssum(n, self.e1_z_fn(parent, n, x, y));
        let e2 = self.ssum(n, self.e2_s_fn(parent, n, x, y));
        // swap : e2_as_SSz = e1_as_zSS  (LHS Σ_S Σ_z, RHS Σ_z Σ_S);
        // we want E1 = E2, i.e. (Σ_z Σ_S) = (Σ_S Σ_z) = symm(swap).
        self.symm(e2, e1, swap)
    }

    /// Per-z leg-3 leaf: `(g3 S z)·w = coeff·(χ_S z·w)`, with
    /// `g3 S z = pw·(χ_S x·χ_S z)`, `coeff = pw·χ_S x`, `w = W_{1/3}(z,y)`,
    /// `pw := (1/3)^{|S|}`. Pure `Rat` reassociation of `pw, χ_S x, χ_S z, w`:
    ///   `(pw·(χx·χz))·w →[assoc pw (χx·χz) w] pw·((χx·χz)·w)
    ///     →[congr (pw·) (assoc χx χz w)]  pw·(χx·(χz·w))
    ///     →[symm (assoc pw χx (χz·w))]    (pw·χx)·(χz·w) = coeff·(χz·w)`.
    fn leg3_leaf(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        x: &Expr,
        y: &Expr,
        s: &Expr,
        z: &Expr,
    ) -> Expr {
        let pw = self.pow(&self.third(), &self.set_size(n, s));
        let chx = self.chi_(n, s, x);
        let chz = self.chi_(n, s, z);
        let w = self.dens(&self.third(), n, z, y);
        let chx_chz = self.mul(chx.clone(), chz.clone());
        let chz_w = self.mul(chz.clone(), w.clone());

        let a0 = self.mul(self.mul(pw.clone(), chx_chz.clone()), w.clone()); // (pw·(χx·χz))·w
        let a1 = self.mul(pw.clone(), self.mul(chx_chz.clone(), w.clone())); // pw·((χx·χz)·w)
        let a2 = self.mul(pw.clone(), self.mul(chx.clone(), chz_w.clone())); // pw·(χx·(χz·w))
        let coeff = self.mul(pw.clone(), chx.clone());
        let a3 = self.mul(coeff.clone(), chz_w.clone()); // (pw·χx)·(χz·w)

        // s1 : a0 = a1  via assoc pw (χx·χz) w
        let s1 = self.mul_assoc(pw.clone(), chx_chz.clone(), w.clone());
        // s2 : a1 = a2  via congr (pw·_) (assoc χx χz w : (χx·χz)·w = χx·(χz·w))
        let inner_assoc = self.mul_assoc(chx.clone(), chz.clone(), w.clone());
        let motive = self.mul_left_motive(parent, &pw);
        let s2 = self.congr_rat(
            self.mul(chx_chz.clone(), w.clone()),
            self.mul(chx.clone(), chz_w.clone()),
            motive,
            inner_assoc,
        );
        // s3 : a2 = a3  via symm (assoc pw χx (χz·w) : (pw·χx)·(χz·w) = pw·(χx·(χz·w)))
        let assoc3 = self.mul_assoc(pw.clone(), chx.clone(), chz_w.clone());
        let s3 = self.symm(a3.clone(), a2.clone(), assoc3);

        let t1 = self.trans(a0.clone(), a1.clone(), a2.clone(), s1, s2);
        self.trans(a0, a2, a3, t1, s3)
    }

    /// Leg 3 (E2 → E3): per S, rewrite each z-summand `(g3 S z)·w → coeff·(χ_S z·w)`
    /// (`ss_congr` over `leg3_leaf`) then pull `coeff` out (`ss_smul`). Lifted to
    /// the outer S-sum by `subsetSum_congr`.
    fn leg3(&self, parent: &EnvDeclBuilder, n: &Expr, x: &Expr, y: &Expr) -> Expr {
        let hcp = self.hcpoint_of(n);
        let hyp = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());

            // pre_fn z := (g3 S z)·w      (E2 inner z-integrand at this S)
            let pre_fn = {
                let mut zb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = zb.fresh_local(hcp.clone());
                let body = self.mul(self.g3(n, x, &s, &z), self.dens(&self.third(), n, &z, y));
                zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
            };
            // coeff·(χ_S z·w) form: post_fn z := coeff·(χ_S z·w)
            let coeff = self.mul(
                self.pow(&self.third(), &self.set_size(n, &s)),
                self.chi_(n, &s, x),
            );
            let post_fn = {
                let mut zb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = zb.fresh_local(hcp.clone());
                let chz_w = self.mul(self.chi_(n, &s, &z), self.dens(&self.third(), n, &z, y));
                let body = self.mul(coeff.clone(), chz_w);
                zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
            };
            // leaf hyp: per z, (g3 S z)·w = coeff·(χ_S z·w)
            let leaf = {
                let mut zb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = zb.fresh_local(hcp.clone());
                let body = self.leg3_leaf(&zb, n, x, y, &s, &z);
                zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
            };
            // step A: Σ_z (g3 S z·w) = Σ_z coeff·(χ_S z·w)
            let sum_pre = self.ssum(n, pre_fn.clone());
            let sum_post = self.ssum(n, post_fn.clone());
            let step_a = self.ss_congr(n, &pre_fn, &post_fn, leaf);
            // step B: Σ_z coeff·(χ_S z·w) = coeff·Σ_z(χ_S z·w)   (ss_smul)
            let chzw_fn = {
                let mut zb = EnvDeclBuilder::child_of(&sb);
                let (z_id, z) = zb.fresh_local(hcp.clone());
                let body = self.mul(self.chi_(n, &s, &z), self.dens(&self.third(), n, &z, y));
                zb.finish_child(zb.mk_lam(z_id, BinderInfo::Default, hcp.clone(), body))
            };
            let step_b = self.ss_smul(n, &coeff, &chzw_fn);
            // target RHS: coeff·Σ_z(χ_S z·w)  = E3 body at this S
            let e3_body = self.mul(coeff.clone(), self.ssum(n, chzw_fn.clone()));
            let body = self.trans(sum_pre, sum_post, e3_body, step_a, step_b);
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };
        let e2 = self.e2_s_fn(parent, n, x, y);
        let e3 = self.e3_s_fn(parent, n, x, y);
        self.ss_congr(n, &e2, &e3, hyp)
    }
}

include!("boolean_analysis_kkl_noise_compose_chain3.rs");
