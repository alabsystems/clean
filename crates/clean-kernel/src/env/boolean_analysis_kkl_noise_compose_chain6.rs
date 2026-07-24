// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_kkl_noise_compose.rs — RUNG 1: the un-normalized
// spatial = spectral 2-norm identity `noise_two_norm_spectral_third`, composing
// `noise_self_adjoint_sq` + `noiseOp_compose_third` + `noise_two_norm_eq_pairing`
// (B3a). Split out only for the 500-line-per-file convention; not standalone.

impl ComposeConsts {
    /// G1 x-integrand `fun x => g x · noiseOp(1/3) n (noiseOp(1/3) n g) x` — the
    /// `noise_self_adjoint_sq` RHS (`Σ_x g x·(T_{1/3}² g)(x)`).
    fn g1_x_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let inner_op = Expr::apps(self.noise_op.clone(), [self.third(), n.clone(), g.clone()]);
        let ttg = self.op_apply(&self.third(), n, &inner_op, &x);
        let body = self.mul(Expr::app(g.clone(), x.clone()), ttg);
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    /// G2 x-integrand `fun x => g x · (cube · noiseOp(1/9) n g x)` — after the
    /// operator-semigroup substitution.
    fn g2_x_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let scaled = self.mul(self.cube(n), self.op_apply(&self.ninth(), n, g, &x));
        let body = self.mul(Expr::app(g.clone(), x.clone()), scaled);
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    /// G3 inner x-integrand (inside `cube·Σ_x(…)`): `fun x => g x · noiseOp(1/9) n
    /// g x` — after pulling `cube` out per x.
    fn g3_inner_x_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.mul(
            Expr::app(g.clone(), x.clone()),
            self.op_apply(&self.ninth(), n, g, &x),
        );
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    /// G4 inner x-integrand (inside `cube·Σ_x(…)`): `fun x => Σ_y (g x·g y)·
    /// W_{1/9}(x,y)` — byte-for-byte B3a's `rhs_x_fn`. (= `⟨T_{1/9}g, g⟩` summand.)
    fn g4_inner_x_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
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
            let body = self.mul(gx_gy, self.dens(&self.ninth(), n, &x, &y));
            let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
            self.ssum(n, f)
        };
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, y_sum))
    }

    /// B3a spectral S-integrand `fun S => ((1/3)^{|S|}·(1/3)^{|S|})·(A·A)` —
    /// byte-for-byte B3a's `lhs_s_fn` (inline popcount, `A := a_coeff`). The RUNG-1
    /// RHS spectral sum factor.
    fn spectral_s_fn(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let pc = self.popcount_inline(&sb, n, &s);
        let w_third = self.pow(&self.third(), &pc);
        let w = self.mul(w_third.clone(), w_third); // (1/3)^|S|·(1/3)^|S|
        let a = self.a_coeff(&sb, n, g, &s);
        let aa = self.mul(a.clone(), a);
        let body = self.mul(w, aa);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

/// `∀ (n : Nat) (g : HCPoint n → Rat),
///    subsetSum n (fun y => noiseOp(1/3) n g y · noiseOp(1/3) n g y)
///      = cube n · subsetSum n (fun S => ((1/3)^{|S|}·(1/3)^{|S|})·(A g S·A g S))`.
fn two_norm_spectral_type(c: &ComposeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let hcp = c.hcpoint_of(&n);

    // LHS: Σ_y (T_{1/3}g y)·(T_{1/3}g y)  — the noise_self_adjoint_sq LHS.
    let lhs_fn = {
        let mut yb = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let tgy = c.op_apply(&c.third(), &n, &g, &y);
        let body = c.mul(tgy.clone(), tgy);
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
    };
    let lhs = c.ssum(&n, lhs_fn);
    let rhs = c.mul(c.cube(&n), c.ssum(&n, c.spectral_s_fn(&b, &n, &g)));
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, concl);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

include!("boolean_analysis_kkl_noise_compose_chain7.rs");
