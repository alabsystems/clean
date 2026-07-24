// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by ..._rung3b_legs.rs — the leg proofs and `parseval_chain`.

impl CoreConsts {
    /// `congrArg (subsetSum n) h` for `h : G = H` at the `HCPoint n → Rat`
    /// function level — lifts a function-equality through `subsetSum n`.
    /// (We instead use `subsetSum_congr`, so this is only the top-level
    /// `congrArg (Rat.mul cube)` style lift; provided as `mul_left_congr`.)
    fn mul_left_congr(
        &self,
        parent: &EnvDeclBuilder,
        left: &Expr,
        a: Expr,
        bb: Expr,
        h: Expr,
    ) -> Expr {
        // congrArg (fun z => left·z) h : left·a = left·bb
        let g = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = b.fresh_local(self.rat.clone());
            let body = self.mul(left.clone(), z);
            b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr(a, bb, g, h)
    }
}

/// Leg D (per x,y under e3→e4): `Σ_S (g S x · g S y) = (a x·a y)·Π(x,y)`.
///   1. `subsetSum_smul`-style: first regroup each summand
///      `(a x·χ_Sx)·(a y·χ_Sy) = (a x·a y)·(χ_Sx·χ_Sy)` by `mul_mul_mul_comm`
///      (under `subsetSum_congr`), giving `Σ_S (a x·a y)·(χ_Sx·χ_Sy)`;
///   2. `subsetSum_smul n (a x·a y) (fun S => χ_Sx·χ_Sy)` pulls the constant out:
///      `= (a x·a y)·Σ_S(χ_Sx·χ_Sy)`;
///   3. the delta `subsetSum_chi_bilinear n x y` rewrites `Σ_S(χ_Sx·χ_Sy)` to
///      `Π_i(1+pm(x i)pm(y i))`, lifted by `congrArg ((a x·a y)·)`.
fn leg_d_xy(
    c: &CoreConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    a: &Expr,
    x: &Expr,
    y: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);
    let ax = Expr::app(a.clone(), x.clone());
    let ay = Expr::app(a.clone(), y.clone());
    let ax_ay = c.mul(ax.clone(), ay.clone());

    // before integrand: fun S => (a x·χ_Sx)·(a y·χ_Sy)
    let before_fn = {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let body = c.mul(c.g(n, a, &s, x), c.g(n, a, &s, y));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };
    // regrouped integrand: fun S => (a x·a y)·(χ_Sx·χ_Sy)
    let chi_chi_fn = {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let body = c.mul(c.chi_(n, &s, x), c.chi_(n, &s, y));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };
    let regrouped_fn = {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let body = c.mul(ax_ay.clone(), c.mul(c.chi_(n, &s, x), c.chi_(n, &s, y)));
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };

    // leg1 : Σ_S before = Σ_S regrouped   (subsetSum_congr + per-S mmmc)
    let h_regroup = {
        let mut sb = EnvDeclBuilder::child_of(parent);
        let (s_id, s) = sb.fresh_local(hcp.clone());
        let chi_x = c.chi_(n, &s, x);
        let chi_y = c.chi_(n, &s, y);
        // mul_mul_mul_comm (a x)(χ_Sx)(a y)(χ_Sy) : (ax·χx)·(ay·χy) = (ax·ay)·(χx·χy)
        let body = c.mmmc(ax.clone(), chi_x, ay.clone(), chi_y);
        sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
    };
    let leg1 = Expr::apps(
        c.subset_sum_congr.clone(),
        [n.clone(), before_fn, regrouped_fn, h_regroup],
    );

    // leg2 : Σ_S regrouped = (a x·a y)·Σ_S(χ_Sx·χ_Sy)   (subsetSum_smul)
    let leg2 = Expr::apps(
        c.subset_sum_smul.clone(),
        [n.clone(), ax_ay.clone(), chi_chi_fn.clone()],
    );

    // leg3 : (a x·a y)·Σ_S(χ_Sx·χ_Sy) = (a x·a y)·Π(x,y)
    //   congrArg ((a x·a y)·) (subsetSum_chi_bilinear n x y).
    let delta = Expr::apps(
        c.subset_chi_bilinear.clone(),
        [n.clone(), x.clone(), y.clone()],
    );
    let ss_chi = c.ssum(n, chi_chi_fn);
    let prod = c.fprod(n, c.prod_int(parent, n, x, y));
    let leg3 = c.mul_left_congr(parent, &ax_ay, ss_chi.clone(), prod.clone(), delta);

    // chain: before = regrouped = (ax·ay)·Σχχ = (ax·ay)·Π
    let ss_before = c.ssum(n, before_fn_clone(c, parent, n, a, x, y));
    let ss_regrouped = c.ssum(n, regrouped_fn_clone(c, parent, n, a, x, y));
    let mid = c.mul(ax_ay.clone(), ss_chi);
    let target = c.mul(ax_ay, prod);
    let t1 = c.trans(ss_before.clone(), ss_regrouped, mid.clone(), leg1, leg2);
    c.trans(ss_before, mid, target, t1, leg3)
}

// Re-builders (alpha-equal copies for the chain endpoints).
fn before_fn_clone(
    c: &CoreConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    a: &Expr,
    x: &Expr,
    y: &Expr,
) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = sb.fresh_local(hcp.clone());
    let body = c.mul(c.g(n, a, &s, x), c.g(n, a, &s, y));
    sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
}
fn regrouped_fn_clone(
    c: &CoreConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    a: &Expr,
    x: &Expr,
    y: &Expr,
) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = sb.fresh_local(hcp.clone());
    let ax = Expr::app(a.clone(), x.clone());
    let ay = Expr::app(a.clone(), y.clone());
    let body = c.mul(c.mul(ax, ay), c.mul(c.chi_(n, &s, x), c.chi_(n, &s, y)));
    sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

include!("boolean_analysis_parseval_rung3b_collapse.rs");
