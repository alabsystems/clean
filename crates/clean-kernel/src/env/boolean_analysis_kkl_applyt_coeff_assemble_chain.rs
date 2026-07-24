// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_kkl_applyt_coeff_assemble.rs — the leg proofs and
// top-level `coeff_value` for `applyT_coeff_eq`.

/// legA (per `x`): `(Σ_y g y·W(ρ,x,y))·χ_S(x) = Σ_y χ_S(x)·(g y·W(ρ,x,y))`.
///   step1: `mul_comm (Σ_y g y·W) χ_S(x)`  : (Σ_y…)·χ_S(x) = χ_S(x)·(Σ_y…);
///   step2: `Eq.symm (subsetSum_smul n χ_S(x) (fun y => g y·W))`
///                                          : χ_S(x)·(Σ_y…) = Σ_y χ_S(x)·(g y·W).
fn coeff_leg_a_x(
    c: &CoeffConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    g: &Expr,
    s: &Expr,
    x: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);
    let chi_sx = c.chi_(n, s, x);
    // gw_fn := fun y => g y·W(ρ,x,y).
    let gw_fn = {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let body = c.mul(Expr::app(g.clone(), y.clone()), c.density(rho, n, x, &y));
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
    };
    let inner_sum = c.ssum(n, gw_fn.clone());
    let lhs = c.mul(inner_sum.clone(), chi_sx.clone());
    let mid = c.mul(chi_sx.clone(), inner_sum.clone());
    // scaled fn : fun y => χ_S(x)·(g y·W).
    let scaled_fn = {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let gw = c.mul(Expr::app(g.clone(), y.clone()), c.density(rho, n, x, &y));
        let body = c.mul(chi_sx.clone(), gw);
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
    };
    let rhs = c.ssum(n, scaled_fn);

    let step1 = c.mul_comm(&inner_sum, &chi_sx);
    let smul = c.ssum_smul(n, &chi_sx, &gw_fn); // Σ_y χ_S(x)·(g y·W) = χ_S(x)·Σ_y…
    let step2 = c.symm(rhs.clone(), mid.clone(), smul);
    c.trans(lhs, mid, rhs, step1, step2)
}

/// Per-`x` regroup `χ_S(x)·(g y·W) = g y·(W·χ_S x)`.
/// `a := χ_S x`, `bb := g y`, `cc := W`:
///   a·(bb·cc) =[comm a (bb·cc)]  (bb·cc)·a
///             =[assoc bb cc a]   bb·(cc·a).
fn coeff_regroup_x(c: &CoeffConsts, a: &Expr, bb: &Expr, cc: &Expr) -> Expr {
    let lhs = c.mul(a.clone(), c.mul(bb.clone(), cc.clone())); // a·(bb·cc)
    let mid = c.mul(c.mul(bb.clone(), cc.clone()), a.clone()); // (bb·cc)·a
    let rhs = c.mul(bb.clone(), c.mul(cc.clone(), a.clone())); // bb·(cc·a)
    let s1 = c.mul_comm(a, &c.mul(bb.clone(), cc.clone()));
    let s2 = c.mul_assoc(bb, cc, a);
    c.trans(lhs, mid, rhs, s1, s2)
}

/// legC (per `y`): `Σ_x χ_S(x)·(g y·W(ρ,x,y)) = g y·(Σ_x W(ρ,x,y)·χ_S(x))`.
fn coeff_leg_c_y(
    c: &CoeffConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    g: &Expr,
    s: &Expr,
    y: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);
    let gy = Expr::app(g.clone(), y.clone());

    // before fn : fun x => χ_S(x)·(g y·W(ρ,x,y)).
    let before_fn = {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let gw = c.mul(gy.clone(), c.density(rho, n, &x, y));
        let body = c.mul(c.chi_(n, s, &x), gw);
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    // regrouped fn : fun x => g y·(W(ρ,x,y)·χ_S(x)).
    let regrouped_fn = {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = c.mul(
            gy.clone(),
            c.mul(c.density(rho, n, &x, y), c.chi_(n, s, &x)),
        );
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    // eigen integrand : fun x => W(ρ,x,y)·χ_S(x).
    let eigen_fn = c.coeff_eigen_x_fn(parent, rho, n, s, y);

    // leg1 : Σ_x before = Σ_x regrouped   (subsetSum_congr + per-x coeff_regroup_x).
    let h_regroup = {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let a = c.chi_(n, s, &x);
        let cc = c.density(rho, n, &x, y);
        let body = coeff_regroup_x(c, &a, &gy, &cc);
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    let leg1 = c.ssum_congr(n, &before_fn, &regrouped_fn, h_regroup);
    // leg2 : Σ_x regrouped = g y·Σ_x (W·χ_S x)   (subsetSum_smul n (g y) eigen_fn).
    let leg2 = c.ssum_smul(n, &gy, &eigen_fn);

    let ss_before = c.ssum(n, coeff_before_fn_clone(c, parent, rho, n, g, s, y));
    let ss_regrouped = c.ssum(n, coeff_regrouped_fn_clone(c, parent, rho, n, g, s, y));
    let ss_eigen = c.ssum(n, c.coeff_eigen_x_fn(parent, rho, n, s, y));
    let target = c.mul(gy, ss_eigen);
    c.trans(ss_before, ss_regrouped, target, leg1, leg2)
}

fn coeff_before_fn_clone(
    c: &CoeffConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    g: &Expr,
    s: &Expr,
    y: &Expr,
) -> Expr {
    let mut xb = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (x_id, x) = xb.fresh_local(hcp.clone());
    let gw = c.mul(Expr::app(g.clone(), y.clone()), c.density(rho, n, &x, y));
    let body = c.mul(c.chi_(n, s, &x), gw);
    xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
}
fn coeff_regrouped_fn_clone(
    c: &CoeffConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    g: &Expr,
    s: &Expr,
    y: &Expr,
) -> Expr {
    let mut xb = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (x_id, x) = xb.fresh_local(hcp.clone());
    let body = c.mul(
        Expr::app(g.clone(), y.clone()),
        c.mul(c.density(rho, n, &x, y), c.chi_(n, s, &x)),
    );
    xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
}

/// legD (per `y`): `g y·(Σ_x W(ρ,x,y)·χ_S(x)) = g y·((2^n·ρ^{|S|})·χ_S(y))`,
/// via `congrArg (g y·) (noiseDensity_apply_chi_eigen ρ n jS y)`.
fn coeff_leg_d_y(
    c: &CoeffConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    g: &Expr,
    js: &Expr,
    y: &Expr,
) -> Expr {
    let s = c.hc_decode(n, js);
    let gy = Expr::app(g.clone(), y.clone());
    let eigen = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.noiseDensity_apply_chi_eigen"),
            vec![],
        ),
        [rho.clone(), n.clone(), js.clone(), y.clone()],
    );
    let lhs = c.ssum(n, c.coeff_eigen_x_fn(parent, rho, n, &s, y)); // Σ_x W·χ_S x
    let coeff = c.mul(c.cube(n), c.pow(rho, &c.set_size(n, &s)));
    let rhs = c.mul(coeff, c.chi_(n, &s, y)); // (2^n·ρ^{|S|})·χ_S y
    c.mul_left_congr(parent, &gy, lhs, rhs, eigen)
}

/// Per-`y` reassoc `g y·((2^n·ρ^{|S|})·χ_S y) = (2^n·ρ^{|S|})·(g y·χ_S y)`.
/// `bb := g y`, `cc := 2^n·ρ^{|S|}`, `d := χ_S y`:
///   bb·(cc·d) =[symm assoc bb cc d]   (bb·cc)·d
///             =[right·comm bb cc]     (cc·bb)·d
///             =[assoc cc bb d]        cc·(bb·d).
fn coeff_regroup_e(
    c: &CoeffConsts,
    parent: &EnvDeclBuilder,
    bb: &Expr,
    cc: &Expr,
    d: &Expr,
) -> Expr {
    let lhs = c.mul(bb.clone(), c.mul(cc.clone(), d.clone())); // bb·(cc·d)
    let bc_d = c.mul(c.mul(bb.clone(), cc.clone()), d.clone()); // (bb·cc)·d
    let cb_d = c.mul(c.mul(cc.clone(), bb.clone()), d.clone()); // (cc·bb)·d
    let rhs = c.mul(cc.clone(), c.mul(bb.clone(), d.clone())); // cc·(bb·d)

    // s1 : bb·(cc·d) = (bb·cc)·d   (Eq.symm (mul_assoc bb cc d)).
    let assoc1 = c.mul_assoc(bb, cc, d); // (bb·cc)·d = bb·(cc·d)
    let s1 = c.symm(bc_d.clone(), lhs.clone(), assoc1);
    // s2 : (bb·cc)·d = (cc·bb)·d   (congrArg (·d) (mul_comm bb cc)).
    let s2 = c.mul_right_congr(
        parent,
        d,
        c.mul(bb.clone(), cc.clone()),
        c.mul(cc.clone(), bb.clone()),
        c.mul_comm(bb, cc),
    );
    // s3 : (cc·bb)·d = cc·(bb·d)   (mul_assoc cc bb d).
    let s3 = c.mul_assoc(cc, bb, d);

    let t1 = c.trans(lhs.clone(), bc_d, cb_d.clone(), s1, s2);
    c.trans(lhs, cb_d, rhs, t1, s3)
}

fn coeff_value(c: &CoeffConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat.clone());
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let g_ty = c.hcpoint_to_rat(&n);
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let fin_p = c.fin_of(&c.pow2(&n));
    let (js_id, js) = b.fresh_local(fin_p.clone());
    let hcp = c.hcpoint_of(&n);
    let s = c.hc_decode(&n, &js);

    // endpoints.
    let a0 = c.ssum(&n, c.a0_x_fn(&b, &rho, &n, &g, &s));
    let a1 = c.ssum(&n, c.a1_x_fn(&b, &rho, &n, &g, &s));
    let a2 = c.ssum(&n, c.a2_y_fn(&b, &rho, &n, &g, &s));
    let a3 = c.ssum(&n, c.a3_y_fn(&b, &rho, &n, &g, &s));
    let a4 = c.ssum(&n, c.a4_y_fn(&b, &rho, &n, &g, &s));
    let a5 = c.ssum(&n, c.a5_y_fn(&b, &rho, &n, &g, &s));
    let coeff = c.mul(c.cube(&n), c.pow(&rho, &c.set_size(&n, &s))); // 2^n·ρ^{|S|}
    let ag = c.ssum(&n, c.ag_fn(&b, &n, &g, &s)); // A_g(S)
    let rhs = c.mul(coeff.clone(), ag.clone()); // (2^n·ρ^{|S|})·A_g(S)

    // legA : a0 = a1   (subsetSum_congr over x).
    let leg_a = {
        let h = {
            let mut xb = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let pf = coeff_leg_a_x(c, &xb, &rho, &n, &g, &s, &x);
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), pf))
        };
        c.ssum_congr(
            &n,
            &c.a0_x_fn(&b, &rho, &n, &g, &s),
            &c.a1_x_fn(&b, &rho, &n, &g, &s),
            h,
        )
    };

    // legB : a1 = a2   (subsetSum_swap n F).  F x y = χ_S(x)·(g y·W(ρ,x,y)).
    let leg_b = {
        let big_f = {
            let mut xb = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = xb.fresh_local(hcp.clone());
            let inner = {
                let mut yb = EnvDeclBuilder::child_of(&xb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let gw = c.mul(Expr::app(g.clone(), y.clone()), c.density(&rho, &n, &x, &y));
                let body = c.mul(c.chi_(&n, &s, &x), gw);
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
            };
            xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), inner))
        };
        Expr::apps(c.subset_sum_swap.clone(), [n.clone(), big_f])
    };

    // legC : a2 = a3   (subsetSum_congr over y).
    let leg_c = {
        let h = {
            let mut yb = EnvDeclBuilder::child_of(&b);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let pf = coeff_leg_c_y(c, &yb, &rho, &n, &g, &s, &y);
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), pf))
        };
        c.ssum_congr(
            &n,
            &c.a2_y_fn(&b, &rho, &n, &g, &s),
            &c.a3_y_fn(&b, &rho, &n, &g, &s),
            h,
        )
    };

    // legD : a3 = a4   (subsetSum_congr over y of the eigen-action congr).
    let leg_d = {
        let h = {
            let mut yb = EnvDeclBuilder::child_of(&b);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let pf = coeff_leg_d_y(c, &yb, &rho, &n, &g, &js, &y);
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), pf))
        };
        c.ssum_congr(
            &n,
            &c.a3_y_fn(&b, &rho, &n, &g, &s),
            &c.a4_y_fn(&b, &rho, &n, &g, &s),
            h,
        )
    };

    // legE : a4 = a5   (subsetSum_congr over y of the per-y reassoc).
    let leg_e = {
        let h = {
            let mut yb = EnvDeclBuilder::child_of(&b);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let gy = Expr::app(g.clone(), y.clone());
            let d = c.chi_(&n, &s, &y);
            let pf = coeff_regroup_e(c, &yb, &gy, &coeff, &d);
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), pf))
        };
        c.ssum_congr(
            &n,
            &c.a4_y_fn(&b, &rho, &n, &g, &s),
            &c.a5_y_fn(&b, &rho, &n, &g, &s),
            h,
        )
    };

    // legF : a5 = (2^n·ρ^{|S|})·A_g(S)   (subsetSum_smul n coeff (ag_fn)).
    let leg_f = c.ssum_smul(&n, &coeff, &c.ag_fn(&b, &n, &g, &s));

    // Assemble: a0 = a1 = a2 = a3 = a4 = a5 = rhs.
    let t1 = c.trans(a0.clone(), a1.clone(), a2.clone(), leg_a, leg_b);
    let t2 = c.trans(a0.clone(), a2.clone(), a3.clone(), t1, leg_c);
    let t3 = c.trans(a0.clone(), a3.clone(), a4.clone(), t2, leg_d);
    let t4 = c.trans(a0.clone(), a4.clone(), a5.clone(), t3, leg_e);
    let proof = c.trans(a0, a5, rhs, t4, leg_f);

    let val = b.mk_lam(js_id, BinderInfo::Default, fin_p, proof);
    let val = b.mk_lam(g_id, BinderInfo::Default, g_ty, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    let val = b.mk_lam(rho_id, BinderInfo::Default, c.rat.clone(), val);
    b.finish(val)
}
