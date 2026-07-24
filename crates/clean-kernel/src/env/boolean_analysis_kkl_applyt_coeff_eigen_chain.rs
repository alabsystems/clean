// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_kkl_applyt_coeff_eigen.rs — the leg proofs and
// top-level `eigen_value` for `noiseDensity_apply_chi_eigen`.

impl CoeffConsts {
    fn mmmc(&self, a: &Expr, b: &Expr, cc: &Expr, d: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
            [a.clone(), b.clone(), cc.clone(), d.clone()],
        )
    }
}

/// Per-`x` regroup `χ_S(x)·(ρ^{|T|}·(χ_T x·χ_T y)) = (ρ^{|T|}·χ_T y)·(χ_T x·χ_S x)`.
/// Writing `a := χ_S x`, `b := ρ^{|T|}`, `cc := χ_T x`, `d := χ_T y`:
///   a·(b·(cc·d)) =[symm assoc]  (a·b)·(cc·d)
///               =[mmmc]         (a·cc)·(b·d)
///               =[comm]         (b·d)·(a·cc)
///               =[congr·comm]   (b·d)·(cc·a).
/// The RHS `(b·d)·(cc·a)` is `(ρ^{|T|}·χ_T y)·(χ_T x·χ_S x)`.
fn eigen_regroup_x(
    c: &CoeffConsts,
    parent: &EnvDeclBuilder,
    a: &Expr,
    b: &Expr,
    cc: &Expr,
    d: &Expr,
) -> Expr {
    let lhs = c.mul(a.clone(), c.mul(b.clone(), c.mul(cc.clone(), d.clone()))); // a·(b·(cc·d))
    let p_ab_cd = c.mul(c.mul(a.clone(), b.clone()), c.mul(cc.clone(), d.clone())); // (a·b)·(cc·d)
    let p_ac_bd = c.mul(c.mul(a.clone(), cc.clone()), c.mul(b.clone(), d.clone())); // (a·cc)·(b·d)
    let p_bd_ac = c.mul(c.mul(b.clone(), d.clone()), c.mul(a.clone(), cc.clone())); // (b·d)·(a·cc)
    let rhs = c.mul(c.mul(b.clone(), d.clone()), c.mul(cc.clone(), a.clone())); // (b·d)·(cc·a)

    // s1 : lhs = (a·b)·(cc·d)   (Eq.symm (mul_assoc a b (cc·d))).
    let assoc = c.mul_assoc(a, b, &c.mul(cc.clone(), d.clone())); // (a·b)·(cc·d) = a·(b·(cc·d))
    let s1 = c.symm(p_ab_cd.clone(), lhs.clone(), assoc);
    // s2 : (a·b)·(cc·d) = (a·cc)·(b·d)   (mmmc a b cc d).
    let s2 = c.mmmc(a, b, cc, d);
    // s3 : (a·cc)·(b·d) = (b·d)·(a·cc)   (mul_comm (a·cc) (b·d)).
    let s3 = c.mul_comm(&c.mul(a.clone(), cc.clone()), &c.mul(b.clone(), d.clone()));
    // s4 : (b·d)·(a·cc) = (b·d)·(cc·a)   (congrArg ((b·d)·) (mul_comm a cc)).
    let s4 = c.mul_left_congr(
        parent,
        &c.mul(b.clone(), d.clone()),
        c.mul(a.clone(), cc.clone()),
        c.mul(cc.clone(), a.clone()),
        c.mul_comm(a, cc),
    );

    let t1 = c.trans(lhs.clone(), p_ab_cd, p_ac_bd.clone(), s1, s2);
    let t2 = c.trans(lhs.clone(), p_ac_bd, p_bd_ac.clone(), t1, s3);
    c.trans(lhs, p_bd_ac, rhs, t2, s4)
}

/// legA (per `S`-character `x`): `(Σ_T W_T)·χ_S(x) = Σ_T χ_S(x)·W_T`,
/// `W_T := ρ^{|T|}·(χ_T x·χ_T y)`.
fn eigen_leg_a_x(
    c: &CoeffConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    s: &Expr,
    y: &Expr,
    x: &Expr,
) -> Expr {
    let chi_sx = c.chi_(n, s, x);
    let w_fn = c.w_summand_fn(parent, rho, n, x, y); // fun T => ρ^{|T|}·(χ_T x·χ_T y)
    let w_sum = c.ssum(n, w_fn.clone());

    let lhs = c.mul(w_sum.clone(), chi_sx.clone()); // (Σ_T W_T)·χ_S(x)
    let mid = c.mul(chi_sx.clone(), w_sum.clone()); // χ_S(x)·(Σ_T W_T)
                                                    // scaled fn : fun T => χ_S(x)·W_T.
    let scaled_fn = {
        let mut tb = EnvDeclBuilder::child_of(parent);
        let hcp = c.hcpoint_of(n);
        let (t_id, t) = tb.fresh_local(hcp.clone());
        let w = c.mul(
            c.pow(rho, &c.set_size(n, &t)),
            c.mul(c.chi_(n, &t, x), c.chi_(n, &t, y)),
        );
        let body = c.mul(chi_sx.clone(), w);
        tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp, body))
    };
    let rhs = c.ssum(n, scaled_fn);

    // step1 : lhs = mid   (mul_comm (Σ_T W_T) χ_S(x)).
    let step1 = c.mul_comm(&w_sum, &chi_sx);
    // smul n χ_S(x) w_fn : Σ_T χ_S(x)·W_T = χ_S(x)·Σ_T W_T   (i.e. rhs = mid).
    let smul = c.ssum_smul(n, &chi_sx, &w_fn);
    // step2 : mid = rhs   (Eq.symm smul).
    let step2 = c.symm(rhs.clone(), mid.clone(), smul);
    c.trans(lhs, mid, rhs, step1, step2)
}

/// legC (per spectral `T`): `Σ_x χ_S(x)·(ρ^{|T|}·(χ_T x·χ_T y)) =
///   (ρ^{|T|}·χ_T y)·(Σ_x χ_T x·χ_S x)`.
fn eigen_leg_c_t(
    c: &CoeffConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    s: &Expr,
    y: &Expr,
    t: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);
    let b = c.pow(rho, &c.set_size(n, t)); // ρ^{|T|}
    let d = c.chi_(n, t, y); // χ_T y
    let coeff = c.mul(b.clone(), d.clone()); // ρ^{|T|}·χ_T y

    // before fn : fun x => χ_S(x)·(ρ^{|T|}·(χ_T x·χ_T y)).
    let before_fn = {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let w = c.mul(b.clone(), c.mul(c.chi_(n, t, &x), d.clone()));
        let body = c.mul(c.chi_(n, s, &x), w);
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    // regrouped fn : fun x => (ρ^{|T|}·χ_T y)·(χ_T x·χ_S x).
    let regrouped_fn = {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = c.mul(coeff.clone(), c.mul(c.chi_(n, t, &x), c.chi_(n, s, &x)));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    let chi_chi_fn = c.chi_chi_fn(parent, n, t, s); // fun x => χ_T x·χ_S x

    // leg1 : Σ_x before = Σ_x regrouped   (subsetSum_congr + per-x regroup).
    let h_regroup = {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let a = c.chi_(n, s, &x); // χ_S x
        let cc = c.chi_(n, t, &x); // χ_T x
        let body = eigen_regroup_x(c, &xb, &a, &b, &cc, &d);
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    let leg1 = c.ssum_congr(n, &before_fn, &regrouped_fn, h_regroup);

    // leg2 : Σ_x regrouped = (ρ^{|T|}·χ_T y)·Σ_x (χ_T x·χ_S x)   (subsetSum_smul).
    let leg2 = c.ssum_smul(n, &coeff, &chi_chi_fn);

    // chain: Σ_x before = Σ_x regrouped = coeff·Σ_x(χ_T x·χ_S x).
    let ss_before = c.ssum(n, eigen_before_fn_clone(c, parent, rho, n, s, y, t));
    let ss_regrouped = c.ssum(n, eigen_regrouped_fn_clone(c, parent, rho, n, s, y, t));
    let ss_chi = c.ssum(n, c.chi_chi_fn(parent, n, t, s));
    let target = c.mul(coeff, ss_chi);
    c.trans(ss_before, ss_regrouped, target, leg1, leg2)
}

// Re-builders (alpha-equal copies for the chain endpoints).
fn eigen_before_fn_clone(
    c: &CoeffConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    s: &Expr,
    y: &Expr,
    t: &Expr,
) -> Expr {
    let mut xb = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (x_id, x) = xb.fresh_local(hcp.clone());
    let b = c.pow(rho, &c.set_size(n, t));
    let d = c.chi_(n, t, y);
    let w = c.mul(b, c.mul(c.chi_(n, t, &x), d));
    let body = c.mul(c.chi_(n, s, &x), w);
    xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
}
fn eigen_regrouped_fn_clone(
    c: &CoeffConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    s: &Expr,
    y: &Expr,
    t: &Expr,
) -> Expr {
    let mut xb = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (x_id, x) = xb.fresh_local(hcp.clone());
    let coeff = c.mul(c.pow(rho, &c.set_size(n, t)), c.chi_(n, t, y));
    let body = c.mul(coeff, c.mul(c.chi_(n, t, &x), c.chi_(n, s, &x)));
    xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
}

include!("boolean_analysis_kkl_applyt_coeff_eigen_chain2.rs");
