// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_xside_core_legs.rs — leg_d_st (inner sign-side
// bilinear collapse), leg_e_js (diagonal collapse over the gate index), and the
// top-level `xcore_chain`.

/// Leg D (per S,T under e3→e4): `Σ_x (g S x · g T x) = (a S·a T)·Π(S,T)`.
///   1. regroup each summand `(a S·χ_Sx)·(a T·χ_Tx) = (a S·a T)·(χ_Sx·χ_Tx)`
///      (`mul_mul_mul_comm` under `subsetSum_congr`);
///   2. `subsetSum_smul n (a S·a T) (fun x => χ_Sx·χ_Tx)` pulls the constant out;
///   3. the SIGN-side delta `subsetSum_chi_sign_bilinear n S T` rewrites
///      `Σ_x(χ_Sx·χ_Tx)` to `Π_i(1+pm(S i)pm(T i))`, lifted by `congrArg((a S·a T)·)`.
fn leg_d_st(
    c: &XCoreConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    a: &Expr,
    s: &Expr,
    t: &Expr,
) -> Expr {
    let hcp = c.hcpoint_of(n);
    let as_ = Expr::app(a.clone(), s.clone());
    let at = Expr::app(a.clone(), t.clone());
    let as_at = c.mul(as_.clone(), at.clone());

    // before integrand: fun x => (a S·χ_Sx)·(a T·χ_Tx)
    let before_fn = {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = c.mul(c.g(n, a, s, &x), c.g(n, a, t, &x));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    // chi-chi integrand: fun x => χ_Sx·χ_Tx
    let chi_chi_fn = {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = c.mul(c.chi_(n, s, &x), c.chi_(n, t, &x));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    let regrouped_fn = {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = c.mul(as_at.clone(), c.mul(c.chi_(n, s, &x), c.chi_(n, t, &x)));
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };

    // leg1 : Σ_x before = Σ_x regrouped   (subsetSum_congr + per-x mmmc)
    let h_regroup = {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let chi_s = c.chi_(n, s, &x);
        let chi_t = c.chi_(n, t, &x);
        // mmmc (a S)(χ_Sx)(a T)(χ_Tx) : (aS·χSx)·(aT·χTx) = (aS·aT)·(χSx·χTx)
        let body = c.mmmc(as_.clone(), chi_s, at.clone(), chi_t);
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    let leg1 = Expr::apps(
        c.subset_sum_congr.clone(),
        [n.clone(), before_fn, regrouped_fn, h_regroup],
    );

    // leg2 : Σ_x regrouped = (a S·a T)·Σ_x(χ_Sx·χ_Tx)   (subsetSum_smul)
    let leg2 = Expr::apps(
        c.subset_sum_smul.clone(),
        [n.clone(), as_at.clone(), chi_chi_fn.clone()],
    );

    // leg3 : (a S·a T)·Σ_x(χ_Sx·χ_Tx) = (a S·a T)·Π(S,T)
    //   congrArg ((a S·a T)·) (subsetSum_chi_sign_bilinear n S T).
    let delta = Expr::apps(c.sign_bilinear.clone(), [n.clone(), s.clone(), t.clone()]);
    let ss_chi = c.ssum(n, chi_chi_fn);
    let prod = c.fprod(n, c.prod_int(parent, n, s, t));
    let leg3 = c.mul_left_congr(parent, &as_at, ss_chi.clone(), prod.clone(), delta);

    // chain: before = regrouped = (aS·aT)·Σχχ = (aS·aT)·Π
    let ss_before = c.ssum(n, xcore_before_fn(c, parent, n, a, s, t));
    let ss_regrouped = c.ssum(n, xcore_regrouped_fn(c, parent, n, a, s, t));
    let mid = c.mul(as_at.clone(), ss_chi);
    let target = c.mul(as_at, prod);
    let t1 = c.trans(ss_before.clone(), ss_regrouped, mid.clone(), leg1, leg2);
    c.trans(ss_before, mid, target, t1, leg3)
}

fn xcore_before_fn(
    c: &XCoreConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    a: &Expr,
    s: &Expr,
    t: &Expr,
) -> Expr {
    let mut xb = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (x_id, x) = xb.fresh_local(hcp.clone());
    let body = c.mul(c.g(n, a, s, &x), c.g(n, a, t, &x));
    xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
}
fn xcore_regrouped_fn(
    c: &XCoreConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    a: &Expr,
    s: &Expr,
    t: &Expr,
) -> Expr {
    let mut xb = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (x_id, x) = xb.fresh_local(hcp.clone());
    let as_ = Expr::app(a.clone(), s.clone());
    let at = Expr::app(a.clone(), t.clone());
    let body = c.mul(c.mul(as_, at), c.mul(c.chi_(n, s, &x), c.chi_(n, t, &x)));
    xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
}

/// Leg E (the diagonal collapse, per OUTER decoded GATE index `jS`):
///   `Σ_T (a S·a T)·Π(S,T) = (a S·a S)·2^n`,  where `S = hcDecode n jS`.
fn leg_e_js(c: &XCoreConsts, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, js: &Expr) -> Expr {
    let pp = c.pow2(n);
    let fin_p = c.fin_of(&pp);
    let s = c.hc_decode(n, js); // the concrete decoded gate
    let as_ = Expr::app(a.clone(), s.clone());

    // f : Fin P → Rat := fun jt => (a S·a(hcDec jt))·Π(S, hcDec jt).
    let f = {
        let mut tb = EnvDeclBuilder::child_of(parent);
        let (jt_id, jt) = tb.fresh_local(fin_p.clone());
        let t = c.hc_decode(n, &jt);
        let at = Expr::app(a.clone(), t.clone());
        let prod = c.fprod(n, c.prod_int(&tb, n, &s, &t));
        let body = c.mul(c.mul(as_.clone(), at), prod);
        tb.finish_child(tb.mk_lam(jt_id, BinderInfo::Default, fin_p.clone(), body))
    };

    // hypothesis H : ∀ jt, (Eq (Fin P) jt jS → False) → f jt = 0.
    let hyp = {
        let mut tb = EnvDeclBuilder::child_of(parent);
        let (jt_id, jt) = tb.fresh_local(fin_p.clone());
        let ne_ty = Expr::pi(
            BinderInfo::Default,
            c.eq_fin_pow(n, &jt, js),
            c.false_c.clone(),
        );
        let (ne_id, ne) = tb.fresh_local(ne_ty.clone());
        let t = c.hc_decode(n, &jt);
        let at = Expr::app(a.clone(), t.clone());
        let prod = c.fprod(n, c.prod_int(&tb, n, &s, &t));
        // ne_sym : Eq (Fin P) jS jt → False := fun e => ne (Eq.symm e).
        let ne_sym = {
            let mut eb = EnvDeclBuilder::child_of(&tb);
            let eq_st = c.eq_fin_pow(n, js, &jt);
            let (e_id, e) = eb.fresh_local(eq_st.clone());
            let e_symm = Expr::apps(
                c.eq_symm.clone(),
                [fin_p.clone(), js.clone(), jt.clone(), e],
            );
            let body = Expr::app(ne.clone(), e_symm);
            eb.finish_child(eb.mk_lam(e_id, BinderInfo::Default, eq_st, body))
        };
        // off : Π(hcDec jS, hcDec jt) = 0   (prod_offdiag_eq_zero n jS jt ne_sym).
        let off = Expr::apps(
            c.prod_offdiag.clone(),
            [n.clone(), js.clone(), jt.clone(), ne_sym],
        );
        let coef = c.mul(as_.clone(), at.clone());
        let mz = Expr::app(c.rat_mul_zero(), coef.clone());
        let cg = c.mul_left_congr(&tb, &coef, prod.clone(), c.rat_zero(), off);
        let lhs = c.mul(coef.clone(), prod);
        let midd = c.mul(coef, c.rat_zero());
        let proof = c.trans(lhs, midd, c.rat_zero(), cg, mz);
        let lam = tb.mk_lam(ne_id, BinderInfo::Default, ne_ty, proof);
        tb.finish_child(tb.mk_lam(jt_id, BinderInfo::Default, fin_p.clone(), lam))
    };

    // collapse : Fin.sum P f = f jS.
    let collapse = Expr::apps(
        c.fin_sum_diag_collapse.clone(),
        [pp.clone(), js.clone(), f, hyp],
    );

    // f jS = (a S·a S)·Π(S,S). Rewrite Π(S,S) → 2^n via prod_diag_eq_cube.
    let as_as = c.mul(as_.clone(), as_.clone());
    let prod_ss = c.fprod(n, c.prod_int(parent, n, &s, &s));
    let fjs = c.mul(as_as.clone(), prod_ss.clone());
    let diag = Expr::apps(c.prod_diag_cube.clone(), [n.clone(), s.clone()]);
    let cube = c.cube(n);
    let leg_cube = c.mul_left_congr(parent, &as_as, prod_ss, cube.clone(), diag);
    let target = c.mul(as_as, cube);

    let t_sum = c.fsum(pp, build_e4_tsum_dec(c, parent, n, a, js));
    c.trans(t_sum, fjs, target, collapse, leg_cube)
}

/// `Fin.sum P f` body matching `e4_s_fn(hcDecode jS)` (the subsetSum-unfolded
/// T-sum at the decoded outer gate index).
fn build_e4_tsum_dec(
    c: &XCoreConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    a: &Expr,
    js: &Expr,
) -> Expr {
    let pp = c.pow2(n);
    let fin_p = c.fin_of(&pp);
    let s = c.hc_decode(n, js);
    let as_ = Expr::app(a.clone(), s.clone());
    let mut tb = EnvDeclBuilder::child_of(parent);
    let (jt_id, jt) = tb.fresh_local(fin_p.clone());
    let t = c.hc_decode(n, &jt);
    let at = Expr::app(a.clone(), t.clone());
    let prod = c.fprod(n, c.prod_int(&tb, n, &s, &t));
    let body = c.mul(c.mul(as_.clone(), at), prod);
    tb.finish_child(tb.mk_lam(jt_id, BinderInfo::Default, fin_p, body))
}

/// `fun (jS : Fin P) => g (hcDecode n jS)` — subsetSum↔Fin.sum bridge integrand.
fn dec_outer(c: &XCoreConsts, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_p = c.fin_of(&c.pow2(n));
    let (js_id, js) = b.fresh_local(fin_p.clone());
    let body = Expr::app(g.clone(), c.hc_decode(n, &js));
    b.finish_child(b.mk_lam(js_id, BinderInfo::Default, fin_p, body))
}

/// `fun S => cube·(a S·a S)` — the legF regroup integrand.
fn regroup_fn_e5(c: &XCoreConsts, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
    let mut sb = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = sb.fresh_local(hcp.clone());
    let as_ = Expr::app(a.clone(), s.clone());
    let body = c.mul(c.cube(n), c.mul(as_.clone(), as_));
    sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

fn xcore_chain(c: &XCoreConsts, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
    let hcp = c.hcpoint_of(n);

    let e0 = c.ssum(n, c.lhs_x_fn(parent, n, a));
    let e1 = c.ssum(n, c.e1_x_fn(parent, n, a));
    let e2 = c.ssum(n, c.e2_s_fn(parent, n, a));
    let e3 = c.ssum(n, c.e3_s_fn(parent, n, a));
    let e4 = c.ssum(n, c.e4_s_fn(parent, n, a));
    let e5 = c.ssum(n, c.e5_s_fn(parent, n, a));
    let rhs = c.mul(c.cube(n), c.ssum(n, c.a_sq_fn(parent, n, a)));

    // legA : e0 = e1   (subsetSum_sq_to_double n g_bundle).
    let leg_a = Expr::apps(
        c.subset_sum_sq_to_double.clone(),
        [n.clone(), c.g_bundle(parent, n, a)],
    );

    // legB : e1 = e2   (subsetSum_swap n F1).
    let leg_b = Expr::apps(
        c.subset_sum_swap.clone(),
        [n.clone(), c.f1_bundle(parent, n, a)],
    );

    // legC : e2 = e3   (subsetSum_congr over S of per-S subsetSum_swap F2s).
    let leg_c = {
        let h = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            // F2s x T = g S x · g T x
            let f2s = {
                let mut xb = EnvDeclBuilder::child_of(&sb);
                let (x_id, x) = xb.fresh_local(hcp.clone());
                let inner = {
                    let mut tb = EnvDeclBuilder::child_of(&xb);
                    let (t_id, t) = tb.fresh_local(hcp.clone());
                    let body = c.mul(c.g(n, a, &s, &x), c.g(n, a, &t, &x));
                    tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), body))
                };
                xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), inner))
            };
            let swap = Expr::apps(c.subset_sum_swap.clone(), [n.clone(), f2s]);
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), swap))
        };
        Expr::apps(
            c.subset_sum_congr.clone(),
            [
                n.clone(),
                c.e2_s_fn(parent, n, a),
                c.e3_s_fn(parent, n, a),
                h,
            ],
        )
    };

    // legD : e3 = e4   (subsetSum_congr over S of subsetSum_congr over T leg_d_st).
    let leg_d = {
        let h = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let before_t = {
                let mut tb = EnvDeclBuilder::child_of(&sb);
                let (t_id, t) = tb.fresh_local(hcp.clone());
                let x_sum = {
                    let mut xb = EnvDeclBuilder::child_of(&tb);
                    let (x_id, x) = xb.fresh_local(hcp.clone());
                    let body = c.mul(c.g(n, a, &s, &x), c.g(n, a, &t, &x));
                    let f =
                        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body));
                    c.ssum(n, f)
                };
                tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), x_sum))
            };
            let after_t = {
                let mut tb = EnvDeclBuilder::child_of(&sb);
                let (t_id, t) = tb.fresh_local(hcp.clone());
                let as_at = c.mul(
                    Expr::app(a.clone(), s.clone()),
                    Expr::app(a.clone(), t.clone()),
                );
                let prod = c.fprod(n, c.prod_int(&tb, n, &s, &t));
                let body = c.mul(as_at, prod);
                tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), body))
            };
            let h_t = {
                let mut tb = EnvDeclBuilder::child_of(&sb);
                let (t_id, t) = tb.fresh_local(hcp.clone());
                let pf = leg_d_st(c, &tb, n, a, &s, &t);
                tb.finish_child(tb.mk_lam(t_id, BinderInfo::Default, hcp.clone(), pf))
            };
            let inner = Expr::apps(
                c.subset_sum_congr.clone(),
                [n.clone(), before_t, after_t, h_t],
            );
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), inner))
        };
        Expr::apps(
            c.subset_sum_congr.clone(),
            [
                n.clone(),
                c.e3_s_fn(parent, n, a),
                c.e4_s_fn(parent, n, a),
                h,
            ],
        )
    };

    // legE : e4 = e5   (Fin.sum_congr P over the decoded outer gate index).
    let leg_e = {
        let before = dec_outer(c, parent, n, &c.e4_s_fn(parent, n, a));
        let after = dec_outer(c, parent, n, &c.e5_s_fn(parent, n, a));
        let h = {
            let mut jb = EnvDeclBuilder::child_of(parent);
            let fin_p = c.fin_of(&c.pow2(n));
            let (js_id, js) = jb.fresh_local(fin_p.clone());
            let pf = leg_e_js(c, &jb, n, a, &js);
            jb.finish_child(jb.mk_lam(js_id, BinderInfo::Default, fin_p, pf))
        };
        Expr::apps(c.fin_sum_congr(), [c.pow2(n), before, after, h])
    };

    // legF : e5 = cube · subsetSum n (a_sq)   (regroup mul_comm + subsetSum_smul).
    let leg_f = {
        let regroup_fn = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let as_ = Expr::app(a.clone(), s.clone());
            let body = c.mul(c.cube(n), c.mul(as_.clone(), as_));
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };
        let h_regroup = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let as_ = Expr::app(a.clone(), s.clone());
            let as_as = c.mul(as_.clone(), as_);
            let body = c.mul_comm(as_as, c.cube(n));
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };
        let leg_f1 = Expr::apps(
            c.subset_sum_congr.clone(),
            [n.clone(), c.e5_s_fn(parent, n, a), regroup_fn, h_regroup],
        );
        let leg_f2 = Expr::apps(
            c.subset_sum_smul.clone(),
            [n.clone(), c.cube(n), c.a_sq_fn(parent, n, a)],
        );
        let mid = c.ssum(n, regroup_fn_e5(c, parent, n, a));
        c.trans(e5.clone(), mid, rhs.clone(), leg_f1, leg_f2)
    };

    // Assemble: e0 = e1 = e2 = e3 = e4 = e5 = rhs.
    let t1 = c.trans(e0.clone(), e1.clone(), e2.clone(), leg_a, leg_b);
    let t2 = c.trans(e0.clone(), e2.clone(), e3.clone(), t1, leg_c);
    let t3 = c.trans(e0.clone(), e3.clone(), e4.clone(), t2, leg_d);
    let t4 = c.trans(e0.clone(), e4, e5.clone(), t3, leg_e);
    c.trans(e0, e5, rhs, t4, leg_f)
}
