// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by boolean_analysis_inversion_chain.rs — legA, legB, legD, legE and
// the top-level `inversion_chain`.

/// Leg A (per S): `(Σ_y b(y)·χ_S(y))·χ_S(x) = Σ_y χ_S(x)·(b(y)·χ_S(y))`.
///   step1: `mul_comm (Σ_y h) χ_S(x)`     :  (Σ_y h)·χ_S(x) = χ_S(x)·(Σ_y h);
///   step2: `Eq.symm (subsetSum_smul n χ_S(x) (fun y => b(y)·χ_S(y)))`
///                                         :  χ_S(x)·(Σ_y h) = Σ_y χ_S(x)·h.
fn leg_a_s(c: &InvConsts, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, x: &Expr, s: &Expr) -> Expr {
    let hcp = c.hcpoint_of(n);
    let chi_sx = c.chi_(n, s, x);
    // h_fn := fun y => b(y)·χ_S(y).
    let h_fn = {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let body = c.mul(Expr::app(b.clone(), y.clone()), c.chi_(n, s, &y));
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
    };
    let inner_sum = c.ssum(n, h_fn.clone());

    // lhs = inner_sum · χ_S(x).
    let lhs = c.mul(inner_sum.clone(), chi_sx.clone());
    // mid = χ_S(x) · inner_sum.
    let mid = c.mul(chi_sx.clone(), inner_sum.clone());
    // rhs = Σ_y χ_S(x)·(b(y)·χ_S(y)).
    let scaled_fn = {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let h = c.mul(Expr::app(b.clone(), y.clone()), c.chi_(n, s, &y));
        let body = c.mul(chi_sx.clone(), h);
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
    };
    let rhs = c.ssum(n, scaled_fn);

    // step1 : lhs = mid.
    let step1 = c.mul_comm(inner_sum.clone(), chi_sx.clone());
    // smul n χ_S(x) h_fn : Σ_y χ_S(x)·h = χ_S(x)·Σ_y h   (i.e. rhs = mid).
    let smul = Expr::apps(c.subset_sum_smul.clone(), [n.clone(), chi_sx.clone(), h_fn]);
    // step2 : mid = rhs  (Eq.symm smul).
    let step2 = c.symm(rhs.clone(), mid.clone(), smul);
    c.trans(lhs, mid, rhs, step1, step2)
}

/// Leg D (diagonal collapse, at the DECODED outer index `jx`):
///   `Σ_y b(y)·Π(x,y) = b(x)·2^n`,  where `x = hcDecode n jx`.
///
/// `subsetSum n (e3_y)` δ-unfolds to `Fin.sum P (fun jy => f jy)` with
/// `f jy = b(hcDec jy)·Π(x, hcDec jy)`.
///   • off-diagonal `jy ≠ jx`: `Π(x, hcDec jy) = Π(hcDec jx, hcDec jy) = 0`
///     (`prod_offdiag_eq_zero n jx jy`), so `f jy = b(·)·0 = 0` (`Rat.mul_zero`);
///   • `Fin.sum_diag_collapse P jx f` lands `f jx = b(x)·Π(x,x)`;
///   • `prod_diag_eq_cube n x : Π(x,x) = 2^n`, lifted by `congrArg (b(x)·)`.
fn leg_d_jx(c: &InvConsts, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, jx: &Expr) -> Expr {
    let pp = c.pow2(n);
    let fin_p = c.fin_of(&pp);
    let x = c.hc_decode(n, jx);
    let bx = Expr::app(b.clone(), x.clone());

    // f : Fin P → Rat := fun jy => b(hcDec jy)·Π(x, hcDec jy).
    let f = {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let (jy_id, jy) = yb.fresh_local(fin_p.clone());
        let y = c.hc_decode(n, &jy);
        let by = Expr::app(b.clone(), y.clone());
        let prod = c.fprod(n, c.prod_int(&yb, n, &x, &y));
        let body = c.mul(by, prod);
        yb.finish_child(yb.mk_lam(jy_id, BinderInfo::Default, fin_p.clone(), body))
    };

    // hyp H : ∀ jy, (Eq (Fin P) jy jx → False) → f jy = 0.
    let hyp = {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let (jy_id, jy) = yb.fresh_local(fin_p.clone());
        let ne_ty = Expr::pi(
            BinderInfo::Default,
            c.eq_fin_pow(n, &jy, jx),
            c.false_c.clone(),
        );
        let (ne_id, ne) = yb.fresh_local(ne_ty.clone());
        let y = c.hc_decode(n, &jy);
        let by = Expr::app(b.clone(), y.clone());
        let prod = c.fprod(n, c.prod_int(&yb, n, &x, &y));
        // ne_sym : Eq (Fin P) jx jy → False := fun e => ne (Eq.symm e).
        let ne_sym = {
            let mut eb = EnvDeclBuilder::child_of(&yb);
            let eq_xy = c.eq_fin_pow(n, jx, &jy);
            let (e_id, e) = eb.fresh_local(eq_xy.clone());
            let e_symm = Expr::apps(
                c.eq_symm.clone(),
                [fin_p.clone(), jx.clone(), jy.clone(), e],
            );
            let body = Expr::app(ne.clone(), e_symm);
            eb.finish_child(eb.mk_lam(e_id, BinderInfo::Default, eq_xy, body))
        };
        // off : Π(hcDec jx, hcDec jy) = 0  (prod_offdiag_eq_zero n jx jy ne_sym).
        let off = Expr::apps(
            c.prod_offdiag.clone(),
            [n.clone(), jx.clone(), jy.clone(), ne_sym],
        );
        // mul_zero (b y) : (b y)·0 = 0.
        let mz = Expr::app(c.rat_mul_zero.clone(), by.clone());
        // congrArg ((b y)·) off : (b y)·Π = (b y)·0.
        let cg = c.mul_left_congr(&yb, &by, prod.clone(), c.rat_zero.clone(), off);
        // f jy = (b y)·Π = (b y)·0 = 0.
        let lhs = c.mul(by.clone(), prod);
        let midd = c.mul(by, c.rat_zero.clone());
        let proof = c.trans(lhs, midd, c.rat_zero.clone(), cg, mz);
        let lam = yb.mk_lam(ne_id, BinderInfo::Default, ne_ty, proof);
        yb.finish_child(yb.mk_lam(jy_id, BinderInfo::Default, fin_p.clone(), lam))
    };

    // collapse : Fin.sum P f = f jx   (f jx = b(x)·Π(x,x), since hcDec jx = x).
    let collapse = Expr::apps(
        c.fin_sum_diag_collapse.clone(),
        [pp.clone(), jx.clone(), f, hyp],
    );

    // f jx = b(x)·Π(x,x). Rewrite Π(x,x) → 2^n via prod_diag_eq_cube.
    let prod_xx = c.fprod(n, c.prod_int(parent, n, &x, &x));
    let fjx = c.mul(bx.clone(), prod_xx.clone());
    let diag = Expr::apps(c.prod_diag_cube.clone(), [n.clone(), x.clone()]);
    let cube = c.cube(n);
    let leg_cube = c.mul_left_congr(parent, &bx, prod_xx, cube.clone(), diag);
    let target = c.mul(bx, cube);

    // Σ_y(...) = f jx = b(x)·2^n.
    let y_sum = c.fsum(pp, build_e3_ysum_dec(c, parent, n, b, jx));
    c.trans(y_sum, fjx, target, collapse, leg_cube)
}

/// `Fin.sum P f` body rebuilt to match `e3_y_fn(hcDecode jx)` after the
/// `subsetSum`-unfold at the decoded outer index.
fn build_e3_ysum_dec(
    c: &InvConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    b: &Expr,
    jx: &Expr,
) -> Expr {
    let pp = c.pow2(n);
    let fin_p = c.fin_of(&pp);
    let x = c.hc_decode(n, jx);
    let mut yb = EnvDeclBuilder::child_of(parent);
    let (jy_id, jy) = yb.fresh_local(fin_p.clone());
    let y = c.hc_decode(n, &jy);
    let by = Expr::app(b.clone(), y.clone());
    let prod = c.fprod(n, c.prod_int(&yb, n, &x, &y));
    let body = c.mul(by, prod);
    yb.finish_child(yb.mk_lam(jy_id, BinderInfo::Default, fin_p, body))
}

/// `fun (jy : Fin P) => g (hcDecode n jy)` — subsetSum↔Fin.sum bridge integrand.
fn dec_index(c: &InvConsts, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
    let mut bld = EnvDeclBuilder::child_of(parent);
    let fin_p = c.fin_of(&c.pow2(n));
    let (jy_id, jy) = bld.fresh_local(fin_p.clone());
    let body = Expr::app(g.clone(), c.hc_decode(n, &jy));
    bld.finish_child(bld.mk_lam(jy_id, BinderInfo::Default, fin_p, body))
}

fn inversion_chain(c: &InvConsts, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, jx: &Expr) -> Expr {
    let hcp = c.hcpoint_of(n);
    let x = c.hc_decode(n, jx);

    // endpoint expressions.
    let e0 = c.ssum(n, c.lhs_s_fn(parent, n, b, &x));
    let e1 = c.ssum(n, c.e1_s_fn(parent, n, b, &x));
    let e2 = c.ssum(n, c.e2_y_fn(parent, n, b, &x));
    let e3 = c.ssum(n, c.e3_y_fn(parent, n, b, &x));
    let e4 = c.ssum(n, c.e4_y_fn(parent, n, b));
    let bx = Expr::app(b.clone(), x.clone());
    let rhs = c.mul(c.cube(n), bx.clone());

    // legA : e0 = e1   (subsetSum_congr over S of the per-S leg_a_s).
    let leg_a = {
        let h = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let pf = leg_a_s(c, &sb, n, b, &x, &s);
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), pf))
        };
        Expr::apps(
            c.subset_sum_congr.clone(),
            [
                n.clone(),
                c.lhs_s_fn(parent, n, b, &x),
                c.e1_s_fn(parent, n, b, &x),
                h,
            ],
        )
    };

    // legB : e1 = e2   (subsetSum_swap n F).  F S y = χ_S(x)·(b(y)·χ_S(y)).
    let leg_b = {
        let big_f = {
            let mut sb = EnvDeclBuilder::child_of(parent);
            let (s_id, s) = sb.fresh_local(hcp.clone());
            let inner = {
                let mut yb = EnvDeclBuilder::child_of(&sb);
                let (y_id, y) = yb.fresh_local(hcp.clone());
                let by_chi = c.mul(Expr::app(b.clone(), y.clone()), c.chi_(n, &s, &y));
                let body = c.mul(c.chi_(n, &s, &x), by_chi);
                yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
            };
            sb.finish_child(sb.mk_lam(s_id, BinderInfo::Default, hcp.clone(), inner))
        };
        Expr::apps(c.subset_sum_swap.clone(), [n.clone(), big_f])
    };

    // legC : e2 = e3   (subsetSum_congr over y of leg_c_y).
    let leg_c = {
        let h = {
            let mut yb = EnvDeclBuilder::child_of(parent);
            let (y_id, y) = yb.fresh_local(hcp.clone());
            let pf = leg_c_y(c, &yb, n, b, &x, &y);
            yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), pf))
        };
        Expr::apps(
            c.subset_sum_congr.clone(),
            [
                n.clone(),
                c.e2_y_fn(parent, n, b, &x),
                c.e3_y_fn(parent, n, b, &x),
                h,
            ],
        )
    };

    // legD : e3 = e4'   where e4' = b(x)·2^n.  (Fin.sum_diag_collapse path; both
    // sides bridge through the decoded y-index.)  We prove `e3 = b(x)·2^n`
    // directly via leg_d_jx (its LHS `Fin.sum P (e3 decoded)` is def-eq to e3).
    let e4_prime = c.mul(bx.clone(), c.cube(n)); // b(x)·2^n
    let leg_d = leg_d_jx(c, parent, n, b, jx);

    // legE : b(x)·2^n = 2^n·b(x)   (mul_comm).
    let leg_e = c.mul_comm(bx.clone(), c.cube(n));

    // We don't actually traverse e4 (= subsetSum of e4_y) — leg_d collapses the
    // y-sum straight to the closed `b(x)·2^n`. Keep `e4` referenced to silence
    // the unused builder while documenting the intermediate shape.
    let _ = e4;

    // Assemble: e0 = e1 = e2 = e3 = b(x)·2^n = 2^n·b(x).
    let t1 = c.trans(e0.clone(), e1.clone(), e2.clone(), leg_a, leg_b);
    let t2 = c.trans(e0.clone(), e2.clone(), e3.clone(), t1, leg_c);
    let t3 = c.trans(e0.clone(), e3.clone(), e4_prime.clone(), t2, leg_d);
    let _ = dec_index;
    c.trans(e0, e4_prime, rhs, t3, leg_e)
}
