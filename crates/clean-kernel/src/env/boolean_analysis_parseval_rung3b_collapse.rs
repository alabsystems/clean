// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by ..._rung3b_chain.rs — the diagonal collapse leg (E), the final
// smul leg (F), and the top-level `parseval_chain`.

impl CoreConsts {
    fn fin_sum_congr(&self) -> Expr {
        Expr::const_(Name::from_string("Fin.sum_congr"), vec![])
    }
    fn rat_mul_zero(&self) -> Expr {
        Expr::const_(Name::from_string("Rat.mul_zero"), vec![])
    }
    fn rat_zero(&self) -> Expr {
        Expr::const_(Name::from_string("Rat.zero"), vec![])
    }
}

/// Leg E (the diagonal collapse, per OUTER decoded index `jx`):
///   `Σ_y (a x·a y)·Π(x,y) = (a x·a x)·2^n`,  where `x = hcDecode n jx`.
///
/// `subsetSum n h δ`-unfolds to `Fin.sum P (fun jy => h (hcDecode n jy))`, so
/// the `y`-sum is `Fin.sum P f` with `f jy = (a x·a(hcDec jy))·Π(x, hcDec jy)`.
///   • off-diagonal `jy ≠ jx`: `Π(x, hcDec jy) = Π(hcDec jx, hcDec jy) = 0`
///     (`prod_offdiag_eq_zero n jx jy`, condition `jx ≠ jy` from `Eq.symm`),
///     so `f jy = (…)·0 = 0` (`Rat.mul_zero`);
///   • `Fin.sum_diag_collapse P jx f` lands `f jx = (a x·a x)·Π(x,x)`;
///   • `prod_diag_eq_cube n x : Π(x,x) = 2^n/1`, lifted by `congrArg ((a x·a x)·)`.
fn leg_e_jx(c: &CoreConsts, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, jx: &Expr) -> Expr {
    let pp = c.pow2(n);
    let fin_p = c.fin_of(&pp);
    let x = c.hc_decode(n, jx); // the concrete cube point
    let ax = Expr::app(a.clone(), x.clone());

    // f : Fin P → Rat := fun jy => (a x·a(hcDec jy))·Π(x, hcDec jy).
    let f = {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let (jy_id, jy) = yb.fresh_local(fin_p.clone());
        let y = c.hc_decode(n, &jy);
        let ay = Expr::app(a.clone(), y.clone());
        let prod = c.fprod(n, c.prod_int(&yb, n, &x, &y));
        let body = c.mul(c.mul(ax.clone(), ay), prod);
        yb.finish_child(yb.mk_lam(jy_id, BinderInfo::Default, fin_p.clone(), body))
    };

    // hypothesis H : ∀ jy, (Eq (Fin P) jy jx → False) → f jy = 0.
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
        let ay = Expr::app(a.clone(), y.clone());
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
        // off : Π(hcDec jx, hcDec jy) = 0   (prod_offdiag_eq_zero n jx jy ne_sym).
        let off = Expr::apps(
            c.prod_offdiag.clone(),
            [n.clone(), jx.clone(), jy.clone(), ne_sym],
        );
        // mul_zero (a x·a y) : (a x·a y)·0 = 0.
        let coef = c.mul(ax.clone(), ay.clone());
        let mz = Expr::app(c.rat_mul_zero(), coef.clone());
        // congrArg ((a x·a y)·) off : (a x·a y)·Π = (a x·a y)·0.
        let cg = c.mul_left_congr(&yb, &coef, prod.clone(), c.rat_zero(), off);
        // f jy = (a x·a y)·0 = 0.
        let lhs = c.mul(coef.clone(), prod);
        let midd = c.mul(coef, c.rat_zero());
        let proof = c.trans(lhs, midd, c.rat_zero(), cg, mz);
        let lam = yb.mk_lam(ne_id, BinderInfo::Default, ne_ty, proof);
        yb.finish_child(yb.mk_lam(jy_id, BinderInfo::Default, fin_p.clone(), lam))
    };

    // collapse : Fin.sum P f = f jx
    //   f jx = (a x·a x)·Π(x,x)   (since hcDec jx = x).
    let collapse = Expr::apps(
        c.fin_sum_diag_collapse.clone(),
        [pp.clone(), jx.clone(), f, hyp],
    );

    // f jx = (a x·a x)·Π(x,x). Rewrite Π(x,x) → 2^n via prod_diag_eq_cube.
    let ax_ax = c.mul(ax.clone(), ax.clone());
    let prod_xx = c.fprod(n, c.prod_int(parent, n, &x, &x));
    let fjx = c.mul(ax_ax.clone(), prod_xx.clone());
    let diag = Expr::apps(c.prod_diag_cube.clone(), [n.clone(), x.clone()]);
    let cube = c.cube(n);
    let leg_cube = c.mul_left_congr(parent, &ax_ax, prod_xx, cube.clone(), diag);
    let target = c.mul(ax_ax, cube);

    // Σ_y(...) = f jx = (a x·a x)·2^n.
    let y_sum = c.fsum(pp, build_e4_ysum_dec(c, parent, n, a, jx));
    c.trans(y_sum, fjx, target, collapse, leg_cube)
}

/// `Fin.sum P f` body rebuilt to match `e4_x_fn(hcDecode jx)` exactly (the
/// `subsetSum`-unfolded y-sum at the decoded outer index).
fn build_e4_ysum_dec(
    c: &CoreConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    a: &Expr,
    jx: &Expr,
) -> Expr {
    let pp = c.pow2(n);
    let fin_p = c.fin_of(&pp);
    let x = c.hc_decode(n, jx);
    let ax = Expr::app(a.clone(), x.clone());
    let mut yb = EnvDeclBuilder::child_of(parent);
    let (jy_id, jy) = yb.fresh_local(fin_p.clone());
    let y = c.hc_decode(n, &jy);
    let ay = Expr::app(a.clone(), y.clone());
    let prod = c.fprod(n, c.prod_int(&yb, n, &x, &y));
    let body = c.mul(c.mul(ax.clone(), ay), prod);
    yb.finish_child(yb.mk_lam(jy_id, BinderInfo::Default, fin_p, body))
}

include!("boolean_analysis_parseval_rung3b_top.rs");
