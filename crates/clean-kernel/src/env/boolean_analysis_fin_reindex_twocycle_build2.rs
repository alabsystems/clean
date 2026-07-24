// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Term builders for `Fin.sum_reindex_twocycle_step` (the 2-cycle inductive
// step). `include!`d (transitively) into the module owning `TwoCycleConsts`.

/// Shared prefix `(k0, σ, hinv, p, hcase, ih)` with derived sizes and the IH
/// type (at size `k = k0+1`).
struct TCPrefix {
    b: EnvDeclBuilder,
    k0: Expr,
    k0_id: crate::expr::FVarId,
    k: Expr, // k0+1
    m: Expr, // k0+2
    sigma: Expr,
    sigma_id: crate::expr::FVarId,
    sigma_ty: Expr,
    hinv: Expr,
    hinv_id: crate::expr::FVarId,
    hinv_ty: Expr,
    p: Expr,
    p_id: crate::expr::FVarId,
    fin_k: Expr,
    hcase: Expr,
    hcase_id: crate::expr::FVarId,
    hcase_ty: Expr,
    ih: Expr,
    ih_id: crate::expr::FVarId,
    ih_ty: Expr,
    fin_m: Expr,
    nat: Expr,
}

/// IH type at size `k`: `∀ (τ : Fin k → Fin k), (∀ j, τ (τ j) = j)
///   → ∀ G, Fin.sum k (fun j => G (τ j)) = Fin.sum k G`.
fn ih_type(c: &TwoCycleConsts, parent: &EnvDeclBuilder, k: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let fin_k = c.fin_of(k);
    let tau_ty = Expr::pi(BinderInfo::Default, fin_k.clone(), fin_k.clone());
    let (tau_id, tau) = d.fresh_local(tau_ty.clone());
    let hinv = {
        let mut e = EnvDeclBuilder::child_of(&d);
        let (j_id, j) = e.fresh_local(fin_k.clone());
        let ttj = Expr::app(tau.clone(), Expr::app(tau.clone(), j.clone()));
        let body = c.eq_fin(k, ttj, j.clone());
        e.finish_child(e.mk_pi(j_id, BinderInfo::Default, fin_k.clone(), body))
    };
    let (hinv_id, _hinv) = d.fresh_local(hinv.clone());
    let g_ty = c.fin_to_rat(k);
    let (g_id, g) = d.fresh_local(g_ty.clone());
    let reindexed = {
        let mut e = EnvDeclBuilder::child_of(&d);
        let (j_id, j) = e.fresh_local(fin_k.clone());
        let body = Expr::app(g.clone(), Expr::app(tau.clone(), j.clone()));
        e.finish_child(e.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
    };
    let concl = c.eq_rat(c.sum(k, &reindexed), c.sum(k, &g));
    let r = d.mk_pi(g_id, BinderInfo::Default, g_ty, concl);
    let r = d.mk_pi(hinv_id, BinderInfo::Default, hinv, r);
    d.finish_child(d.mk_pi(tau_id, BinderInfo::Default, tau_ty, r))
}

fn make_tc_prefix(c: &TwoCycleConsts) -> TCPrefix {
    let mut b = EnvDeclBuilder::new();
    let (k0_id, k0) = b.fresh_local(c.nat.clone());
    let k = c.succ(&k0); // k0+1
    let m = c.succ(&k); // k0+2
    let fin_m = c.fin_of(&m);
    let fin_k = c.fin_of(&k);

    let sigma_ty = Expr::pi(BinderInfo::Default, fin_m.clone(), fin_m.clone());
    let (sigma_id, sigma) = b.fresh_local(sigma_ty.clone());

    let hinv_ty = {
        let mut hb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = hb.fresh_local(fin_m.clone());
        let ssx = Expr::app(sigma.clone(), Expr::app(sigma.clone(), x.clone()));
        let body = c.eq_fin(&m, ssx, x.clone());
        hb.finish_child(hb.mk_pi(x_id, BinderInfo::Default, fin_m.clone(), body))
    };
    let (hinv_id, hinv) = b.fresh_local(hinv_ty.clone());

    let (p_id, p) = b.fresh_local(fin_k.clone());

    // hcase : σ (last k) = castSucc k p
    let hcase_ty = c.eq_fin(
        &m,
        Expr::app(sigma.clone(), c.last(&k)),
        c.cast_succ(&k, &p),
    );
    let (hcase_id, hcase) = b.fresh_local(hcase_ty.clone());

    let ih_ty = ih_type(c, &b, &k);
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    TCPrefix {
        b,
        k0,
        k0_id,
        k,
        m,
        sigma,
        sigma_id,
        sigma_ty,
        hinv,
        hinv_id,
        hinv_ty,
        p,
        p_id,
        fin_k,
        hcase,
        hcase_id,
        hcase_ty,
        ih,
        ih_id,
        ih_ty,
        fin_m,
        nat: c.nat.clone(),
    }
}

fn close_tc_prefix(pre: &TCPrefix, body: Expr, pi: bool) -> Expr {
    let bind = |id, ty: Expr, inner: Expr| -> Expr {
        if pi {
            pre.b.mk_pi(id, BinderInfo::Default, ty, inner)
        } else {
            pre.b.mk_lam(id, BinderInfo::Default, ty, inner)
        }
    };
    let e = bind(pre.ih_id, pre.ih_ty.clone(), body);
    let e = bind(pre.hcase_id, pre.hcase_ty.clone(), e);
    let e = bind(pre.p_id, pre.fin_k.clone(), e);
    let e = bind(pre.hinv_id, pre.hinv_ty.clone(), e);
    let e = bind(pre.sigma_id, pre.sigma_ty.clone(), e);
    let e = bind(pre.k0_id, pre.nat.clone(), e);
    pre.b.finish(e)
}

fn twocycle_step_type(c: &TwoCycleConsts) -> Expr {
    let mut pre = make_tc_prefix(c);
    let f_ty = c.fin_to_rat(&pre.m);
    let (f_id, f) = pre.b.fresh_local(f_ty.clone());
    let reindexed = {
        let mut d = EnvDeclBuilder::child_of(&pre.b);
        let (jx_id, jx) = d.fresh_local(pre.fin_m.clone());
        let body = Expr::app(f.clone(), Expr::app(pre.sigma.clone(), jx.clone()));
        d.finish_child(d.mk_lam(jx_id, BinderInfo::Default, pre.fin_m.clone(), body))
    };
    let concl = c.eq_rat(c.sum(&pre.m, &reindexed), c.sum(&pre.m, &f));
    let body = pre.b.mk_pi(f_id, BinderInfo::Default, f_ty, concl);
    close_tc_prefix(&pre, body, true)
}

include!("boolean_analysis_fin_reindex_twocycle_build3.rs");
