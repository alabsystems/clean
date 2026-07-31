// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Term builders for the σ'' complement bundle (2-cycle branch of the keystone).
// `include!`d into `boolean_analysis_fin_sigma_complement.rs`; shares its
// `SigmaComplementConsts` + imports. Each builder returns a closed Expr.

/// Shared binder prefix: introduces `k, σ, hinv, p, hcase` and returns the
/// builder plus those fvars and the common derived types.
struct CPrefix {
    b: EnvDeclBuilder,
    k: Expr,
    k_id: crate::expr::FVarId,
    sigma: Expr,
    sigma_id: crate::expr::FVarId,
    sigma_ty: Expr,
    hinv: Expr,
    hinv_id: crate::expr::FVarId,
    hinv_ty: Expr,
    p: Expr,
    p_id: crate::expr::FVarId,
    hcase: Expr,
    hcase_id: crate::expr::FVarId,
    hcase_ty: Expr,
    fin_succ: Expr,
    fin_k: Expr,
    nat: Expr,
}

fn make_cprefix(c: &SigmaComplementConsts) -> CPrefix {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let succ_k = c.succ(&k);
    let fin_succ = c.fin_of(&succ_k);
    let fin_k = c.fin_of(&k);

    let sigma_ty = Expr::pi(BinderInfo::Default, fin_succ.clone(), fin_succ.clone());
    let (sigma_id, sigma) = b.fresh_local(sigma_ty.clone());

    // hinv : ∀ x : Fin (k+1), σ (σ x) = x
    let hinv_ty = {
        let mut hb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = hb.fresh_local(fin_succ.clone());
        let ssx = Expr::app(sigma.clone(), Expr::app(sigma.clone(), x.clone()));
        let body = c.eq_fin(&succ_k, ssx, x.clone());
        hb.finish_child(hb.mk_pi(x_id, BinderInfo::Default, fin_succ.clone(), body))
    };
    let (hinv_id, hinv) = b.fresh_local(hinv_ty.clone());

    // p : Fin k
    let (p_id, p) = b.fresh_local(fin_k.clone());

    // hcase : σ (last k) = castSucc k p
    let hcase_ty = c.eq_fin(
        &succ_k,
        Expr::app(sigma.clone(), c.last(&k)),
        c.cast_succ(&k, &p),
    );
    let (hcase_id, hcase) = b.fresh_local(hcase_ty.clone());

    CPrefix {
        b,
        k,
        k_id,
        sigma,
        sigma_id,
        sigma_ty,
        hinv,
        hinv_id,
        hinv_ty,
        p,
        p_id,
        hcase,
        hcase_id,
        hcase_ty,
        fin_succ,
        fin_k,
        nat: c.nat.clone(),
    }
}

/// Close `k, σ, hinv, p, hcase` over `body`.
fn close_cprefix(pre: &CPrefix, body: Expr, pi: bool) -> Expr {
    let bind = |id, ty: Expr, inner: Expr| -> Expr {
        if pi {
            pre.b.mk_pi(id, BinderInfo::Default, ty, inner)
        } else {
            pre.b.mk_lam(id, BinderInfo::Default, ty, inner)
        }
    };
    let e = bind(pre.hcase_id, pre.hcase_ty.clone(), body);
    let e = bind(pre.p_id, pre.fin_k.clone(), e);
    let e = bind(pre.hinv_id, pre.hinv_ty.clone(), e);
    let e = bind(pre.sigma_id, pre.sigma_ty.clone(), e);
    let e = bind(pre.k_id, pre.nat.clone(), e);
    pre.b.finish(e)
}

// ===========================================================================
// Fin.sigmaComplement_partner :
//   (k)(σ)(hinv)(p)(hcase) → @Eq (Fin (k+1)) (σ (castSucc k p)) (last k)
//
//   hinv (last k) : σ (σ (last k)) = last k.
//   congrArg σ hcase : σ (σ (last k)) = σ (castSucc p).
//   So (congrArg σ hcase).symm.trans (hinv (last k)) :
//      σ (castSucc p) = σ (σ (last k)) = last k.
// ===========================================================================
fn partner_type(c: &SigmaComplementConsts) -> Expr {
    let pre = make_cprefix(c);
    let succ_k = c.succ(&pre.k);
    let lhs = Expr::app(pre.sigma.clone(), c.cast_succ(&pre.k, &pre.p));
    let concl = c.eq_fin(&succ_k, lhs, c.last(&pre.k));
    close_cprefix(&pre, concl, true)
}

fn partner_value(c: &SigmaComplementConsts) -> Expr {
    let pre = make_cprefix(c);
    let last_k = c.last(&pre.k);
    let sig_last = Expr::app(pre.sigma.clone(), last_k.clone()); // σ (last k)
    let cs_p = c.cast_succ(&pre.k, &pre.p); // castSucc p
    let sig_cs_p = Expr::app(pre.sigma.clone(), cs_p.clone()); // σ (castSucc p)
    let ss_last = Expr::app(pre.sigma.clone(), sig_last.clone()); // σ (σ (last k))

    // congrArg σ hcase : σ (σ (last k)) = σ (castSucc p)
    let cong = Expr::apps(
        c.congr_arg.clone(),
        [
            pre.fin_succ.clone(),
            pre.fin_succ.clone(),
            sig_last.clone(),
            cs_p.clone(),
            pre.sigma.clone(),
            pre.hcase.clone(),
        ],
    );
    // symm : σ (castSucc p) = σ (σ (last k))
    let cong_sym = Expr::apps(
        c.eq_symm.clone(),
        [
            pre.fin_succ.clone(),
            ss_last.clone(),
            sig_cs_p.clone(),
            cong,
        ],
    );
    // hinv (last k) : σ (σ (last k)) = last k
    let hinv_last = Expr::app(pre.hinv.clone(), last_k.clone());
    // trans : σ (castSucc p) = last k
    let body = Expr::apps(
        c.eq_trans.clone(),
        [
            pre.fin_succ.clone(),
            sig_cs_p,
            ss_last,
            last_k,
            cong_sym,
            hinv_last,
        ],
    );
    close_cprefix(&pre, body, false)
}

// ===========================================================================
// Fin.sigmaComplement_ne_last :
//   (k)(σ)(hinv)(p)(hcase)(j : Fin k)(hne : val j ≠ val p)
//     → @Eq (Fin (k+1)) (σ (castSucc k j)) (last k) → False
//
// If σ (castSucc j) = last, then σ (σ (castSucc j)) = σ (last) = castSucc p, but
// also σ (σ (castSucc j)) = castSucc j by hinv, so castSucc j = castSucc p, hence
// (castSucc_inj) j = p, hence val j = val p (congrArg val), contradicting hne.
// ===========================================================================
fn ne_last_type(c: &SigmaComplementConsts) -> Expr {
    let mut pre = make_cprefix(c);
    let succ_k = c.succ(&pre.k);
    let (j_id, j) = pre.b.fresh_local(pre.fin_k.clone());
    // hne : val j = val p → False
    let val_j = c.val(&pre.k, &j);
    let val_p = c.val(&pre.k, &pre.p);
    let eq_vjp = c.eq_nat(val_j, val_p);
    let hne_ty = Expr::pi(BinderInfo::Default, eq_vjp, c.false_c.clone());
    let (hne_id, _hne) = pre.b.fresh_local(hne_ty.clone());
    // e : σ (castSucc j) = last k
    let e_ty = c.eq_fin(
        &succ_k,
        Expr::app(pre.sigma.clone(), c.cast_succ(&pre.k, &j)),
        c.last(&pre.k),
    );
    let (e_id, _e) = pre.b.fresh_local(e_ty.clone());
    let body = pre
        .b
        .mk_pi(e_id, BinderInfo::Default, e_ty, c.false_c.clone());
    let body = pre.b.mk_pi(hne_id, BinderInfo::Default, hne_ty, body);
    let body = pre
        .b
        .mk_pi(j_id, BinderInfo::Default, pre.fin_k.clone(), body);
    close_cprefix(&pre, body, true)
}

fn ne_last_value(c: &SigmaComplementConsts) -> Expr {
    let mut pre = make_cprefix(c);
    let succ_k = c.succ(&pre.k);
    let (j_id, j) = pre.b.fresh_local(pre.fin_k.clone());
    let val_j = c.val(&pre.k, &j);
    let val_p = c.val(&pre.k, &pre.p);
    let eq_vjp = c.eq_nat(val_j.clone(), val_p.clone());
    let hne_ty = Expr::pi(BinderInfo::Default, eq_vjp.clone(), c.false_c.clone());
    let (hne_id, hne) = pre.b.fresh_local(hne_ty.clone());

    let cs_j = c.cast_succ(&pre.k, &j); // castSucc j
    let last_k = c.last(&pre.k);
    let e_ty = c.eq_fin(
        &succ_k,
        Expr::app(pre.sigma.clone(), cs_j.clone()),
        last_k.clone(),
    );
    let (e_id, e) = pre.b.fresh_local(e_ty.clone());

    let sig_cs_j = Expr::app(pre.sigma.clone(), cs_j.clone()); // σ (castSucc j)
    let sig_last = Expr::app(pre.sigma.clone(), last_k.clone()); // σ (last)
    let ss_cs_j = Expr::app(pre.sigma.clone(), sig_cs_j.clone()); // σ (σ (castSucc j))
    let cs_p = c.cast_succ(&pre.k, &pre.p); // castSucc p

    // congrArg σ e : σ (σ (castSucc j)) = σ (last k)
    let cong_e = Expr::apps(
        c.congr_arg.clone(),
        [
            pre.fin_succ.clone(),
            pre.fin_succ.clone(),
            sig_cs_j.clone(),
            last_k.clone(),
            pre.sigma.clone(),
            e.clone(),
        ],
    );
    // hinv (castSucc j) : σ (σ (castSucc j)) = castSucc j  → symm: castSucc j = σ(σ(castSucc j))
    let hinv_cs_j = Expr::app(pre.hinv.clone(), cs_j.clone());
    let hinv_cs_j_sym = Expr::apps(
        c.eq_symm.clone(),
        [
            pre.fin_succ.clone(),
            ss_cs_j.clone(),
            cs_j.clone(),
            hinv_cs_j,
        ],
    );
    // chain: castSucc j = σ(σ(castSucc j)) = σ(last) = castSucc p
    //   step1: castSucc j = σ(σ(castSucc j))   [hinv_cs_j_sym]
    //   step2: σ(σ(castSucc j)) = σ(last)       [cong_e]
    //   step3: σ(last) = castSucc p             [hcase]
    let ab = Expr::apps(
        c.eq_trans.clone(),
        [
            pre.fin_succ.clone(),
            cs_j.clone(),
            ss_cs_j.clone(),
            sig_last.clone(),
            hinv_cs_j_sym,
            cong_e,
        ],
    );
    let cs_j_eq_cs_p = Expr::apps(
        c.eq_trans.clone(),
        [
            pre.fin_succ.clone(),
            cs_j.clone(),
            sig_last.clone(),
            cs_p.clone(),
            ab,
            pre.hcase.clone(),
        ],
    );
    // Fin.castSucc_inj k j p cs_j_eq_cs_p : j = p
    let j_eq_p = Expr::apps(
        c.cast_succ_inj.clone(),
        [pre.k.clone(), j.clone(), pre.p.clone(), cs_j_eq_cs_p],
    );
    // congrArg (Fin.val k) j_eq_p : val j = val p
    let val_fn = Expr::app(c.fin_val.clone(), pre.k.clone()); // Fin.val k : Fin k → Nat
    let vj_eq_vp = Expr::apps(
        c.congr_arg.clone(),
        [
            pre.fin_k.clone(),
            c.nat.clone(),
            j.clone(),
            pre.p.clone(),
            val_fn,
            j_eq_p,
        ],
    );
    // hne vj_eq_vp : False
    let false_pf = Expr::app(hne.clone(), vj_eq_vp);

    let body = pre.b.mk_lam(e_id, BinderInfo::Default, e_ty, false_pf);
    let body = pre.b.mk_lam(hne_id, BinderInfo::Default, hne_ty, body);
    let body = pre
        .b
        .mk_lam(j_id, BinderInfo::Default, pre.fin_k.clone(), body);
    close_cprefix(&pre, body, false)
}

include!("boolean_analysis_fin_sigma_complement_build2.rs");
