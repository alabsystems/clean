// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// The `hc43_core_step` value chain (S1 LHS-split → S2 two-point → cross/close).
// `include!`d into `boolean_analysis_hc43_core_step_build.rs`. No new globals.

/// Build the `hc43_core_step` proof value:
/// `fun ρ h h_cm h_tp h_close m ih => <motive (m+1) body>`.
fn build_hc43_step_value(c: &Hc43StepConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (rho_id, rho) = b.fresh_local(c.rat());
    let h_ty = hyp_contract_ty(&c.o, &rho);
    let (h_id, h) = b.fresh_local(h_ty.clone());
    let hcm_ty = h_cm_ty(c);
    let (hcm_id, h_cm) = b.fresh_local(hcm_ty.clone());
    let htp_ty = h_tp_universal_ty(c, &b, &rho);
    let (htp_id, h_tp) = b.fresh_local(htp_ty.clone());
    let hclose_ty = h_close_ty(c, &b, &rho);
    let (hclose_id, h_close) = b.fresh_local(hclose_ty.clone());
    let (m_id, m) = b.fresh_local(c.nat());
    let mot_m = step_motive_body(c, &b, &rho, &m);
    let (ih_id, ih) = b.fresh_local(mot_m.clone());

    // The motive (m+1) is a Π-telescope over (F s r hs hr hr1 hrecon hnn h4n).
    let sm = c.succ(&m);
    let fn_ty = c.f_type(&sm);
    let (f_id, f) = b.fresh_local(fn_ty.clone());
    let (s_id, s) = b.fresh_local(fn_ty.clone());
    let (r_id, r) = b.fresh_local(fn_ty.clone());
    let hs_ty = forall_scale_nonneg_ty(&c.o, &b, &sm, &s);
    let (hs_id, hs) = b.fresh_local(hs_ty.clone());
    let hr_ty = forall_r_nonneg_ty(&c.o, &b, &sm, &r);
    let (hr_id, hr) = b.fresh_local(hr_ty.clone());
    let hr1_ty = forall_r_lt_one_ty(&c.o, &b, &sm, &r);
    let (hr1_id, hr1) = b.fresh_local(hr1_ty.clone());
    let hrecon_ty = forall_recon_ty(&c.o, &b, &sm, &f, &s, &r);
    let (hrecon_id, hrecon) = b.fresh_local(hrecon_ty.clone());
    let hnn_ty = forall_lhs_nonneg_ty(&c.o, &b, &rho, &sm, &f);
    let (hnn_id, hnn) = b.fresh_local(hnn_ty.clone());
    let h4n_ty = c.rle(&c.rat_zero(), &c.pow4n(&sm));
    let (h4n_id, h4n) = b.fresh_local(h4n_ty.clone());

    let ctx = StepCtx {
        rho: rho.clone(),
        h: h.clone(),
        h_cm: h_cm.clone(),
        h_tp: h_tp.clone(),
        h_close: h_close.clone(),
        m: m.clone(),
        ih: ih.clone(),
        f: f.clone(),
        s: s.clone(),
        r: r.clone(),
        hs: hs.clone(),
        hr: hr.clone(),
        hr1: hr1.clone(),
        hrecon: hrecon.clone(),
        hnn: hnn.clone(),
        h4n: h4n.clone(),
    };

    let body = build_step_concl(c, &b, &ctx);

    // Re-abstract the motive (m+1) telescope.
    let e = b.mk_lam(h4n_id, BinderInfo::Default, h4n_ty, body);
    let e = b.mk_lam(hnn_id, BinderInfo::Default, hnn_ty, e);
    let e = b.mk_lam(hrecon_id, BinderInfo::Default, hrecon_ty, e);
    let e = b.mk_lam(hr1_id, BinderInfo::Default, hr1_ty, e);
    let e = b.mk_lam(hr_id, BinderInfo::Default, hr_ty, e);
    let e = b.mk_lam(hs_id, BinderInfo::Default, hs_ty, e);
    let e = b.mk_lam(r_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_lam(s_id, BinderInfo::Default, fn_ty.clone(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, fn_ty, e);
    // outer step binders.
    let e = b.mk_lam(ih_id, BinderInfo::Default, mot_m, e);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat(), e);
    let e = b.mk_lam(hclose_id, BinderInfo::Default, hclose_ty, e);
    let e = b.mk_lam(htp_id, BinderInfo::Default, htp_ty, e);
    let e = b.mk_lam(hcm_id, BinderInfo::Default, hcm_ty, e);
    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, e);
    b.finish(b.mk_lam(rho_id, BinderInfo::Default, c.rat(), e))
}

/// The bound locals of the `motive (m+1)` body, threaded into the chain.
struct StepCtx {
    rho: Expr,
    #[allow(dead_code)]
    h: Expr,
    #[allow(dead_code)]
    h_cm: Expr,
    #[allow(dead_code)]
    h_tp: Expr,
    h_close: Expr,
    m: Expr,
    #[allow(dead_code)]
    ih: Expr,
    f: Expr,
    s: Expr,
    r: Expr,
    hs: Expr,
    #[allow(dead_code)]
    hr: Expr,
    #[allow(dead_code)]
    hr1: Expr,
    #[allow(dead_code)]
    hrecon: Expr,
    hnn: Expr,
    h4n: Expr,
}

include!("boolean_analysis_hc43_core_step_chain2.rs");
