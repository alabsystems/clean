// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// PER-COORDINATE dual-HC EQUALITY builders (eL / m_eq / eR). `include!`d into
// `boolean_analysis_kkl_dualhc_percoord_build.rs`. Regular `//` comments only.

/// eL : `(D·D)·(Wn·Wn) = W·W`, where `Wn = W·Dinv`, given `dwd_cancel : D·Dinv = 1`.
fn build_e_l(
    c: &PerCoordConsts,
    parent: &EnvDeclBuilder,
    big_d: &Expr,
    d_inv: &Expr,
    w: &Expr,
    w_norm: &Expr,  // = W·Dinv
    d_cancel: Expr, // D·Dinv = 1
) -> Expr {
    let d = big_d;
    let wn = w_norm;
    // dwd : D·Wn = W   (D·(W·Dinv) = W).
    let dinv_w = c.mul(d_inv.clone(), w.clone()); // Dinv·W
    let d_dinv = c.mul(d.clone(), d_inv.clone()); // D·Dinv
    let one_w = c.mul(c.rat_one.clone(), w.clone());
    let d_wn = c.mul(d.clone(), wn.clone()); // D·(W·Dinv)
    let d_dinvw = c.mul(d.clone(), dinv_w.clone()); // D·(Dinv·W)
    let d_dinv_w = c.mul(d_dinv.clone(), w.clone()); // (D·Dinv)·W
    let s1 = c.congr_l(
        parent,
        d,
        wn.clone(),
        dinv_w.clone(),
        c.comm(w.clone(), d_inv.clone()),
    );
    // assoc D Dinv W : (D·Dinv)·W = D·(Dinv·W) ; symm → D·(Dinv·W) = (D·Dinv)·W.
    let s2 = c.symm(
        d_dinv_w.clone(),
        d_dinvw.clone(),
        c.assoc(d.clone(), d_inv.clone(), w.clone()),
    ); // D·(Dinv·W) = (D·Dinv)·W
    let s3 = c.congr_r(parent, w, d_dinv.clone(), c.rat_one.clone(), d_cancel);
    let s4 = c.one_mul_at(w.clone());
    let dwd = {
        let ch = c.trans(d_wn.clone(), d_dinvw.clone(), d_dinv_w.clone(), s1, s2);
        let ch = c.trans(d_wn.clone(), d_dinv_w.clone(), one_w.clone(), ch, s3);
        c.trans(d_wn.clone(), one_w, w.clone(), ch, s4)
    };

    // regroup : (D·D)·(Wn·Wn) = (D·Wn)·(D·Wn).
    let dd = c.mul(d.clone(), d.clone());
    let wnwn = c.mul(wn.clone(), wn.clone());
    let dd_wnwn = c.mul(dd.clone(), wnwn.clone());
    let d_wnwn = c.mul(d.clone(), wnwn.clone()); // D·(Wn·Wn)
    let dwn_wn = c.mul(d_wn.clone(), wn.clone()); // (D·Wn)·Wn
    let wnd_wn = c.mul(c.mul(wn.clone(), d.clone()), wn.clone()); // (Wn·D)·Wn
    let wn_dwn = c.mul(wn.clone(), d_wn.clone()); // Wn·(D·Wn)
    let dwn_dwn = c.mul(d_wn.clone(), d_wn.clone()); // (D·Wn)·(D·Wn)

    let d_d_wnwn = c.mul(d.clone(), d_wnwn.clone()); // D·(D·(Wn·Wn))
    let r1 = c.assoc(d.clone(), d.clone(), wnwn.clone()); // (D·D)·(Wn·Wn) = D·(D·(Wn·Wn))
    let r2 = c.congr_l(
        parent,
        d,
        d_wnwn.clone(),
        dwn_wn.clone(),
        c.symm(
            d_wn_wn_assoc_lhs(c, d, wn),
            d_wnwn.clone(),
            c.assoc(d.clone(), wn.clone(), wn.clone()),
        ),
    ); // D·(D·(Wn·Wn)) = D·((D·Wn)·Wn)
    let d_dwn_wn = c.mul(d.clone(), dwn_wn.clone());
    let d_wnd_wn = c.mul(d.clone(), wnd_wn.clone());
    let r3 = c.congr_l(
        parent,
        d,
        dwn_wn.clone(),
        wnd_wn.clone(),
        c.congr_r(
            parent,
            wn,
            d_wn.clone(),
            c.mul(wn.clone(), d.clone()),
            c.comm(d.clone(), wn.clone()),
        ),
    ); // D·((D·Wn)·Wn) = D·((Wn·D)·Wn)
    let d_wn_dwn = c.mul(d.clone(), wn_dwn.clone());
    let r4 = c.congr_l(
        parent,
        d,
        wnd_wn.clone(),
        wn_dwn.clone(),
        c.assoc(wn.clone(), d.clone(), wn.clone()),
    ); // D·((Wn·D)·Wn) = D·(Wn·(D·Wn))
    let r5 = c.assoc(d.clone(), wn.clone(), d_wn.clone()); // (D·Wn)·(D·Wn) = D·(Wn·(D·Wn))
    let r5 = c.symm(dwn_dwn.clone(), d_wn_dwn.clone(), r5); // D·(Wn·(D·Wn)) = (D·Wn)·(D·Wn)

    // (D·Wn)·(D·Wn) = W·W via dwd.
    let w_dwn = c.mul(w.clone(), d_wn.clone());
    let ww = c.mul(w.clone(), w.clone());
    let c1 = c.congr_r(parent, &d_wn, d_wn.clone(), w.clone(), dwd.clone()); // (D·Wn)·(D·Wn)=W·(D·Wn)
    let c2 = c.congr_l(parent, w, d_wn.clone(), w.clone(), dwd); // W·(D·Wn)=W·W

    // chain it all : (D·D)·(Wn·Wn) → ... → W·W.
    let ch = c.trans(dd_wnwn.clone(), d_d_wnwn.clone(), d_dwn_wn.clone(), r1, r2);
    let ch = c.trans(dd_wnwn.clone(), d_dwn_wn.clone(), d_wnd_wn.clone(), ch, r3);
    let ch = c.trans(dd_wnwn.clone(), d_wnd_wn.clone(), d_wn_dwn.clone(), ch, r4);
    let ch = c.trans(dd_wnwn.clone(), d_wn_dwn.clone(), dwn_dwn.clone(), ch, r5);
    let ch = c.trans(dd_wnwn.clone(), dwn_dwn.clone(), w_dwn.clone(), ch, c1);
    c.trans(dd_wnwn, w_dwn, ww, ch, c2)
}

// helper: the LHS of `assoc D Wn Wn` is `(D·Wn)·Wn`; we need its expression to
// state the symm. (D·Wn)·Wn.
fn d_wn_wn_assoc_lhs(c: &PerCoordConsts, d: &Expr, wn: &Expr) -> Expr {
    c.mul(c.mul(d.clone(), wn.clone()), wn.clone())
}

/// m_eq : `m = pow2n·Inf` from `h_m : m·pow2n = (pow2n·pow2n)·Inf` and
/// `p2_cancel : pow2n·inv pow2n = 1`. (Reusable; currently exercised by the
/// standalone `dualhc_m_cancel` smoke path — the main per-coord assembly threads
/// the measure identity as a hypothesis, see the module report.)
#[allow(dead_code)]
fn build_m_eq(
    c: &PerCoordConsts,
    parent: &EnvDeclBuilder,
    m: &Expr,
    pow2n: &Expr,
    inf: &Expr,
    h_m: Expr,
    p2_cancel: Expr, // p·inv p = 1
) -> Expr {
    let p = pow2n;
    let pinv = c.inv(p.clone());
    let pp = c.mul(p.clone(), p.clone()); // p·p
    let pp_inf = c.mul(pp.clone(), inf.clone()); // (p·p)·Inf
    let mp = c.mul(m.clone(), p.clone()); // m·p

    // lhs_eq : (m·p)·pinv = m.
    let mp_pinv = c.mul(mp.clone(), pinv.clone());
    let p_pinv = c.mul(p.clone(), pinv.clone());
    let m_ppinv = c.mul(m.clone(), p_pinv.clone());
    let m_one = c.mul(m.clone(), c.rat_one.clone());
    let a1 = c.assoc(m.clone(), p.clone(), pinv.clone()); // (m·p)·pinv = m·(p·pinv)
    let a2 = c.congr_l(
        parent,
        m,
        p_pinv.clone(),
        c.rat_one.clone(),
        p2_cancel.clone(),
    );
    let a3 = c.mul_one_at(m.clone());
    let lhs_eq = {
        let ch = c.trans(mp_pinv.clone(), m_ppinv.clone(), m_one.clone(), a1, a2);
        c.trans(mp_pinv.clone(), m_one, m.clone(), ch, a3)
    };

    // rhs_eq : ((p·p)·Inf)·pinv = p·Inf.
    let ppinf_pinv = c.mul(pp_inf.clone(), pinv.clone());
    let inf_pinv = c.mul(inf.clone(), pinv.clone());
    let pinv_inf = c.mul(pinv.clone(), inf.clone());
    let pp_infpinv = c.mul(pp.clone(), inf_pinv.clone());
    let pp_pinvinf = c.mul(pp.clone(), pinv_inf.clone());
    let pppinv = c.mul(pp.clone(), pinv.clone()); // (p·p)·pinv
    let pppinv_inf = c.mul(pppinv.clone(), inf.clone());
    let p_ppinv = c.mul(p.clone(), p_pinv.clone()); // p·(p·pinv)
    let p_ppinv_inf = c.mul(p_ppinv.clone(), inf.clone());
    let p_one = c.mul(p.clone(), c.rat_one.clone());
    let p_one_inf = c.mul(p_one.clone(), inf.clone());
    let p_inf = c.mul(p.clone(), inf.clone());

    let b1 = c.assoc(pp.clone(), inf.clone(), pinv.clone()); // ((p·p)·Inf)·pinv = (p·p)·(Inf·pinv)
    let b2 = c.congr_l(
        parent,
        &pp,
        inf_pinv.clone(),
        pinv_inf.clone(),
        c.comm(inf.clone(), pinv.clone()),
    );
    // assoc (p·p) pinv inf : ((p·p)·pinv)·inf = (p·p)·(pinv·inf) ; symm reverses.
    let b3 = c.symm(
        pppinv_inf.clone(),
        pp_pinvinf.clone(),
        c.assoc(pp.clone(), pinv.clone(), inf.clone()),
    );
    let b4 = c.congr_r(
        parent,
        inf,
        pppinv.clone(),
        p_ppinv.clone(),
        c.assoc(p.clone(), p.clone(), pinv.clone()),
    );
    let b5 = c.congr_r(
        parent,
        inf,
        p_ppinv.clone(),
        p_one.clone(),
        c.congr_l(parent, p, p_pinv.clone(), c.rat_one.clone(), p2_cancel),
    );
    let b6 = c.congr_r(
        parent,
        inf,
        p_one.clone(),
        p.clone(),
        c.mul_one_at(p.clone()),
    );
    let rhs_eq = {
        let ch = c.trans(
            ppinf_pinv.clone(),
            pp_infpinv.clone(),
            pp_pinvinf.clone(),
            b1,
            b2,
        );
        let ch = c.trans(
            ppinf_pinv.clone(),
            pp_pinvinf.clone(),
            pppinv_inf.clone(),
            ch,
            b3,
        );
        let ch = c.trans(
            ppinf_pinv.clone(),
            pppinv_inf.clone(),
            p_ppinv_inf.clone(),
            ch,
            b4,
        );
        let ch = c.trans(
            ppinf_pinv.clone(),
            p_ppinv_inf.clone(),
            p_one_inf.clone(),
            ch,
            b5,
        );
        c.trans(ppinf_pinv.clone(), p_one_inf, p_inf.clone(), ch, b6)
    };

    // combine : m = (m·p)·pinv = ((p·p)·Inf)·pinv = p·Inf.
    let t1 = c.symm(mp_pinv.clone(), m.clone(), lhs_eq); // m = (m·p)·pinv
    let t2 = c.congr_r(parent, &pinv, mp.clone(), pp_inf.clone(), h_m); // (m·p)·pinv = ((p·p)·Inf)·pinv
    let ch = c.trans(m.clone(), mp_pinv.clone(), ppinf_pinv.clone(), t1, t2);
    c.trans(m.clone(), ppinf_pinv.clone(), p_inf, ch, rhs_eq)
}

include!("boolean_analysis_kkl_dualhc_percoord_er.rs");
