// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof-term builders for `BoolAnalysis.deriv_holder_fourth_support`
//! (component **M-Hölder**). Split out of
//! `boolean_analysis_kkl_dualres_holder.rs` to keep both files within the
//! 500-line module budget; the type, registration, and tests live in the parent
//! module, the support-mask bridge / `M → 4·W` regroup / final assembly here.
//!
//! See the parent module's doc comment for the full statement and outline. All
//! builders are `pub(super)` over the shared `HolderResConsts`.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_kkl_dualres_holder::HolderResConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};

/// Build the type + proof of `BoolAnalysis.deriv_holder_fourth_support`.
pub(super) fn build_holder_res(c: &HolderResConsts) -> (Expr, Expr) {
    let cube16 = |cnt: &Expr| {
        c.mul(
            c.mul(c.lit(16), cnt.clone()),
            c.mul(cnt.clone(), cnt.clone()),
        )
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat());
        let (a_id, a) = b.fresh_local(c.hcpoint_to_rat(&n));
        let (p_id, p) = b.fresh_local(c.hcpoint_to_bool(&n));
        let (q_id, q) = b.fresh_local(c.hcpoint_to_bool(&n));

        let l = c.ssum(&n, c.a_d_fn(&b, &n, &a, &p, &q));
        let cnt = c.ssum(&n, c.x_fn(&b, &n, &p, &q));
        let f4 = c.ssum(&n, c.a4_fn(&b, &n, &a)); // Σ (a²)·(a²)
        let ll = c.mul(l.clone(), l.clone());
        let lhs = c.mul(ll.clone(), ll);
        let rhs = c.mul(f4, cube16(&cnt));
        let concl = c.le(lhs, rhs);

        let e = b.mk_pi(q_id, BinderInfo::Default, c.hcpoint_to_bool(&n), concl);
        let e = b.mk_pi(p_id, BinderInfo::Default, c.hcpoint_to_bool(&n), e);
        let e = b.mk_pi(a_id, BinderInfo::Default, c.hcpoint_to_rat(&n), e);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat());
        let (a_id, a) = b.fresh_local(c.hcpoint_to_rat(&n));
        let (p_id, p) = b.fresh_local(c.hcpoint_to_bool(&n));
        let (q_id, q) = b.fresh_local(c.hcpoint_to_bool(&n));

        let proof = build_proof(c, &b, &n, &a, &p, &q);

        let e = b.mk_lam(q_id, BinderInfo::Default, c.hcpoint_to_bool(&n), proof);
        let e = b.mk_lam(p_id, BinderInfo::Default, c.hcpoint_to_bool(&n), e);
        let e = b.mk_lam(a_id, BinderInfo::Default, c.hcpoint_to_rat(&n), e);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.nat(), e);
        b.finish(e)
    };

    (ty, value)
}

fn mask_hyp(
    c: &HolderResConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    a: &Expr,
    p: &Expr,
    q: &Expr,
) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (x_id, x) = d.fresh_local(hcp.clone());
    let ax = Expr::app(a.clone(), x.clone());
    let dd = c.deriv_at(p, q, &x);
    let xx = c.ind_at(p, q, &x);
    let ad = c.mul(ax.clone(), dd.clone());
    let ad_x = c.mul(ad.clone(), xx.clone());
    let a_dx = c.mul(ax.clone(), c.mul(dd.clone(), xx.clone()));
    // mul_assoc a D X : (a·D)·X = a·(D·X)
    let assoc = c.mul_assoc(ax.clone(), dd.clone(), xx.clone());
    // deriv_mask (p x)(q x) : D·X = D
    let dmask = c.deriv_mask(
        Expr::app(p.clone(), x.clone()),
        Expr::app(q.clone(), x.clone()),
    );
    // congrArg (a·) dmask : a·(D·X) = a·D
    let cong = c.congr_arg(
        c.mul(dd.clone(), xx.clone()),
        dd.clone(),
        c.lam_mul_left(&d, &ax),
        dmask,
    );
    let body = c.trans(ad_x, a_dx, ad, assoc, cong);
    d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
}

/// `∀ x, (a x·D x)·(a x·D x) = 4·((a x·a x)·X x)` — the `M → 4·W` regroup.
pub(super) fn ad_sq_hyp(
    c: &HolderResConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    a: &Expr,
    p: &Expr,
    q: &Expr,
) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (x_id, x) = d.fresh_local(hcp.clone());
    let ax = Expr::app(a.clone(), x.clone());
    let dd = c.deriv_at(p, q, &x);
    let xx = c.ind_at(p, q, &x);
    let four = c.lit(4);
    let ad = c.mul(ax.clone(), dd.clone());
    let aa = c.mul(ax.clone(), ax.clone());
    let dd_dd = c.mul(dd.clone(), dd.clone());
    let four_x = c.mul(four.clone(), xx.clone());
    let aa_x = c.mul(aa.clone(), xx.clone());

    // s1 : (a·D)·(a·D) = (a·a)·(D·D)   [mmmc a D a D]
    let lhs = c.mul(ad.clone(), ad.clone());
    let aa_dddd = c.mul(aa.clone(), dd_dd.clone());
    let s1 = c.mmmc(ax.clone(), dd.clone(), ax.clone(), dd.clone());
    // s2 : (a·a)·(D·D) = (a·a)·(4·X)   [congrArg ((a·a)·) (symm disagree_sq)]
    //   disagree_sq (p x)(q x) : 4·X = D·D ; symm : D·D = 4·X
    let dsq = c.disagree_sq(
        Expr::app(p.clone(), x.clone()),
        Expr::app(q.clone(), x.clone()),
    );
    let dsq_symm = c.symm(four_x.clone(), dd_dd.clone(), dsq);
    let aa_4x = c.mul(aa.clone(), four_x.clone());
    let s2 = c.congr_arg(
        dd_dd.clone(),
        four_x.clone(),
        c.lam_mul_left(&d, &aa),
        dsq_symm,
    );
    // s3 : (a·a)·(4·X) = 4·((a·a)·X)
    //   = trans( symm(mul_assoc (a·a) 4 X) : (a·a)·(4·X) = ((a·a)·4)·X
    //          , trans( congrArg (·X) (mul_comm (a·a) 4) : ((a·a)·4)·X = (4·(a·a))·X
    //                 , mul_assoc 4 (a·a) X : (4·(a·a))·X = 4·((a·a)·X) ))
    let aa_4 = c.mul(aa.clone(), four.clone());
    let four_aa = c.mul(four.clone(), aa.clone());
    let aa4_x = c.mul(aa_4.clone(), xx.clone());
    let four_aa_x = c.mul(four_aa.clone(), xx.clone());
    let four_aax = c.mul(four.clone(), aa_x.clone());
    let assoc1 = c.mul_assoc(aa.clone(), four.clone(), xx.clone()); // ((a·a)·4)·X = (a·a)·(4·X)
    let assoc1_symm = c.symm(aa4_x.clone(), aa_4x.clone(), assoc1); // (a·a)·(4·X) = ((a·a)·4)·X
    let mc = Expr::apps(c.mul_comm_const(), [aa.clone(), four.clone()]); // (a·a)·4 = 4·(a·a)
    let cong_x = c.congr_arg(aa_4.clone(), four_aa.clone(), c.lam_mul_right(&d, &xx), mc);
    let assoc2 = c.mul_assoc(four.clone(), aa.clone(), xx.clone()); // (4·(a·a))·X = 4·((a·a)·X)
    let s3_inner = c.trans(
        aa4_x.clone(),
        four_aa_x.clone(),
        four_aax.clone(),
        cong_x,
        assoc2,
    );
    let s3 = c.trans(
        aa_4x.clone(),
        aa4_x.clone(),
        four_aax.clone(),
        assoc1_symm,
        s3_inner,
    );

    // chain : lhs = (a·a)·(D·D) = (a·a)·(4·X) = 4·((a·a)·X)
    let chain_tail = c.trans(aa_dddd.clone(), aa_4x.clone(), four_aax.clone(), s2, s3);
    let body = c.trans(lhs, aa_dddd, four_aax, s1, chain_tail);
    d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
}

/// The proof body of `deriv_holder_fourth_support`.
pub(super) fn build_proof(
    c: &HolderResConsts,
    b: &EnvDeclBuilder,
    n: &Expr,
    a: &Expr,
    p: &Expr,
    q: &Expr,
) -> Expr {
    let four = c.lit(4);
    // endpoints
    let l = c.ssum(n, c.a_d_fn(b, n, a, p, q)); // Σ aD
    let pm_l = c.ssum(n, c.adx_fn(b, n, a, p, q)); // Σ (aD)·X
    let m = c.ssum(n, c.ad_sq_fn(b, n, a, p, q)); // Σ (aD)·(aD)
    let w = c.ssum(n, c.aax_fn(b, n, a, p, q)); // Σ (a²)·X
    let cnt = c.ssum(n, c.x_fn(b, n, p, q)); // Σ X
    let cnt_xx = c.ssum(n, c.xx_fn(b, n, p, q)); // Σ X·X
    let f4 = c.ssum(n, c.a4_fn(b, n, a)); // Σ a⁴

    let ll = c.mul(l.clone(), l.clone());
    let ww = c.mul(w.clone(), w.clone());
    let m_cntxx = c.mul(m.clone(), cnt_xx.clone());
    let f4_cntxx = c.mul(f4.clone(), cnt_xx.clone());
    let four_w = c.mul(four.clone(), w.clone());
    let four_w_cnt = c.mul(four_w.clone(), cnt.clone());
    let f4_cnt = c.mul(f4.clone(), cnt.clone());
    let m_cnt = c.mul(m.clone(), cnt.clone());

    // CS shadows
    let cs1 = Expr::apps(
        c.cs_const(),
        [n.clone(), c.a_d_fn(b, n, a, p, q), c.x_fn(b, n, p, q)],
    ); // pm_l·pm_l ≤ M·cntXX
    let cs2 = Expr::apps(
        c.cs_const(),
        [n.clone(), c.aa_fn(b, n, a), c.x_fn(b, n, p, q)],
    ); // w·w ≤ f4·cntXX

    // cntXX = cnt
    let h_cntxx = Expr::apps(c.ind_sq_const(), [n.clone(), c.notbeq_fn(b, n, p, q)]);
    // pm_l = l  (mask bridge)
    let bridge_l = c.ssum_congr(
        n,
        c.adx_fn(b, n, a, p, q),
        c.a_d_fn(b, n, a, p, q),
        mask_hyp(c, b, n, a, p, q),
    );
    // M = 4·W
    let m_eq_4w = {
        let congr = c.ssum_congr(
            n,
            c.ad_sq_fn(b, n, a, p, q),
            c.four_aax_fn(b, n, a, p, q),
            ad_sq_hyp(c, b, n, a, p, q),
        );
        let smul = c.ssum_smul(n, four.clone(), c.aax_fn(b, n, a, p, q));
        let s_four_w = c.ssum(n, c.four_aax_fn(b, n, a, p, q));
        c.trans(m.clone(), s_four_w, four_w.clone(), congr, smul)
    };

    // ── h1 : l·l ≤ (4·w)·cnt ──────────────────────────────────────────────
    // cs1 : pm_l·pm_l ≤ M·cntXX. subst pm_l→l (both), cntXX→cnt, M→4w.
    let pm_l_sq = c.mul(pm_l.clone(), pm_l.clone());
    let h1a = {
        // motive z => z·z ≤ M·cntXX
        let mut dd = EnvDeclBuilder::child_of(b);
        let (z_id, z) = dd.fresh_local(c.rat());
        let body = c.le(c.mul(z.clone(), z.clone()), m_cntxx.clone());
        let motive = dd.finish_child(dd.mk_lam(z_id, BinderInfo::Default, c.rat(), body));
        c.subst(motive, pm_l.clone(), l.clone(), bridge_l, cs1)
    }; // l·l ≤ M·cntXX
    let _ = pm_l_sq;
    let h1b = {
        // motive z => l·l ≤ M·z ; subst cntXX→cnt
        let mut dd = EnvDeclBuilder::child_of(b);
        let (z_id, z) = dd.fresh_local(c.rat());
        let body = c.le(ll.clone(), c.mul(m.clone(), z));
        let motive = dd.finish_child(dd.mk_lam(z_id, BinderInfo::Default, c.rat(), body));
        c.subst(motive, cnt_xx.clone(), cnt.clone(), h_cntxx.clone(), h1a)
    }; // l·l ≤ M·cnt
    let h1 = {
        // motive z => l·l ≤ z·cnt ; subst M→4w
        let mut dd = EnvDeclBuilder::child_of(b);
        let (z_id, z) = dd.fresh_local(c.rat());
        let body = c.le(ll.clone(), c.mul(z, cnt.clone()));
        let motive = dd.finish_child(dd.mk_lam(z_id, BinderInfo::Default, c.rat(), body));
        c.subst(motive, m.clone(), four_w.clone(), m_eq_4w, h1b)
    }; // l·l ≤ (4·w)·cnt
    let _ = (m_cnt, four_w_cnt);

    // ── h2 : w·w ≤ f4·cnt ─────────────────────────────────────────────────
    let h2 = {
        // motive z => w·w ≤ f4·z ; subst cntXX→cnt
        let mut dd = EnvDeclBuilder::child_of(b);
        let (z_id, z) = dd.fresh_local(c.rat());
        let body = c.le(ww.clone(), c.mul(f4.clone(), z));
        let motive = dd.finish_child(dd.mk_lam(z_id, BinderInfo::Default, c.rat(), body));
        c.subst(motive, cnt_xx.clone(), cnt.clone(), h_cntxx, cs2)
    };
    let _ = (f4_cntxx, f4_cnt);

    // ── nonnegativities ───────────────────────────────────────────────────
    let h_l2_nn = c.sq_nonneg(l.clone()); // 0 ≤ l·l
    let h_w_nn = c.ssum_nonneg(
        b,
        n,
        |c, x| c.mul(c.aa_at(a, x), c.ind_at(p, q, x)),
        |c, x| {
            c.mul_nonneg(
                c.aa_at(a, x),
                c.ind_at(p, q, x),
                c.sq_nonneg(Expr::app(a.clone(), x.clone())),
                c.ind_nonneg(c.notbeq_at(p, q, x)),
            )
        },
    ); // 0 ≤ W
    let h_cnt_nn = c.ssum_nonneg(
        b,
        n,
        |c, x| c.ind_at(p, q, x),
        |c, x| c.ind_nonneg(c.notbeq_at(p, q, x)),
    ); // 0 ≤ cnt
    let h_f4_nn = c.ssum_nonneg(
        b,
        n,
        |c, x| {
            let aa = c.aa_at(a, x);
            c.mul(aa.clone(), aa)
        },
        |c, x| c.sq_nonneg(c.aa_at(a, x)),
    ); // 0 ≤ f4

    // ── finish with holder_quad_combine ───────────────────────────────────
    Expr::apps(
        c.combine_const(),
        [ll, w, cnt, f4, h_l2_nn, h_w_nn, h_cnt_nn, h_f4_nn, h1, h2],
    )
}
