// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// KKL UNCONDITIONAL dichotomy — Case A (a large coordinate exists). `include!`d
// into `boolean_analysis_kkl_maxinf_uncond_cases.rs`.

impl UncondConsts {
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
            [a, b],
        )
    }
    fn right_distrib(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.right_distrib"), vec![]),
            [a, b, cc],
        )
    }
    fn mul_one(&self, a: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.mul_one"), vec![]), [a])
    }
    fn natcast_nonneg(&self, m: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.natCast_nonneg"), vec![]),
            [m.clone()],
        )
    }
    /// `Rat.mul_inv Q Q (Q≠0)(Q≠0) : inv(Q·Q) = inv Q · inv Q`.
    fn mul_inv(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_inv"), vec![]),
            [a, b, ha, hb],
        )
    }
    /// `Rat.le_of_mul_le_mul_left_pos a b c (0<c)(c·a ≤ c·b) : a ≤ b`.
    fn le_of_mul_le_left(&self, a: Expr, b: Expr, cc: Expr, hc: Expr, hle: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_of_mul_le_mul_left_pos"), vec![]),
            [a, b, cc, hc, hle],
        )
    }
}

/// Case A (large coordinate): `he : ∃ i, τ ≤ Inf_i`. `Exists.elim` to `(i, hi)`,
/// then `Exists.intro i (K·Var ≤ K ≤ 2n·τ ≤ 2n·Inf_i)`.
#[allow(clippy::too_many_arguments)]
fn build_case_a(
    c: &UncondConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f: &Expr,
    _k: &Expr,
    kcast: &Expr,
    nn: &Expr,
    _p: &Expr,
    q: &Expr,
    qq: &Expr,
    two_nn: &Expr,
    tau: &Expr,
    var: &Expr,
    _i_tot: &Expr,
    large_pred: &Expr,
    exists_large: &Expr,
    concl: &Expr,
    hthr: &Expr,
    _h0: &Expr,
    _hp_nn: &Expr,
    _hq_nn: &Expr,
    _hd_nn: &Expr,
    hq_pos: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(parent);
    let (he_id, he) = ch.fresh_local(exists_large.clone());

    // Shared τ/QQ cancellation facts.
    let hq_ne = c.ne_of_pos(q.clone(), hq_pos.clone());
    let h_qq_pos = c.mul_pos(q.clone(), q.clone(), hq_pos.clone(), hq_pos.clone()); // 0 < QQ
    let h_qq_ne = c.ne_of_pos(qq.clone(), h_qq_pos.clone());
    // e_tau_inv : δ·δ = inv(QQ).  (τ = δ·δ; mul_inv Q Q : inv(Q·Q) = δ·δ; symm.)
    let inv_qq = c.inv(qq.clone());
    let e_tau_inv = c.symm(
        inv_qq.clone(),
        tau.clone(),
        c.mul_inv(q.clone(), q.clone(), hq_ne.clone(), hq_ne),
    );
    // e_qq_tau_1 : QQ·τ = 1.  (subst inv QQ → τ in QQ·inv QQ = 1.)
    let e_qq_tau_1 = {
        let cancel = c.mul_inv_cancel(qq.clone(), h_qq_ne); // QQ·inv QQ = 1
        let motive = {
            let mut d = EnvDeclBuilder::child_of(&ch);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.eq_rat(c.mul(qq.clone(), t), c.rat_one.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        // h : inv QQ = τ  := symm e_tau_inv.
        c.subst(
            motive,
            inv_qq.clone(),
            tau.clone(),
            c.symm(tau.clone(), inv_qq.clone(), e_tau_inv),
            cancel,
        )
    };

    // The Exists.elim function: λ (i : Fin n)(hi : τ ≤ Inf_i) => Exists.intro i proof_i.
    let elim_fn = {
        let mut eb = EnvDeclBuilder::child_of(&ch);
        let fin_n = c.fin_of(n);
        let (i_id, i) = eb.fresh_local(fin_n.clone());
        let infi = c.influence_of(n, f, &i);
        let tau_le_infi = c.rat_le(tau.clone(), infi.clone());
        let (hi_id, hi) = eb.fresh_local(tau_le_infi.clone());

        let g_i = c.mul(nn.clone(), infi.clone()); // Nn·Inf_i
        let k_var = c.mul(kcast.clone(), var.clone()); // K·Var

        // (1) K·Var ≤ K.
        let h_kvar_le_k = {
            // K·Var ≤ K·1.
            let h = c.mul_le_left(
                kcast.clone(),
                var.clone(),
                c.rat_one.clone(),
                Expr::apps(
                    Expr::const_(Name::from_string("BoolAnalysis.variance_le_one"), vec![]),
                    [n.clone(), f.clone()],
                ),
                c.natcast_nonneg(&c.succ(_k)),
            );
            // K·1 = K; subst RHS → K; motive t := K·Var ≤ t.
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&eb);
                let (t_id, t) = d.fresh_local(c.rat.clone());
                let body = c.rat_le(k_var.clone(), t);
                d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            c.subst(
                motive,
                c.mul(kcast.clone(), c.rat_one.clone()),
                kcast.clone(),
                c.mul_one(kcast.clone()),
                h,
            )
        };

        // (2) K ≤ (Nn+Nn)·τ.
        let two_nn_tau = c.mul(two_nn.clone(), tau.clone());
        let h_k_le_2nntau = build_k_le_2nntau(
            c,
            &eb,
            kcast,
            two_nn,
            tau,
            q,
            qq,
            &e_qq_tau_1,
            hthr,
            hq_pos,
            &two_nn_tau,
        );

        // (3) (Nn+Nn)·τ ≤ (Nn+Nn)·Inf_i.
        let h_2nn_nonneg = build_two_nn_nonneg(c, &eb, n, two_nn);
        let two_nn_infi = c.mul(two_nn.clone(), infi.clone());
        let h_step3 = c.mul_le_left(two_nn.clone(), tau.clone(), infi.clone(), hi, h_2nn_nonneg);

        // (4) (Nn+Nn)·Inf_i = Nn·Inf_i + Nn·Inf_i  (right_distrib Nn Nn Inf_i).
        let e_distrib = c.right_distrib(nn.clone(), nn.clone(), infi.clone());

        // chain (1)-(3): K·Var ≤ (Nn+Nn)·Inf_i.
        let h_kvar_le_k_le = c.le_trans(
            k_var.clone(),
            kcast.clone(),
            two_nn_tau.clone(),
            h_kvar_le_k,
            h_k_le_2nntau,
        );
        let h_kvar_le_2nninfi = c.le_trans(
            k_var.clone(),
            two_nn_tau.clone(),
            two_nn_infi.clone(),
            h_kvar_le_k_le,
            h_step3,
        );
        // subst (Nn+Nn)·Inf_i → Nn·Inf_i + Nn·Inf_i; motive t := K·Var ≤ t.
        let proof_i = {
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&eb);
                let (t_id, t) = d.fresh_local(c.rat.clone());
                let body = c.rat_le(k_var.clone(), t);
                d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            c.subst(
                motive,
                two_nn_infi.clone(),
                c.add(g_i.clone(), g_i.clone()),
                e_distrib,
                h_kvar_le_2nninfi,
            )
        };

        // Exists.intro i proof_i : ∃ j, K·Var ≤ Nn·Inf_j + Nn·Inf_j.
        let exi = Expr::apps(
            Expr::const_(Name::from_string("Exists.intro"), vec![c.u1.clone()]),
            [
                fin_n.clone(),
                uncond_pred(c, parent, n, f, kcast, nn, var),
                i.clone(),
                proof_i,
            ],
        );
        let lam = eb.mk_lam(hi_id, BinderInfo::Default, tau_le_infi, exi);
        eb.finish_child(eb.mk_lam(i_id, BinderInfo::Default, fin_n, lam))
    };

    // Exists.elim.{1} (Fin n) large_pred concl he elim_fn : concl.
    let result = Expr::apps(
        Expr::const_(Name::from_string("Exists.elim"), vec![c.u1.clone()]),
        [
            c.fin_of(n),
            large_pred.clone(),
            concl.clone(),
            he.clone(),
            elim_fn,
        ],
    );
    ch.finish_child(ch.mk_lam(he_id, BinderInfo::Default, exists_large.clone(), result))
}

/// `K ≤ (Nn+Nn)·τ`: from `hthr : K·QQ ≤ Nn+Nn` and `QQ·τ = 1`, cancel `QQ>0`.
#[allow(clippy::too_many_arguments)]
fn build_k_le_2nntau(
    c: &UncondConsts,
    parent: &EnvDeclBuilder,
    kcast: &Expr,
    two_nn: &Expr,
    tau: &Expr,
    q: &Expr,
    qq: &Expr,
    e_qq_tau_1: &Expr,
    hthr: &Expr,
    hq_pos: &Expr,
    two_nn_tau: &Expr,
) -> Expr {
    // h_qq_pos : 0 < QQ = Q·Q.
    let h_qq_pos = c.mul_pos(q.clone(), q.clone(), hq_pos.clone(), hq_pos.clone());

    // e_rhs : QQ·((Nn+Nn)·τ) = Nn+Nn.
    //   QQ·((Nn+Nn)·τ) = QQ·(τ·(Nn+Nn))   [congr_l QQ (mul_comm (Nn+Nn) τ)]
    //                 = (QQ·τ)·(Nn+Nn)    [symm (mul_assoc QQ τ (Nn+Nn))]
    //                 = 1·(Nn+Nn)         [congr_r (Nn+Nn) (QQ·τ = 1)]
    //                 = Nn+Nn             [one_mul (Nn+Nn)]
    let qq_2nntau = c.mul(qq.clone(), two_nn_tau.clone());
    let tau_2nn = c.mul(tau.clone(), two_nn.clone());
    let qq_tau_2nn = c.mul(qq.clone(), tau_2nn.clone());
    let qqtau_2nn = c.mul(c.mul(qq.clone(), tau.clone()), two_nn.clone());

    let e1 = c.congr_mul_l(
        parent,
        qq,
        two_nn_tau.clone(),
        tau_2nn.clone(),
        c.mul_comm(two_nn.clone(), tau.clone()),
    ); // QQ·((Nn+Nn)·τ) = QQ·(τ·(Nn+Nn))
    let e2 = c.symm(
        qqtau_2nn.clone(),
        qq_tau_2nn.clone(),
        c.mul_assoc(qq.clone(), tau.clone(), two_nn.clone()),
    ); // QQ·(τ·(Nn+Nn)) = (QQ·τ)·(Nn+Nn)
    let e3 = c.congr_mul_r(
        parent,
        two_nn,
        c.mul(qq.clone(), tau.clone()),
        c.rat_one.clone(),
        e_qq_tau_1.clone(),
    ); // (QQ·τ)·(Nn+Nn) = 1·(Nn+Nn)
    let e4 = c.one_mul(two_nn.clone()); // 1·(Nn+Nn) = Nn+Nn

    let one_2nn = c.mul(c.rat_one.clone(), two_nn.clone());
    let e12 = c.eq_trans(
        qq_2nntau.clone(),
        qq_tau_2nn.clone(),
        qqtau_2nn.clone(),
        e1,
        e2,
    );
    let e123 = c.eq_trans(
        qq_2nntau.clone(),
        qqtau_2nn.clone(),
        one_2nn.clone(),
        e12,
        e3,
    );
    let e_rhs = c.eq_trans(qq_2nntau.clone(), one_2nn, two_nn.clone(), e123, e4); // QQ·((Nn+Nn)·τ) = Nn+Nn

    // hthr' : QQ·K ≤ Nn+Nn  (subst K·QQ → QQ·K via mul_comm; motive t := t ≤ Nn+Nn).
    let h_qqk_le_2nn = {
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.rat_le(t, two_nn.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        c.subst(
            motive,
            c.mul(kcast.clone(), qq.clone()),
            c.mul(qq.clone(), kcast.clone()),
            c.mul_comm(kcast.clone(), qq.clone()),
            hthr.clone(),
        )
    };
    // h_qqk_le_qq_2nntau : QQ·K ≤ QQ·((Nn+Nn)·τ)  (subst Nn+Nn → QQ·((Nn+Nn)·τ) via symm e_rhs).
    let h_premise = {
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.rat_le(c.mul(qq.clone(), kcast.clone()), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        c.subst(
            motive,
            two_nn.clone(),
            qq_2nntau.clone(),
            c.symm(qq_2nntau.clone(), two_nn.clone(), e_rhs),
            h_qqk_le_2nn,
        )
    };
    // K ≤ (Nn+Nn)·τ  (le_of_mul_le_mul_left_pos K ((Nn+Nn)·τ) QQ (0<QQ) premise).
    c.le_of_mul_le_left(
        kcast.clone(),
        two_nn_tau.clone(),
        qq.clone(),
        h_qq_pos,
        h_premise,
    )
}

/// `0 ≤ Nn+Nn`: `add_le_add 0 Nn 0 Nn (0≤Nn)(0≤Nn) : 0+0 ≤ Nn+Nn`; `0+0 = 0`.
/// `Nn = natCast n`, so `natCast_nonneg n : 0 ≤ Nn`.
fn build_two_nn_nonneg(c: &UncondConsts, parent: &EnvDeclBuilder, n: &Expr, two_nn: &Expr) -> Expr {
    let nn = c.natcast(n);
    let h_nn_nn = c.natcast_nonneg(n);
    let h_00_le = c.add_le_add(
        c.rat_zero.clone(),
        nn.clone(),
        c.rat_zero.clone(),
        nn.clone(),
        h_nn_nn.clone(),
        h_nn_nn,
    ); // 0+0 ≤ Nn+Nn
       // 0+0 = 0; subst LHS → 0; motive t := t ≤ Nn+Nn.
    let motive = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = d.fresh_local(c.rat.clone());
        let body = c.rat_le(t, two_nn.clone());
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.subst(
        motive,
        c.add(c.rat_zero.clone(), c.rat_zero.clone()),
        c.rat_zero.clone(),
        c.zero_add(c.rat_zero.clone()),
        h_00_le,
    )
}
