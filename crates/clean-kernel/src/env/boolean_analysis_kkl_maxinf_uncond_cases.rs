// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// KKL UNCONDITIONAL dichotomy — the two case branches. `include!`d into
// `boolean_analysis_kkl_maxinf_uncond_body.rs`.

/// Case B (no large coordinate): `hne : ¬∃ i, τ ≤ Inf_i`. Build
/// `h1 : ∀ i, Inf_i ≤ τ` and feed the conditional theorem.
#[allow(clippy::too_many_arguments)]
fn build_case_b(
    c: &UncondConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    f: &Expr,
    _kcast: &Expr,
    delta: &Expr,
    tau: &Expr,
    i_tot: &Expr,
    large_pred: &Expr,
    not_exists: &Expr,
    concl: &Expr,
    hpos: &Expr,
    h0: &Expr,
    hd_nn: &Expr,
    hdd1: &Expr,
    hp_nn: &Expr,
    hq_nn: &Expr,
    hq_ne: &Expr,
    hd_pos: &Expr,
    p: &Expr,
    q: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(parent);
    let (hne_id, hne) = ch.fresh_local(not_exists.clone());

    // h1 : ∀ (i : Fin n), Inf_i ≤ τ.
    let h1 = {
        let mut d = EnvDeclBuilder::child_of(&ch);
        let fin_n = c.fin_of(n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let infi = c.influence_of(n, f, &i);
        let tau_le_infi = c.rat_le(tau.clone(), infi.clone());
        let infi_le_tau = c.rat_le(infi.clone(), tau.clone());

        // ¬(τ ≤ Inf_i) := fun (h : τ ≤ Inf_i) => hne (Exists.intro _ large_pred i h).
        let not_tau_le = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (h_id, h) = e.fresh_local(tau_le_infi.clone());
            let exi = Expr::apps(
                Expr::const_(Name::from_string("Exists.intro"), vec![c.u1.clone()]),
                [c.fin_of(n), large_pred.clone(), i.clone(), h],
            );
            let body = Expr::app(hne.clone(), exi); // : False
            e.finish_child(e.mk_lam(h_id, BinderInfo::Default, tau_le_infi.clone(), body))
        };

        // Rat.le_total τ (Inf_i) : Or (τ ≤ Inf_i)(Inf_i ≤ τ).
        let h_total = Expr::apps(
            Expr::const_(Name::from_string("Rat.le_total"), vec![]),
            [tau.clone(), infi.clone()],
        );
        // left: τ ≤ Inf_i contradicts not_tau_le → False.elim (Inf_i ≤ τ).
        let tot_left = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (hl_id, hl) = e.fresh_local(tau_le_infi.clone());
            let h_false = Expr::app(not_tau_le.clone(), hl);
            let body = u_false_elim(infi_le_tau.clone(), h_false);
            e.finish_child(e.mk_lam(hl_id, BinderInfo::Default, tau_le_infi.clone(), body))
        };
        // right: Inf_i ≤ τ → it.
        let tot_right = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let (hr_id, hr) = e.fresh_local(infi_le_tau.clone());
            e.finish_child(e.mk_lam(hr_id, BinderInfo::Default, infi_le_tau.clone(), hr))
        };
        let body = u_or_elim(
            &d,
            tau_le_infi,
            infi_le_tau.clone(),
            infi_le_tau,
            h_total,
            tot_left,
            tot_right,
        );
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };

    // hkt : K·(9^k·(δ·I)) ≤ I.
    let hkt = build_hkt(
        c, &ch, n, f, k, delta, i_tot, hp_nn, hq_nn, hq_ne, hd_nn, p, q,
    );

    // kkl_exists_max_influence n k f δ hpos hd_nn hdd1 h0 h1 hkt : ∃ i, ...
    let result = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.kkl_exists_max_influence"),
            vec![],
        ),
        [
            n.clone(),
            k.clone(),
            f.clone(),
            delta.clone(),
            hpos.clone(),
            hd_nn.clone(),
            hdd1.clone(),
            h0.clone(),
            h1,
            hkt,
        ],
    );
    let _ = (concl, hd_pos);
    ch.finish_child(ch.mk_lam(hne_id, BinderInfo::Default, not_exists.clone(), result))
}

/// Build `hkt : K·(9^k·(δ·I)) ≤ I`. Reshape LHS to `(P·δ)·I` and bound it by
/// `1·I = I` using `P·δ ≤ Q·δ = 1`.
#[allow(clippy::too_many_arguments)]
fn build_hkt(
    c: &UncondConsts,
    parent: &EnvDeclBuilder,
    _n: &Expr,
    _f: &Expr,
    k: &Expr,
    delta: &Expr,
    i_tot: &Expr,
    hp_nn: &Expr,
    _hq_nn: &Expr,
    hq_ne: &Expr,
    hd_nn: &Expr,
    p: &Expr,
    q: &Expr,
) -> Expr {
    let kcast = c.natcast(&c.succ(k));
    let p9 = c.pow9(k);
    // P ≤ Q = P+1:  add_le_add P P 0 1 (le_refl P)(0≤1); P+0 = P.
    let hp_le_q = {
        // P+0 ≤ P+1.
        let h_p0_le_p1 = c.add_le_add(
            p.clone(),
            p.clone(),
            c.rat_zero.clone(),
            c.rat_one.clone(),
            c.le_refl(p.clone()),
            c.le_of_lt_via(
                parent,
                c.rat_zero.clone(),
                c.rat_one.clone(),
                c.zero_lt_one(),
            ),
        );
        // P+0 = P; subst LHS → P.  motive t := t ≤ Q (= P+1).
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.rat_le(t, q.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        c.subst(
            motive,
            c.add(p.clone(), c.rat_zero.clone()),
            p.clone(),
            c.add_zero(p.clone()),
            h_p0_le_p1,
        )
    };
    // P·δ ≤ Q·δ.
    let h_pd_le_qd = c.mul_le_right(delta.clone(), p.clone(), q.clone(), hp_le_q, hd_nn.clone());
    // Q·δ = Q·inv Q = 1.
    let h_qd_eq_1 = c.mul_inv_cancel(q.clone(), hq_ne.clone());
    // P·δ ≤ 1  (subst Q·δ → 1; motive t := P·δ ≤ t).
    let h_pd_le_1 = {
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.rat_le(c.mul(p.clone(), delta.clone()), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        c.subst(
            motive,
            c.mul(q.clone(), delta.clone()),
            c.rat_one.clone(),
            h_qd_eq_1,
            h_pd_le_qd,
        )
    };
    // 0 ≤ I directly (total_influence_nonneg gives ≤, not <).
    let _ = hp_nn;
    let pd = c.mul(p.clone(), delta.clone());
    let h_i_nn = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.total_influence_nonneg"),
            vec![],
        ),
        [_n.clone(), _f.clone()],
    );
    // (P·δ)·I ≤ 1·I  (mul_le_right I (P·δ) 1 (P·δ≤1)(0≤I)).
    let h_pdi_le_1i = c.mul_le_right(
        i_tot.clone(),
        pd.clone(),
        c.rat_one.clone(),
        h_pd_le_1,
        h_i_nn,
    );
    // 1·I = I.
    let e_1i = c.one_mul(i_tot.clone());
    // (P·δ)·I ≤ I  (subst 1·I → I; motive t := (P·δ)·I ≤ t).
    let h_pdi_le_i = {
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(c.rat.clone());
            let body = c.rat_le(c.mul(pd.clone(), i_tot.clone()), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        c.subst(
            motive,
            c.mul(c.rat_one.clone(), i_tot.clone()),
            i_tot.clone(),
            e_1i,
            h_pdi_le_1i,
        )
    };

    // e_reshape : (P·δ)·I = K·(9^k·(δ·I)).
    //   P·δ = (K·9^k)·δ = K·(9^k·δ)  (mul_assoc K 9^k δ).
    //   (P·δ)·I = (K·(9^k·δ))·I      (congr_mul_r I …).
    //   (K·(9^k·δ))·I = K·((9^k·δ)·I) (mul_assoc K (9^k·δ) I).
    //   K·((9^k·δ)·I) = K·(9^k·(δ·I)) (congr_mul_l K (mul_assoc 9^k δ I)).
    let e_assoc_k = c.mul_assoc(kcast.clone(), p9.clone(), delta.clone()); // (K·9^k)·δ = K·(9^k·δ)
    let e1 = c.congr_mul_r(
        parent,
        i_tot,
        pd.clone(), // = (K·9^k)·δ  (P ≡ K·9^k syntactically)
        c.mul(kcast.clone(), c.mul(p9.clone(), delta.clone())),
        e_assoc_k,
    );
    let e_assoc_k2 = c.mul_assoc(
        kcast.clone(),
        c.mul(p9.clone(), delta.clone()),
        i_tot.clone(),
    ); // (K·(9^k·δ))·I = K·((9^k·δ)·I)
    let e_assoc_inner = c.mul_assoc(p9.clone(), delta.clone(), i_tot.clone()); // (9^k·δ)·I = 9^k·(δ·I)
    let e3 = c.congr_mul_l(
        parent,
        &kcast,
        c.mul(c.mul(p9.clone(), delta.clone()), i_tot.clone()),
        c.mul(p9.clone(), c.mul(delta.clone(), i_tot.clone())),
        e_assoc_inner,
    );
    // chain: (P·δ)·I = (K·(9^k·δ))·I = K·((9^k·δ)·I) = K·(9^k·(δ·I)).
    let lhs_target_1 = c.mul(
        c.mul(kcast.clone(), c.mul(p9.clone(), delta.clone())),
        i_tot.clone(),
    );
    let mid = c.mul(
        kcast.clone(),
        c.mul(c.mul(p9.clone(), delta.clone()), i_tot.clone()),
    );
    let rhs_final = c.mul(
        kcast.clone(),
        c.mul(p9.clone(), c.mul(delta.clone(), i_tot.clone())),
    );
    let e12 = c.eq_trans(
        c.mul(pd.clone(), i_tot.clone()),
        lhs_target_1.clone(),
        mid.clone(),
        e1,
        e_assoc_k2,
    );
    let e_reshape = c.eq_trans(
        c.mul(pd.clone(), i_tot.clone()),
        mid.clone(),
        rhs_final.clone(),
        e12,
        e3,
    );

    // hkt : K·(9^k·(δ·I)) ≤ I  (subst (P·δ)·I → K·(9^k·(δ·I)); motive t := t ≤ I).
    let motive = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (t_id, t) = d.fresh_local(c.rat.clone());
        let body = c.rat_le(t, i_tot.clone());
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.subst(
        motive,
        c.mul(pd.clone(), i_tot.clone()),
        rhs_final,
        e_reshape,
        h_pdi_le_i,
    )
}

include!("boolean_analysis_kkl_maxinf_uncond_casea.rs");
