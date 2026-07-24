// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Proof builders for the per-coordinate dual-HC home stretch
// (`boolean_analysis_kkl_dualhc_percoord.rs`). `include!`d so the file stays
// under the 500-line convention.

/// `BoolAnalysis.dualhc_h2` value/type. `D := ofNat(2^n)` (≡ `powNat 2 n`).
fn build_h2(c: &PercoordConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));
    let (ri_id, ri) = b.fresh_local(c.rat());

    let inf = c.influence_of(&n, &f, &i);
    let hrp_ty = c.is_rpow32_of(&inf, &ri);
    let w_i = c.w_i(&b, &n, &f, &i);
    let p8 = c.pow(&c.rat_lit(8), &n); // powNat 8 n  (base 8)
    let p8_ri = c.mul(p8.clone(), ri.clone());
    let four = c.four();
    let concl = c.le(w_i.clone(), c.mul(four.clone(), p8_ri.clone()));

    let (hrp_id, hrp_v) = b.fresh_local(hrp_ty.clone());

    let tail = if for_value {
        // Scale base = `P := powNat 2 n` (`Rat.powNat (mk(ofNat 2) 1) n`). This is
        // the spelling EVERY downstream leaf actually uses:
        //   • `dualhc_m_pow2_eq_4pow_influence n f i : m·P = (P·P)·Inf_i`  (P, NOT
        //     the `ofNat(2^n)` cast `D`);
        //   • `dualhc_final_le`'s hyp slot is `IsRpow32 (m·P) r`  (P);
        //   • `dualhc_pow8_eq_two_pow_cube n : powNat 8 n = (P·P)·P`     (P).
        // Scaling at `P` lands `rpow32_scale`'s output directly in the P spelling,
        // so the chain closes with TWO rewrites (no `powNat_two_eq_ofNat_pow`
        // bridge / no `D` at all).
        let two_rat = c.two_rat(); // mk(ofNat 2)1
        let p2 = c.pow(&two_rat, &n); // P := powNat 2 n

        // 0 ≤ P : powNat_nonneg 2 n (0≤2).
        let h0two = c.le_of_ble_refl(c.order.rat_zero.clone(), two_rat.clone()); // 0 ≤ 2
        let h0p = c.pow_nonneg(&two_rat, &n, h0two); // 0 ≤ powNat 2 n

        // rpow32_scale P Inf_i ri h0p hrp : IsRpow32 ((P·P)·Inf_i) (((P·P)·P)·ri).
        let scaled = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.rpow32_scale"), vec![]),
            [p2.clone(), inf.clone(), ri.clone(), h0p, hrp_v],
        );
        let pp = c.mul(p2.clone(), p2.clone()); // P·P
        let ppp = c.mul(pp.clone(), p2.clone()); // (P·P)·P
        let pp_inf = c.mul(pp.clone(), inf.clone()); // (P·P)·Inf_i
        let ppp_ri = c.mul(ppp.clone(), ri.clone()); // ((P·P)·P)·ri
        let m = c.m(&b, &n, &f, &i); // m (= dualhc_final_le's m)
        let m_p2 = c.mul(m.clone(), p2.clone()); // m·P  (final hyp slot)

        // (a) rewrite (P·P)·Inf_i → m·P, via symm(dualhc_m_pow2_eq_4pow_influence).
        let m_norm = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.dualhc_m_pow2_eq_4pow_influence"),
                vec![],
            ),
            [n.clone(), f.clone(), i.clone()],
        ); // m·P = (P·P)·Inf_i
        let ppinf_eq_mp = c.symm(m_p2.clone(), pp_inf.clone(), m_norm); // (P·P)·Inf_i = m·P
        let motive_a = {
            let mut dd = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = dd.fresh_local(c.rat());
            let body = c.is_rpow32_of(&t, &ppp_ri);
            dd.finish_child(dd.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        let step_a = c.subst(motive_a, pp_inf.clone(), m_p2.clone(), ppinf_eq_mp, scaled);
        // step_a : IsRpow32 (m·P) (((P·P)·P)·ri).

        // (b) rewrite ((P·P)·P)·ri → (powNat 8 n)·ri, via congr (·ri) along
        //   ppp_eq_p8 : (P·P)·P = powNat 8 n  [symm dualhc_pow8_eq_two_pow_cube].
        let pow8cube = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.dualhc_pow8_eq_two_pow_cube"),
                vec![],
            ),
            [n.clone()],
        ); // powNat 8 n = (P·P)·P
        let ppp_eq_p8 = c.symm(p8.clone(), ppp.clone(), pow8cube); // (P·P)·P = powNat 8 n
        let cong_b = {
            let mot = c.mul_right_motive(&b, &ri);
            c.congr(ppp.clone(), p8.clone(), mot, ppp_eq_p8)
        }; // ((P·P)·P)·ri = (powNat 8 n)·ri
        let motive_b = {
            let mut dd = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = dd.fresh_local(c.rat());
            let body = c.is_rpow32_of(&m_p2, &t);
            dd.finish_child(dd.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        let step_b = c.subst(motive_b, ppp_ri.clone(), p8_ri.clone(), cong_b, step_a);
        // step_b : IsRpow32 (m·(powNat 2 n)) ((powNat 8 n)·ri)
        //   — exactly the dualhc_final_le hyp shape.

        // dualhc_final_le n f i ((powNat 8 n)·ri) step_b : W ≤ four·((powNat 8 n)·ri).
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.dualhc_final_le"), vec![]),
            [n.clone(), f.clone(), i.clone(), p8_ri.clone(), step_b],
        )
    } else {
        concl
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, hrp_id, hrp_ty, tail);
    let e = bind(&b, ri_id, c.rat(), e);
    let e = bind(&b, i_id, c.fin_of(&n), e);
    let e = bind(&b, f_id, f_ty, e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}

/// `BoolAnalysis.dualhc_percoord_linear` value/type.
fn build_percoord(c: &PercoordConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));
    let (ri_id, ri) = b.fresh_local(c.rat());

    let inf = c.influence_of(&n, &f, &i);
    let hrp_ty = c.is_rpow32_of(&inf, &ri);
    let wb = c.wb(&b, &n, &k, &f, &i);
    let p9k = c.pow(&c.nine(), &k); // 9^k
    let four = c.four();
    let q = c.mul(four.clone(), p9k.clone()); // four·9^k
    let q_ri = c.mul(q.clone(), ri.clone());
    let concl = c.le(wb.clone(), q_ri.clone());

    let (hrp_id, hrp_v) = b.fresh_local(hrp_ty.clone());

    let tail = if for_value {
        let p8 = c.pow(&c.rat_lit(8), &n); // 8^n
        let w_i = c.w_i(&b, &n, &f, &i);

        // 0 ≤ 9^k.
        let h0_9k = c.pow_nonneg(
            &c.nine(),
            &k,
            c.le_of_ble_refl(c.order.rat_zero.clone(), c.nine()),
        );

        // H1 : 8^n·Wb ≤ 9^k·W_i.
        let h1 = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.dualhc_h1"), vec![]),
            [n.clone(), k.clone(), f.clone(), i.clone()],
        );

        // H2 : W_i ≤ four·(8^n·ri).
        let h2 = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.dualhc_h2"), vec![]),
            [n.clone(), f.clone(), i.clone(), ri.clone(), hrp_v],
        );

        // H3 : 9^k·(four·(8^n·ri)) = 8^n·((four·9^k)·ri).   Pure Rat ring.
        let p8_ri = c.mul(p8.clone(), ri.clone()); // 8^n·ri
        let four_p8ri = c.mul(four.clone(), p8_ri.clone()); // four·(8^n·ri)
        let lhs = c.mul(p9k.clone(), four_p8ri.clone()); // 9^k·(four·(8^n·ri))
        let rhs = c.mul(p8.clone(), q_ri.clone()); // 8^n·((four·9^k)·ri)
        let h3 = build_percoord_h3(c, &b, &p9k, &four, &p8, &ri);
        let _ = (lhs, rhs); // documented endpoints

        // dualhc_norm_cancel_8n n Wb W_i ri 9^k (four·9^k) h0_9k H1 H2 H3 : Wb ≤ (four·9^k)·ri.
        Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.dualhc_norm_cancel_8n"),
                vec![],
            ),
            [
                n.clone(),
                wb.clone(),
                w_i.clone(),
                ri.clone(),
                p9k.clone(),
                q.clone(),
                h0_9k,
                h1,
                h2,
                h3,
            ],
        )
    } else {
        concl
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, hrp_id, hrp_ty, tail);
    let e = bind(&b, ri_id, c.rat(), e);
    let e = bind(&b, i_id, c.fin_of(&n), e);
    let e = bind(&b, f_id, f_ty, e);
    let e = bind(&b, k_id, c.nat.clone(), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}

/// H3 : `9^k·(four·(8^n·ri)) = 8^n·((four·9^k)·ri)`. Pure-ring `mul_comm`/`mul_assoc`
/// chain.  Write `P := 9^k`, `F := four`, `C := 8^n`.
///
/// ```text
///   P·(F·(C·ri))
/// = P·((F·C)·ri)        [congr (P·) (symm (assoc F C ri))]
/// = (P·(F·C))·ri        [symm (assoc P (F·C) ri)]
/// = ((F·C)·P)·ri        [congr (·ri) (mul_comm P (F·C))]      -- regroup to put C outer
/// ... we instead build directly to 8^n·((four·9^k)·ri):
/// = (C·(F·P))·ri        [congr (·ri) ( (F·C)·P = C·(F·P) )]
/// = C·((F·P)·ri)        [assoc C (F·P) ri]
/// ```
/// where `(F·C)·P = C·(F·P)` is itself a `mul_comm`/`mul_assoc` chain.
fn build_percoord_h3(
    c: &PercoordConsts,
    parent: &EnvDeclBuilder,
    p9k: &Expr,
    four: &Expr,
    p8: &Expr,
    ri: &Expr,
) -> Expr {
    // Abbreviations.
    let p = p9k.clone(); // P = 9^k
    let ff = four.clone(); // F = four
    let cc = p8.clone(); // C = 8^n
    let c_ri = c.mul(cc.clone(), ri.clone()); // C·ri
    let f_cri = c.mul(ff.clone(), c_ri.clone()); // F·(C·ri)
    let lhs = c.mul(p.clone(), f_cri.clone()); // P·(F·(C·ri))

    let fc = c.mul(ff.clone(), cc.clone()); // F·C
    let fc_ri = c.mul(fc.clone(), ri.clone()); // (F·C)·ri
    let p_fc_ri = c.mul(p.clone(), fc_ri.clone()); // P·((F·C)·ri)
    let p_fc = c.mul(p.clone(), fc.clone()); // P·(F·C)
    let pfc_ri = c.mul(p_fc.clone(), ri.clone()); // (P·(F·C))·ri

    let fp = c.mul(ff.clone(), p.clone()); // F·P
    let c_fp = c.mul(cc.clone(), fp.clone()); // C·(F·P)
    let cfp_ri = c.mul(c_fp.clone(), ri.clone()); // (C·(F·P))·ri
    let q = c.mul(ff.clone(), p.clone()); // four·9^k = F·P = q
    let q_ri = c.mul(q.clone(), ri.clone()); // (four·9^k)·ri
    let rhs = c.mul(cc.clone(), q_ri.clone()); // C·((four·9^k)·ri)

    // e1 : P·(F·(C·ri)) = P·((F·C)·ri)   [congr (P·) (symm assoc F C ri)]
    let assoc_fcri = c.mul_assoc(ff.clone(), cc.clone(), ri.clone()); // (F·C)·ri = F·(C·ri)
    let fcri_eq_fcri = c.symm(fc_ri.clone(), f_cri.clone(), assoc_fcri); // F·(C·ri) = (F·C)·ri
    let e1 = {
        let mot = c.mul_left_motive(parent, &p);
        c.congr(f_cri.clone(), fc_ri.clone(), mot, fcri_eq_fcri)
    };
    // e2 : P·((F·C)·ri) = (P·(F·C))·ri   [symm (assoc P (F·C) ri)]
    let assoc_p = c.mul_assoc(p.clone(), fc.clone(), ri.clone()); // (P·(F·C))·ri = P·((F·C)·ri)
    let e2 = c.symm(pfc_ri.clone(), p_fc_ri.clone(), assoc_p);
    // e3 : (P·(F·C))·ri = (C·(F·P))·ri   [congr (·ri) (P·(F·C) = C·(F·P))]
    let pfc_eq_cfp = build_pfc_eq_cfp(c, parent, &p, &ff, &cc);
    let e3 = {
        let mot = c.mul_right_motive(parent, ri);
        c.congr(p_fc.clone(), c_fp.clone(), mot, pfc_eq_cfp)
    };
    // e4 : (C·(F·P))·ri = C·((F·P)·ri)   [assoc C (F·P) ri]
    let e4 = c.mul_assoc(cc.clone(), fp.clone(), ri.clone());

    // chain : lhs = P·((F·C)·ri) = (P·(F·C))·ri = (C·(F·P))·ri = C·((F·P)·ri) = rhs.
    let t1 = c.trans(lhs.clone(), p_fc_ri.clone(), pfc_ri.clone(), e1, e2);
    let t2 = c.trans(lhs.clone(), pfc_ri.clone(), cfp_ri.clone(), t1, e3);
    // (C·(F·P))·ri  and  C·((F·P)·ri) ; rhs = C·((four·9^k)·ri) where four·9^k = F·P = q.
    // q_ri ≡ (F·P)·ri syntactically (q = mul four p9k = F·P). rhs = C·(q_ri).
    let _ = (q_ri, rhs);
    c.trans(
        lhs.clone(),
        cfp_ri.clone(),
        c.mul(cc.clone(), c.mul(fp.clone(), ri.clone())),
        t2,
        e4,
    )
}

/// `P·(F·C) = C·(F·P)` via `mul_comm`/`mul_assoc`. `P,F,C : Rat`.
///
/// ```text
///   P·(F·C)
/// = (P·F)·C        [symm (assoc P F C)]
/// = C·(P·F)        [mul_comm (P·F) C]
/// = C·(F·P)        [congr (C·) (mul_comm P F)]
/// ```
fn build_pfc_eq_cfp(
    c: &PercoordConsts,
    parent: &EnvDeclBuilder,
    p: &Expr,
    ff: &Expr,
    cc: &Expr,
) -> Expr {
    let fc = c.mul(ff.clone(), cc.clone()); // F·C
    let p_fc = c.mul(p.clone(), fc.clone()); // P·(F·C)
    let pf = c.mul(p.clone(), ff.clone()); // P·F
    let pf_c = c.mul(pf.clone(), cc.clone()); // (P·F)·C
    let c_pf = c.mul(cc.clone(), pf.clone()); // C·(P·F)
    let fp = c.mul(ff.clone(), p.clone()); // F·P
    let c_fp = c.mul(cc.clone(), fp.clone()); // C·(F·P)

    // a1 : P·(F·C) = (P·F)·C   [symm (assoc P F C)]
    let assoc = c.mul_assoc(p.clone(), ff.clone(), cc.clone()); // (P·F)·C = P·(F·C)
    let a1 = c.symm(pf_c.clone(), p_fc.clone(), assoc);
    // a2 : (P·F)·C = C·(P·F)   [mul_comm (P·F) C]
    let a2 = c.mul_comm(pf.clone(), cc.clone());
    // a3 : C·(P·F) = C·(F·P)   [congr (C·) (mul_comm P F)]
    let a3 = {
        let mot = c.mul_left_motive(parent, cc);
        c.congr(
            pf.clone(),
            fp.clone(),
            mot,
            c.mul_comm(p.clone(), ff.clone()),
        )
    };
    let t1 = c.trans(p_fc.clone(), pf_c.clone(), c_pf.clone(), a1, a2);
    c.trans(p_fc.clone(), c_pf.clone(), c_fp.clone(), t1, a3)
}

/// `BoolAnalysis.kkl_lowband_mass_fired` value/type — fire the assembly on the
/// proven `dualhc_h_dual_sum`.
fn build_fired(c: &PercoordConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (eps_id, eps) = b.fresh_local(c.rat());
    let (s_id, s) = b.fresh_local(c.rat());
    let r_ty = c.fin_to_rat(&n);
    let (r_id, r) = b.fresh_local(r_ty.clone());

    // Hypotheses (byte-for-byte the assembly's nn/le/h0s/hse/rp shapes).
    let nn_hyp = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let body = c.le0(c.influence_of(&n, &f, &i));
        d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    };
    let le_hyp = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let body = c.le(c.influence_of(&n, &f, &i), eps.clone());
        d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    };
    let h0s = c.le0(s.clone());
    let hse = c.eq_rat(c.mul(s.clone(), s.clone()), eps.clone());
    let rp_hyp = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let infl = c.influence_of(&n, &f, &i);
        let ri = Expr::app(r.clone(), i);
        let body = c.is_rpow32_of(&infl, &ri);
        d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    };

    let p9k = c.pow(&c.nine(), &k);
    let four = c.four();
    let bbig = c.mul(four.clone(), p9k.clone()); // B = four·9^k
    let four_m = c.mul(four.clone(), c.m_lo(&b, &n, &k, &f)); // 4·M_{1..k}
    let ti = c.total_influence_of(&n, &f);
    let b_s = c.mul(bbig.clone(), s.clone()); // B·s
    let concl = c.le(four_m.clone(), c.mul(b_s.clone(), ti.clone())); // 4·M ≤ (B·s)·I[f]

    let (hnn_id, hnn_v) = b.fresh_local(nn_hyp.clone());
    let (hle_id, hle_v) = b.fresh_local(le_hyp.clone());
    let (h0s_id, h0s_v) = b.fresh_local(h0s.clone());
    let (hse_id, hse_v) = b.fresh_local(hse.clone());
    let (hrp_id, hrp_v) = b.fresh_local(rp_hyp.clone());

    let tail = if for_value {
        // 0 ≤ B = four·9^k : mul_nonneg four 9^k (0≤4) (0≤9^k).
        let h0four = c.le_of_ble_refl(c.order.rat_zero.clone(), four.clone());
        let h0_9k = c.pow_nonneg(
            &c.nine(),
            &k,
            c.le_of_ble_refl(c.order.rat_zero.clone(), c.nine()),
        );
        let h0b = c.mul_nonneg(four.clone(), p9k.clone(), h0four, h0_9k);

        // h_dual := dualhc_h_dual_sum n k f r hrp : Σ_i Wb_i ≤ (four·9^k)·Σ_i r_i.
        let h_dual = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.dualhc_h_dual_sum"), vec![]),
            [n.clone(), k.clone(), f.clone(), r.clone(), hrp_v.clone()],
        );

        // kkl_lowband_mass_of_dual_hc n k f eps s B r nn le h0s hse rp h0b h_dual.
        Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.kkl_lowband_mass_of_dual_hc"),
                vec![],
            ),
            [
                n.clone(),
                k.clone(),
                f.clone(),
                eps.clone(),
                s.clone(),
                bbig.clone(),
                r.clone(),
                hnn_v,
                hle_v,
                h0s_v,
                hse_v,
                hrp_v,
                h0b,
                h_dual,
            ],
        )
    } else {
        concl
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, hrp_id, rp_hyp, tail);
    let e = bind(&b, hse_id, hse, e);
    let e = bind(&b, h0s_id, h0s, e);
    let e = bind(&b, hle_id, le_hyp, e);
    let e = bind(&b, hnn_id, nn_hyp, e);
    let e = bind(&b, r_id, r_ty, e);
    let e = bind(&b, s_id, c.rat(), e);
    let e = bind(&b, eps_id, c.rat(), e);
    let e = bind(&b, f_id, f_ty, e);
    let e = bind(&b, k_id, c.nat.clone(), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}

/// `BoolAnalysis.dualhc_h_dual_sum` value/type. The assembly's `h_dual` at
/// `B := four·9^k`.
fn build_h_dual(c: &PercoordConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let r_ty = c.fin_to_rat(&n);
    let (r_id, r) = b.fresh_local(r_ty.clone());

    let p9k = c.pow(&c.nine(), &k);
    let four = c.four();
    let q = c.mul(four.clone(), p9k.clone()); // B = four·9^k

    // hyp : ∀ i, IsRpow32 (Influence n f i) (r i).
    let rp_hyp = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let infl = c.influence_of(&n, &f, &i);
        let ri = Expr::app(r.clone(), i);
        let body = c.is_rpow32_of(&infl, &ri);
        d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    };

    // sum_w := Fin.sum n (fun i => subsetSum n (coord_w_band_fn n k f i)).
    let sum_w_fn = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let body = c.wb(&ch, &n, &k, &f, &i);
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };
    let sum_w = c.fin_sum_of(&n, sum_w_fn.clone());
    let sum_r = c.fin_sum_of(&n, r.clone());
    let concl = c.le(sum_w.clone(), c.mul(q.clone(), sum_r.clone()));

    let (hrp_id, hrp_v) = b.fresh_local(rp_hyp.clone());

    let tail = if for_value {
        // g := fun i => (four·9^k)·(r i)  (the scaled RHS summand).
        let g_fn = {
            let mut ch = EnvDeclBuilder::child_of(&b);
            let fin_n = c.fin_of(&n);
            let (i_id, i) = ch.fresh_local(fin_n.clone());
            let ri = Expr::app(r.clone(), i);
            let body = c.mul(q.clone(), ri);
            ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        let sum_g = c.fin_sum_of(&n, g_fn.clone());

        // pointwise : ∀ i, Wb_i ≤ (four·9^k)·(r i).
        let pointwise = {
            let mut ch = EnvDeclBuilder::child_of(&b);
            let fin_n = c.fin_of(&n);
            let (i_id, i) = ch.fresh_local(fin_n.clone());
            let ri = Expr::app(r.clone(), i.clone());
            let hrp_i = Expr::app(hrp_v.clone(), i.clone()); // IsRpow32 (Inf_i) (r i)
            let body = Expr::apps(
                Expr::const_(
                    Name::from_string("BoolAnalysis.dualhc_percoord_linear"),
                    vec![],
                ),
                [n.clone(), k.clone(), f.clone(), i.clone(), ri, hrp_i],
            );
            ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };

        // Fin.sum_le n sum_w_fn g_fn pointwise : Fin.sum n sum_w_fn ≤ Fin.sum n g_fn.
        let sum_le = Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_le"), vec![]),
            [n.clone(), sum_w_fn.clone(), g_fn.clone(), pointwise],
        );

        // Fin.sum_smul n (four·9^k) r : Fin.sum n (fun i => B·(r i)) = B·Fin.sum n r.
        //   g_fn ≡ fun i => B·(r i)  syntactically, so its LHS matches sum_g.
        let smul = Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_smul"), vec![]),
            [n.clone(), q.clone(), r.clone()],
        ); // Fin.sum n (fun i => B·(r i)) = B·Fin.sum n r
        let b_sum_r = c.mul(q.clone(), sum_r.clone());

        // transport sum_le along smul : motive t => sum_w ≤ t.
        let motive = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = d.fresh_local(c.rat());
            let body = c.le(sum_w.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        c.subst(motive, sum_g.clone(), b_sum_r.clone(), smul, sum_le)
    } else {
        concl
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, hrp_id, rp_hyp, tail);
    let e = bind(&b, r_id, r_ty, e);
    let e = bind(&b, f_id, f_ty, e);
    let e = bind(&b, k_id, c.nat.clone(), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}
