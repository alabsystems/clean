// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// KKL finish — RUNG 6b type/proof builder. `include!`d into
// `boolean_analysis_kkl_maxinf.rs` so it shares `MaxInfConsts` and keeps the
// registration module under the 500-line convention. (Regular `//` comments
// only — inner doc `//!` is not allowed at an `include!` site.)

/// Build the type (`for_value=false`) / proof (`for_value=true`) of
/// `BoolAnalysis.kkl_exists_max_influence`.
fn build_maxinf(c: &MaxInfConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());
    let (d_id, d) = b.fresh_local(c.rat.clone());
    let dd = c.mul(d.clone(), d.clone());

    let hpos_ty = c.pos_nat(&n);
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());
    let hd_ty = c.rat_le(c.rat_zero(), d.clone());
    let (hd_id, hd) = b.fresh_local(hd_ty.clone());
    let hdd1_ty = c.rat_lt(dd.clone(), c.rat_one());
    let (hdd1_id, hdd1) = b.fresh_local(hdd1_ty.clone());
    let h0_ty = c.h0_hyp(&b, &n, &f);
    let (h0_id, h0) = b.fresh_local(h0_ty.clone());
    let h1_ty = c.h1_hyp(&b, &n, &f, &dd);
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());

    let i_tot = c.total_influence_of(&n, &f);
    let p9 = c.pow9(&k);
    let d_i = c.mul(d.clone(), i_tot.clone());
    let p9_di = c.mul(p9.clone(), d_i.clone()); // 9^k·(δ·I)
    let kcast = c.natcast(&c.succ(&k)); // K := natCast(k+1)
    let k_t = c.mul(kcast.clone(), p9_di.clone()); // (k+1)·(9^k·δ·I)
    let hkt_ty = c.rat_le(k_t.clone(), i_tot.clone());
    let (hkt_id, hkt) = b.fresh_local(hkt_ty.clone());

    // Conclusion: ∃ i, K·Var ≤ (Nn·Inf_i) + (Nn·Inf_i).
    let v = c.variance_of(&n, &f);
    let k_v = c.mul(kcast.clone(), v.clone()); // c := K·Var
    let nn = c.natcast(&n); // Nn := natCast n
    let concl = {
        let pred = {
            let mut pb = EnvDeclBuilder::child_of(&b);
            let fin_n = c.fin_of(&n);
            let (i_id, i) = pb.fresh_local(fin_n.clone());
            let g_i = c.mul(nn.clone(), c.influence_of(&n, &f, &i));
            let body = c.rat_le(k_v.clone(), c.add(g_i.clone(), g_i));
            pb.finish_child(pb.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        Expr::apps(
            Expr::const_(Name::from_string("Exists"), vec![c.u1.clone()]),
            [c.fin_of(&n), pred],
        )
    };

    let body = if for_value {
        let ff = c.f_fn(&b, &n, &f); // F := fun i => g i + g i
        let gg = c.g_fn(&b, &n, &f); // g := fun i => Nn·Inf_i
        let inf = c.inf_fn(&b, &n, &f); // Inf := fun i => Inf_i

        // (1) cond : K·Var ≤ I + I.
        let cond = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.kkl_conditional_var_bound"),
                vec![],
            ),
            [
                n.clone(),
                k.clone(),
                f.clone(),
                d.clone(),
                hd.clone(),
                // hdd0 : 0 ≤ d·d  := mul_nonneg d d hd hd.
                Expr::apps(
                    Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]),
                    [d.clone(), d.clone(), hd.clone(), hd.clone()],
                ),
                hdd1.clone(),
                h0.clone(),
                h1.clone(),
                hkt.clone(),
            ],
        );

        // (2) hNn : 0 ≤ Nn.
        let h_nn = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.natCast_nonneg"), vec![]),
            [n.clone()],
        );

        // (3) h_scaled : Nn·(K·Var) ≤ Nn·(I+I).
        let i_plus_i = c.add(i_tot.clone(), i_tot.clone());
        let nn_kv = c.mul(nn.clone(), k_v.clone());
        let nn_ii = c.mul(nn.clone(), i_plus_i.clone());
        let h_scaled = Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]),
            [nn.clone(), k_v.clone(), i_plus_i.clone(), cond, h_nn],
        );

        // (4) e_distrib : Nn·(I+I) = Nn·I + Nn·I.
        let nn_i = c.mul(nn.clone(), i_tot.clone());
        let nn_i_plus_nn_i = c.add(nn_i.clone(), nn_i.clone());
        let e_distrib = Expr::apps(
            Expr::const_(Name::from_string("Rat.left_distrib"), vec![]),
            [nn.clone(), i_tot.clone(), i_tot.clone()],
        );

        // (5) eSc : Σ(const (K·Var)) = Nn·(K·Var).
        //   Fin.sum_const n (K·Var) : Σ(fun _ => K·Var) = (natCast n)·(K·Var).
        let sum_const_kv = c.fin_sum(&n, {
            let mut cb = EnvDeclBuilder::child_of(&b);
            let fin_n = c.fin_of(&n);
            let (i_id, _i) = cb.fresh_local(fin_n.clone());
            cb.finish_child(cb.mk_lam(i_id, BinderInfo::Default, fin_n, k_v.clone()))
        });
        let e_sc = Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_const"), vec![]),
            [n.clone(), k_v.clone()],
        );

        // (6) eSg : Σ g = Nn·I.
        //   Fin.sum_smul n Nn Inf : Σ(fun i => Nn·Inf_i) = Nn·Σ Inf, and Σ Inf ≡ I.
        let sum_g = c.fin_sum(&n, gg.clone());
        let sum_inf = c.fin_sum(&n, inf.clone());
        let e_sg = Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_smul"), vec![]),
            [n.clone(), nn.clone(), inf.clone()],
        ); // Σ g = Nn·(Σ Inf)   (Σ Inf ≡ I by δ)
        let nn_sum_inf = c.mul(nn.clone(), sum_inf.clone());

        // (7) eSF : Σ F = Σ g + Σ g.
        let sum_f = c.fin_sum(&n, ff.clone());
        let sum_g_plus_sum_g = c.add(sum_g.clone(), sum_g.clone());
        let e_sf0 = Expr::apps(
            Expr::const_(Name::from_string("Fin.sum_add"), vec![]),
            [n.clone(), gg.clone(), gg.clone()],
        ); // Σ F = Σ g + Σ g
           //   eSF' : Σ F = (Nn·I) + (Nn·I)   transport both legs along eSg.
           //   leg1 : Σ g + Σ g = (Nn·I) + Σ g   congr_add_r (Σ g) eSg
        let l1 = c.congr_add_r(&b, &sum_g, sum_g.clone(), nn_sum_inf.clone(), e_sg.clone());
        let nn_si_plus_sum_g = c.add(nn_sum_inf.clone(), sum_g.clone());
        //   leg2 : (Nn·I) + Σ g = (Nn·I) + (Nn·I)   congr_add_l (Nn·I) eSg
        let l2 = c.congr_add_l(
            &b,
            &nn_sum_inf,
            sum_g.clone(),
            nn_sum_inf.clone(),
            e_sg.clone(),
        );
        let nn_si_plus_nn_si = c.add(nn_sum_inf.clone(), nn_sum_inf.clone());
        let l12 = c.trans(
            sum_g_plus_sum_g.clone(),
            nn_si_plus_sum_g.clone(),
            nn_si_plus_nn_si.clone(),
            l1,
            l2,
        );
        // eSF : Σ F = (Nn·I) + (Nn·I).
        let e_sf = c.trans(
            sum_f.clone(),
            sum_g_plus_sum_g.clone(),
            nn_si_plus_nn_si.clone(),
            e_sf0,
            l12,
        );

        // (8) hsum : Σ(const (K·Var)) ≤ Σ F.
        //   Start from h_scaled : Nn·(K·V) ≤ Nn·(I+I).
        //   8a: rewrite RHS Nn·(I+I) ↦ (Nn·I)+(Nn·I) via e_distrib.
        let motive_8a = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = m.fresh_local(c.rat.clone());
            let body = c.rat_le(nn_kv.clone(), z);
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h8a = c.subst(
            motive_8a,
            nn_ii.clone(),
            nn_i_plus_nn_i.clone(),
            e_distrib,
            h_scaled,
        );
        //   8b: rewrite RHS (Nn·I)+(Nn·I) ↦ Σ F via symm eSF.
        let e_sf_symm = c.symm(sum_f.clone(), nn_si_plus_nn_si.clone(), e_sf);
        let motive_8b = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = m.fresh_local(c.rat.clone());
            let body = c.rat_le(nn_kv.clone(), z);
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h8b = c.subst(
            motive_8b,
            nn_si_plus_nn_si.clone(),
            sum_f.clone(),
            e_sf_symm,
            h8a,
        );
        //   8c: rewrite LHS Nn·(K·V) ↦ Σ(const (K·V)) via symm eSc.
        let e_sc_symm = c.symm(sum_const_kv.clone(), nn_kv.clone(), e_sc);
        let motive_8c = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = m.fresh_local(c.rat.clone());
            let body = c.rat_le(z, sum_f.clone());
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let hsum = c.subst(
            motive_8c,
            nn_kv.clone(),
            sum_const_kv.clone(),
            e_sc_symm,
            h8b,
        );

        // (9) ∃ i, K·V ≤ F i := exists_ge_of_sum_ge_pos n (K·V) F hpos hsum.
        Expr::apps(
            Expr::const_(Name::from_string("Fin.exists_ge_of_sum_ge_pos"), vec![]),
            [n.clone(), k_v.clone(), ff.clone(), hpos.clone(), hsum],
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
    let e = bind(&b, hkt_id, hkt_ty, body);
    let e = bind(&b, h1_id, h1_ty, e);
    let e = bind(&b, h0_id, h0_ty, e);
    let e = bind(&b, hdd1_id, hdd1_ty, e);
    let e = bind(&b, hd_id, hd_ty, e);
    let e = bind(&b, hpos_id, hpos_ty, e);
    let e = bind(&b, d_id, c.rat.clone(), e);
    let e = bind(&b, f_id, bf_ty, e);
    let e = bind(&b, k_id, c.nat.clone(), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}
