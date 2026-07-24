// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// KKL finish — RUNG 5 proof-term + hypothesis builders. `include!`d into
// `boolean_analysis_kkl_conditional.rs` so it shares `CondConsts` and keeps
// the registration module under the 500-line convention. (Regular `//`
// comments only — inner doc `//!` is not allowed at an `include!` site.)

/// `∀ (i : Fin n), Rat.le Rat.zero (Influence n f i)`.
fn h0_hyp(c: &CondConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), n.clone());
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let inf = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.Influence"), vec![]),
        [n.clone(), f.clone(), i.clone()],
    );
    let body = c.rat_le(c.rat_zero(), inf);
    b.finish_child(b.mk_pi(i_id, BinderInfo::Default, fin_n, body))
}

/// `∀ (i : Fin n), Rat.le (Influence n f i) (d·d)`.
fn h1_hyp(c: &CondConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, dd: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_n = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), n.clone());
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let inf = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.Influence"), vec![]),
        [n.clone(), f.clone(), i.clone()],
    );
    let body = c.rat_le(inf, dd.clone());
    b.finish_child(b.mk_pi(i_id, BinderInfo::Default, fin_n, body))
}

/// Build the type (`for_value=false`) / proof (`for_value=true`).
fn build_conditional(c: &CondConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());
    let (d_id, d) = b.fresh_local(c.rat.clone());
    let dd = c.mul(d.clone(), d.clone());

    let hd_ty = c.rat_le(c.rat_zero(), d.clone());
    let (hd_id, _hd) = b.fresh_local(hd_ty.clone());
    let hdd0_ty = c.rat_le(c.rat_zero(), dd.clone());
    let (hdd0_id, hdd0) = b.fresh_local(hdd0_ty.clone());
    let hdd1_ty = c.rat_lt(dd.clone(), c.rat_one());
    let (hdd1_id, hdd1) = b.fresh_local(hdd1_ty.clone());
    let h0_ty = h0_hyp(c, &b, &n, &f);
    let (h0_id, h0) = b.fresh_local(h0_ty.clone());
    let h1_ty = h1_hyp(c, &b, &n, &f, &dd);
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());

    let p9 = c.pow9(&k);
    let i_tot = c.total_influence_of(&n, &f);
    let d_i = c.mul(d.clone(), i_tot.clone()); // δ·I
    let t = c.mul(p9.clone(), d_i.clone()); // t := 9^k·(δ·I)
    let kcast = c.natcast(&c.succ(k.clone())); // K := natCast(k+1)
    let k_t = c.mul(kcast.clone(), t.clone()); // K·t

    let hkt_ty = c.rat_le(k_t.clone(), i_tot.clone());
    let (hkt_id, hkt) = b.fresh_local(hkt_ty.clone());

    let v = c.variance_of(&n, &f);
    let k_v = c.mul(kcast.clone(), v.clone()); // K·V
    let concl = c.rat_le(k_v.clone(), c.add(i_tot.clone(), i_tot.clone()));

    let body = if for_value {
        let m = c.m_lo(&b, &n, &k, &f); // M
        let four = c.four();
        let four_m = c.mul(four.clone(), m.clone()); // 4·M

        // Σwn — byte-identical to rung 2's RHS Fin.sum and rung 4c's LHS.
        // We re-spell it via rung 4c's RHS instead (4·dI) by going through the
        // bridge directly; the rung 2 RHS Σwn is the SHARED middle term.
        let sigma = {
            // Fin.sum n (fun i => W_norm_i). Reconstructed via the bridge's LHS
            // term builder is unnecessary: rung 2 produces `9^k·Σwn` and rung 4c
            // consumes `Σwn`; we name `Σwn` by applying rung 2's conclusion which
            // is `4·M ≤ 9^k·Σwn`. We capture Σwn by reading it off the bridge.
            wnorm_sum_term(c, &b, &n, &f)
        };
        let p9_sigma = c.mul(p9.clone(), sigma.clone()); // 9^k·Σwn
        let four_di = c.mul(four.clone(), d_i.clone()); // 4·(δ·I)
        let p9_4di = c.mul(p9.clone(), four_di.clone()); // 9^k·(4·δ·I)
        let four_t = c.mul(four.clone(), t.clone()); // 4·t = 4·(9^k·δ·I)

        // (1) r2 : 4·M ≤ 9^k·Σwn.
        let r2 = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.kkl_lowband_le_wnorm_sum"),
                vec![],
            ),
            [n.clone(), k.clone(), f.clone()],
        );
        // (2) br : Σwn ≤ 4·δI.
        let br = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.kkl_wnorm_sum_le_rat"),
                vec![],
            ),
            [
                n.clone(),
                f.clone(),
                d.clone(),
                _hd.clone(),
                hdd0.clone(),
                hdd1.clone(),
                h0.clone(),
                h1.clone(),
            ],
        );
        // (3) h9 : 0 ≤ 9^k.
        let h9 = Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_nonneg"), vec![]),
            [
                Expr::app(c.rat_of_nat.clone(), c.nat_lit(9)),
                k.clone(),
                c.zero_le_nine(),
            ],
        );
        // (4) mono : 9^k·Σwn ≤ 9^k·(4·δI).
        let mono = Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]),
            [p9.clone(), sigma.clone(), four_di.clone(), br, h9],
        );
        // (5) r2' : 4·M ≤ 9^k·(4·δI).
        let le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);
        let r2p = Expr::apps(
            le_trans.clone(),
            [four_m.clone(), p9_sigma.clone(), p9_4di.clone(), r2, mono],
        );
        // (6) eR : 9^k·(4·δI) = 4·(9^k·δI).
        //   9^k·(4·δI) = (9^k·4)·δI   symm (assoc 9^k 4 δI)
        //             = (4·9^k)·δI   congr_r δI (comm 9^k 4)
        //             = 4·(9^k·δI)   assoc 4 9^k δI
        let p9_4 = c.mul(p9.clone(), four.clone());
        let p9_4_di = c.mul(p9_4.clone(), d_i.clone());
        let four_p9 = c.mul(four.clone(), p9.clone());
        let four_p9_di = c.mul(four_p9.clone(), d_i.clone());
        let e1 = c.symm(
            p9_4_di.clone(),
            p9_4di.clone(),
            c.assoc(p9.clone(), four.clone(), d_i.clone()),
        );
        let e2 = c.congr_r(
            &b,
            &d_i,
            p9_4.clone(),
            four_p9.clone(),
            c.comm(p9.clone(), four.clone()),
        );
        let e3 = c.assoc(four.clone(), p9.clone(), d_i.clone());
        let e12 = c.trans(p9_4di.clone(), p9_4_di.clone(), four_p9_di.clone(), e1, e2);
        let e_r = c.trans(p9_4di.clone(), four_p9_di.clone(), four_t.clone(), e12, e3);
        // (7) r2'' : 4·M ≤ 4·t   subst (fun z => 4·M ≤ z) eR r2'.
        let motive_r = {
            let mut m2 = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = m2.fresh_local(c.rat.clone());
            let body = c.rat_le(four_m.clone(), z);
            m2.finish_child(m2.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let r2pp = c.subst(motive_r, p9_4di.clone(), four_t.clone(), e_r, r2p);
        // (8) hMt : M ≤ t   le_of_mul_le_mul_left_pos M t 4 (0<4) r2''.
        let h_mt = Expr::apps(
            Expr::const_(Name::from_string("Rat.le_of_mul_le_mul_left_pos"), vec![]),
            [m.clone(), t.clone(), four.clone(), c.four_pos(), r2pp],
        );
        // (9) r3 : K·(V − t) ≤ I.
        let r3 = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.kkl_variance_pinch_of_lowband_le"),
                vec![],
            ),
            [n.clone(), k.clone(), f.clone(), t.clone(), h_mt],
        );
        let v_sub_t = c.sub(v.clone(), t.clone()); // V − t
        let k_vsubt = c.mul(kcast.clone(), v_sub_t.clone()); // K·(V−t)

        // (10) eV : V = (V − t) + t   symm (sub_add_cancel t V).
        let v_sub_t_plus_t = c.add(v_sub_t.clone(), t.clone()); // (V−t)+t
        let sub_add_cancel = Expr::const_(Name::from_string("Rat.sub_add_cancel"), vec![]);
        let sac = Expr::apps(sub_add_cancel, [t.clone(), v.clone()]); // (V−t)+t = V
        let e_v = c.symm(v_sub_t_plus_t.clone(), v.clone(), sac); // V = (V−t)+t

        // (11) eKV : K·V = K·(V−t) + K·t.
        //   K·V = K·((V−t)+t)   congr_l K eV
        //       = K·(V−t) + K·t left_distrib K (V−t) t
        let k_vsubt_plus_t = c.mul(kcast.clone(), v_sub_t_plus_t.clone()); // K·((V−t)+t)
        let kvsubt_plus_kt = c.add(k_vsubt.clone(), k_t.clone()); // K·(V−t)+K·t
        let cong_kv = c.congr_l(&b, &kcast, v.clone(), v_sub_t_plus_t.clone(), e_v);
        let ld = Expr::apps(
            Expr::const_(Name::from_string("Rat.left_distrib"), vec![]),
            [kcast.clone(), v_sub_t.clone(), t.clone()],
        );
        let e_kv = c.trans(
            k_v.clone(),
            k_vsubt_plus_t.clone(),
            kvsubt_plus_kt.clone(),
            cong_kv,
            ld,
        );

        // (12) add_le : K·(V−t) + K·t ≤ I + I.
        let add_le = Expr::apps(
            Expr::const_(Name::from_string("Rat.add_le_add"), vec![]),
            [
                k_vsubt.clone(),
                i_tot.clone(),
                k_t.clone(),
                i_tot.clone(),
                r3,
                hkt,
            ],
        );

        // (13) K·V ≤ I+I   subst (fun z => z ≤ I+I) (symm eKV) add_le.
        let e_kv_symm = c.symm(k_v.clone(), kvsubt_plus_kt.clone(), e_kv);
        let motive_f = {
            let mut m2 = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = m2.fresh_local(c.rat.clone());
            let body = c.rat_le(z, c.add(i_tot.clone(), i_tot.clone()));
            m2.finish_child(m2.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        c.subst(
            motive_f,
            kvsubt_plus_kt.clone(),
            k_v.clone(),
            e_kv_symm,
            add_le,
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
    let e = bind(&b, hdd0_id, hdd0_ty, e);
    let e = bind(&b, hd_id, hd_ty, e);
    let e = bind(&b, d_id, c.rat.clone(), e);
    let e = bind(&b, f_id, bf_ty, e);
    let e = bind(&b, k_id, c.nat.clone(), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}

/// `Σ_i W_norm_i := Fin.sum n (fun i => W_norm_i)` — BYTE-IDENTICAL to rung 2's
/// `wn_fn` Fin.sum and rung 4c's `wn_rat_fn`. Reconstructed here (the
/// `noiseOp(1/3) D_i (pm∘f)` two-norm normalized by `inv(8^n)`).
fn wnorm_sum_term(c: &CondConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin = Expr::const_(Name::from_string("Fin"), vec![]);
    let fin_n = Expr::app(fin, n.clone());
    let (i_id, i) = b.fresh_local(fin_n.clone());
    let w_norm = w_norm_i(c, &b, n, f, &i);
    let lam = b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, w_norm));
    Expr::apps(
        Expr::const_(Name::from_string("Fin.sum"), vec![]),
        [n.clone(), lam],
    )
}

/// `W_norm_i := (subsetSum n (fun y => (T_{1/3} D_i (pm∘f) y)²)) · inv(8^n)`.
fn w_norm_i(c: &CondConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
    let hcp = c.hcpoint_of(n);
    let pm = Expr::const_(Name::from_string("BoolAnalysis.pm"), vec![]);
    let hc_flip = Expr::const_(Name::from_string("BoolAnalysis.hcFlip"), vec![]);
    let noise_op = Expr::const_(Name::from_string("BoolAnalysis.noiseOp"), vec![]);
    let subset_sum = Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]);
    let rat_inv = Expr::const_(Name::from_string("Rat.inv"), vec![]);

    // D_i (pm∘f) := fun (x : HCPoint n) => pm(f x) - pm(f (hcFlip n x i)).
    let g = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let fx = Expr::app(pm.clone(), Expr::app(f.clone(), x.clone()));
        let flip = Expr::apps(hc_flip.clone(), [n.clone(), x.clone(), i.clone()]);
        let fflip = Expr::app(pm.clone(), Expr::app(f.clone(), flip));
        let body = c.sub(fx, fflip);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp.clone(), body))
    };
    // third := Rat.mk (Int.ofNat 1) 3.
    let third = Expr::apps(
        c.rat_mk.clone(),
        [Expr::app(c.int_of_nat.clone(), c.one_nat()), c.nat_lit(3)],
    );
    // T g := noiseOp (1/3) n g.
    let tg = Expr::apps(noise_op, [third, n.clone(), g]);
    // W := subsetSum n (fun y => (T g y)·(T g y)).
    let w = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (y_id, y) = d.fresh_local(hcp.clone());
        let tgy = Expr::app(tg.clone(), y.clone());
        let body = c.mul(tgy.clone(), tgy);
        let lam = d.finish_child(d.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body));
        Expr::apps(subset_sum, [n.clone(), lam])
    };
    // inv(8^n) := Rat.inv (powNat (mk(ofNat 8)1) n).
    let eight = Expr::apps(
        c.rat_mk.clone(),
        [Expr::app(c.int_of_nat.clone(), c.nat_lit(8)), c.one_nat()],
    );
    let pow8 = Expr::apps(c.pow_nat.clone(), [eight, n.clone()]);
    let d_inv = Expr::app(rat_inv, pow8);
    c.mul(w, d_inv)
}
