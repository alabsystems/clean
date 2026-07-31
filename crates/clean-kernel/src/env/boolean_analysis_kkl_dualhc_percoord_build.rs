// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// PER-COORDINATE dual-HC term builder (`build_per_coord`). `include!`d into
// `boolean_analysis_kkl_dualhc_percoord.rs` — shares its `PerCoordConsts` and
// imports. Split out to keep each file under the 500-line convention. (Regular
// `//` comments: inner doc `//!` is not allowed at an `include!` site.)

impl PerCoordConsts {
    fn ofnat(&self, k: usize) -> Expr {
        let mut nat = self.nat_zero.clone();
        for _ in 0..k {
            nat = Expr::app(self.nat_succ.clone(), nat);
        }
        Expr::app(Expr::const_(Name::from_string("Rat.ofNat"), vec![]), nat)
    }
    fn nat_lit(&self, k: usize) -> Expr {
        let mut nat = self.nat_zero.clone();
        for _ in 0..k {
            nat = Expr::app(self.nat_succ.clone(), nat);
        }
        nat
    }
    /// `0 < (lit k)` via `@Int.NonNeg.mk (k-1)`.
    fn lit_pos(&self, k: usize) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            self.nat_lit(k - 1),
        )
    }
    fn pow_pos_at(&self, k: usize, n: &Expr) -> Expr {
        Expr::apps(
            self.pow_pos.clone(),
            [self.lit(k), n.clone(), self.lit_pos(k)],
        )
    }
    fn mul_pos_at(&self, a: Expr, bb: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.mul_pos.clone(), [a, bb, ha, hb])
    }
    fn ne_at(&self, a: Expr, ha: Expr) -> Expr {
        Expr::apps(self.ne_zero_of_pos.clone(), [a, ha])
    }
    fn inv_cancel_at(&self, a: Expr, hne: Expr) -> Expr {
        Expr::apps(self.mul_inv_cancel.clone(), [a, hne])
    }
}

/// Build the type (`for_value = false`) or proof value (`for_value = true`) of
/// `dualhc_per_coord`.
fn build_per_coord(c: &PerCoordConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.bool_fn_of(&n));
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let half = c.half();
    let four = c.lit(4);
    let sixteen = c.mul(four.clone(), four.clone()); // byte-match sq_le's 16
    let big_d = c.pow_of(8, &n); // 8^n (byte-match sq_le's pow8)
    let pow2n = c.pow_of(2, &n);
    let d_inv = c.inv(big_d.clone());

    let g = c.deriv_lam(&b, &n, &f, &i);
    let tg = c.op(&n, &g);

    let w = c.ssum(
        &n,
        c.lam_hcp(&b, &n, |y| {
            let tgy = Expr::app(tg.clone(), y.clone());
            c.mul(tgy.clone(), tgy)
        }),
    );
    let m = c.ssum(
        &n,
        c.lam_hcp(&b, &n, |x| {
            let gx = Expr::app(g.clone(), x.clone());
            c.mul(c.mul(gx.clone(), gx), c.mul(half.clone(), half.clone()))
        }),
    );
    let m_cube = c.mul(m.clone(), c.mul(m.clone(), m.clone()));
    let inf = c.influence_of(&n, &f, &i);
    let w_norm = c.mul(w.clone(), d_inv.clone());

    let four_of = c.ofnat(4);
    let sixteen_of = c.ofnat(16);
    let _ = &pow2n;

    let ww = c.mul(w.clone(), w.clone());
    let wn_wn = c.mul(w_norm.clone(), w_norm.clone());
    let cc = c.mul(big_d.clone(), big_d.clone()); // 64^n = 8^n·8^n
    let cube16 = c.mul(
        c.mul(sixteen_of.clone(), inf.clone()),
        c.mul(inf.clone(), inf.clone()),
    );

    // hypothesis types.
    //   h_meas : (8^n·8^n)·cube16(Inf) = 16·(m_cube·8^n)   -- the MEASURE identity
    //            (the pure-`Rat`+`powNat` `64^n`-bookkeeping; from m = 2^n·Inf and
    //             (2^n)³ = 8^n — see the module report).
    let rhs_bound = c.mul(sixteen.clone(), c.mul(m_cube.clone(), big_d.clone()));
    let h_meas_ty = c.eq_rat(c.mul(cc.clone(), cube16.clone()), rhs_bound.clone());
    let h0_ty = c.le(c.rat_zero.clone(), inf.clone());
    let h1_ty = c.lt(inf.clone(), c.rat_one.clone());

    let (hm_id, h_meas) = b.fresh_local(h_meas_ty.clone());
    let (h0_id, h0) = b.fresh_local(h0_ty.clone());
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());

    // 0 ≤ W, 0 ≤ inv(8^n), 0 ≤ W_norm, 0 ≤ 4.
    let hw_nonneg = build_w_nonneg(c, &b, &n, &tg);
    let h_dinv_nonneg = build_dinv_nonneg(c, &big_d, &n);
    let h_wnorm_nonneg = {
        let mul_nonneg = Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]);
        Expr::apps(
            mul_nonneg,
            [w.clone(), d_inv.clone(), hw_nonneg, h_dinv_nonneg],
        )
    };
    let h4_nonneg = {
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let refl = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [bool_c, btrue],
        );
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]),
            [c.rat_zero.clone(), four_of.clone(), refl],
        )
    };

    let concl = {
        let of_wn = Expr::apps(
            c.nnreal_of_rat.clone(),
            [w_norm.clone(), h_wnorm_nonneg.clone()],
        );
        let four_nn = Expr::apps(
            c.nnreal_of_rat.clone(),
            [four_of.clone(), h4_nonneg.clone()],
        );
        let pow32 = Expr::apps(c.nnreal_pow32.clone(), [inf.clone(), h0.clone()]);
        let rhs = Expr::apps(c.nnreal_mul.clone(), [four_nn, pow32]);
        Expr::apps(c.nnreal_le.clone(), [of_wn, rhs])
    };

    let body = if for_value {
        // positivity / cancellation atoms.
        let h_d_pos = c.pow_pos_at(8, &n);
        let h_cc_pos = c.mul_pos_at(
            big_d.clone(),
            big_d.clone(),
            h_d_pos.clone(),
            h_d_pos.clone(),
        );
        let h_d_ne = c.ne_at(big_d.clone(), h_d_pos);
        let h_d_cancel = c.inv_cancel_at(big_d.clone(), h_d_ne); // 8^n·inv 8^n = 1

        // eL : (8^n·8^n)·(W_norm·W_norm) = W·W.
        let e_l = build_e_l(c, &b, &big_d, &d_inv, &w, &w_norm, h_d_cancel);

        // landed squared bound : W·W ≤ 16·(m_cube·8^n).
        let bound = Expr::apps(c.sq_le.clone(), [n.clone(), f.clone(), i.clone()]);

        // transport LHS along eL (W·W → cc·wn_wn).
        let cc_wnwn = c.mul(cc.clone(), wn_wn.clone());
        let motive_l = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = d.fresh_local(c.rat.clone());
            let body = c.le(z, rhs_bound.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let e_l_symm = c.symm(cc_wnwn.clone(), ww.clone(), e_l); // W·W = cc·wn_wn
        let step_l = c.subst_prop(motive_l, ww.clone(), cc_wnwn.clone(), e_l_symm, bound);

        // transport RHS along h_meas (16·(m_cube·8^n) → cc·cube16).
        let cc_cube = c.mul(cc.clone(), cube16.clone());
        let motive_r = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = d.fresh_local(c.rat.clone());
            let body = c.le(cc_wnwn.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        // h_meas : cc·cube16 = 16·(m_cube·8^n) ; symm gives 16·(m_cube·8^n) = cc·cube16.
        let h_meas_symm = c.symm(cc_cube.clone(), rhs_bound.clone(), h_meas);
        let h_mul = c.subst_prop(
            motive_r,
            rhs_bound.clone(),
            cc_cube.clone(),
            h_meas_symm,
            step_l,
        );

        // cancel cc>0 : wn_wn ≤ cube16(Inf).
        let cancel = Expr::apps(
            c.le_cancel.clone(),
            [wn_wn.clone(), cube16.clone(), cc.clone(), h_cc_pos, h_mul],
        );

        // connect : ofRat W_norm ≤ 4·pow32 Inf.
        Expr::apps(
            c.desq.clone(),
            [
                w_norm.clone(),
                inf.clone(),
                h_wnorm_nonneg.clone(),
                h0.clone(),
                h1.clone(),
                cancel,
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
    let e = bind(&b, h1_id, h1_ty, body);
    let e = bind(&b, h0_id, h0_ty, e);
    let e = bind(&b, hm_id, h_meas_ty, e);
    let e = bind(&b, i_id, c.fin_of(&n), e);
    let e = bind(&b, f_id, c.bool_fn_of(&n), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}

/// Build the type (`for_value = false`) or proof value (`for_value = true`) of
/// `dualhc_per_coord_uncond` — `dualhc_per_coord` with `h_meas` DISCHARGED by
/// `build_h_meas`. Drops the `h_meas` binder; otherwise the same conclusion.
fn build_per_coord_uncond(c: &PerCoordConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.bool_fn_of(&n));
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let _half = c.half();
    let big_d = c.pow_of(8, &n); // 8^n
    let d_inv = c.inv(big_d.clone());

    let g = c.deriv_lam(&b, &n, &f, &i);
    let tg = c.op(&n, &g);
    let w = c.ssum(
        &n,
        c.lam_hcp(&b, &n, |y| {
            let tgy = Expr::app(tg.clone(), y.clone());
            c.mul(tgy.clone(), tgy)
        }),
    );
    let inf = c.influence_of(&n, &f, &i);
    let w_norm = c.mul(w.clone(), d_inv.clone());
    let four_of = c.ofnat(4);

    let h0_ty = c.le(c.rat_zero.clone(), inf.clone());
    let h1_ty = c.lt(inf.clone(), c.rat_one.clone());
    let (h0_id, h0) = b.fresh_local(h0_ty.clone());
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());

    // 0 ≤ W_norm, 0 ≤ 4 (byte-match build_per_coord's nonneg witnesses).
    let hw_nonneg = build_w_nonneg(c, &b, &n, &tg);
    let h_dinv_nonneg = build_dinv_nonneg(c, &big_d, &n);
    let h_wnorm_nonneg = {
        let mul_nonneg = Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]);
        Expr::apps(
            mul_nonneg,
            [w.clone(), d_inv.clone(), hw_nonneg, h_dinv_nonneg],
        )
    };
    let h4_nonneg = {
        let bool_c = Expr::const_(Name::from_string("Bool"), vec![]);
        let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let refl = Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [bool_c, btrue],
        );
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]),
            [c.rat_zero.clone(), four_of.clone(), refl],
        )
    };

    let concl = {
        let of_wn = Expr::apps(c.nnreal_of_rat.clone(), [w_norm.clone(), h_wnorm_nonneg]);
        let four_nn = Expr::apps(c.nnreal_of_rat.clone(), [four_of.clone(), h4_nonneg]);
        let pow32 = Expr::apps(c.nnreal_pow32.clone(), [inf.clone(), h0.clone()]);
        let rhs = Expr::apps(c.nnreal_mul.clone(), [four_nn, pow32]);
        Expr::apps(c.nnreal_le.clone(), [of_wn, rhs])
    };

    let body = if for_value {
        // h_meas DISCHARGED : build_h_meas c b n f i.
        let h_meas = build_h_meas(c, &b, &n, &f, &i);
        // apply the h_meas-taking core: dualhc_per_coord n f i h_meas h0 h1.
        let core = Expr::const_(Name::from_string("BoolAnalysis.dualhc_per_coord"), vec![]);
        Expr::apps(
            core,
            [
                n.clone(),
                f.clone(),
                i.clone(),
                h_meas,
                h0.clone(),
                h1.clone(),
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
    let e = bind(&b, h1_id, h1_ty, body);
    let e = bind(&b, h0_id, h0_ty, e);
    let e = bind(&b, i_id, c.fin_of(&n), e);
    let e = bind(&b, f_id, c.bool_fn_of(&n), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}

/// `0 ≤ W` where `W = subsetSum n (fun y => tg y·tg y)` — `Fin.sum_nonneg` of the
/// decoded squared summand.
fn build_w_nonneg(c: &PerCoordConsts, parent: &EnvDeclBuilder, n: &Expr, tg: &Expr) -> Expr {
    let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
    let two = Expr::app(
        c.nat_succ.clone(),
        Expr::app(c.nat_succ.clone(), c.nat_zero.clone()),
    );
    let pow2 = Expr::apps(nat_pow, [two, n.clone()]);
    let fin_pow = c.fin_of(&pow2);
    let hc_decode = Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]);
    let sq_nonneg = Expr::const_(Name::from_string("Rat.sq_nonneg"), vec![]);
    let fin_sum_nonneg = Expr::const_(Name::from_string("Fin.sum_nonneg"), vec![]);

    let decoded_fn = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = d.fresh_local(fin_pow.clone());
        let dec = Expr::apps(hc_decode.clone(), [n.clone(), j.clone()]);
        let tgx = Expr::app(tg.clone(), dec);
        let body = c.mul(tgx.clone(), tgx);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_pow.clone(), body))
    };
    let per = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = d.fresh_local(fin_pow.clone());
        let dec = Expr::apps(hc_decode.clone(), [n.clone(), j.clone()]);
        let tgx = Expr::app(tg.clone(), dec);
        let body = Expr::app(sq_nonneg.clone(), tgx);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_pow.clone(), body))
    };
    Expr::apps(fin_sum_nonneg, [pow2, decoded_fn, per])
}

/// `0 ≤ inv(8^n)` from `0 < inv(8^n)` via the `lt_iff_le_not_le` idiom:
/// `And.left (Iff.mp (Rat.lt_iff_le_not_le 0 (inv 8^n)) (inv_pos …))`.
fn build_dinv_nonneg(c: &PerCoordConsts, big_d: &Expr, n: &Expr) -> Expr {
    let inv_pos = Expr::const_(Name::from_string("Rat.inv_pos"), vec![]);
    let lt_iff = Expr::const_(Name::from_string("Rat.lt_iff_le_not_le"), vec![]);
    let h_d_pos = c.pow_pos_at(8, n);
    let d_inv = c.inv(big_d.clone());
    let h_inv_pos = Expr::apps(inv_pos, [big_d.clone(), h_d_pos]); // 0 < inv 8^n
                                                                   // le_branch := le 0 (inv 8^n) ; not_le := Not (le (inv 8^n) 0).
    let le_branch = c.le(c.rat_zero.clone(), d_inv.clone());
    let not_le = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        c.le(d_inv.clone(), c.rat_zero.clone()),
    );
    let iff_app = Expr::apps(lt_iff, [c.rat_zero.clone(), d_inv.clone()]);
    let lt_ty = c.lt(c.rat_zero.clone(), d_inv.clone());
    let and_ty = Expr::apps(
        Expr::const_(Name::from_string("And"), vec![]),
        [le_branch.clone(), not_le.clone()],
    );
    let iff_mp = Expr::apps(
        Expr::const_(Name::from_string("Iff.mp"), vec![]),
        [lt_ty, and_ty, iff_app, h_inv_pos],
    );
    Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [le_branch, not_le, iff_mp],
    )
}

include!("boolean_analysis_kkl_dualhc_percoord_eqs.rs");
