// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Proof builder for the H1 connect (`boolean_analysis_kkl_dualhc_h1connect.rs`).

impl H1ConnectConsts {
    /// `mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]),
            [a, b, ha, hb],
        )
    }
    /// `ind_nonneg b : 0 ≤ ind b`.
    fn ind_nonneg(&self, b: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("BoolAnalysis.ind_nonneg"), vec![]),
            b,
        )
    }
    /// `fourier_sq_nonneg n f S : 0 ≤ f̂(S)·f̂(S)`.
    fn fourier_sq_nonneg(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.fourier_sq_nonneg"), vec![]),
            [n.clone(), f.clone(), s.clone()],
        )
    }
    /// `∀ S, 0 ≤ w S` proof term (the RUNG A `hw` argument).
    fn hw_proof(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let si = Expr::app(s.clone(), i.clone());
        let c4 = self.mul(self.four(), self.ind_(si.clone())); // 4·ind(S i)
        let fsq = self.fsq(n, f, &s);
        // 0 ≤ 4·ind(S i)
        let h_c4 = self.mul_nonneg(
            self.four(),
            self.ind_(si.clone()),
            self.le_of_ble_refl(self.order.rat_zero.clone(), self.four()),
            self.ind_nonneg(si),
        );
        // 0 ≤ (4·ind)·(f̂·f̂)
        let body = self.mul_nonneg(c4, fsq, h_c4, self.fourier_sq_nonneg(n, f, &s));
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

fn build_h1(c: &H1ConnectConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let f_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let third = c.third();
    let ninth = c.mul(third.clone(), third.clone()); // 1/9
    let c8 = c.pow(&c.eight(), &n); // 8^n
    let p9k = c.pow(&c.nine(), &k); // 9^k

    // integrands / sums
    let w_fn = c.w_fn(&b, &n, &f, &i);
    let feed_fn = c.feed_fn(&b, &n, &f, &i);
    let mble_fn = c.mble_fn(&b, &n, &k, &f, &i);
    let notble_fn = c.notble_fn(&b, &n, &k, &f, &i);
    let coord_fn = c.coord_w_band_fn(&b, &n, &k, &f, &i);

    let feed = c.ssum(&n, feed_fn.clone());
    let mble = c.ssum(&n, mble_fn.clone());
    let notble_sum = c.ssum(&n, notble_fn.clone());
    let wb = c.ssum(&n, coord_fn.clone()); // W^{≤k}[D_i f]
    let w_i = c.w_i(&b, &n, &f, &i); // band-form LHS

    let c8_wb = c.mul(c8.clone(), wb.clone());
    let p9k_wi = c.mul(p9k.clone(), w_i.clone());
    let concl = c.le(c8_wb.clone(), p9k_wi.clone());

    let tail = if for_value {
        // ── Step 1 : RUNG A → ninth^k · Mble ≤ feed ───────────────────────────
        let ninth_k = c.pow(&ninth, &k); // (1/9)^k
        let ninth_k_mble = c.mul(ninth_k.clone(), mble.clone());
        let h_0b = c.le_of_ble_refl(c.order.rat_zero.clone(), ninth.clone()); // 0 ≤ 1/9
        let h_b1 = c.le_of_ble_refl(ninth.clone(), c.one()); // 1/9 ≤ 1
        let hw = c.hw_proof(&b, &n, &f, &i); // ∀ S, 0 ≤ w S
        let rung_a = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_low_band_extract"),
                vec![],
            ),
            [
                n.clone(),
                k.clone(),
                ninth.clone(),
                w_fn.clone(),
                h_0b,
                h_b1,
                hw,
            ],
        ); // ninth^k · Mble ≤ feed

        // ── Step 2 : clear-out → Mble ≤ P9k · feed ────────────────────────────
        // 0 ≤ 9^k
        let h0_9k = c.pow_nonneg(
            &c.nine(),
            &k,
            c.le_of_ble_refl(c.order.rat_zero.clone(), c.nine()),
        );
        // P9k·(ninth^k·Mble) ≤ P9k·feed
        let step2a = c.mul_le_left(
            p9k.clone(),
            ninth_k_mble.clone(),
            feed.clone(),
            rung_a,
            h0_9k,
        );
        // EQ : P9k·(ninth^k·Mble) = Mble
        //   (a) P9k·(ninth^k·Mble) = (P9k·ninth^k)·Mble    [symm assoc P9k ninth^k Mble]
        let p9k_ninthk = c.mul(p9k.clone(), ninth_k.clone());
        let p9kninthk_mble = c.mul(p9k_ninthk.clone(), mble.clone());
        let assoc1 = c.mul_assoc(p9k.clone(), ninth_k.clone(), mble.clone()); // (P9k·ninth^k)·Mble = P9k·(ninth^k·Mble)
        let e_a = c.symm(
            p9kninthk_mble.clone(),
            c.mul(p9k.clone(), ninth_k_mble.clone()),
            assoc1,
        );
        //   (b) (P9k·ninth^k) = (9·ninth)^k     [symm (powNat_mul_base 9 ninth k)]
        let nine_ninth = c.mul(c.nine(), ninth.clone()); // 9·(1/9)
        let nine_ninth_k = c.pow(&nine_ninth, &k); // (9·(1/9))^k
        let pmb = c.pow_mul_base(&c.nine(), &ninth, &k); // (9·ninth)^k = 9^k·ninth^k
        let e_b0 = c.symm(nine_ninth_k.clone(), p9k_ninthk.clone(), pmb); // P9k·ninth^k = (9·ninth)^k
                                                                          //       congr (·Mble) : (P9k·ninth^k)·Mble = ((9·ninth)^k)·Mble
        let e_b = {
            let mot = c.mul_right_motive(&b, &mble);
            c.congr(p9k_ninthk.clone(), nine_ninth_k.clone(), mot, e_b0)
        };
        let nineninthk_mble = c.mul(nine_ninth_k.clone(), mble.clone());
        //   (c) (9·ninth)^k = 1^k   [congr (·^k) nine_third_third_eq_one]
        let nttone = Expr::const_(
            Name::from_string("BoolAnalysis.nine_third_third_eq_one"),
            vec![],
        ); // 9·(third·third) = 1
        let one_k = c.pow(&c.one(), &k); // 1^k
        let e_c0 = {
            let mot = c.pow_k_motive(&b, &k);
            c.congr(nine_ninth.clone(), c.one(), mot, nttone)
        }; // (9·ninth)^k = 1^k
           //       congr (·Mble) : ((9·ninth)^k)·Mble = (1^k)·Mble
        let e_c = {
            let mot = c.mul_right_motive(&b, &mble);
            c.congr(nine_ninth_k.clone(), one_k.clone(), mot, e_c0)
        };
        let onek_mble = c.mul(one_k.clone(), mble.clone());
        //   (d) 1^k = 1   [powNat_one_base k] ; congr (·Mble) : (1^k)·Mble = 1·Mble
        let pob = Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_one_base"), vec![]),
            [k.clone()],
        ); // 1^k = 1
        let e_d = {
            let mot = c.mul_right_motive(&b, &mble);
            c.congr(one_k.clone(), c.one(), mot, pob)
        };
        let one_mble = c.mul(c.one(), mble.clone());
        //   (e) 1·Mble = Mble   [one_mul Mble]
        let e_e = c.one_mul(mble.clone());
        // chain EQ : P9k·(ninth^k·Mble) = Mble
        let p9k_ninthk_mble_full = c.mul(p9k.clone(), ninth_k_mble.clone());
        let eq_t1 = c.trans(
            p9k_ninthk_mble_full.clone(),
            p9kninthk_mble.clone(),
            nineninthk_mble.clone(),
            e_a,
            e_b,
        );
        let eq_t2 = c.trans(
            p9k_ninthk_mble_full.clone(),
            nineninthk_mble.clone(),
            onek_mble.clone(),
            eq_t1,
            e_c,
        );
        let eq_t3 = c.trans(
            p9k_ninthk_mble_full.clone(),
            onek_mble.clone(),
            one_mble.clone(),
            eq_t2,
            e_d,
        );
        let eq_clear = c.trans(
            p9k_ninthk_mble_full.clone(),
            one_mble.clone(),
            mble.clone(),
            eq_t3,
            e_e,
        );
        // transport step2a along eq_clear : motive t => t ≤ P9k·feed
        let p9k_feed = c.mul(p9k.clone(), feed.clone());
        let motive2 = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = d.fresh_local(c.rat());
            let body = c.le(t, p9k_feed.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        let step2 = c.subst(
            motive2,
            p9k_ninthk_mble_full.clone(),
            mble.clone(),
            eq_clear,
            step2a,
        ); // Mble ≤ P9k·feed

        // ── Step 3 : mask swap + band regroup → Wb ≤ P9k·feed ─────────────────
        // mask swap : Mble = notble_sum
        let mask_swap = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_mask_ble_eq_not_ble"),
                vec![],
            ),
            [n.clone(), k.clone(), w_fn.clone()],
        ); // subsetSum (ble mask · w) = subsetSum (not-ble mask · w)
           // band regroup : notble_sum = Wb
        let regroup = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.dualhc_band_regroup"),
                vec![],
            ),
            [n.clone(), k.clone(), f.clone(), i.clone()],
        ); // subsetSum (notble) = subsetSum (coord_w_band)
           // Mble = Wb   [trans mask_swap regroup]
        let mble_eq_wb = c.trans(
            mble.clone(),
            notble_sum.clone(),
            wb.clone(),
            mask_swap,
            regroup,
        );
        // transport step2 along Mble = Wb : motive t => t ≤ P9k·feed
        let motive3 = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = d.fresh_local(c.rat());
            let body = c.le(t, p9k_feed.clone());
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        let step3 = c.subst(motive3, mble.clone(), wb.clone(), mble_eq_wb, step2); // Wb ≤ P9k·feed

        // ── Step 4 : scale by c8 → c8·Wb ≤ P9k·W_i ────────────────────────────
        // 0 ≤ 8^n
        let h0_8n = c.pow_nonneg(
            &c.eight(),
            &n,
            c.le_of_ble_refl(c.order.rat_zero.clone(), c.eight()),
        );
        // c8·Wb ≤ c8·(P9k·feed)
        let step4a = c.mul_le_left(c8.clone(), wb.clone(), p9k_feed.clone(), step3, h0_8n);
        let c8_p9k_feed = c.mul(c8.clone(), p9k_feed.clone()); // c8·(P9k·feed)

        // EQ2 : c8·(P9k·feed) = P9k·W_i
        //   (i) c8·(P9k·feed) = P9k·(c8·feed)   [mul_left_comm c8 P9k feed]
        //       = (c8·P9k)·feed [symm assoc] = (P9k·c8)·feed [congr(·feed)(comm)] = P9k·(c8·feed) [assoc]
        let c8_p9k = c.mul(c8.clone(), p9k.clone());
        let p9k_c8 = c.mul(p9k.clone(), c8.clone());
        let c8p9k_feed = c.mul(c8_p9k.clone(), feed.clone());
        let p9kc8_feed = c.mul(p9k_c8.clone(), feed.clone());
        let c8_feed = c.mul(c8.clone(), feed.clone());
        let p9k_c8feed = c.mul(p9k.clone(), c8_feed.clone());
        //   lc1 : c8·(P9k·feed) = (c8·P9k)·feed   [symm assoc c8 P9k feed]
        let assoc_i = c.mul_assoc(c8.clone(), p9k.clone(), feed.clone());
        let lc1 = c.symm(c8p9k_feed.clone(), c8_p9k_feed.clone(), assoc_i);
        //   lc2 : (c8·P9k)·feed = (P9k·c8)·feed   [congr(·feed)(comm c8 P9k)]
        let lc2 = {
            let mot = c.mul_right_motive(&b, &feed);
            c.congr(
                c8_p9k.clone(),
                p9k_c8.clone(),
                mot,
                c.mul_comm(c8.clone(), p9k.clone()),
            )
        };
        //   lc3 : (P9k·c8)·feed = P9k·(c8·feed)   [assoc P9k c8 feed]
        let lc3 = c.mul_assoc(p9k.clone(), c8.clone(), feed.clone());
        let lc12 = c.trans(
            c8_p9k_feed.clone(),
            c8p9k_feed.clone(),
            p9kc8_feed.clone(),
            lc1,
            lc2,
        );
        let move_p9k = c.trans(
            c8_p9k_feed.clone(),
            p9kc8_feed.clone(),
            p9k_c8feed.clone(),
            lc12,
            lc3,
        );
        //   (ii) c8·feed = W_i :  c8 = D·(D·D) and (D·(D·D))·feed = W_i.
        let dcap = c.cube(&n); // D
        let dd = c.mul(dcap.clone(), dcap.clone()); // D·D
        let dd_d = c.mul(dd.clone(), dcap.clone()); // (D·D)·D
        let d_dd = c.mul(dcap.clone(), dd.clone()); // D·(D·D)
                                                    // c8 = (powNat2·powNat2)·powNat2   [dualhc_pow8_eq_two_pow_cube n]
        let p2 = c.pow(&c.two_rat(), &n); // powNat 2 n
        let p2p2 = c.mul(p2.clone(), p2.clone());
        let p2p2_p2 = c.mul(p2p2.clone(), p2.clone());
        let pow8_cube = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.dualhc_pow8_eq_two_pow_cube"),
                vec![],
            ),
            [n.clone()],
        ); // 8^n = (powNat2·powNat2)·powNat2
           // p2 = D   [powNat_two_eq_ofNat_pow n]
        let p2_eq_d = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.powNat_two_eq_ofNat_pow"),
                vec![],
            ),
            [n.clone()],
        ); // powNat 2 n = D
           // ((p2·p2)·p2) = ((D·D)·D) : three nested congr along p2=D
           //   c1 : p2·p2 = D·p2     [congr (·p2) p2_eq_d]   -- wait, want p2·p2 = D·D
           //   Use: p2·p2 = D·p2 [congr (·p2) p2=D], then D·p2 = D·D [congr (D·) p2=D].
        let d_p2 = c.mul(dcap.clone(), p2.clone());
        let cc1 = {
            let mot = c.mul_right_motive(&b, &p2);
            c.congr(p2.clone(), dcap.clone(), mot, p2_eq_d.clone())
        }; // p2·p2 = D·p2
        let cc2 = {
            let mot = c.mul_left_motive(&b, &dcap);
            c.congr(p2.clone(), dcap.clone(), mot, p2_eq_d.clone())
        }; // D·p2 = D·D
        let p2p2_eq_dd = c.trans(p2p2.clone(), d_p2.clone(), dd.clone(), cc1, cc2); // p2·p2 = D·D
                                                                                    //   (p2·p2)·p2 = (D·D)·p2  [congr (·p2) p2p2_eq_dd]
        let dd_p2 = c.mul(dd.clone(), p2.clone());
        let cc3 = {
            let mot = c.mul_right_motive(&b, &p2);
            c.congr(p2p2.clone(), dd.clone(), mot, p2p2_eq_dd)
        }; // (p2·p2)·p2 = (D·D)·p2
           //   (D·D)·p2 = (D·D)·D  [congr ((D·D)·) p2_eq_d]
        let cc4 = {
            let mot = c.mul_left_motive(&b, &dd);
            c.congr(p2.clone(), dcap.clone(), mot, p2_eq_d)
        }; // (D·D)·p2 = (D·D)·D
        let p2p2p2_eq_ddd = c.trans(p2p2_p2.clone(), dd_p2.clone(), dd_d.clone(), cc3, cc4); // (p2·p2)·p2 = (D·D)·D
                                                                                             // c8 = (D·D)·D   [trans pow8_cube p2p2p2_eq_ddd]
        let c8_eq_ddd = c.trans(
            c8.clone(),
            p2p2_p2.clone(),
            dd_d.clone(),
            pow8_cube,
            p2p2p2_eq_ddd,
        );
        // (D·D)·D = D·(D·D)  [mul_assoc D D D]
        let ddd_eq_d_dd = c.mul_assoc(dcap.clone(), dcap.clone(), dcap.clone());
        // c8 = D·(D·D)
        let c8_eq_d_dd = c.trans(
            c8.clone(),
            dd_d.clone(),
            d_dd.clone(),
            c8_eq_ddd,
            ddd_eq_d_dd,
        );
        //   c8·feed = (D·(D·D))·feed   [congr (·feed) c8_eq_d_dd]
        let ddd_feed = c.mul(d_dd.clone(), feed.clone()); // (D·(D·D))·feed
        let c8feed_eq_dddfeed = {
            let mot = c.mul_right_motive(&b, &feed);
            c.congr(c8.clone(), d_dd.clone(), mot, c8_eq_d_dd)
        }; // c8·feed = (D·(D·D))·feed
           //   (D·(D·D))·feed = W_i   [symm dualhc_W_eq_band_form n f i]
        let band_form = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.dualhc_W_eq_band_form"),
                vec![],
            ),
            [n.clone(), f.clone(), i.clone()],
        ); // W_i = (D·(D·D))·feed
        let dddfeed_eq_wi = c.symm(w_i.clone(), ddd_feed.clone(), band_form); // (D·(D·D))·feed = W_i
                                                                              // c8·feed = W_i
        let c8feed_eq_wi = c.trans(
            c8_feed.clone(),
            ddd_feed.clone(),
            w_i.clone(),
            c8feed_eq_dddfeed,
            dddfeed_eq_wi,
        );
        //   P9k·(c8·feed) = P9k·W_i   [congr (P9k·) c8feed_eq_wi]
        let p9k_c8feed_eq_p9kwi = {
            let mot = c.mul_left_motive(&b, &p9k);
            c.congr(c8_feed.clone(), w_i.clone(), mot, c8feed_eq_wi)
        }; // P9k·(c8·feed) = P9k·W_i
           // EQ2 : c8·(P9k·feed) = P9k·W_i  [trans move_p9k p9k_c8feed_eq_p9kwi]
        let eq2 = c.trans(
            c8_p9k_feed.clone(),
            p9k_c8feed.clone(),
            p9k_wi.clone(),
            move_p9k,
            p9k_c8feed_eq_p9kwi,
        );
        // transport step4a along EQ2 : motive t => c8·Wb ≤ t
        let motive4 = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = d.fresh_local(c.rat());
            let body = c.le(c8_wb.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        c.subst(motive4, c8_p9k_feed.clone(), p9k_wi.clone(), eq2, step4a) // c8·Wb ≤ P9k·W_i
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
    let e = bind(&b, i_id, c.fin_of(&n), tail);
    let e = bind(&b, f_id, f_ty, e);
    let e = bind(&b, k_id, c.nat.clone(), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}
