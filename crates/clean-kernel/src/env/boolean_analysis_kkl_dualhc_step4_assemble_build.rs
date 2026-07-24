// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// STEP-4 assembly term builder (`build_assemble`). `include!`d into
// `boolean_analysis_kkl_dualhc_step4_assemble.rs` — shares its `AsmConsts` and
// imports. Split out to keep each file under the 500-line convention. (Regular
// `//` comments: inner doc `//!` is not allowed at an `include!` site.)

/// Build the type (`for_value = false`) or proof value (`for_value = true`) of
/// `dualhc_step4_sq_le`.
fn build_assemble(c: &AsmConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.bool_fn_of(&n));
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let half = c.half();
    let four = c.four();
    let sixteen = c.mul(four.clone(), four.clone());
    let pow8 = c.pow8(&n);

    // g := deriv lambda ; tg := op g ; ttg := op tg (= STEP 2's weight w).
    let g = c.deriv_lam(&b, &n, &f, &i);
    let tg = c.op(&n, &g);
    let ttg = c.op(&n, &tg);

    // m := subsetSum n (fun x => (g x·g x)·(half·half))  (STEP 2's measure).
    let m = c.ssum(&n, {
        c.lam_hcp(&b, &n, |_d, x| {
            let gx = Expr::app(g.clone(), x.clone());
            c.mul(c.mul(gx.clone(), gx), c.mul(half.clone(), half.clone()))
        })
    });
    let m_cube = c.mul(m.clone(), c.mul(m.clone(), m.clone())); // m·(m·m)

    // W := subsetSum n (fun y => (tg y)·(tg y)).
    let w = c.ssum(&n, {
        c.lam_hcp(&b, &n, |_d, y| {
            let tgy = Expr::app(tg.clone(), y.clone());
            c.mul(tgy.clone(), tgy)
        })
    });
    let ww = c.mul(w.clone(), w.clone());

    // Y := m_cube · pow8  ; concl : W·W ≤ 16·Y.
    let y = c.mul(m_cube.clone(), pow8.clone());
    let sixteen_y = c.mul(sixteen.clone(), y.clone());
    let concl = c.le(ww.clone(), sixteen_y.clone());

    let tail = if for_value {
        // ── 0 ≤ Y := mul_nonneg m_cube pow8 (0≤m_cube) (0≤pow8). ──────────────
        // 0 ≤ m : `m = subsetSum n G ≡ Fin.sum (2^n) (fun j => G (decode j))`
        // (subsetSum δ-unfolds), so `Fin.sum_nonneg (2^n) decodedFn per` with the
        // *decoded* Fin-indexed summand `fun j => (g(decode j)·g(decode j))·(½·½)`.
        let m_decoded_fn = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (j_id, j) = d.fresh_local(c.fin_pow(&n));
            let decode = Expr::apps(
                Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
                [n.clone(), j.clone()],
            );
            let gx = Expr::app(g.clone(), decode.clone());
            let body = c.mul(c.mul(gx.clone(), gx), c.mul(half.clone(), half.clone()));
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_pow(&n), body))
        };
        let m_per = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (j_id, j) = d.fresh_local(c.fin_pow(&n));
            let decode = Expr::apps(
                Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
                [n.clone(), j.clone()],
            );
            let gx = Expr::app(g.clone(), decode.clone());
            let gg = c.mul(gx.clone(), gx.clone());
            let hh = c.mul(half.clone(), half.clone());
            let body = c.mul_nonneg(gg, hh, c.sq_nonneg(gx), c.sq_nonneg(half.clone()));
            d.finish_child(d.mk_lam(j_id, BinderInfo::Default, c.fin_pow(&n), body))
        };
        let m_nonneg = c.fin_sum_nonneg(&c.pow2(&n), m_decoded_fn, m_per); // 0 ≤ m
        let m_sq = c.mul(m.clone(), m.clone());
        let mc_nonneg = c.mul_nonneg(
            m.clone(),
            m_sq.clone(),
            m_nonneg.clone(),
            c.mul_nonneg(m.clone(), m.clone(), m_nonneg.clone(), m_nonneg),
        ); // 0 ≤ m·(m·m)
        let pow8_nonneg = c.pow_nat_nonneg(c.rat_eight(), &n, c.nonneg_lit(c.rat_eight())); // 0 ≤ 8^n
        let y_nonneg = c.mul_nonneg(m_cube.clone(), pow8.clone(), mc_nonneg.clone(), pow8_nonneg);

        // ── STEP 2 at (n,f,i,ttg) : pow4(p_folded) ≤ m_cube · sumw4. ─────────
        let step2 = Expr::apps(
            c.step2.clone(),
            [n.clone(), f.clone(), i.clone(), ttg.clone()],
        );
        // p_folded base (STEP 2's, inlined deriv) ; glue's LHS (with g lambda) is
        // def-eq. sumw4 := subsetSum n (fun x => pow4 (ttg x)).
        let sumw4 = c.ssum(
            &n,
            c.lam_hcp(&b, &n, |_d, x| c.pow4(Expr::app(ttg.clone(), x.clone()))),
        );

        // glue (n, g) : subsetSum n (fun x => (g x·half)·(ttg x)) = half·W.
        let glue = Expr::apps(c.step4_glue.clone(), [n.clone(), g.clone()]);
        let glue_lhs = c.ssum(&n, {
            c.lam_hcp(&b, &n, |_d, x| {
                let gx = Expr::app(g.clone(), x.clone());
                let ttgx = Expr::app(ttg.clone(), x.clone());
                c.mul(c.mul(gx, half.clone()), ttgx)
            })
        });
        let half_w = c.mul(half.clone(), w.clone());
        // subst step2's LHS-base `glue_lhs` → `half·W`:
        //   motive t := pow4 t ≤ m_cube · sumw4.  step2 : motive glue_lhs (def-eq).
        let mc_sumw4 = c.mul(m_cube.clone(), sumw4.clone());
        let motive_lhs = c.lam_rat(&b, |t| c.le(c.pow4(t), mc_sumw4.clone()));
        let step2_w = c.subst(motive_lhs, glue_lhs.clone(), half_w.clone(), glue, step2);
        // step2_w : pow4(half·W) ≤ m_cube · sumw4.

        // ── STEP 3 + fold : sumw4 ≤ pow8·(W·W). ──────────────────────────────
        let step3 = Expr::apps(c.step3.clone(), [n.clone(), g.clone()]);
        // step3 : Fin.sum (2^n) (fun jx => pow4 (noiseFn 1/3 n tg jx))
        //           ≤ pow8 · ((Fin.sum (2^n) (fun jx => (tg(decode jx))·(tg(decode jx)))) is sq'd)
        // The RHS inner sum ≡ W (subsetSum fold), so step3 RHS ≡ pow8·(W·W).
        // fold bridge : noiseFn 1/3 n tg jx = ttg (decode jx) ; lift pow4 over the
        // Fin.sum by Fin.sum_congr to get  sumw4 = LHS3.
        let lhs3_fn = {
            // fun jx => pow4 (noiseFn 1/3 n tg jx)   (STEP 3's LHS summand)
            let mut d = EnvDeclBuilder::child_of(&b);
            let (jx_id, jx) = d.fresh_local(c.fin_pow(&n));
            let nf = Expr::apps(c.noise_fn(&n, &tg), [jx.clone()]);
            let body = c.pow4(nf);
            d.finish_child(d.mk_lam(jx_id, BinderInfo::Default, c.fin_pow(&n), body))
        };
        let sumw4_fn = {
            // fun jx => pow4 (ttg (decode jx))   (sumw4's underlying Fin.sum summand)
            let mut d = EnvDeclBuilder::child_of(&b);
            let (jx_id, jx) = d.fresh_local(c.fin_pow(&n));
            let decode = Expr::apps(
                Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
                [n.clone(), jx.clone()],
            );
            let body = c.pow4(Expr::app(ttg.clone(), decode));
            d.finish_child(d.mk_lam(jx_id, BinderInfo::Default, c.fin_pow(&n), body))
        };
        // pointwise : fun jx => congrArg pow4 (fold 1/3 n tg jx)
        //   fold jx : noiseFn 1/3 n tg jx = noiseOp 1/3 n tg (decode jx) = ttg (decode jx)
        let pw3 = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (jx_id, jx) = d.fresh_local(c.fin_pow(&n));
            let nf = Expr::apps(c.noise_fn(&n, &tg), [jx.clone()]);
            let decode = Expr::apps(
                Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]),
                [n.clone(), jx.clone()],
            );
            let ttg_dec = Expr::app(ttg.clone(), decode);
            let fold = Expr::apps(
                c.fold.clone(),
                [c.rho_third(), n.clone(), tg.clone(), jx.clone()],
            );
            // congrArg pow4 : pow4 (noiseFn..) = pow4 (ttg (decode jx))
            let pow4_lam = c.lam_rat(&d, |t| c.pow4(t));
            let body = c.congr_arg(nf, ttg_dec, pow4_lam, fold);
            d.finish_child(d.mk_lam(jx_id, BinderInfo::Default, c.fin_pow(&n), body))
        };
        // Fin.sum_congr (2^n) lhs3_fn sumw4_fn pw3 : Fin.sum lhs3_fn = Fin.sum sumw4_fn.
        // Fin.sum lhs3_fn ≡ LHS3 (step3 LHS) ; Fin.sum sumw4_fn ≡ sumw4 (subsetSum fold).
        let fin_sum_congr = Expr::const_(Name::from_string("Fin.sum_congr"), vec![]);
        let lhs3_eq_sumw4 = Expr::apps(
            fin_sum_congr,
            [c.pow2(&n), lhs3_fn.clone(), sumw4_fn.clone(), pw3],
        ); // LHS3 = sumw4
           // step3 RHS = pow8·(W·W) (def-eq: inner sum is W). Transport step3 along
           // (LHS3 = sumw4) with motive t := t ≤ pow8·(W·W):
        let pow8_ww = c.mul(pow8.clone(), ww.clone());
        let lhs3 = c.ssum(&n, lhs3_fn); // def-eq to Fin.sum lhs3_fn; but we need the Fin.sum form...
        let _ = lhs3;
        // step3's stated LHS IS Fin.sum (2^n) lhs3_fn (NOT subsetSum) — use it raw.
        let lhs3_finsum = {
            let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);
            Expr::apps(
                fin_sum,
                [c.pow2(&n), {
                    // rebuild lhs3_fn (Fn is not Clone-friendly across uses) :
                    let mut d = EnvDeclBuilder::child_of(&b);
                    let (jx_id, jx) = d.fresh_local(c.fin_pow(&n));
                    let nf = Expr::apps(c.noise_fn(&n, &tg), [jx.clone()]);
                    let body = c.pow4(nf);
                    d.finish_child(d.mk_lam(jx_id, BinderInfo::Default, c.fin_pow(&n), body))
                }],
            )
        };
        let motive_3 = c.lam_rat(&b, |t| c.le(t, pow8_ww.clone()));
        let sumw4_le = c.subst(motive_3, lhs3_finsum, sumw4.clone(), lhs3_eq_sumw4, step3);
        // sumw4_le : sumw4 ≤ pow8·(W·W).

        // ── m_cube · sumw4 ≤ m_cube · (pow8·(W·W)). ──────────────────────────
        let scaled = c.mul_le_left(
            m_cube.clone(),
            sumw4.clone(),
            pow8_ww.clone(),
            sumw4_le,
            mc_nonneg.clone(),
        ); // m_cube·sumw4 ≤ m_cube·(pow8·(W·W))

        // ── transitivity : pow4(half·W) ≤ m_cube·(pow8·(W·W)). ───────────────
        let le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);
        let pow4_hw = c.pow4(half_w.clone());
        let mc_pow8_ww = c.mul(m_cube.clone(), pow8_ww.clone());
        let chained = Expr::apps(
            le_trans,
            [
                pow4_hw.clone(),
                mc_sumw4.clone(),
                mc_pow8_ww.clone(),
                step2_w,
                scaled,
            ],
        ); // pow4(half·W) ≤ m_cube·(pow8·(W·W))

        // ── reassoc m_cube·(pow8·(W·W)) = (m_cube·pow8)·(W·W) = Y·(W·W). ──────
        let assoc = c.mul_assoc(m_cube.clone(), pow8.clone(), ww.clone()); // (mc·pow8)·(W·W) = mc·(pow8·(W·W))
        let mc_pow8 = c.mul(m_cube.clone(), pow8.clone()); // = Y
        let mcpow8_ww = c.mul(mc_pow8.clone(), ww.clone()); // (mc·pow8)·(W·W) = Y·(W·W)
        let assoc_sym = c.symm(mcpow8_ww.clone(), mc_pow8_ww.clone(), assoc); // mc·(pow8·(W·W)) = (mc·pow8)·(W·W)
                                                                              // transport chained along assoc_sym (motive t := pow4(half·W) ≤ t):
        let motive_a = c.lam_rat(&b, |t| c.le(pow4_hw.clone(), t));
        let hyp_desq = c.subst(
            motive_a,
            mc_pow8_ww.clone(),
            mcpow8_ww.clone(),
            assoc_sym,
            chained,
        );
        // hyp_desq : pow4(half·W) ≤ Y·(W·W)   (Y := mc·pow8)

        // ── desq cancel : W·W ≤ 16·Y. ────────────────────────────────────────
        Expr::apps(c.desq.clone(), [w.clone(), y.clone(), y_nonneg, hyp_desq])
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
    let e = bind(&b, f_id, c.bool_fn_of(&n), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}
