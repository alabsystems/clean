// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// `build_s1` — the genuine `lhs_nn = split_summand_finsum` NNReal equality.
// `include!`d into `boolean_analysis_hc43_core_step_s1.rs`. Axiom-free.

/// `fun (w : Rat) => pow4 w` — the congr carrier for the pow4-of-noiseFn rewrite.
fn pow4_lam(c: &Hc43StepConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (w_id, w) = b.fresh_local(c.rat());
    let body = c.pow4(&w);
    b.finish_child(b.mk_lam(w_id, BinderInfo::Default, c.rat(), body))
}

/// Pointwise rewrite `pow4(noiseFn (m+1) F (castP idx_k)) = pow4(leg k)` for all k,
/// as a `∀ k, …` lambda (the `Fin.sum_congr` hypothesis). `low` selects
/// `noiseFn_succ_low` (→ `G+ρH`) / `_high` (→ `G−ρH`).
fn half_congr_pw(c: &Hc43StepConsts, parent: &EnvDeclBuilder, ctx: &StepCtx, low: bool) -> Expr {
    let p2m = c.pow2(&ctx.m);
    let fin = c.fin_of(&p2m);
    let sm = c.succ(&ctx.m);
    let pl = pow4_lam(c, parent);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = b.fresh_local(fin.clone());
    // noiseFn_succ_{low,high} ρ m F k : noiseFn (m+1) F (castP idx_k) = leg k.
    let succ_eq = if low {
        c.nf_succ_low(&ctx.rho, &ctx.m, &ctx.f, &k)
    } else {
        c.nf_succ_high(&ctx.rho, &ctx.m, &ctx.f, &k)
    };
    let mapped = if low {
        cast_add_idx(c, &ctx.m, &k)
    } else {
        add_nat_idx(c, &ctx.m, &k)
    };
    let casted = cast_p(c, &b, &ctx.m, &mapped);
    let noise_at = c.noise_fn(&ctx.rho, &sm, &ctx.f, &casted);
    let g = c.noise_fn(&ctx.rho, &ctx.m, &c.g_part_of(&ctx.m, &ctx.f), &k);
    let hh = c.noise_fn(&ctx.rho, &ctx.m, &c.lift_h_of(&ctx.m, &ctx.f), &k);
    let rho_h = c.rmul(&ctx.rho, &hh);
    let leg = if low {
        c.rat_add(&g, &rho_h)
    } else {
        c.rat_sub(&g, &rho_h)
    };
    // congrArg pow4 succ_eq : pow4 (noiseFn …) = pow4 (leg k).
    let body = c.congr_arg_rat(&noise_at, &leg, pl, succ_eq);
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, fin, body))
}

/// Build S1 : `lhs_nn = split_summand_finsum`.
#[allow(clippy::too_many_lines)]
fn build_s1(
    c: &Hc43StepConsts,
    parent: &EnvDeclBuilder,
    ctx: &StepCtx,
    lhs_nn: &Expr,
    split_fs: &Expr,
    hlo: &Expr,
    hhi: &Expr,
) -> Expr {
    let p2m = c.pow2(&ctx.m);
    let sm = c.succ(&ctx.m);
    let p2sm = c.pow2(&sm);

    // ── Rat-level summands & sums ──
    let pf = pf_fn(c, parent, ctx); // fun jx => pow4(noiseFn (m+1) F jx)
    let pf_lo_half = pf_half_fn(c, parent, ctx, true); // pow4(noiseFn …(castP castAdd k))
    let pf_hi_half = pf_half_fn(c, parent, ctx, false);
    let pf_lo_leg = pf_leg_fn(c, parent, ctx, true); // pow4(lo k)
    let pf_hi_leg = pf_leg_fn(c, parent, ctx, false); // pow4(hi k)

    let s_full = c.fin_sum(&p2sm, &pf);
    let s_lo_half = c.fin_sum(&p2m, &pf_lo_half);
    let s_hi_half = c.fin_sum(&p2m, &pf_hi_half);
    let s_lo_leg = c.fin_sum(&p2m, &pf_lo_leg);
    let s_hi_leg = c.fin_sum(&p2m, &pf_hi_leg);

    // (C) finSumPow2SuccSplit m pf : s_full = s_lo_half + s_hi_half.
    let split = c.pow2_split(&ctx.m, &pf);
    let lo_plus_hi_half = c.rat_add(&s_lo_half, &s_hi_half);

    // (A) s_lo_half = s_lo_leg  [Fin.sum_congr + pointwise congrArg pow4 noiseFn_succ_low]
    let cong_lo = c.fin_sum_congr(
        &p2m,
        &pf_lo_half,
        &pf_lo_leg,
        half_congr_pw(c, parent, ctx, true),
    );
    // (B) s_hi_half = s_hi_leg
    let cong_hi = c.fin_sum_congr(
        &p2m,
        &pf_hi_half,
        &pf_hi_leg,
        half_congr_pw(c, parent, ctx, false),
    );

    // (s_lo_half + s_hi_half) = (s_lo_leg + s_hi_leg)  by congr on Rat.add.
    let add_c = Expr::const_(Name::from_string("Rat.add"), vec![]);
    let cong_left = {
        // (s_lo_half + s_hi_half) = (s_lo_leg + s_hi_half)
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(c.rat());
            let body = Expr::apps(add_c.clone(), [w, s_hi_half.clone()]);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat(), body))
        };
        c.congr_arg_rat(&s_lo_half, &s_lo_leg, f, cong_lo)
    };
    let mid_add = c.rat_add(&s_lo_leg, &s_hi_half);
    let cong_right = {
        // (s_lo_leg + s_hi_half) = (s_lo_leg + s_hi_leg)
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(c.rat());
            let body = Expr::apps(add_c.clone(), [s_lo_leg.clone(), w]);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat(), body))
        };
        c.congr_arg_rat(&s_hi_half, &s_hi_leg, f, cong_hi)
    };
    let leg_add = c.rat_add(&s_lo_leg, &s_hi_leg);
    let half_eq_leg = c.trans_rat(&lo_plus_hi_half, &mid_add, &leg_add, cong_left, cong_right);
    // s_full = (s_lo_leg + s_hi_leg)
    let s_full_eq_leg = c.trans_rat(&s_full, &lo_plus_hi_half, &leg_add, split, half_eq_leg);

    // ── NNReal lift ──
    // nonneg sums: 0 ≤ s_lo_leg, 0 ≤ s_hi_leg, 0 ≤ s_full(=leg_add).
    let h_lo_sum = c.fin_sum_nonneg(&p2m, &pf_lo_leg, hlo.clone());
    let h_hi_sum = c.fin_sum_nonneg(&p2m, &pf_hi_leg, hhi.clone());
    // hsum_full : 0 ≤ s_full via Fin.sum_nonneg over pf (pow4 ≥ 0).
    let pf_nonneg = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (jx_id, jx) = d.fresh_local(c.fin_of(&p2sm));
        let body = c.pow4_nonneg(&c.noise_fn(&ctx.rho, &sm, &ctx.f, &jx));
        d.finish_child(d.mk_lam(jx_id, BinderInfo::Default, c.fin_of(&p2sm), body))
    };
    let hsum_full = c.fin_sum_nonneg(&p2sm, &pf, pf_nonneg);
    // hsum_legadd : 0 ≤ (s_lo_leg + s_hi_leg) — transport hsum_full along s_full_eq_leg.
    let hsum_legadd = {
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(c.rat());
            let body = c.rle(&c.rat_zero(), &w);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat(), body))
        };
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![c.l1()]),
            [
                c.rat(),
                motive,
                s_full.clone(),
                leg_add.clone(),
                s_full_eq_leg.clone(),
                hsum_full.clone(),
            ],
        )
    };

    // lhs_nn = ofRat s_full hsum_full   [finSum_ofRat (2^(m+1)) pf hnn hsum_full]
    let finsum_ofrat_full = c.finsum_ofrat(&p2sm, &pf, &ctx.hnn, &hsum_full);
    let ofrat_full = c.ofrat(&s_full, &hsum_full);

    // ofRat s_full hsum_full = ofRat leg_add hsum_legadd  [ofrat_transport along s_full_eq_leg]
    let ofrat_full_eq_legadd = c.ofrat_transport(
        parent,
        &s_full,
        &leg_add,
        &hsum_full,
        &hsum_legadd,
        s_full_eq_leg.clone(),
    );
    let ofrat_legadd = c.ofrat(&leg_add, &hsum_legadd);

    // ofRat leg_add hsum_legadd = ofRat s_lo_leg h_lo_sum + ofRat s_hi_leg h_hi_sum
    //   [symm (ofRat_add s_lo_leg s_hi_leg h_lo_sum h_hi_sum hsum_legadd)]
    let ofrat_add_eq = c.ofrat_add(&s_lo_leg, &s_hi_leg, &h_lo_sum, &h_hi_sum, &hsum_legadd);
    let ofrat_lo = c.ofrat(&s_lo_leg, &h_lo_sum);
    let ofrat_hi = c.ofrat(&s_hi_leg, &h_hi_sum);
    let ofrat_lo_plus_hi = c.nnadd(&ofrat_lo, &ofrat_hi);
    let legadd_eq_split = c.symm_nn(&ofrat_lo_plus_hi, &ofrat_legadd, ofrat_add_eq);

    // ofRat s_lo_leg = finSum (ofrat_leg_fn low)  [symm (finSum_ofRat 2^m pf_lo_leg hlo h_lo_sum)]
    let ofrat_leg_lo_fn = ofrat_leg_fn(c, parent, ctx, hlo, true);
    let finsum_lo = c.finsum(&p2m, &ofrat_leg_lo_fn);
    let finsum_ofrat_lo = c.finsum_ofrat(&p2m, &pf_lo_leg, hlo, &h_lo_sum);
    let lo_eq_finsum = c.symm_nn(&finsum_lo, &ofrat_lo, finsum_ofrat_lo);

    let ofrat_leg_hi_fn = ofrat_leg_fn(c, parent, ctx, hhi, false);
    let finsum_hi = c.finsum(&p2m, &ofrat_leg_hi_fn);
    let finsum_ofrat_hi = c.finsum_ofrat(&p2m, &pf_hi_leg, hhi, &h_hi_sum);
    let hi_eq_finsum = c.symm_nn(&finsum_hi, &ofrat_hi, finsum_ofrat_hi);

    // (ofRat s_lo_leg + ofRat s_hi_leg) = (finsum_lo + finsum_hi)  [congr both]
    let add_nn_c = Expr::const_(Name::from_string("NNReal.add"), vec![]);
    let cong_nn_left = {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(c.nnreal());
            let body = Expr::apps(add_nn_c.clone(), [w, ofrat_hi.clone()]);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.nnreal(), body))
        };
        c.congr_arg_nn(&ofrat_lo, &finsum_lo, f, lo_eq_finsum)
    };
    let mid_nn = c.nnadd(&finsum_lo, &ofrat_hi);
    let cong_nn_right = {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (w_id, w) = d.fresh_local(c.nnreal());
            let body = Expr::apps(add_nn_c.clone(), [finsum_lo.clone(), w]);
            d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.nnreal(), body))
        };
        c.congr_arg_nn(&ofrat_hi, &finsum_hi, f, hi_eq_finsum)
    };
    let finsum_lo_plus_hi = c.nnadd(&finsum_lo, &finsum_hi);
    let split_eq_finsums = c.trans_nn(
        &ofrat_lo_plus_hi,
        &mid_nn,
        &finsum_lo_plus_hi,
        cong_nn_left,
        cong_nn_right,
    );

    // (finsum_lo + finsum_hi) = finSum (fun k => ofRat(pow4 lo)+ofRat(pow4 hi)) = split_fs
    //   [symm (NNReal.finSum_add 2^m ofrat_leg_lo_fn ofrat_leg_hi_fn)]
    let finsum_add_eq = c.finsum_add(&p2m, &ofrat_leg_lo_fn, &ofrat_leg_hi_fn);
    let finsums_eq_split = c.symm_nn(split_fs, &finsum_lo_plus_hi, finsum_add_eq);

    // ── chain it all: lhs_nn = ofrat_full = ofrat_legadd = ofrat_lo_plus_hi
    //                       = finsum_lo_plus_hi = split_fs ──
    let t1 = c.trans_nn(
        lhs_nn,
        &ofrat_full,
        &ofrat_legadd,
        finsum_ofrat_full,
        ofrat_full_eq_legadd,
    );
    let t2 = c.trans_nn(
        lhs_nn,
        &ofrat_legadd,
        &ofrat_lo_plus_hi,
        t1,
        legadd_eq_split,
    );
    let t3 = c.trans_nn(
        lhs_nn,
        &ofrat_lo_plus_hi,
        &finsum_lo_plus_hi,
        t2,
        split_eq_finsums,
    );
    c.trans_nn(lhs_nn, &finsum_lo_plus_hi, split_fs, t3, finsums_eq_split)
}
