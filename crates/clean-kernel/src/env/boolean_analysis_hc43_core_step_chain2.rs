// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// `build_step_concl` — the S1 (genuine LHS finSum reshape) → close body for
// `hc43_core_step`'s `motive (m+1)` conclusion. `include!`d into
// `boolean_analysis_hc43_core_step_chain.rs`.
//
// BUILD STATUS / HONEST GAP (see report + design §11):
//   * S1 is GENUINE, kernel-checked: it proves the `motive (m+1)` LHS
//     `NNReal.finSum (2^(m+1)) (ofRat ∘ pow4 ∘ noiseFn …)` EQUALS the split-summand
//     finSum `Σ_k (ofRat(pow4 lo) + ofRat(pow4 hi))` via `finSum_ofRat` (forward),
//     `finSumPow2SuccSplit` (the Rat last-coord split), `noiseFn_succ_low/high`
//     (the leg rewrite under `Fin.sum_congr`), `NNReal.ofRat_add`, and
//     `finSum_ofRat` (backward on each half).
//   * The two-point bound (S2), the cube-fold, and the `4^(m+1)` scalar close are
//     the named open residual `h_close` (the §11 cross-term wall). `h_cm`/`h_tp`
//     as stated do NOT compose to it (S2 gives `Σ 4·(A³+B³)`, whose collapse
//     `4·(NG³+NH³)` is NOT `≤ 4^(m+1)·NF1³` without the irrational cross-term).
//     `h_close` is an EXPLICIT minor premise (NOT an axiom, NOT a sorry).

/// `fun (jx : Fin (2^(m+1))) => NNReal.ofRat (pow4 (noiseFn ρ (m+1) F jx)) (hnn jx)`
/// — the motive (m+1) LHS summand.
fn lhs_nn_summand(c: &Hc43StepConsts, parent: &EnvDeclBuilder, ctx: &StepCtx) -> Expr {
    let sm = c.succ(&ctx.m);
    let fin = c.fin_of(&c.pow2(&sm));
    let mut b = EnvDeclBuilder::child_of(parent);
    let (jx_id, jx) = b.fresh_local(fin.clone());
    let body = c.ofrat(
        &c.pow4(&c.noise_fn(&ctx.rho, &sm, &ctx.f, &jx)),
        &Expr::app(ctx.hnn.clone(), jx.clone()),
    );
    b.finish_child(b.mk_lam(jx_id, BinderInfo::Default, fin, body))
}

/// Build the `motive (m+1)` conclusion proof body: `S1` reshape then `h_close`.
fn build_step_concl(c: &Hc43StepConsts, parent: &EnvDeclBuilder, ctx: &StepCtx) -> Expr {
    let sm = c.succ(&ctx.m);

    // The motive (m+1) LHS and RHS.
    let lhs_nn = {
        let summand = lhs_nn_summand(c, parent, ctx);
        c.finsum(&c.pow2(&sm), &summand)
    };
    let rhs = c.nnmul(
        &c.ofrat(&c.pow4n(&sm), &ctx.h4n),
        &c.norm43_cubed_app(&sm, &ctx.f, &ctx.s, &ctx.r, &ctx.hs),
    );

    // The per-point nonneg witnesses for the split halves (pow4 ≥ 0 always).
    let hlo = build_lo_nonneg(c, parent, ctx);
    let hhi = build_hi_nonneg(c, parent, ctx);

    // S1 : lhs_nn = split_summand_finsum.
    let split_fs = split_summand_finsum(c, parent, &ctx.rho, &ctx.m, &ctx.f, &hlo, &hhi);
    let s1 = build_s1(c, parent, ctx, &lhs_nn, &split_fs, &hlo, &hhi);

    // h_close applied : split_summand_finsum ≤ rhs.
    let close = Expr::apps(
        ctx.h_close.clone(),
        [
            ctx.m.clone(),
            ctx.f.clone(),
            ctx.s.clone(),
            ctx.r.clone(),
            ctx.hs.clone(),
            hlo.clone(),
            hhi.clone(),
            ctx.h4n.clone(),
        ],
    );

    // subst_le_left along (S1 : lhs_nn = split_fs) : lhs_nn ≤ rhs.
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = mb.fresh_local(c.nnreal());
        let body = c.nnle(&w, &rhs);
        mb.finish_child(mb.mk_lam(w_id, BinderInfo::Default, c.nnreal(), body))
    };
    // Eq.subst motive (from = split_fs)(to = lhs_nn) (symm s1) close : lhs_nn ≤ rhs.
    c.subst_nn_prop(
        motive,
        &split_fs,
        &lhs_nn,
        c.symm_nn(&lhs_nn, &split_fs, s1),
        close,
    )
}

/// `fun (k : Fin (2^m)) => pow4_nonneg (lo k) : ∀ k, 0 ≤ pow4 (lo k)`.
fn build_lo_nonneg(c: &Hc43StepConsts, parent: &EnvDeclBuilder, ctx: &StepCtx) -> Expr {
    let fin = c.fin_of(&c.pow2(&ctx.m));
    let g_part = c.g_part_of(&ctx.m, &ctx.f);
    let lift_h = c.lift_h_of(&ctx.m, &ctx.f);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = b.fresh_local(fin.clone());
    let g = c.noise_fn(&ctx.rho, &ctx.m, &g_part, &k);
    let hh = c.noise_fn(&ctx.rho, &ctx.m, &lift_h, &k);
    let lo = c.rat_add(&g, &c.rmul(&ctx.rho, &hh));
    let body = c.pow4_nonneg(&lo);
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, fin, body))
}

/// `fun (k : Fin (2^m)) => pow4_nonneg (hi k) : ∀ k, 0 ≤ pow4 (hi k)`.
fn build_hi_nonneg(c: &Hc43StepConsts, parent: &EnvDeclBuilder, ctx: &StepCtx) -> Expr {
    let fin = c.fin_of(&c.pow2(&ctx.m));
    let g_part = c.g_part_of(&ctx.m, &ctx.f);
    let lift_h = c.lift_h_of(&ctx.m, &ctx.f);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = b.fresh_local(fin.clone());
    let g = c.noise_fn(&ctx.rho, &ctx.m, &g_part, &k);
    let hh = c.noise_fn(&ctx.rho, &ctx.m, &lift_h, &k);
    let hi = c.rat_sub(&g, &c.rmul(&ctx.rho, &hh));
    let body = c.pow4_nonneg(&hi);
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, fin, body))
}

include!("boolean_analysis_hc43_core_step_s1.rs");
