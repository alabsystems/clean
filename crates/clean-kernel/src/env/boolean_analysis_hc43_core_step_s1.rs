// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// S1 — the genuine `motive (m+1)` LHS reshape for `hc43_core_step`:
//   `lhs_nn = split_summand_finsum`  (NNReal Eq, kernel-checked, axiom-free).
// `include!`d into `boolean_analysis_hc43_core_step_chain2.rs`.

// Index-cast helpers (mirroring `noiseFn_succ_low/high`'s split indices).

/// `Fin.castAdd (2^m) (2^m) k`.
fn cast_add_idx(c: &Hc43StepConsts, m: &Expr, k: &Expr) -> Expr {
    let p2m = c.pow2(m);
    Expr::apps(
        Expr::const_(Name::from_string("Fin.castAdd"), vec![]),
        [p2m.clone(), p2m.clone(), k.clone()],
    )
}
/// `Fin.addNat (2^m) (2^m) k`.
fn add_nat_idx(c: &Hc43StepConsts, m: &Expr, k: &Expr) -> Expr {
    let p2m = c.pow2(m);
    Expr::apps(
        Expr::const_(Name::from_string("Fin.addNat"), vec![]),
        [p2m.clone(), p2m.clone(), k.clone()],
    )
}
/// `castP m M` — the `Fin (2^m + 2^m) → Fin (2^(m+1))` transport (`Eq.ndrec` along
/// `Nat.pow_two_succ`), byte-for-byte `finSumPow2SuccSplit`'s split transport so
/// the `noiseFn_succ_low/high` LHS index matches.
fn cast_p(c: &Hc43StepConsts, parent: &EnvDeclBuilder, m: &Expr, mapped: &Expr) -> Expr {
    let nat = c.nat();
    let p2m = c.pow2(m);
    let sum_pow = Expr::apps(
        Expr::const_(Name::from_string("Nat.add"), vec![]),
        [p2m.clone(), p2m.clone()],
    );
    let sm = c.succ(m);
    let p2sm = c.pow2(&sm);
    let e_fwd = Expr::app(
        Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
        m.clone(),
    );
    let l1 = crate::level::Level::succ(crate::level::Level::zero());
    let e = Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
        [nat.clone(), p2sm.clone(), sum_pow.clone(), e_fwd],
    );
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (mm_id, mm) = mb.fresh_local(nat.clone());
        let body = c.fin_of(&mm);
        mb.finish_child(mb.mk_lam(mm_id, BinderInfo::Default, nat.clone(), body))
    };
    Expr::apps(
        Expr::const_(Name::from_string("Eq.ndrec"), vec![l1.clone(), l1]),
        [nat, sum_pow, motive, mapped.clone(), p2sm, e],
    )
}

/// `fun (jx : Fin (2^(m+1))) => pow4 (noiseFn ρ (m+1) F jx)` — the Rat LHS summand.
fn pf_fn(c: &Hc43StepConsts, parent: &EnvDeclBuilder, ctx: &StepCtx) -> Expr {
    let sm = c.succ(&ctx.m);
    let fin = c.fin_of(&c.pow2(&sm));
    let mut b = EnvDeclBuilder::child_of(parent);
    let (jx_id, jx) = b.fresh_local(fin.clone());
    let body = c.pow4(&c.noise_fn(&ctx.rho, &sm, &ctx.f, &jx));
    b.finish_child(b.mk_lam(jx_id, BinderInfo::Default, fin, body))
}

/// `fun (k : Fin (2^m)) => pow4 (noiseFn ρ (m+1) F (castP (castAdd/addNat k)))`
/// — the Rat split half-summand (the `finSumPow2SuccSplit` RHS summand).
fn pf_half_fn(c: &Hc43StepConsts, parent: &EnvDeclBuilder, ctx: &StepCtx, low: bool) -> Expr {
    let p2m = c.pow2(&ctx.m);
    let fin = c.fin_of(&p2m);
    let sm = c.succ(&ctx.m);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = b.fresh_local(fin.clone());
    let mapped = if low {
        cast_add_idx(c, &ctx.m, &k)
    } else {
        add_nat_idx(c, &ctx.m, &k)
    };
    let casted = cast_p(c, &b, &ctx.m, &mapped);
    let body = c.pow4(&c.noise_fn(&ctx.rho, &sm, &ctx.f, &casted));
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, fin, body))
}

/// `fun (k : Fin (2^m)) => pow4 (lo k)` / `pow4 (hi k)` — the rewritten half
/// summand (the `noiseFn_succ_low/high` RHS under `pow4`).
fn pf_leg_fn(c: &Hc43StepConsts, parent: &EnvDeclBuilder, ctx: &StepCtx, low: bool) -> Expr {
    let p2m = c.pow2(&ctx.m);
    let fin = c.fin_of(&p2m);
    let g_part = c.g_part_of(&ctx.m, &ctx.f);
    let lift_h = c.lift_h_of(&ctx.m, &ctx.f);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = b.fresh_local(fin.clone());
    let g = c.noise_fn(&ctx.rho, &ctx.m, &g_part, &k);
    let hh = c.noise_fn(&ctx.rho, &ctx.m, &lift_h, &k);
    let rho_h = c.rmul(&ctx.rho, &hh);
    let leg = if low {
        c.rat_add(&g, &rho_h)
    } else {
        c.rat_sub(&g, &rho_h)
    };
    let body = c.pow4(&leg);
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, fin, body))
}

/// `fun (k : Fin (2^m)) => NNReal.ofRat (pow4 (lo/hi k)) (h_k)` — the NNReal lift
/// of a single rewritten half (the `finSum_ofRat` backward summand).
fn ofrat_leg_fn(
    c: &Hc43StepConsts,
    parent: &EnvDeclBuilder,
    ctx: &StepCtx,
    h_nonneg: &Expr,
    low: bool,
) -> Expr {
    let p2m = c.pow2(&ctx.m);
    let fin = c.fin_of(&p2m);
    let g_part = c.g_part_of(&ctx.m, &ctx.f);
    let lift_h = c.lift_h_of(&ctx.m, &ctx.f);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = b.fresh_local(fin.clone());
    let g = c.noise_fn(&ctx.rho, &ctx.m, &g_part, &k);
    let hh = c.noise_fn(&ctx.rho, &ctx.m, &lift_h, &k);
    let rho_h = c.rmul(&ctx.rho, &hh);
    let leg = if low {
        c.rat_add(&g, &rho_h)
    } else {
        c.rat_sub(&g, &rho_h)
    };
    let body = c.ofrat(&c.pow4(&leg), &Expr::app(h_nonneg.clone(), k.clone()));
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, fin, body))
}

include!("boolean_analysis_hc43_core_step_s1_proof.rs");
