// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Proof-term builder for `BoolAnalysis.hc24_core_step`.
// `include!`d into `boolean_analysis_hc24_step.rs`.

/// `3·(ρ·ρ) ≤ 1` — the shared hypothesis (matches hc24_core_concl + two_point).
fn step_hyp_ty(c: &StepConsts, rho: &Expr) -> Expr {
    let rho_sq = c.mul(rho.clone(), rho.clone());
    c.le(c.mul(c.three(), rho_sq), c.one())
}

/// The IH premise type `∀ (F' : HCPoint n → Rat), <concl n F'>`.
fn step_ih_ty(c: &StepConsts, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (f_id, f) = b.fresh_local(c.f_type(n));
    let concl = hc24_core_concl(&c.o, &b, rho, n, &f);
    b.finish_child(b.mk_pi(f_id, BinderInfo::Default, c.f_type(n), concl))
}

/// `fun (k : Fin (2^n)) => pow4 (noiseFn ρ (n+1) F (castP (idx k)))` — the
/// `finSumPow2SuccSplit` half-summand at `Pow4Fn := fun jx => pow4(noiseFn …)`.
fn split_pow4_fn(
    c: &StepConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    f: &Expr,
    low: bool,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
    let idx = if low {
        c.cast_add.clone()
    } else {
        c.add_nat.clone()
    };
    let mapped = Expr::apps(idx, [p2n.clone(), p2n.clone(), k.clone()]);
    let casted = step_cast_p(c, &b, n, &mapped);
    let sn = c.succ(n);
    let body = c.pow4(&c.noise_fn(rho, &sn, f, &casted));
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), body))
}

/// `fun (k : Fin (2^n)) => splitLow k + splitHigh k`.
fn split_sum_fn(c: &StepConsts, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
    let lo = split_pow4_at(c, &b, rho, n, f, true, &k);
    let hi = split_pow4_at(c, &b, rho, n, f, false, &k);
    let body = c.add(lo, hi);
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), body))
}

/// `pow4 (noiseFn ρ (n+1) F (castP (idx k)))` at a concrete `k`.
fn split_pow4_at(
    c: &StepConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    f: &Expr,
    low: bool,
    k: &Expr,
) -> Expr {
    let p2n = c.pow2(n);
    let idx = if low {
        c.cast_add.clone()
    } else {
        c.add_nat.clone()
    };
    let mapped = Expr::apps(idx, [p2n.clone(), p2n.clone(), k.clone()]);
    let casted = step_cast_p(c, parent, n, &mapped);
    let sn = c.succ(n);
    c.pow4(&c.noise_fn(rho, &sn, f, &casted))
}

/// `fun (k : Fin (2^n)) => (1+1)·sq(sq(G k) + sq(H k))` — the two-point RHS.
fn two_sq_sum_fn(c: &StepConsts, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
    let body = c.mul(c.two(), c.sq(&sq_g_plus_sq_h(c, rho, n, f, &k)));
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), body))
}

/// `fun (k : Fin (2^n)) => sq(sq(G k) + sq(H k))`.
fn sq_sum_fn(c: &StepConsts, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
    let body = c.sq(&sq_g_plus_sq_h(c, rho, n, f, &k));
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), body))
}

/// `sq(G k) + sq(H k)` at a concrete `k`.
fn sq_g_plus_sq_h(c: &StepConsts, rho: &Expr, n: &Expr, f: &Expr, k: &Expr) -> Expr {
    let g = c.noise_fn(rho, n, &c.g_part_of(n, f), k);
    let h = c.noise_fn(rho, n, &c.lift_h_of(n, f), k);
    c.add(c.sq(&g), c.sq(&h))
}

/// `fun (k : Fin (2^n)) => sq(G k)`  (the Cauchy-Schwarz `a` leg).
fn sq_g_fn(c: &StepConsts, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
    let g = c.noise_fn(rho, n, &c.g_part_of(n, f), &k);
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), c.sq(&g)))
}
/// `fun (k : Fin (2^n)) => sq(H k)`  (the Cauchy-Schwarz `b` leg).
fn sq_h_fn(c: &StepConsts, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
    let h = c.noise_fn(rho, n, &c.lift_h_of(n, f), &k);
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), c.sq(&h)))
}

/// `fun (k : Fin (2^n)) => pow4(G k)`  (the IH-bounded `P` summand).
fn pow4_g_fn(c: &StepConsts, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
    let g = c.noise_fn(rho, n, &c.g_part_of(n, f), &k);
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), c.pow4(&g)))
}
/// `fun (k : Fin (2^n)) => pow4(H k)`  (the IH-bounded `Q` summand).
fn pow4_h_fn(c: &StepConsts, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
    let h = c.noise_fn(rho, n, &c.lift_h_of(n, f), &k);
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), c.pow4(&h)))
}

/// `fun (k : Fin (2^n)) => sq(G k)·sq(H k)`  (the `R` summand).
fn r_fn(c: &StepConsts, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
    let g = c.noise_fn(rho, n, &c.g_part_of(n, f), &k);
    let h = c.noise_fn(rho, n, &c.lift_h_of(n, f), &k);
    let body = c.mul(c.sq(&g), c.sq(&h));
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), body))
}

/// `fun (k : Fin (2^n)) => (pow4(G k) + pow4(H k)) + (1+1)·(sq(G k)·sq(H k))`
/// — the `add_sq_regroup` RHS, used to split `Σ sq(sq G + sq H)`.
fn regroup_fn(c: &StepConsts, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
    let g = c.noise_fn(rho, n, &c.g_part_of(n, f), &k);
    let h = c.noise_fn(rho, n, &c.lift_h_of(n, f), &k);
    let pp = c.add(c.pow4(&g), c.pow4(&h)); // pow4 G + pow4 H  (= sq G·sq G + sq H·sq H)
    let r = c.mul(c.sq(&g), c.sq(&h));
    let body = c.add(pp, c.mul(c.two(), r));
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), body))
}

/// `fun (k : Fin (2^n)) => pow4(G k) + pow4(H k)`  (the `P+Q` sum-add leg).
fn pp_fn(c: &StepConsts, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
    let g = c.noise_fn(rho, n, &c.g_part_of(n, f), &k);
    let h = c.noise_fn(rho, n, &c.lift_h_of(n, f), &k);
    let body = c.add(c.pow4(&g), c.pow4(&h));
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), body))
}

/// `fun (k : Fin (2^n)) => (1+1)·(sq(G k)·sq(H k))`  (the `2R` sum-smul leg).
fn two_r_fn(c: &StepConsts, parent: &EnvDeclBuilder, rho: &Expr, n: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
    let g = c.noise_fn(rho, n, &c.g_part_of(n, f), &k);
    let h = c.noise_fn(rho, n, &c.lift_h_of(n, f), &k);
    let body = c.mul(c.two(), c.mul(c.sq(&g), c.sq(&h)));
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), body))
}

/// `castP n M` — byte-for-byte the split transport.
fn step_cast_p(c: &StepConsts, parent: &EnvDeclBuilder, n: &Expr, mapped: &Expr) -> Expr {
    let nat = c.nat();
    let p2n = c.pow2(n);
    let sum_pow = Expr::apps(
        Expr::const_(Name::from_string("Nat.add"), vec![]),
        [p2n.clone(), p2n.clone()],
    );
    let sn = c.succ(n);
    let p2sn = c.pow2(&sn);
    let e_fwd = Expr::app(
        Expr::const_(Name::from_string("Nat.pow_two_succ"), vec![]),
        n.clone(),
    );
    let e = Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![c.l1.clone()]),
        [nat.clone(), p2sn.clone(), sum_pow.clone(), e_fwd],
    );
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(parent);
        let (m_id, m) = mb.fresh_local(nat.clone());
        let body = c.fin_of(&m);
        mb.finish_child(mb.mk_lam(m_id, BinderInfo::Default, nat.clone(), body))
    };
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.ndrec"),
            vec![c.l1.clone(), c.l1.clone()],
        ),
        [nat, sum_pow, motive, mapped.clone(), p2sn, e],
    )
}

include!("boolean_analysis_hc24_step_chain.rs");
