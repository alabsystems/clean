// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// The `hc24_core_step` sub-leg proof builders. `include!`d into the build module.

/// `SG` / `SH` : `Σ_{2^n} sq(gPart|liftH n F (hcDecode n k))` — matches both the
/// IH conclusion's inner sum and `hc24S7`'s `SG`/`SH`.
fn sum_sq_decode(
    c: &StepConsts,
    parent: &EnvDeclBuilder,
    _rho: &Expr,
    n: &Expr,
    f: &Expr,
    is_g: bool,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
    let dec = c.decode(n, &k);
    let lift = if is_g {
        c.g_part_of(n, f)
    } else {
        c.lift_h_of(n, f)
    };
    let body = c.sq(&Expr::app(lift, dec));
    let fnc = b.finish_child(b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), body));
    c.sum(&c.pow2(n), fnc)
}

/// `SF'` : `Σ_{2^(n+1)} sq(F (hcDecode (n+1) jx))`.
fn sum_sf(c: &StepConsts, parent: &EnvDeclBuilder, f: &Expr, n: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let sn = c.succ(n);
    let p2sn = c.pow2(&sn);
    let (jx_id, jx) = b.fresh_local(c.fin_of(&p2sn));
    let body = c.sq(&Expr::app(f.clone(), c.decode(&sn, &jx)));
    let fnc = b.finish_child(b.mk_lam(jx_id, BinderInfo::Default, c.fin_of(&p2sn), body));
    c.sum(&p2sn_n(c, n), fnc)
}
fn p2sn_n(c: &StepConsts, n: &Expr) -> Expr {
    c.pow2(&c.succ(n))
}

/// `Rat.add_le_add a b c d h_ab h_cd : a+c ≤ b+d`.
fn add_le_add(
    c: &StepConsts,
    a: &Expr,
    bv: &Expr,
    cc: &Expr,
    dd: &Expr,
    h_ab: Expr,
    h_cd: Expr,
) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.add_le_add"), vec![]),
        [a.clone(), bv.clone(), cc.clone(), dd.clone(), h_ab, h_cd],
    )
}

/// `0 ≤ (1+1)` : `le_trans 0 1 2 (0≤1) (1≤2)`.
fn step_zero_le_two(c: &StepConsts) -> Expr {
    let hc = crate::env::boolean_analysis_hc_bounds_proofs::HcBoundsConsts::new();
    hc.zero_le_two()
}

/// `0 ≤ Σ f` for a square-leg summand `f` (each `f k = a·a`), via `Fin.sum_nonneg`
/// + pointwise `Rat.sq_nonneg`. `inner k` returns the squared base `a` at `k`.
fn sum_sq_nonneg(
    c: &StepConsts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    f: &Expr,
    inner: &dyn Fn(&StepConsts, &Expr) -> Expr,
) -> Expr {
    let pw = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let p2n = c.pow2(n);
        let (k_id, k) = d.fresh_local(c.fin_of(&p2n));
        let body = c.sq_nonneg(&inner(c, &k)); // 0 ≤ (inner k)·(inner k)
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), body))
    };
    c.sum_nonneg(&c.pow2(n), f, pw)
}

/// S2 pointwise hypothesis: `fun k => <proof : split_sum k ≤ two_sq_sum k>`.
fn step_s2_pointwise(
    c: &StepConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    hyp: &Expr,
    f: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));

    let g = c.noise_fn(rho, n, &c.g_part_of(n, f), &k);
    let h = c.noise_fn(rho, n, &c.lift_h_of(n, f), &k);

    // two_point (G k) (H k) ρ hyp : pow4(G+ρH) + pow4(G−ρH) ≤ (1+1)·sq(sq G + sq H)
    let tpb = c.two_point(&g, &h, rho, hyp.clone());

    // rho_h := ρ·H ;  sum := G+ρH ;  diff := G−ρH ;  pow4 of each.
    let rho_h = c.mul(rho.clone(), h.clone());
    let plus = c.add(g.clone(), rho_h.clone());
    let minus = c.sub(g.clone(), rho_h.clone());
    let p4_plus = c.pow4(&plus);
    let p4_minus = c.pow4(&minus);

    // low_p k = pow4(noiseFn ρ (n+1) F (castP(castAdd k))) ; high_p k likewise.
    let low_inner = step_split_noise(c, &b, rho, n, f, true, &k);
    let high_inner = step_split_noise(c, &b, rho, n, f, false, &k);
    let low_p = c.pow4(&low_inner);
    let high_p = c.pow4(&high_inner);

    // h1 : low_p = pow4(G+ρH)   [congrArg pow4 (noiseFn_succ_low ρ n F k)]
    let nlow = c.nf_succ_low(rho, n, f, &k); // noiseFn... = G+ρH
    let plam = pow4_lam(c, &b);
    let h1 = c.congr_arg(low_inner.clone(), plus.clone(), plam.clone(), nlow);
    // h2 : high_p = pow4(G−ρH)   [congrArg pow4 (noiseFn_succ_high ρ n F k)]
    let nhigh = c.nf_succ_high(rho, n, f, &k); // noiseFn... = G−ρH
    let h2 = c.congr_arg(high_inner.clone(), minus.clone(), plam, nhigh);

    // heq : low_p + high_p = pow4(G+ρH) + pow4(G−ρH)
    let add_c = c.add_c();
    let hl = c.cong_left(
        &b,
        &add_c,
        low_p.clone(),
        p4_plus.clone(),
        high_p.clone(),
        h1,
    );
    let mid = c.add(p4_plus.clone(), high_p.clone());
    let hr = c.cong_right(
        &b,
        &add_c,
        high_p.clone(),
        p4_minus.clone(),
        p4_plus.clone(),
        h2,
    );
    let lhs_sum = c.add(low_p.clone(), high_p.clone());
    let rhs_sum = c.add(p4_plus.clone(), p4_minus.clone());
    let heq = c.trans(lhs_sum.clone(), mid, rhs_sum.clone(), hl, hr);

    // two_sq_sum k = (1+1)·sq(sq G + sq H)   (= two_point RHS, defeq)
    let two_sq = c.mul(c.two(), c.sq(&c.add(c.sq(&g), c.sq(&h))));

    // subst_le_left along symm(heq) applied to tpb : low_p + high_p ≤ two_sq.
    // heq : lhs_sum = rhs_sum ; symm gives rhs_sum = lhs_sum (the subst direction).
    let heq_sym = c.symm(lhs_sum.clone(), rhs_sum.clone(), heq);
    let proof = c.subst_le_left(&b, two_sq, rhs_sum.clone(), lhs_sum.clone(), heq_sym, tpb);
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), proof))
}
fn lhs_sum_clone(c: &StepConsts, a: &Expr, b: &Expr) -> Expr {
    c.add(a.clone(), b.clone())
}

/// `noiseFn ρ (n+1) F (castP (idx k))` at a concrete `k`.
fn step_split_noise(
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
    c.noise_fn(rho, &c.succ(n), f, &casted)
}

/// S3 pointwise hypothesis: `fun k => <add_sq_regroup (sq G k) (sq H k)>`.
/// `add_sq_regroup A B : (A+B)·(A+B) = (A·A + B·B) + (1+1)·(A·B)`, defeq to
/// `sq_sum k = regroup k` since `sq G k · sq G k = pow4 G k` etc.
fn step_s3_regroup_pw(
    c: &StepConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    f: &Expr,
) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let p2n = c.pow2(n);
    let (k_id, k) = b.fresh_local(c.fin_of(&p2n));
    let g = c.noise_fn(rho, n, &c.g_part_of(n, f), &k);
    let h = c.noise_fn(rho, n, &c.lift_h_of(n, f), &k);
    let sq_g = c.sq(&g);
    let sq_h = c.sq(&h);
    let body = c.add_sq_regroup(&sq_g, &sq_h);
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), body))
}

/// S4–S5: `R ≤ 8^n·SG·SH`.
#[allow(clippy::too_many_arguments)]
fn step_s45_r_bound(
    c: &StepConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    ih: &Expr,
    f: &Expr,
    big_p: &Expr,
    big_q: &Expr,
    big_r: &Expr,
    sq_g: &Expr,
    sq_h: &Expr,
    pow4_g: &Expr,
    pow4_h: &Expr,
    r_summand: &Expr,
    sg: &Expr,
    sh: &Expr,
) -> Expr {
    let pow8n = c.pow8(n);
    let pow8_sgsh = c.mul(pow8n.clone(), c.mul(sg.clone(), sh.clone())); // 8^n·SG·SH

    // CS : (Σ sq_g·sq_h)² ≤ (Σ sq_g·sq_g)·(Σ sq_h·sq_h) = P·Q
    //   note Σ(fun k => sq_g k · sq_h k) = R (defeq), Σ(sq_g·sq_g)=P, Σ(sq_h·sq_h)=Q.
    let cs = c.cauchy_schwarz(&c.pow2(n), sq_g, sq_h); // (R)·(R) ≤ P·Q  (defeq forms)
    let rr = c.mul(big_r.clone(), big_r.clone());
    let pq = c.mul(big_p.clone(), big_q.clone());

    // IH bounds.
    let ih_g = Expr::app(ih.clone(), c.g_part_of(n, f)); // P ≤ 8^n SG²
    let ih_h = Expr::app(ih.clone(), c.lift_h_of(n, f)); // Q ≤ 8^n SH²
    let pow8_sg2 = c.mul(pow8n.clone(), c.sq(sg));
    let pow8_sh2 = c.mul(pow8n.clone(), c.sq(sh));

    // nonneg facts.
    // 0 ≤ Q  (Σ pow4 H = Σ (H·H)·(H·H), sum of squares of squares).
    let zero_le_q = sum_sq_nonneg(c, parent, n, pow4_h, &|c2, k| {
        let h = c2.noise_fn(rho, n, &c2.lift_h_of(n, f), k);
        c2.sq(&h) // pow4 H = (sq H)·(sq H)
    });
    // 0 ≤ 8^n SG²  (= 8^n·(SG·SG), via mul_nonneg(0≤8^n, 0≤SG²)).
    let zero_le_pow8 = step_zero_le_pow8(c, parent, n);
    let zero_le_sg2 = c.sq_nonneg(sg);
    let zero_le_a = c.mul_nonneg(&pow8n, &c.sq(sg), zero_le_pow8.clone(), zero_le_sg2);

    // P·Q ≤ (8^n SG²)·Q   [mlr Q P (8^n SG²) ih_g (0≤Q)]
    let pq_le_aq = c.mlr(big_q, big_p, &pow8_sg2, ih_g, zero_le_q);
    let aq = c.mul(pow8_sg2.clone(), big_q.clone());
    // (8^n SG²)·Q ≤ (8^n SG²)·(8^n SH²)   [mll (8^n SG²) Q (8^n SH²) ih_h (0≤8^n SG²)]
    let aq_le_ab = c.mll(&pow8_sg2, big_q, &pow8_sh2, ih_h, zero_le_a);
    let ab = c.mul(pow8_sg2.clone(), pow8_sh2.clone());
    // P·Q ≤ A·B
    let pq_le_ab = c.le_trans(&pq, &aq, &ab, pq_le_aq, aq_le_ab);

    // R·R ≤ A·B   [le_trans (R·R) (P·Q) (A·B) cs pq_le_ab]
    let rr_le_ab = c.le_trans(&rr, &pq, &ab, cs, pq_le_ab);

    // A·B = (8^n SG·SH)·(8^n SG·SH)   [ring identity prod_sq]
    let ab_eq = step_ab_eq_sq(c, parent, &pow8n, sg, sh);
    let pow8_sgsh_sq = c.mul(pow8_sgsh.clone(), pow8_sgsh.clone());
    // R·R ≤ (8^n SG·SH)²   [subst_le_right along ab_eq]
    let rr_le_sq = c.subst_le_right(parent, rr, ab, pow8_sgsh_sq, ab_eq, rr_le_ab);

    // 0 ≤ R  (sum of sq G · sq H, products of squares).
    let zero_le_r = sum_prod_sq_nonneg(c, parent, rho, n, f, r_summand);
    // 0 ≤ 8^n SG·SH.
    let zero_le_sgsh = c.mul_nonneg(
        &c.mul(sg.clone(), sh.clone()),
        &pow8n,
        step_sgsh_nonneg(c, parent, rho, n, f, sg, sh),
        zero_le_pow8,
    );
    // Reassociate: mul_nonneg gives 0 ≤ (SG·SH)·8^n ; we need 0 ≤ 8^n·(SG·SH).
    let zero_le_target = fix_nonneg_comm(
        c,
        parent,
        &c.mul(sg.clone(), sh.clone()),
        &pow8n,
        zero_le_sgsh,
    );

    // le_of_sq_le_sq R (8^n SG·SH) (0≤R) (0≤8^n SG·SH) (R·R ≤ (8^n SG·SH)²) : R ≤ 8^n SG·SH
    c.le_of_sq_le_sq(big_r, &pow8_sgsh, zero_le_r, zero_le_target, rr_le_sq)
}

/// `0 ≤ 8^n` via `Rat.powNat_nonneg 8 n (0 ≤ 8)`.
fn step_zero_le_pow8(c: &StepConsts, parent: &EnvDeclBuilder, n: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.powNat_nonneg"), vec![]),
        [c.eight_rat(), n.clone(), step_zero_le_eight(c, parent)],
    )
}
/// `0 ≤ 8`  (= `0 ≤ eight_rat`). Build `0 ≤ 2·(2·2)` by `mul_nonneg` of `0 ≤ 2`,
/// then transport along the defeq `2·(2·2) = eight_rat` (`Eq.refl eight_rat`,
/// which checks at the stated type since `2·(2·2)` reduces to `eight_rat`).
fn step_zero_le_eight(c: &StepConsts, parent: &EnvDeclBuilder) -> Expr {
    let hc = crate::env::boolean_analysis_hc_bounds_proofs::HcBoundsConsts::new();
    let two = c.two();
    let zero_le_two = hc.zero_le_two();
    let two_two = c.mul(two.clone(), two.clone());
    let zero_le_4 = c.mul_nonneg(&two, &two, zero_le_two.clone(), zero_le_two.clone());
    let two_cubed = c.mul(two.clone(), two_two.clone()); // 2·(2·2)
    let zero_le_8 = c.mul_nonneg(&two, &two_two, zero_le_two, zero_le_4); // 0 ≤ 2·(2·2)
                                                                          // h_num : 2·(2·2) = eight_rat   [Eq.refl eight_rat, defeq]
    let h_num = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![c.l1.clone()]),
        [c.rat(), c.eight_rat()],
    );
    let zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    c.subst_le_right(parent, zero, two_cubed, c.eight_rat(), h_num, zero_le_8)
}

/// `0 ≤ Σ (sq G · sq H)` = `0 ≤ R` via `Fin.sum_nonneg` + pointwise
/// `mul_nonneg (sq_nonneg G) (sq_nonneg H)`.
fn sum_prod_sq_nonneg(
    c: &StepConsts,
    parent: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    f: &Expr,
    r_summand: &Expr,
) -> Expr {
    let pw = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let p2n = c.pow2(n);
        let (k_id, k) = d.fresh_local(c.fin_of(&p2n));
        let g = c.noise_fn(rho, n, &c.g_part_of(n, f), &k);
        let h = c.noise_fn(rho, n, &c.lift_h_of(n, f), &k);
        let body = c.mul_nonneg(&c.sq(&g), &c.sq(&h), c.sq_nonneg(&g), c.sq_nonneg(&h));
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), body))
    };
    c.sum_nonneg(&c.pow2(n), r_summand, pw)
}

/// `0 ≤ SG·SH` via `mul_nonneg (0≤SG)(0≤SH)`, with `0 ≤ SG`/`0 ≤ SH` from
/// `Fin.sum_nonneg` over square summands.
fn step_sgsh_nonneg(
    c: &StepConsts,
    parent: &EnvDeclBuilder,
    _rho: &Expr,
    n: &Expr,
    f: &Expr,
    sg: &Expr,
    sh: &Expr,
) -> Expr {
    let zero_le_sg = sg_nonneg(c, parent, n, f, true);
    let zero_le_sh = sg_nonneg(c, parent, n, f, false);
    let _ = (sg, sh);
    let sg2 = sum_sq_decode(c, parent, _rho, n, f, true);
    let sh2 = sum_sq_decode(c, parent, _rho, n, f, false);
    c.mul_nonneg(&sg2, &sh2, zero_le_sg, zero_le_sh)
}
/// `0 ≤ Σ_{2^n} sq(lift n F (dec k))`.
fn sg_nonneg(c: &StepConsts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, is_g: bool) -> Expr {
    let sum_fn = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let p2n = c.pow2(n);
        let (k_id, k) = d.fresh_local(c.fin_of(&p2n));
        let lift = if is_g {
            c.g_part_of(n, f)
        } else {
            c.lift_h_of(n, f)
        };
        let body = c.sq(&Expr::app(lift, c.decode(n, &k)));
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), body))
    };
    let pw = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let p2n = c.pow2(n);
        let (k_id, k) = d.fresh_local(c.fin_of(&p2n));
        let lift = if is_g {
            c.g_part_of(n, f)
        } else {
            c.lift_h_of(n, f)
        };
        let base = Expr::app(lift, c.decode(n, &k));
        let body = c.sq_nonneg(&base);
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.fin_of(&p2n), body))
    };
    c.sum_nonneg(&c.pow2(n), &sum_fn, pw)
}

/// `0 ≤ (SG·SH)·8^n  ⟹  0 ≤ 8^n·(SG·SH)` via `subst` along `mul_comm`.
fn fix_nonneg_comm(
    c: &StepConsts,
    parent: &EnvDeclBuilder,
    sgsh: &Expr,
    pow8: &Expr,
    h: Expr,
) -> Expr {
    let from = c.mul(sgsh.clone(), pow8.clone());
    let to = c.mul(pow8.clone(), sgsh.clone());
    let h_comm = c.mcomm(sgsh, pow8); // (SG·SH)·8^n = 8^n·(SG·SH)
                                      // motive (fun x => 0 ≤ x) along h_comm
    subst_zero_le(c, parent, from, to, h_comm, h)
}

/// `subst` with motive `fun x => 0 ≤ x` along `h_eq : from = to`, given
/// `h : 0 ≤ from`, producing `0 ≤ to`.
fn subst_zero_le(
    c: &StepConsts,
    parent: &EnvDeclBuilder,
    from: Expr,
    to: Expr,
    h_eq: Expr,
    h: Expr,
) -> Expr {
    let zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    c.subst_le_right(parent, zero, from, to, h_eq, h)
}

/// `(8^n SG²)·(8^n SH²) = (8^n SG·SH)·(8^n SG·SH)`  — pure Rat ring identity.
fn step_ab_eq_sq(
    c: &StepConsts,
    parent: &EnvDeclBuilder,
    pow8: &Expr,
    sg: &Expr,
    sh: &Expr,
) -> Expr {
    // Build via the four-factor commute lemma on `(p·sg²)·(p·sh²)`.
    // (p·(sg·sg))·(p·(sh·sh)) = (p·(sg·sh))·(p·(sg·sh)).
    // Use `Rat.mul_mul_mul_comm`-grade rearrangement; we route it through a
    // dedicated proof helper.
    step_prod_sq_eq(c, parent, pow8, sg, sh)
}

include!("boolean_analysis_hc24_step_legs2.rs");
