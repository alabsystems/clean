// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// The `hc24_core_step` proof chain (S1–S8). `include!`d into the build module.

/// `fun (w : Rat) => pow4 w` — the `congrArg` carrier for the pow4 transport.
fn pow4_lam(c: &StepConsts, parent: &EnvDeclBuilder) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(parent);
    let (w_id, w) = ch.fresh_local(c.rat());
    let body = c.pow4(&w);
    ch.finish_child(ch.mk_lam(w_id, BinderInfo::Default, c.rat(), body))
}

/// Build the type + proof of `hc24_core_step`.
fn build_step(c: &StepConsts) -> (Expr, Expr) {
    // ── Type.
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (rho_id, rho) = b.fresh_local(c.rat());
        let (n_id, n) = b.fresh_local(c.nat());
        let h_ty = step_hyp_ty(c, &rho);
        let (h_id, _) = b.fresh_local(h_ty.clone());
        let ih_ty = step_ih_ty(c, &b, &rho, &n);
        let (ih_id, _) = b.fresh_local(ih_ty.clone());
        let sn = c.succ(&n);
        let f_ty = c.f_type(&sn);
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let concl = hc24_core_concl(&c.o, &b, &rho, &sn, &f);
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, concl);
        let e = b.mk_pi(ih_id, BinderInfo::Default, ih_ty, e);
        let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, e);
        let e = b.mk_pi(n_id, BinderInfo::Default, c.nat(), e);
        let e = b.mk_pi(rho_id, BinderInfo::Default, c.rat(), e);
        b.finish(e)
    };

    // ── Proof.
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (rho_id, rho) = b.fresh_local(c.rat());
        let (n_id, n) = b.fresh_local(c.nat());
        let h_ty = step_hyp_ty(c, &rho);
        let (h_id, hyp) = b.fresh_local(h_ty.clone());
        let ih_ty = step_ih_ty(c, &b, &rho, &n);
        let (ih_id, ih) = b.fresh_local(ih_ty.clone());
        let sn = c.succ(&n);
        let f_ty = c.f_type(&sn);
        let (f_id, f) = b.fresh_local(f_ty.clone());

        let proof = build_step_body(c, &b, &rho, &n, &hyp, &ih, &f);

        let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, proof);
        let e = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, e);
        let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, e);
        let e = b.mk_lam(n_id, BinderInfo::Default, c.nat(), e);
        let e = b.mk_lam(rho_id, BinderInfo::Default, c.rat(), e);
        b.finish(e)
    };

    (ty, value)
}

/// The body proof `<concl (n+1) F>` given ρ, n, hyp, ih, F.
#[allow(clippy::too_many_lines)]
fn build_step_body(
    c: &StepConsts,
    b: &EnvDeclBuilder,
    rho: &Expr,
    n: &Expr,
    hyp: &Expr,
    ih: &Expr,
    f: &Expr,
) -> Expr {
    let p2n = c.pow2(n);
    let sn = c.succ(n);
    let p2sn = c.pow2(&sn);
    let two = c.two();
    let pow8n = c.pow8(n);
    let add_c = c.add_c();
    let _mul_c = c.mul_c();

    // ── The leaf functions / sums.
    let pow4_full = {
        // fun (jx : Fin (2^(n+1))) => pow4 (noiseFn ρ (n+1) F jx)
        let mut d = EnvDeclBuilder::child_of(b);
        let (jx_id, jx) = d.fresh_local(c.fin_of(&p2sn));
        let body = c.pow4(&c.noise_fn(rho, &sn, f, &jx));
        d.finish_child(d.mk_lam(jx_id, BinderInfo::Default, c.fin_of(&p2sn), body))
    };
    let low_p = split_pow4_fn(c, b, rho, n, f, true);
    let high_p = split_pow4_fn(c, b, rho, n, f, false);
    let split_sum = split_sum_fn(c, b, rho, n, f);
    let two_sq_sum = two_sq_sum_fn(c, b, rho, n, f);
    let sq_sum = sq_sum_fn(c, b, rho, n, f);
    let regroup = regroup_fn(c, b, rho, n, f);
    let pp = pp_fn(c, b, rho, n, f);
    let two_r = two_r_fn(c, b, rho, n, f);
    let pow4_g = pow4_g_fn(c, b, rho, n, f);
    let pow4_h = pow4_h_fn(c, b, rho, n, f);
    let r_summand = r_fn(c, b, rho, n, f);
    let sq_g = sq_g_fn(c, b, rho, n, f);
    let sq_h = sq_h_fn(c, b, rho, n, f);

    let lhs_full = c.sum(&p2sn, pow4_full.clone()); // LHS(n+1)
    let sum_low = c.sum(&p2n, low_p.clone());
    let sum_high = c.sum(&p2n, high_p.clone());
    let s_split = c.sum(&p2n, split_sum.clone());
    let s_two_sq = c.sum(&p2n, two_sq_sum.clone());
    let ss = c.sum(&p2n, sq_sum.clone()); // SS = Σ sq(sq G + sq H)
    let s_regroup = c.sum(&p2n, regroup.clone());
    let big_p = c.sum(&p2n, pow4_g.clone()); // P
    let big_q = c.sum(&p2n, pow4_h.clone()); // Q
    let big_r = c.sum(&p2n, r_summand.clone()); // R
    let s_pp = c.sum(&p2n, pp.clone());
    let s_two_r = c.sum(&p2n, two_r.clone());

    // SG, SH (the gPart/liftH square-sums). These match IH RHS + hc24S7.
    let sg = sum_sq_decode(c, b, rho, n, f, true);
    let sh = sum_sq_decode(c, b, rho, n, f, false);
    // SF' = Σ_{2^(n+1)} sq(F (hcDecode (n+1) jx))   (the goal's inner sum).
    let sf = sum_sf(c, b, f, n);

    // =====================================================================
    // S1 :  LHS(n+1) = Σ split_sum
    // =====================================================================
    let split = c.pow2_split(n, &pow4_full); // LHS = Σ low + Σ high
    let merge = c.symm(
        s_split.clone(),
        c.add(sum_low.clone(), sum_high.clone()),
        c.sum_add(&p2n, &low_p, &high_p),
    );
    let lhs_eq_split = c.trans(
        lhs_full.clone(),
        c.add(sum_low.clone(), sum_high.clone()),
        s_split.clone(),
        split,
        merge,
    );

    // =====================================================================
    // S2 :  Σ split_sum ≤ Σ two_sq_sum   (pointwise two-point bound)
    // =====================================================================
    let s2_pw = step_s2_pointwise(c, b, rho, n, hyp, f);
    let s2 = c.sum_le(&p2n, &split_sum, &two_sq_sum, s2_pw);

    // pull (1+1) :  Σ two_sq_sum = (1+1)·SS
    let pull = c.sum_smul(&p2n, &two, &sq_sum);
    let two_ss = c.mul(two.clone(), ss.clone());
    // Σ split_sum ≤ (1+1)·SS   [subst_le_right along pull]
    let s_split_le_two_ss = c.subst_le_right(
        b,
        s_split.clone(),
        s_two_sq.clone(),
        two_ss.clone(),
        pull,
        s2,
    );

    // =====================================================================
    // S3 :  SS = (P + Q) + (1+1)·R
    // =====================================================================
    // (a) Σ sq_sum = Σ regroup    [sum_congr along add_sq_regroup]
    let regroup_pw = step_s3_regroup_pw(c, b, rho, n, f);
    let ss_eq_regroup = c.sum_congr(&p2n, &sq_sum, &regroup, regroup_pw);
    // (b) Σ regroup = Σ pp + Σ two_r   [Fin.sum_add n pp two_r]
    let regroup_eq_add = c.sum_add(&p2n, &pp, &two_r);
    let pp_plus_twor = c.add(s_pp.clone(), s_two_r.clone());
    // (c) Σ pp = P + Q   [Fin.sum_add n pow4_g pow4_h]
    let s_pp_eq_pq = c.sum_add(&p2n, &pow4_g, &pow4_h);
    let p_plus_q = c.add(big_p.clone(), big_q.clone());
    // (d) Σ two_r = (1+1)·R   [Fin.sum_smul n (1+1) r_summand]
    let s_two_r_eq_2r = c.sum_smul(&p2n, &two, &r_summand);
    let two_r_val = c.mul(two.clone(), big_r.clone());
    // assemble SS = (P+Q) + (1+1)R:
    //   SS = Σ regroup = (Σpp + Σtwo_r) = ((P+Q) + Σtwo_r) = ((P+Q) + (1+1)R)
    let ss_eq_ppadd = c.trans(
        ss.clone(),
        s_regroup.clone(),
        pp_plus_twor.clone(),
        ss_eq_regroup,
        regroup_eq_add,
    );
    let hl3 = c.cong_left(
        b,
        &add_c,
        s_pp.clone(),
        p_plus_q.clone(),
        s_two_r.clone(),
        s_pp_eq_pq,
    );
    let mid3 = c.add(p_plus_q.clone(), s_two_r.clone());
    let hr3 = c.cong_right(
        b,
        &add_c,
        s_two_r.clone(),
        two_r_val.clone(),
        p_plus_q.clone(),
        s_two_r_eq_2r,
    );
    let ss_target = c.add(p_plus_q.clone(), two_r_val.clone());
    let ppadd_eq_target = c.trans(pp_plus_twor.clone(), mid3, ss_target.clone(), hl3, hr3);
    let ss_eq_target = c.trans(
        ss.clone(),
        pp_plus_twor.clone(),
        ss_target.clone(),
        ss_eq_ppadd,
        ppadd_eq_target,
    );

    // =====================================================================
    // S4–S5 :  R ≤ 8^n·SG·SH    (Cauchy-Schwarz + IH + le_of_sq_le_sq)
    // =====================================================================
    let r_le = step_s45_r_bound(
        c, b, rho, n, ih, f, &big_p, &big_q, &big_r, &sq_g, &sq_h, &pow4_g, &pow4_h, &r_summand,
        &sg, &sh,
    );
    // IH bounds:
    let ih_g = Expr::app(ih.clone(), c.g_part_of(n, f)); // P ≤ 8^n·SG²
    let ih_h = Expr::app(ih.clone(), c.lift_h_of(n, f)); // Q ≤ 8^n·SH²
    let pow8_sg2 = c.mul(pow8n.clone(), c.sq(&sg));
    let pow8_sh2 = c.mul(pow8n.clone(), c.sq(&sh));
    let pow8_sgsh = c.mul(pow8n.clone(), c.mul(sg.clone(), sh.clone()));

    // =====================================================================
    // S5' :  (P+Q) + (1+1)R ≤ (8^n SG² + 8^n SH²) + (1+1)·(8^n SG·SH)
    // =====================================================================
    // P+Q ≤ 8^n SG² + 8^n SH²
    let pq_le = add_le_add(c, &big_p, &pow8_sg2, &big_q, &pow8_sh2, ih_g, ih_h);
    let bnd_pq = c.add(pow8_sg2.clone(), pow8_sh2.clone());
    // (1+1)R ≤ (1+1)(8^n SG·SH)   [mll (1+1) R (8^n SG·SH) r_le (0≤1+1)]
    let zero_le_two = step_zero_le_two(c);
    let two_r_le = c.mll(&two, &big_r, &pow8_sgsh, r_le, zero_le_two);
    let bnd_2r = c.mul(two.clone(), pow8_sgsh.clone());
    // chain: (P+Q)+(1+1)R ≤ bnd_pq + bnd_2r
    let target_le = add_le_add(c, &p_plus_q, &bnd_pq, &two_r_val, &bnd_2r, pq_le, two_r_le);
    let bound = c.add(bnd_pq.clone(), bnd_2r.clone());

    // SS ≤ bound   [subst_le_left along (SS = (P+Q)+(1+1)R)]
    let ss_le_bound = c.subst_le_left(
        b,
        bound.clone(),
        ss_target.clone(),
        ss.clone(),
        c.symm(ss.clone(), ss_target.clone(), ss_eq_target),
        target_le,
    );

    // =====================================================================
    // S6 :  bound = 8^n·(SG+SH)²
    // =====================================================================
    let bound_eq = step_s6_assemble(c, b, &pow8n, &sg, &sh, &bnd_pq, &bnd_2r);
    let sg_plus_sh = c.add(sg.clone(), sh.clone());
    let pow8_sgsh2 = c.mul(pow8n.clone(), c.sq(&sg_plus_sh)); // 8^n·(SG+SH)²
                                                              // SS ≤ 8^n(SG+SH)²
    let ss_le_assembled = c.subst_le_right(
        b,
        ss.clone(),
        bound.clone(),
        pow8_sgsh2.clone(),
        bound_eq,
        ss_le_bound,
    );

    // (1+1)·SS ≤ (1+1)·(8^n(SG+SH)²)   [mll (1+1) SS (8^n(SG+SH)²) ss_le (0≤1+1)]
    let zero_le_two2 = step_zero_le_two(c);
    let two_ss_le = c.mll(&two, &ss, &pow8_sgsh2, ss_le_assembled, zero_le_two2);
    let two_pow8_sgsh2 = c.mul(two.clone(), pow8_sgsh2.clone());

    // Σ split_sum ≤ (1+1)·(8^n(SG+SH)²)   [le_trans]
    let s_split_le_final = c.le_trans(
        &s_split,
        &two_ss,
        &two_pow8_sgsh2,
        s_split_le_two_ss,
        two_ss_le,
    );

    // LHS(n+1) ≤ (1+1)·(8^n(SG+SH)²)   [subst_le_left along (LHS = Σ split_sum)]
    let lhs_le_final = c.subst_le_left(
        b,
        two_pow8_sgsh2.clone(),
        s_split.clone(),
        lhs_full.clone(),
        c.symm(lhs_full.clone(), s_split.clone(), lhs_eq_split),
        s_split_le_final,
    );

    // =====================================================================
    // S7 + S8 :  (1+1)·(8^n(SG+SH)²) = 8^{n+1}·SF'²   (close)
    // =====================================================================
    let final_eq = step_s78_close(
        c,
        b,
        &pow8n,
        n,
        &sg,
        &sh,
        &sf,
        f,
        &sg_plus_sh,
        &two_pow8_sgsh2,
    );
    let goal_rhs = c.mul(c.pow8(&sn), c.sq(&sf)); // 8^{n+1}·sq(SF')
                                                  // LHS(n+1) ≤ 8^{n+1}·SF'²
    c.subst_le_right(
        b,
        lhs_full,
        two_pow8_sgsh2,
        goal_rhs,
        final_eq,
        lhs_le_final,
    )
}

include!("boolean_analysis_hc24_step_legs.rs");
