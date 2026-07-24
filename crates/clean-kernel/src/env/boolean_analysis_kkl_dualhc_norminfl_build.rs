// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Term builders for boolean_analysis_kkl_dualhc_norminfl.rs (the STEP-2c
// influence-normalization bridge). `include!`d into that module to keep each
// file under the 500-line convention; shares `NormInflConsts` + its imports.

/// Build the type (`for_value = false`) or proof value (`for_value = true`) of
/// `cube_mul_div_self_cancel`.
fn build_cube_cancel(c: &NormInflConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (p_id, p) = b.fresh_local(c.rat());

    let d = c.denom(&n);
    let dinv = c.inv(d.clone());
    let p_dinv = c.mul(p.clone(), dinv.clone()); // P·D⁻¹  (≡ Influence)
    let dd = c.mul(d.clone(), d.clone()); // D·D
    let lhs = c.mul(p.clone(), d.clone()); // P·D
    let rhs = c.mul(dd.clone(), p_dinv.clone()); // (D·D)·(P·D⁻¹)
    let concl = c.eq(lhs.clone(), rhs.clone());

    let tail = if for_value {
        // Build RHS = LHS, then symm.
        // r0 := (D·D)·(P·D⁻¹)
        let r0 = rhs.clone();
        // e1 : (D·D)·(P·D⁻¹) = D·(D·(P·D⁻¹))     [mul_assoc D D (P·D⁻¹)]
        let d_pdinv = c.mul(d.clone(), p_dinv.clone()); // D·(P·D⁻¹)
        let r1 = c.mul(d.clone(), d_pdinv.clone());
        let e1 = c.mul_assoc(d.clone(), d.clone(), p_dinv.clone());

        // sub1 : D·(P·D⁻¹) = (D·P)·D⁻¹            [symm (mul_assoc D P D⁻¹)]
        let dp = c.mul(d.clone(), p.clone()); // D·P
        let dp_dinv = c.mul(dp.clone(), dinv.clone()); // (D·P)·D⁻¹
        let assoc_dpdi = c.mul_assoc(d.clone(), p.clone(), dinv.clone()); // (D·P)·D⁻¹ = D·(P·D⁻¹)
        let sub1 = c.symm(dp_dinv.clone(), d_pdinv.clone(), assoc_dpdi);
        // e2 : D·(D·(P·D⁻¹)) = D·((D·P)·D⁻¹)       [congr (D·) sub1]
        let g_dmul = c.lam_rat(&b, |t| c.mul(d.clone(), t));
        let r2 = c.mul(d.clone(), dp_dinv.clone());
        let e2 = c.congr_arg(d_pdinv.clone(), dp_dinv.clone(), g_dmul.clone(), sub1);

        // sub2 : (D·P)·D⁻¹ = (P·D)·D⁻¹             [congr (·D⁻¹) (mul_comm D P)]
        let pd = c.mul(p.clone(), d.clone()); // P·D
        let pd_dinv = c.mul(pd.clone(), dinv.clone()); // (P·D)·D⁻¹
        let comm_dp = c.mul_comm(d.clone(), p.clone()); // D·P = P·D
        let g_mul_dinv = c.lam_rat(&b, |t| c.mul(t, dinv.clone()));
        let sub2 = c.congr_arg(dp.clone(), pd.clone(), g_mul_dinv, comm_dp);
        // e3 : D·((D·P)·D⁻¹) = D·((P·D)·D⁻¹)       [congr (D·) sub2]
        let r3 = c.mul(d.clone(), pd_dinv.clone());
        let e3 = c.congr_arg(dp_dinv.clone(), pd_dinv.clone(), g_dmul.clone(), sub2);

        // sub3 : (P·D)·D⁻¹ = P·(D·D⁻¹)             [mul_assoc P D D⁻¹]
        let d_dinv = c.mul(d.clone(), dinv.clone()); // D·D⁻¹
        let p_d_dinv = c.mul(p.clone(), d_dinv.clone()); // P·(D·D⁻¹)
        let sub3 = c.mul_assoc(p.clone(), d.clone(), dinv.clone());
        // e4 : D·((P·D)·D⁻¹) = D·(P·(D·D⁻¹))       [congr (D·) sub3]
        let r4 = c.mul(d.clone(), p_d_dinv.clone());
        let e4 = c.congr_arg(pd_dinv.clone(), p_d_dinv.clone(), g_dmul.clone(), sub3);

        // sub4a : D·D⁻¹ = 1                        [mul_inv_cancel D (D≠0)]
        let inv_cancel = c.mul_inv_cancel(d.clone(), c.d_ne_zero(&n));
        // sub4 : P·(D·D⁻¹) = P·1                   [congr (P·) sub4a]
        let one = c.one();
        let p_one = c.mul(p.clone(), one.clone()); // P·1
        let g_pmul = c.lam_rat(&b, |t| c.mul(p.clone(), t));
        let sub4 = c.congr_arg(d_dinv.clone(), one.clone(), g_pmul.clone(), inv_cancel);
        // e5 : D·(P·(D·D⁻¹)) = D·(P·1)             [congr (D·) sub4]
        let r5 = c.mul(d.clone(), p_one.clone());
        let e5 = c.congr_arg(p_d_dinv.clone(), p_one.clone(), g_dmul.clone(), sub4);

        // sub5 : P·1 = P                            [mul_comm P 1 then one_mul, OR mul_one]
        // We use mul_comm P 1 : P·1 = 1·P, then one_mul P : 1·P = P.
        let one_p = c.mul(one.clone(), p.clone()); // 1·P
        let comm_p1 = c.mul_comm(p.clone(), one.clone()); // P·1 = 1·P
        let onemul_p = c.one_mul(p.clone()); // 1·P = P
        let sub5 = c.trans(p_one.clone(), one_p.clone(), p.clone(), comm_p1, onemul_p);
        // e6 : D·(P·1) = D·P                        [congr (D·) sub5]
        let dp_target = c.mul(d.clone(), p.clone()); // D·P
        let e6 = c.congr_arg(p_one.clone(), p.clone(), g_dmul.clone(), sub5);

        // e7 : D·P = P·D                            [mul_comm D P]
        let e7 = c.mul_comm(d.clone(), p.clone());

        // Chain r0 = r1 = r2 = r3 = r4 = r5 = D·P = P·D.
        let t1 = c.trans(r0.clone(), r1.clone(), r2.clone(), e1, e2);
        let t2 = c.trans(r0.clone(), r2.clone(), r3.clone(), t1, e3);
        let t3 = c.trans(r0.clone(), r3.clone(), r4.clone(), t2, e4);
        let t4 = c.trans(r0.clone(), r4.clone(), r5.clone(), t3, e5);
        let t5 = c.trans(r0.clone(), r5.clone(), dp_target.clone(), t4, e6);
        let t6 = c.trans(r0.clone(), dp_target.clone(), lhs.clone(), t5, e7);
        // t6 : RHS = LHS  (i.e. rhs = lhs); we need lhs = rhs.
        c.symm(rhs.clone(), lhs.clone(), t6)
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
    let e = bind(&b, p_id, c.rat(), tail);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}

/// Build the type (`for_value = false`) or proof value (`for_value = true`) of
/// `dualhc_m_pow2_eq_4pow_influence`.
fn build_m_norm(c: &NormInflConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (f_id, f) = b.fresh_local(c.bool_fn_of(&n));
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let d = c.denom(&n);
    let m = c.m_of(&b, &n, &f, &i); // m_i
    let p = c.p_of(&b, &n, &f, &i); // P = subsetSum(ind_fn) (≡ Influence·D after norm)
    let infl = c.influence_of(&n, &f, &i); // Influence n f i ≡ P·D⁻¹ def-eq

    let m_d = c.mul(m.clone(), d.clone()); // m_i · D
    let dd = c.mul(d.clone(), d.clone()); // D·D
    let dd_infl = c.mul(dd.clone(), infl.clone()); // (D·D)·Inf
    let concl = c.eq(m_d.clone(), dd_infl.clone());

    let tail = if for_value {
        // step1 : m_i = P   (dualhc_step2_m_eq_disagree_mass n f i).
        let step1 = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.dualhc_step2_m_eq_disagree_mass"),
                vec![],
            ),
            [n.clone(), f.clone(), i.clone()],
        );
        // e1 : m_i·D = P·D   [congr (·D) step1].
        let g_mul_d = c.lam_rat(&b, |t| c.mul(t, d.clone()));
        let p_d = c.mul(p.clone(), d.clone()); // P·D
        let e1 = c.congr_arg(m.clone(), p.clone(), g_mul_d, step1);

        // step2 : P·D = (D·D)·(P·D⁻¹)   (cube_mul_div_self_cancel n P).
        let step2 = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.cube_mul_div_self_cancel"),
                vec![],
            ),
            [n.clone(), p.clone()],
        );
        // (D·D)·(P·D⁻¹) is DEF-EQ to (D·D)·Influence (Influence ≡ P·D⁻¹), so its
        // type is `P·D = (D·D)·Influence` up to def-eq. The kernel accepts step2
        // directly at the target type `P·D = (D·D)·Inf` because `Influence n f i`
        // reduces to `P·D⁻¹` (Expect/Rat.div/subsetSum all reducible). We chain
        // e1 (m_i·D = P·D) with step2 (P·D = (D·D)·Inf).
        c.trans(m_d.clone(), p_d.clone(), dd_infl.clone(), e1, step2)
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
