// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// The `NNReal.cube_minkowski_merge` type/value builders + the RHS-expansion ring
// identity. `include!`d into `algebra_nnreal_cube_minkowski_merge.rs`.

/// The six free locals (U₁,S₁,T₁,U₂,S₂,T₂) + the four hypotheses, then the body.
fn build_merge(c: &MergeConsts) -> (Expr, Expr) {
    // h1 : U₁³ ≤ S₁²T₁ ; h2 : U₂³ ≤ S₂²T₂
    let h1_ty = |u1: &Expr, s1: &Expr, t1: &Expr| c.nnle(&c.cube(u1), &c.sq_t(s1, t1));
    let h2_ty = |u2: &Expr, s2: &Expr, t2: &Expr| c.nnle(&c.cube(u2), &c.sq_t(s2, t2));
    let u1sq_u2 = |u1: &Expr, u2: &Expr| c.mul(&c.mul(u1, u1), u2); // (U₁·U₁)·U₂
    let u1_u2sq = |u1: &Expr, u2: &Expr| c.mul(&c.mul(u1, u2), u2); // (U₁·U₂)·U₂
    let p_term = |s1: &Expr, s2: &Expr, t1: &Expr| c.mul(&c.mul(s1, s2), t1); // S₁S₂T₁
    let pp_term = |s1: &Expr, s2: &Expr, t2: &Expr| c.mul(&c.mul(s1, s2), t2); // S₁S₂T₂
    let q_term = |s1: &Expr, t2: &Expr| c.mul(&c.mul(s1, s1), t2); // S₁²T₂
    let qp_term = |s2: &Expr, t1: &Expr| c.mul(&c.mul(s2, s2), t1); // S₂²T₁

    let ha_ty = |u1: &Expr, u2: &Expr, s1: &Expr, s2: &Expr, t1: &Expr, t2: &Expr| {
        let lhs = c.three(&u1sq_u2(u1, u2));
        let rhs = c.two_plus(&p_term(s1, s2, t1), &q_term(s1, t2));
        c.nnle(&lhs, &rhs)
    };
    let hb_ty = |u1: &Expr, u2: &Expr, s1: &Expr, s2: &Expr, t1: &Expr, t2: &Expr| {
        let lhs = c.three(&u1_u2sq(u1, u2));
        let rhs = c.two_plus(&pp_term(s1, s2, t2), &qp_term(s2, t1));
        c.nnle(&lhs, &rhs)
    };
    let concl_ty = |u1: &Expr, u2: &Expr, s1: &Expr, s2: &Expr, t1: &Expr, t2: &Expr| {
        let us = c.add(u1, u2);
        let lhs = c.mul(&c.mul(&us, &us), &us);
        let ss = c.add(s1, s2);
        let tt = c.add(t1, t2);
        let rhs = c.mul(&c.mul(&ss, &ss), &tt);
        c.nnle(&lhs, &rhs)
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (u1_id, u1) = b.fresh_local(c.nnreal.clone());
        let (s1_id, s1) = b.fresh_local(c.nnreal.clone());
        let (t1_id, t1) = b.fresh_local(c.nnreal.clone());
        let (u2_id, u2) = b.fresh_local(c.nnreal.clone());
        let (s2_id, s2) = b.fresh_local(c.nnreal.clone());
        let (t2_id, t2) = b.fresh_local(c.nnreal.clone());
        let h1t = h1_ty(&u1, &s1, &t1);
        let (h1_id, _) = b.fresh_local(h1t.clone());
        let h2t = h2_ty(&u2, &s2, &t2);
        let (h2_id, _) = b.fresh_local(h2t.clone());
        let hat = ha_ty(&u1, &u2, &s1, &s2, &t1, &t2);
        let (ha_id, _) = b.fresh_local(hat.clone());
        let hbt = hb_ty(&u1, &u2, &s1, &s2, &t1, &t2);
        let (hb_id, _) = b.fresh_local(hbt.clone());
        let concl = concl_ty(&u1, &u2, &s1, &s2, &t1, &t2);
        let e = b.mk_pi(hb_id, BinderInfo::Default, hbt, concl);
        let e = b.mk_pi(ha_id, BinderInfo::Default, hat, e);
        let e = b.mk_pi(h2_id, BinderInfo::Default, h2t, e);
        let e = b.mk_pi(h1_id, BinderInfo::Default, h1t, e);
        let e = b.mk_pi(t2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_pi(s2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_pi(u2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_pi(t1_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_pi(s1_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_pi(u1_id, BinderInfo::Default, c.nnreal.clone(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (u1_id, u1) = b.fresh_local(c.nnreal.clone());
        let (s1_id, s1) = b.fresh_local(c.nnreal.clone());
        let (t1_id, t1) = b.fresh_local(c.nnreal.clone());
        let (u2_id, u2) = b.fresh_local(c.nnreal.clone());
        let (s2_id, s2) = b.fresh_local(c.nnreal.clone());
        let (t2_id, t2) = b.fresh_local(c.nnreal.clone());
        let h1t = h1_ty(&u1, &s1, &t1);
        let (h1_id, h1) = b.fresh_local(h1t.clone());
        let h2t = h2_ty(&u2, &s2, &t2);
        let (h2_id, h2) = b.fresh_local(h2t.clone());
        let hat = ha_ty(&u1, &u2, &s1, &s2, &t1, &t2);
        let (ha_id, ha) = b.fresh_local(hat.clone());
        let hbt = hb_ty(&u1, &u2, &s1, &s2, &t1, &t2);
        let (hb_id, hb) = b.fresh_local(hbt.clone());

        let proof = build_merge_value(c, &b, &u1, &s1, &t1, &u2, &s2, &t2, h1, h2, ha, hb);

        let e = b.mk_lam(hb_id, BinderInfo::Default, hbt, proof);
        let e = b.mk_lam(ha_id, BinderInfo::Default, hat, e);
        let e = b.mk_lam(h2_id, BinderInfo::Default, h2t, e);
        let e = b.mk_lam(h1_id, BinderInfo::Default, h1t, e);
        let e = b.mk_lam(t2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_lam(s2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_lam(u2_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_lam(t1_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_lam(s1_id, BinderInfo::Default, c.nnreal.clone(), e);
        let e = b.mk_lam(u1_id, BinderInfo::Default, c.nnreal.clone(), e);
        b.finish(e)
    };

    (ty, value)
}

/// The merge proof body. Builds (cube binomial) → (term-wise bound) → (RHS reassemble).
#[allow(clippy::too_many_arguments)]
fn build_merge_value(
    c: &MergeConsts,
    b: &EnvDeclBuilder,
    u1: &Expr,
    s1: &Expr,
    t1: &Expr,
    u2: &Expr,
    s2: &Expr,
    t2: &Expr,
    h1: Expr,
    h2: Expr,
    ha: Expr,
    hb: Expr,
) -> Expr {
    // ── canonical left-nested monomials ──
    let u1c = c.cube(u1); // U₁³
    let u2c = c.cube(u2); // U₂³
    let c1 = c.sq_t(s1, t1); // S₁²T₁
    let c2 = c.sq_t(s2, t2); // S₂²T₂
    let u1sq_u2 = c.mul(&c.mul(u1, u1), u2); // (U₁·U₁)·U₂
    let u1_u2sq = c.mul(&c.mul(u1, u2), u2); // (U₁·U₂)·U₂
    let three_a = c.three(&u1sq_u2); // 3U₁²U₂
    let three_b = c.three(&u1_u2sq); // 3U₁U₂²
    let p = c.mul(&c.mul(s1, s2), t1); // S₁S₂T₁
    let q = c.mul(&c.mul(s1, s1), t2); // S₁²T₂
    let pp = c.mul(&c.mul(s1, s2), t2); // S₁S₂T₂
    let qp = c.mul(&c.mul(s2, s2), t1); // S₂²T₁
    let a1 = c.two_plus(&p, &q); // 2P+Q  (splitA RHS)
    let a2 = c.two_plus(&pp, &qp); // 2P'+Q' (splitB RHS)

    // ── add_cube U₁ U₂ : ((U₁+U₂)·(U₁+U₂))·(U₁+U₂) = (U₁³+3U₁²U₂)+(3U₁U₂²+U₂³) ──
    // (NB: NNReal.add_cube's RHS uses the `(t+t)+t` 3· form, matching `three`.)
    let cube_eq = c.add_cube(u1, u2);
    let lhs_cube = {
        let us = c.add(u1, u2);
        c.mul(&c.mul(&us, &us), &us)
    };
    let cube_expanded = c.add(&c.add(&u1c, &three_a), &c.add(&three_b, &u2c));

    // ── term-wise bound: (U₁³+3U₁²U₂) ≤ (S₁²T₁ + (2P+Q)) via add_le_add h1 ha ──
    let left_bound = c.add_le_add(&u1c, &c1, &three_a, &a1, h1, ha);
    let left_bounded = c.add(&c1, &a1);
    // (3U₁U₂²+U₂³) ≤ ((2P'+Q') + S₂²T₂) via add_le_add hb h2
    let right_bound = c.add_le_add(&three_b, &a2, &u2c, &c2, hb, h2);
    let right_bounded = c.add(&a2, &c2);
    // outer add_le_add : cube_expanded ≤ (left_bounded + right_bounded)
    let left_summand = c.add(&u1c, &three_a);
    let right_summand = c.add(&three_b, &u2c);
    let bound = c.add_le_add(
        &left_summand,
        &left_bounded,
        &right_summand,
        &right_bounded,
        left_bound,
        right_bound,
    );
    // bound : cube_expanded ≤ bound_sum, where bound_sum := (c1+a1)+(a2+c2).
    let bound_sum = c.add(&left_bounded, &right_bounded);

    // ── transport bound's LHS cube_expanded back to lhs_cube along symm cube_eq ──
    // goal_after : lhs_cube ≤ bound_sum.
    let motive_lhs = {
        let mut mb = EnvDeclBuilder::child_of(b);
        let (w_id, w) = mb.fresh_local(c.nnreal.clone());
        let body = c.nnle(&w, &bound_sum);
        mb.finish_child(mb.mk_lam(w_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    let bound_lhs = c.subst(
        motive_lhs,
        &cube_expanded,
        &lhs_cube,
        c.symm(&lhs_cube, &cube_expanded, cube_eq),
        bound,
    );

    // ── RHS expansion identity: target_rhs = bound_sum, then transport ──
    // target_rhs := ((S₁+S₂)·(S₁+S₂))·(T₁+T₂).
    let ss = c.add(s1, s2);
    let tt = c.add(t1, t2);
    let target_rhs = c.mul(&c.mul(&ss, &ss), &tt);
    let rhs_eq = build_rhs_expand(c, b, s1, s2, t1, t2); // target_rhs = bound_sum

    // transport bound_lhs : lhs_cube ≤ bound_sum  along symm rhs_eq (bound_sum → target_rhs)
    let motive_rhs = {
        let mut mb = EnvDeclBuilder::child_of(b);
        let (w_id, w) = mb.fresh_local(c.nnreal.clone());
        let body = c.nnle(&lhs_cube, &w);
        mb.finish_child(mb.mk_lam(w_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    c.subst(
        motive_rhs,
        &bound_sum,
        &target_rhs,
        c.symm(&target_rhs, &bound_sum, rhs_eq),
        bound_lhs,
    )
}

/// `((S₁+S₂)·(S₁+S₂))·(T₁+T₂) = (S₁²T₁ + (2P+Q)) + ((2P'+Q') + S₂²T₂)`
/// where `P=S₁S₂T₁, Q=S₁²T₂, P'=S₁S₂T₂, Q'=S₂²T₁`.
///
/// Built by full distribution to a flat normal form, then `add_assoc`/`add_comm`
/// reshaping. The normal form is the right-leaning 8-atom sum
/// `S₁²T₁ + (S₁S₂T₁ + (S₁S₂T₁ + (S₁²T₂ + (S₁S₂T₂ + (S₁S₂T₂ + (S₂²T₁ + S₂²T₂))))))`.
fn build_rhs_expand(
    c: &MergeConsts,
    b: &EnvDeclBuilder,
    s1: &Expr,
    s2: &Expr,
    t1: &Expr,
    t2: &Expr,
) -> Expr {
    let ss = c.add(s1, s2);
    let tt = c.add(t1, t2);
    let target = c.mul(&c.mul(&ss, &ss), &tt);

    // SQ := (S₁+S₂)·(S₁+S₂) = add_sq form (S₁² + (S₁S₂+S₁S₂)) + S₂².
    let s1s1 = c.mul(s1, s1);
    let s1s2 = c.mul(s1, s2);
    let s2s2 = c.mul(s2, s2);
    let s1s2_2 = c.add(&s1s2, &s1s2);
    let sq_lead = c.add(&s1s1, &s1s2_2);
    let sq = c.add(&sq_lead, &s2s2); // (S₁²+(S₁S₂+S₁S₂))+S₂²

    // add_sq S₁ S₂ : (S₁+S₂)·(S₁+S₂) = SQ.
    let h_addsq = Expr::apps(
        Expr::const_(Name::from_string("NNReal.add_sq"), vec![]),
        [s1.clone(), s2.clone()],
    );
    // step0 : ((S₁+S₂)·(S₁+S₂))·(T₁+T₂) = SQ·(T₁+T₂)  [congr (·(T₁+T₂)) h_addsq]
    let ss_ss = c.mul(&ss, &ss);
    let step0 = c.cong_mul_left(b, &tt, &ss_ss, &sq, h_addsq);
    let sq_tt = c.mul(&sq, &tt);

    // step1 : SQ·(T₁+T₂) = SQ·T₁ + SQ·T₂   [mul_add SQ T₁ T₂]
    let step1 = c.mul_add(&sq, t1, t2);
    let sq_t1 = c.mul(&sq, t1);
    let sq_t2 = c.mul(&sq, t2);
    let sqt1_plus_sqt2 = c.add(&sq_t1, &sq_t2);

    // ── expand SQ·T₁ = ((S₁²+(S₁S₂+S₁S₂))+S₂²)·T₁ ──
    // add_mul sq_lead s2s2 T₁ : SQ·T₁ = sq_lead·T₁ + (S₂²)·T₁
    let e_sqt1_1 = c.add_mul(&sq_lead, &s2s2, t1);
    let lead_t1 = c.mul(&sq_lead, t1); // (S₁²+(S₁S₂+S₁S₂))·T₁
    let s2s2_t1 = c.mul(&s2s2, t1); // S₂²T₁ = Q'
    let lead_t1_plus = c.add(&lead_t1, &s2s2_t1);
    // add_mul S₁² (S₁S₂+S₁S₂) T₁ : sq_lead·T₁ = (S₁²)·T₁ + (S₁S₂+S₁S₂)·T₁
    let e_lead_t1 = c.add_mul(&s1s1, &s1s2_2, t1);
    let s1s1_t1 = c.mul(&s1s1, t1); // S₁²T₁ = c1
    let cross_t1 = c.mul(&s1s2_2, t1); // (S₁S₂+S₁S₂)·T₁
    let s1s1t1_plus_cross = c.add(&s1s1_t1, &cross_t1);
    // congr (·+ S₂²T₁) e_lead_t1
    let c_sqt1 = c.cong_add_left(b, &s2s2_t1, &lead_t1, &s1s1t1_plus_cross, e_lead_t1);
    let inner_t1 = c.add(&s1s1t1_plus_cross, &s2s2_t1); // ((S₁²T₁ + cross_t1) + S₂²T₁)
    let h_sqt1 = c.trans(&sq_t1, &lead_t1_plus, &inner_t1, e_sqt1_1, c_sqt1);
    // cross_t1 = (S₁S₂+S₁S₂)·T₁ = S₁S₂T₁ + S₁S₂T₁  [add_mul S₁S₂ S₁S₂ T₁]
    let e_cross_t1 = c.add_mul(&s1s2, &s1s2, t1);
    let s1s2_t1 = c.mul(&s1s2, t1); // S₁S₂T₁ = P
    let p_plus_p = c.add(&s1s2_t1, &s1s2_t1);

    // ── expand SQ·T₂ similarly ──
    let e_sqt2_1 = c.add_mul(&sq_lead, &s2s2, t2);
    let lead_t2 = c.mul(&sq_lead, t2);
    let s2s2_t2 = c.mul(&s2s2, t2); // S₂²T₂ = c2
    let lead_t2_plus = c.add(&lead_t2, &s2s2_t2);
    let e_lead_t2 = c.add_mul(&s1s1, &s1s2_2, t2);
    let s1s1_t2 = c.mul(&s1s1, t2); // S₁²T₂ = Q
    let cross_t2 = c.mul(&s1s2_2, t2); // (S₁S₂+S₁S₂)·T₂
    let s1s1t2_plus_cross = c.add(&s1s1_t2, &cross_t2);
    let c_sqt2 = c.cong_add_left(b, &s2s2_t2, &lead_t2, &s1s1t2_plus_cross, e_lead_t2);
    let inner_t2 = c.add(&s1s1t2_plus_cross, &s2s2_t2);
    let h_sqt2 = c.trans(&sq_t2, &lead_t2_plus, &inner_t2, e_sqt2_1, c_sqt2);
    let e_cross_t2 = c.add_mul(&s1s2, &s1s2, t2);
    let s1s2_t2 = c.mul(&s1s2, t2); // S₁S₂T₂ = P'
    let pp_plus_pp = c.add(&s1s2_t2, &s1s2_t2);

    // step2 : SQ·T₁ + SQ·T₂ = inner_t1 + inner_t2
    let c2a = c.cong_add_left(b, &sq_t2, &sq_t1, &inner_t1, h_sqt1);
    let inner_t1_plus_sqt2 = c.add(&inner_t1, &sq_t2);
    let c2b = c.cong_add_right(b, &inner_t1, &sq_t2, &inner_t2, h_sqt2);
    let inner_sum = c.add(&inner_t1, &inner_t2);
    let step2 = c.trans(&sqt1_plus_sqt2, &inner_t1_plus_sqt2, &inner_sum, c2a, c2b);

    // Now `inner_sum = ((c1 + cross_t1) + Q') + ((Q + cross_t2) + c2)`.
    // We want to reach `bound_sum := (c1 + ((P+P)+Q)) + (((P'+P')+Q') + c2)`.
    // First rewrite cross_t1 → (P+P), cross_t2 → (P'+P').
    // congr replacing cross_t1 in inner_t1 = (c1 + cross_t1) + Q'.
    //   inner_t1' := ((c1 + (P+P)) + Q')   (= the bracketing we will reshape).
    let c1_plus_cross_t1 = c.add(&s1s1_t1, &cross_t1);
    let c1_plus_pp = c.add(&s1s1_t1, &p_plus_p);
    let rw_cross_t1 = c.cong_add_right(b, &s1s1_t1, &cross_t1, &p_plus_p, e_cross_t1);
    // lift into ( · + Q')
    let rw_inner_t1_lead =
        c.cong_add_left(b, &s2s2_t1, &c1_plus_cross_t1, &c1_plus_pp, rw_cross_t1);
    let inner_t1_b = c.add(&c1_plus_pp, &s2s2_t1); // ((c1 + (P+P)) + Q')
                                                   // inner_t1 = inner_t1_b
                                                   // (h: inner_t1 = inner_t1_b)

    // similarly cross_t2 → (P'+P') in inner_t2 = (Q + cross_t2) + c2.
    let q_plus_cross_t2 = c.add(&s1s1_t2, &cross_t2);
    let q_plus_ppp = c.add(&s1s1_t2, &pp_plus_pp);
    let rw_cross_t2 = c.cong_add_right(b, &s1s1_t2, &cross_t2, &pp_plus_pp, e_cross_t2);
    let rw_inner_t2_lead = c.cong_add_left(b, &s2s2_t2, &q_plus_cross_t2, &q_plus_ppp, rw_cross_t2);
    let inner_t2_b = c.add(&q_plus_ppp, &s2s2_t2); // ((Q + (P'+P')) + c2)

    // rewrite inner_sum = inner_t1 + inner_t2 → inner_t1_b + inner_t2_b
    let rw_sum_left = c.cong_add_left(b, &inner_t2, &inner_t1, &inner_t1_b, rw_inner_t1_lead);
    let inner_t1b_plus_t2 = c.add(&inner_t1_b, &inner_t2);
    let rw_sum_right = c.cong_add_right(b, &inner_t1_b, &inner_t2, &inner_t2_b, rw_inner_t2_lead);
    let inner_sum_b = c.add(&inner_t1_b, &inner_t2_b);
    let rw_sum = c.trans(
        &inner_sum,
        &inner_t1b_plus_t2,
        &inner_sum_b,
        rw_sum_left,
        rw_sum_right,
    );

    // ── now reshape inner_sum_b = (((c1+(P+P))+Q') + ((Q+(P'+P'))+c2))
    //     into bound_sum := ((c1 + ((P+P)+Q)) + (((P'+P')+Q') + c2)).
    //   This is a pure add_assoc/add_comm reshuffle of the 8 atoms.
    let reshape = build_reshape(
        c,
        b,
        &s1s1_t1,
        &p_plus_p,
        &s2s2_t1,
        &s1s1_t2,
        &pp_plus_pp,
        &s2s2_t2,
    );
    // reshape : inner_sum_b = bound_sum.

    // chain target = SQ·(T₁+T₂) [step0] = SQ·T₁+SQ·T₂ [step1] = inner_sum [step2]
    //              = inner_sum_b [rw_sum] = bound_sum [reshape].
    let chain01 = c.trans(&target, &sq_tt, &sqt1_plus_sqt2, step0, step1);
    let chain012 = c.trans(&target, &sqt1_plus_sqt2, &inner_sum, chain01, step2);
    let chain_to_b = c.trans(&target, &inner_sum, &inner_sum_b, chain012, rw_sum);
    let bound_sum = {
        let p = &s1s2_t1;
        let pp = &s1s2_t2;
        let q = &s1s1_t2;
        let qp = &s2s2_t1;
        let a1 = c.two_plus(p, q);
        let a2 = c.two_plus(pp, qp);
        let c1_plus_a1 = c.add(&s1s1_t1, &a1);
        let a2_plus_c2 = c.add(&a2, &s2s2_t2);
        c.add(&c1_plus_a1, &a2_plus_c2)
    };
    c.trans(&target, &inner_sum_b, &bound_sum, chain_to_b, reshape)
}

/// Reshape `(((c1+x)+qp) + ((q+y)+c2)) = ((c1 + (x+q)) + ((y+qp) + c2))`
/// where `x=P+P`, `y=P'+P'`. Pure `add_assoc`/`add_comm`.
///
/// LHS  L := ((c1+x)+qp) + ((q+y)+c2)
/// RHS  R := (c1 + (x+q)) + ((y+qp) + c2)
#[allow(clippy::too_many_arguments)]
fn build_reshape(
    c: &MergeConsts,
    b: &EnvDeclBuilder,
    c1: &Expr,
    x: &Expr,
    qp: &Expr,
    q: &Expr,
    y: &Expr,
    c2: &Expr,
) -> Expr {
    // Strategy: flatten both to the right-leaning normal form
    //   NF := c1 + (x + (q + (y + (qp + c2)))).
    // L = ((c1+x)+qp) + ((q+y)+c2) → NF, and R = (c1+(x+q)) + ((y+qp)+c2) → NF,
    // then L = R by trans(L→NF, symm(R→NF)).
    let nf_tail = {
        // qp + c2
        let t5 = c.add(qp, c2);
        // y + (qp+c2)
        let t4 = c.add(y, &t5);
        // q + (y+(qp+c2))
        let t3 = c.add(q, &t4);
        // x + (q+...)
        let t2 = c.add(x, &t3);
        // c1 + (x+...)
        c.add(c1, &t2)
    };
    let l = {
        let c1_x = c.add(c1, x);
        let l1 = c.add(&c1_x, qp); // (c1+x)+qp
        let q_y = c.add(q, y);
        let r1 = c.add(&q_y, c2); // (q+y)+c2
        c.add(&l1, &r1)
    };
    let r = {
        let x_q = c.add(x, q);
        let l1 = c.add(c1, &x_q); // c1+(x+q)
        let y_qp = c.add(y, qp);
        let r1 = c.add(&y_qp, c2); // (y+qp)+c2
        c.add(&l1, &r1)
    };
    let l_to_nf = flatten_to_nf_l(c, b, c1, x, qp, q, y, c2, &nf_tail);
    let r_to_nf = flatten_to_nf_r(c, b, c1, x, qp, q, y, c2, &nf_tail);
    c.trans(&l, &nf_tail, &r, l_to_nf, c.symm(&r, &nf_tail, r_to_nf))
}

/// `L = ((c1+x)+qp) + ((q+y)+c2)  =  c1 + (x + (q + (y + (qp + c2))))`.
#[allow(clippy::too_many_arguments)]
fn flatten_to_nf_l(
    c: &MergeConsts,
    b: &EnvDeclBuilder,
    c1: &Expr,
    x: &Expr,
    qp: &Expr,
    q: &Expr,
    y: &Expr,
    c2: &Expr,
    nf: &Expr,
) -> Expr {
    // L = (A + B) where A=((c1+x)+qp), B=((q+y)+c2).
    let c1_x = c.add(c1, x);
    let a = c.add(&c1_x, qp); // ((c1+x)+qp)
    let q_y = c.add(q, y);
    let bcap = c.add(&q_y, c2); // ((q+y)+c2)
    let l = c.add(&a, &bcap);

    // Step 1: A = (c1+x)+qp  → c1 + (x+qp)   [add_assoc c1 x qp]
    let a_assoc = c.add_assoc(c1, x, qp); // ((c1+x)+qp) = c1+(x+qp)
    let x_qp = c.add(x, qp);
    let a1 = c.add(c1, &x_qp); // c1+(x+qp)

    // Step 2: B = (q+y)+c2 → q+(y+c2)        [add_assoc q y c2]
    let b_assoc = c.add_assoc(q, y, c2);
    let y_c2 = c.add(y, c2);
    let b1 = c.add(q, &y_c2); // q+(y+c2)

    // Rewrite L → (a1 + b1).
    let rw_a = c.cong_add_left(b, &bcap, &a, &a1, a_assoc);
    let a1_plus_b = c.add(&a1, &bcap);
    let rw_b = c.cong_add_right(b, &a1, &bcap, &b1, b_assoc);
    let l1 = c.add(&a1, &b1);
    let l_to_l1 = c.trans(&l, &a1_plus_b, &l1, rw_a, rw_b);

    // Now L1 = (c1+(x+qp)) + (q+(y+c2)). add_assoc c1 (x+qp) (q+(y+c2)):
    //   = c1 + ((x+qp) + (q+(y+c2))).
    let l1_assoc = c.add_assoc(c1, &x_qp, &b1);
    let inner = c.add(&x_qp, &b1); // (x+qp)+(q+(y+c2))
    let l2 = c.add(c1, &inner);
    // We must transform `inner = (x+qp)+(q+(y+c2))` into `x + (q+(y+(qp+c2)))`.
    // inner = (x+qp)+(q+(y+c2)).
    //   add_assoc x qp (q+(y+c2)) : (x+qp)+(q+(y+c2)) = x + (qp + (q+(y+c2))).
    let q_y_c2 = c.add(q, &y_c2);
    let inner_assoc = c.add_assoc(x, qp, &q_y_c2);
    let qp_plus = c.add(qp, &q_y_c2); // qp + (q+(y+c2))
    let inner2 = c.add(x, &qp_plus); // x + (qp + (q+(y+c2)))
                                     // We need x + (q + (y + (qp + c2))).  So transform `qp + (q+(y+c2))` → `q + (y+(qp+c2))`.
    let tail_eq = build_tail_swap(c, b, qp, q, y, c2);
    // tail_eq : qp + (q+(y+c2)) = q + (y+(qp+c2)).
    let qp_c2 = c.add(qp, c2);
    let y_qp_c2 = c.add(y, &qp_c2);
    let q_tail = c.add(q, &y_qp_c2); // q+(y+(qp+c2))  (= nf tail after c1+x)
    let rw_tail = c.cong_add_right(b, x, &qp_plus, &q_tail, tail_eq);
    let inner3 = c.add(x, &q_tail); // x + (q+(y+(qp+c2)))
    let inner_to_3 = c.trans(&inner, &inner2, &inner3, inner_assoc, rw_tail);
    // lift inner→inner3 under (c1 + ·)
    let rw_l2 = c.cong_add_right(b, c1, &inner, &inner3, inner_to_3);
    let l3 = c.add(c1, &inner3); // c1 + (x+(q+(y+(qp+c2)))) = nf
                                 // chain: L = L1 = L2 = (c1+inner3=nf)
    let l_to_l2 = c.trans(&l, &l1, &l2, l_to_l1, l1_assoc);
    let l_to_nf = c.trans(&l, &l2, &l3, l_to_l2, rw_l2);
    let _ = nf; // l3 is defeq to nf by construction
    l_to_nf
}

/// `qp + (q+(y+c2)) = q + (y+(qp+c2))`  (move `qp` past `q,y`). Pure assoc/comm.
fn build_tail_swap(
    c: &MergeConsts,
    b: &EnvDeclBuilder,
    qp: &Expr,
    q: &Expr,
    y: &Expr,
    c2: &Expr,
) -> Expr {
    // LHS = qp + (q+(y+c2)).
    let y_c2 = c.add(y, c2);
    let q_y_c2 = c.add(q, &y_c2);
    let lhs = c.add(qp, &q_y_c2);
    // add_comm qp (q+(y+c2)) : qp + (q+(y+c2)) = (q+(y+c2)) + qp.
    let step1 = c.add_comm(qp, &q_y_c2);
    let swapped = c.add(&q_y_c2, qp); // (q+(y+c2)) + qp
                                      // add_assoc q (y+c2) qp : (q+(y+c2))+qp = q + ((y+c2)+qp).
    let step2 = c.add_assoc(q, &y_c2, qp);
    let yc2_qp = c.add(&y_c2, qp); // (y+c2)+qp
    let q_tail1 = c.add(q, &yc2_qp); // q + ((y+c2)+qp)
                                     // transform (y+c2)+qp → y+(c2+qp) → y+(qp+c2).
                                     // add_assoc y c2 qp : (y+c2)+qp = y+(c2+qp).
    let yc2_qp_assoc = c.add_assoc(y, c2, qp);
    let c2_qp = c.add(c2, qp);
    let y_c2qp = c.add(y, &c2_qp); // y+(c2+qp)
                                   // add_comm c2 qp : c2+qp = qp+c2.  lift under (y + ·).
    let comm_c2qp = c.add_comm(c2, qp);
    let qp_c2 = c.add(qp, c2);
    let rw = c.cong_add_right(b, y, &c2_qp, &qp_c2, comm_c2qp);
    let y_qpc2 = c.add(y, &qp_c2); // y+(qp+c2)
    let yc2qp_to_target = c.trans(&yc2_qp, &y_c2qp, &y_qpc2, yc2_qp_assoc, rw);
    // lift under (q + ·): q+((y+c2)+qp) = q+(y+(qp+c2)).
    let rw_q = c.cong_add_right(b, q, &yc2_qp, &y_qpc2, yc2qp_to_target);
    let q_target = c.add(q, &y_qpc2); // q+(y+(qp+c2))
                                      // chain: lhs = swapped [step1] = q_tail1 [step2] = q_target [rw_q].
    let l_to_qt1 = c.trans(&lhs, &swapped, &q_tail1, step1, step2);
    c.trans(&lhs, &q_tail1, &q_target, l_to_qt1, rw_q)
}

/// `R = (c1+(x+q)) + ((y+qp)+c2)  =  c1 + (x + (q + (y + (qp + c2))))`.
#[allow(clippy::too_many_arguments)]
fn flatten_to_nf_r(
    c: &MergeConsts,
    b: &EnvDeclBuilder,
    c1: &Expr,
    x: &Expr,
    qp: &Expr,
    q: &Expr,
    y: &Expr,
    c2: &Expr,
    nf: &Expr,
) -> Expr {
    let x_q = c.add(x, q);
    let a = c.add(c1, &x_q); // c1+(x+q)
    let y_qp = c.add(y, qp);
    let bcap = c.add(&y_qp, c2); // (y+qp)+c2
    let r = c.add(&a, &bcap);

    // add_assoc c1 (x+q) ((y+qp)+c2) : R = c1 + ((x+q) + ((y+qp)+c2)).
    let r_assoc = c.add_assoc(c1, &x_q, &bcap);
    let inner = c.add(&x_q, &bcap); // (x+q)+((y+qp)+c2)
    let r1 = c.add(c1, &inner);

    // transform inner = (x+q)+((y+qp)+c2) → x+(q+(y+(qp+c2))).
    // add_assoc x q ((y+qp)+c2) : (x+q)+B = x + (q+B), B=((y+qp)+c2).
    let inner_assoc = c.add_assoc(x, q, &bcap);
    let q_plus_b = c.add(q, &bcap); // q + ((y+qp)+c2)
    let inner2 = c.add(x, &q_plus_b); // x + (q + ((y+qp)+c2))
                                      // transform B = (y+qp)+c2 → y+(qp+c2).   add_assoc y qp c2.
    let b_assoc = c.add_assoc(y, qp, c2);
    let qp_c2 = c.add(qp, c2);
    let y_qpc2 = c.add(y, &qp_c2); // y+(qp+c2)
                                   // lift under (q + ·): q+((y+qp)+c2) = q+(y+(qp+c2)).
    let rw_qb = c.cong_add_right(b, q, &bcap, &y_qpc2, b_assoc);
    let q_target = c.add(q, &y_qpc2); // q+(y+(qp+c2))
                                      // q_plus_b → q_target
                                      // lift under (x + ·)
    let rw_inner2 = c.cong_add_right(b, x, &q_plus_b, &q_target, rw_qb);
    let inner3 = c.add(x, &q_target); // x+(q+(y+(qp+c2)))
                                      // chain inner = inner2 [inner_assoc] = inner3 [rw_inner2]
    let inner_to_3 = c.trans(&inner, &inner2, &inner3, inner_assoc, rw_inner2);
    // lift under (c1 + ·): r1 = c1+inner → c1+inner3
    let rw_r1 = c.cong_add_right(b, c1, &inner, &inner3, inner_to_3);
    let r2 = c.add(c1, &inner3); // = nf
                                 // chain R = r1 [r_assoc] = r2 [rw_r1]
    let r_to_r1 = r_assoc;
    let r_to_nf = c.trans(&r, &r1, &r2, r_to_r1, rw_r1);
    let _ = nf;
    r_to_nf
}
