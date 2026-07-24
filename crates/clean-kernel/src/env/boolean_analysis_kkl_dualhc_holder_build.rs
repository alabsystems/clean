// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Proof-term builders for the rational 4th-power Hölder lemma R2
// (`BoolAnalysis.sum_prod_pow4_le_m3_sumpow4`). `include!`d into
// `boolean_analysis_kkl_dualhc_holder.rs` — shares its `HolderConsts`,
// `lam_fn`/`forall_x` helpers, and imports. See that module's docs for
// the statement and the proof outline. Split out to keep each file
// under the 500-line convention. (Regular `//` comments: inner doc
// comments `//!` are not allowed at an `include!` site.)

/// The proof term of `sum_prod_pow4_le_m3_sumpow4` at the bound binders/hyps.
fn build_holder_proof(
    c: &HolderConsts,
    b: &EnvDeclBuilder,
    n: &Expr,
    e: &Expr,
    w: &Expr,
    chi: &Expr,
    m: &Expr,
    p: &Expr,
    sum_w4: &Expr,
    m_sq: &Expr,
    m_cube: &Expr,
    ew_fn: &Expr,
    w4_fn: &Expr,
    h1: &Expr, // ∀ x, chi x = e x·e x
    h2: &Expr, // ∀ x, e x·chi x = e x
    h3: &Expr, // ∀ x, chi x·chi x = chi x
    h4: &Expr, // ∀ x, chi x ≤ 1
    h5: &Expr, // 0 ≤ m
    h6: &Expr, // m = Σ chi
) -> Expr {
    let e_of = |x: &Expr| Expr::app(e.clone(), x.clone());
    let w_of = |x: &Expr| Expr::app(w.clone(), x.clone());
    let chi_of = |x: &Expr| Expr::app(chi.clone(), x.clone());

    // ════════════════════════════════════════════════════════════════════
    //  Integrands used by the two Cauchy–Schwarz applications.
    // ════════════════════════════════════════════════════════════════════
    // chiw := x ↦ chi x · w x   (CS1's `b` leg).
    let chiw_fn = lam_fn(c, b, n, |_d, x| c.mul(chi_of(x), w_of(x)));
    // chiw2 := x ↦ chi x · (w x · w x)   (CS2's `b` leg).
    let chiw2_fn = lam_fn(c, b, n, |_d, x| c.mul(chi_of(x), c.sq(w_of(x))));

    // CS1 integrands (as produced by Fin.sum_cauchy_schwarz N e chiw):
    //   a·b  = x ↦ e x · (chi x · w x)
    //   a·a  = x ↦ e x · e x
    //   b·b  = x ↦ (chi x · w x) · (chi x · w x)
    let e_chiw_fn = lam_fn(c, b, n, |_d, x| c.mul(e_of(x), c.mul(chi_of(x), w_of(x))));
    let ee_fn = lam_fn(c, b, n, |_d, x| c.mul(e_of(x), e_of(x)));
    let q_fn = lam_fn(c, b, n, |_d, x| {
        let cw = c.mul(chi_of(x), w_of(x));
        c.mul(cw.clone(), cw)
    });
    // CS2 integrands (Fin.sum_cauchy_schwarz N chi chiw2):
    //   a·b  = x ↦ chi x · (chi x · (w x·w x))
    //   a·a  = x ↦ chi x · chi x
    //   b·b  = x ↦ (chi x·(w x·w x)) · (chi x·(w x·w x))
    let chi_chiw2_fn = lam_fn(c, b, n, |_d, x| {
        c.mul(chi_of(x), c.mul(chi_of(x), c.sq(w_of(x))))
    });
    let chichi_fn = lam_fn(c, b, n, |_d, x| c.mul(chi_of(x), chi_of(x)));
    let r_fn = lam_fn(c, b, n, |_d, x| {
        let cw2 = c.mul(chi_of(x), c.sq(w_of(x)));
        c.mul(cw2.clone(), cw2)
    });

    // The named sums.
    let s_e_chiw = c.sum(n, e_chiw_fn.clone()); // Σ e·(chi·w)
    let s_ee = c.sum(n, ee_fn.clone()); // Σ e·e
    let q = c.sum(n, q_fn.clone()); // Σ (chi·w)²
    let s_chi_chiw2 = c.sum(n, chi_chiw2_fn.clone()); // Σ chi·(chi·w²)
    let s_chichi = c.sum(n, chichi_fn.clone()); // Σ chi·chi
    let r = c.sum(n, r_fn.clone()); // Σ (chi·w²)²
    let sum_chi = c.sum(n, chi.clone()); // Σ chi

    // ════════════════════════════════════════════════════════════════════
    //  CS1 : (Σ e·chiw)·(Σ e·chiw) ≤ (Σ e·e)·Q.  Rewrite LHS → P, (Σ e·e) → m.
    // ════════════════════════════════════════════════════════════════════
    let cs1 = c.cauchy(n, e.clone(), chiw_fn.clone());

    // eq_lhs1 : s_e_chiw = P    via Fin.sum_congr (pointwise e·(chi·w) = e·w).
    let pw_lhs1 = forall_x(c, b, n, false, |d, x| {
        // e·(chi·w) = (e·chi)·w   [symm mul_assoc e chi w]
        let lhs = c.mul(e_of(x), c.mul(chi_of(x), w_of(x)));
        let mid = c.mul(c.mul(e_of(x), chi_of(x)), w_of(x));
        let rhs = c.mul(e_of(x), w_of(x));
        // mul_assoc e chi w : (e·chi)·w = e·(chi·w); symm gives e·(chi·w) = (e·chi)·w
        let assoc = c.mul_assoc(e_of(x), chi_of(x), w_of(x));
        let step1 = c.symm(mid.clone(), lhs.clone(), assoc);
        // (e·chi)·w = e·w   via congrArg (·w) of (e·chi = e) [H2 x]
        let h2x = Expr::app(h2.clone(), x.clone()); // e·chi = e
        let mul_w = {
            // fun t => t · w x   (child_of d so t's id is disjoint from x's)
            let mut dd = EnvDeclBuilder::child_of(d);
            let (t_id, t) = dd.fresh_local(c.rat());
            let body = c.mul(t, w_of(x));
            dd.finish_child(dd.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        let step2 = c.congr_arg(c.mul(e_of(x), chi_of(x)), e_of(x), mul_w, h2x);
        // chain: e·(chi·w) = (e·chi)·w = e·w
        c.trans(lhs, mid, rhs, step1, step2)
    });
    let eq_lhs1 = c.sum_congr(n, e_chiw_fn.clone(), ew_fn.clone(), pw_lhs1); // s_e_chiw = P

    // eq_see : s_ee = m.   s_ee = Σ chi (congr e·e=chi) ; Σ chi = m (symm H6).
    let pw_ee = forall_x(c, b, n, false, |_d, x| {
        // e·e = chi   := symm (H1 x : chi = e·e)
        let h1x = Expr::app(h1.clone(), x.clone()); // chi = e·e
        c.symm(chi_of(x), c.mul(e_of(x), e_of(x)), h1x)
    });
    let ee_eq_sumchi = c.sum_congr(n, ee_fn.clone(), chi.clone(), pw_ee); // s_ee = Σ chi
    let sumchi_eq_m = c.symm(m.clone(), sum_chi.clone(), h6.clone()); // Σ chi = m
    let eq_see = c.trans(
        s_ee.clone(),
        sum_chi.clone(),
        m.clone(),
        ee_eq_sumchi,
        sumchi_eq_m,
    );

    // h_cs1 : P·P ≤ m·Q   (two substs into cs1).
    //   step A: subst s_e_chiw → P in motive `fun t => (t·t) ≤ (s_ee·Q)`.
    let h_cs1a = {
        let motive = {
            let mut d = EnvDeclBuilder::child_of(b);
            let (t_id, t) = d.fresh_local(c.rat());
            let body = c.le(c.mul(t.clone(), t), c.mul(s_ee.clone(), q.clone()));
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        c.subst(motive, s_e_chiw.clone(), p.clone(), eq_lhs1, cs1)
    }; // : P·P ≤ s_ee·Q
       //   step B: subst s_ee → m in motive `fun t => (P·P) ≤ (t·Q)`.
    let h_cs1 = {
        let motive = {
            let mut d = EnvDeclBuilder::child_of(b);
            let (t_id, t) = d.fresh_local(c.rat());
            let body = c.le(c.mul(p.clone(), p.clone()), c.mul(t, q.clone()));
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        c.subst(motive, s_ee.clone(), m.clone(), eq_see, h_cs1a)
    }; // : P·P ≤ m·Q

    // ════════════════════════════════════════════════════════════════════
    //  CS2 : (Σ chi·chiw2)·(…) ≤ (Σ chi·chi)·R.  Rewrite LHS → Q, (Σ chi·chi) → m.
    // ════════════════════════════════════════════════════════════════════
    let cs2 = c.cauchy(n, chi.clone(), chiw2_fn.clone());

    // eq_lhs2 : s_chi_chiw2 = Q.   pointwise chi·(chi·w²) = (chi·w)·(chi·w).
    let pw_lhs2 = forall_x(c, b, n, false, |_d, x| {
        // chi·(chi·w²) = (chi·chi)·(w·w)   [symm mul_assoc chi chi (w·w)]
        let lhs = c.mul(chi_of(x), c.mul(chi_of(x), c.sq(w_of(x))));
        let mid = c.mul(c.mul(chi_of(x), chi_of(x)), c.sq(w_of(x)));
        let assoc = c.mul_assoc(chi_of(x), chi_of(x), c.sq(w_of(x)));
        let step1 = c.symm(mid.clone(), lhs.clone(), assoc); // lhs = mid
                                                             // (chi·chi)·(w·w) = (chi·w)·(chi·w)   [symm mul_mul_mul_comm chi w chi w]
                                                             // mul_mul_mul_comm chi w chi w : (chi·w)·(chi·w) = (chi·chi)·(w·w)
        let cw = c.mul(chi_of(x), w_of(x));
        let rhs = c.mul(cw.clone(), cw.clone());
        let mmmc = c.mul_mul_mul_comm(chi_of(x), w_of(x), chi_of(x), w_of(x)); // (chi·w)·(chi·w) = (chi·chi)·(w·w)
        let step2 = c.symm(rhs.clone(), mid.clone(), mmmc); // mid = rhs
        c.trans(lhs, mid, rhs, step1, step2)
    });
    let eq_lhs2 = c.sum_congr(n, chi_chiw2_fn.clone(), q_fn.clone(), pw_lhs2); // s_chi_chiw2 = Q

    // eq_schichi : s_chichi = m.   s_chichi = Σ chi (congr chi·chi=chi via H3) ; Σ chi = m.
    let pw_chichi = forall_x(c, b, n, false, |_d, x| Expr::app(h3.clone(), x.clone())); // chi·chi = chi
    let schichi_eq_sumchi = c.sum_congr(n, chichi_fn.clone(), chi.clone(), pw_chichi); // s_chichi = Σ chi
    let sumchi_eq_m2 = c.symm(m.clone(), sum_chi.clone(), h6.clone()); // Σ chi = m
    let eq_schichi = c.trans(
        s_chichi.clone(),
        sum_chi.clone(),
        m.clone(),
        schichi_eq_sumchi,
        sumchi_eq_m2,
    );

    // h_cs2 : Q·Q ≤ m·R   (two substs into cs2).
    let h_cs2a = {
        let motive = {
            let mut d = EnvDeclBuilder::child_of(b);
            let (t_id, t) = d.fresh_local(c.rat());
            let body = c.le(c.mul(t.clone(), t), c.mul(s_chichi.clone(), r.clone()));
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        c.subst(motive, s_chi_chiw2.clone(), q.clone(), eq_lhs2, cs2)
    }; // : Q·Q ≤ s_chichi·R
    let h_cs2 = {
        let motive = {
            let mut d = EnvDeclBuilder::child_of(b);
            let (t_id, t) = d.fresh_local(c.rat());
            let body = c.le(c.mul(q.clone(), q.clone()), c.mul(t, r.clone()));
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        c.subst(motive, s_chichi.clone(), m.clone(), eq_schichi, h_cs2a)
    }; // : Q·Q ≤ m·R

    build_holder_chain(
        c, b, n, w, chi, m, p, sum_w4, m_sq, m_cube, w4_fn, &r_fn, &q_fn, q, r, h3, h4, h5, h_cs1,
        h_cs2,
    )
}

/// Final monotone chain: from `h_cs1 : P·P ≤ m·Q`, `h_cs2 : Q·Q ≤ m·R`, and
/// `R ≤ Σw⁴`, conclude `pow4(P) ≤ (m·(m·m))·Σw⁴`.
fn build_holder_chain(
    c: &HolderConsts,
    b: &EnvDeclBuilder,
    n: &Expr,
    w: &Expr,
    chi: &Expr,
    m: &Expr,
    p: &Expr,
    sum_w4: &Expr,
    m_sq: &Expr,   // m·m
    m_cube: &Expr, // m·(m·m)
    w4_fn: &Expr,
    r_fn: &Expr,
    q_fn: &Expr,
    q: Expr,     // Σ (chi·w)²
    r: Expr,     // Σ (chi·w²)²
    h3: &Expr,   // ∀ x, chi x·chi x = chi x
    h4: &Expr,   // ∀ x, chi x ≤ 1
    h5: &Expr,   // 0 ≤ m
    h_cs1: Expr, // P·P ≤ m·Q
    h_cs2: Expr, // Q·Q ≤ m·R
) -> Expr {
    let w_of = |x: &Expr| Expr::app(w.clone(), x.clone());
    let chi_of = |x: &Expr| Expr::app(chi.clone(), x.clone());

    let pp = c.mul(p.clone(), p.clone()); // P·P
    let mq = c.mul(m.clone(), q.clone()); // m·Q
    let qq = c.mul(q.clone(), q.clone()); // Q·Q
    let mr = c.mul(m.clone(), r.clone()); // m·R
    let pow4_p = c.pow4(p.clone()); // (P·P)·(P·P)

    // (a) 0 ≤ P·P.
    let nn_pp = c.sq_nonneg(p.clone());
    // (b) 0 ≤ Q  (sum of squares).
    let nn_q = {
        let per = forall_x(c, b, n, false, |_d, x| {
            c.sq_nonneg(c.mul(chi_of(x), w_of(x)))
        });
        c.sum_nonneg(n, q_fn.clone(), per)
    };
    // (c) 0 ≤ m·Q.
    let nn_mq = c.mul_nonneg(m.clone(), q.clone(), h5.clone(), nn_q);
    // (d) 0 ≤ m·m.
    let nn_mm = c.mul_nonneg(m.clone(), m.clone(), h5.clone(), h5.clone());

    // step4 : (P·P)·(P·P) ≤ (m·Q)·(P·P)   [mul_le_right PP PP mQ h_cs1 (0≤PP)]
    let step4 = c.mul_le_right(
        pp.clone(),
        pp.clone(),
        mq.clone(),
        h_cs1.clone(),
        nn_pp.clone(),
    );
    // step5 : (m·Q)·(P·P) ≤ (m·Q)·(m·Q)   [mul_le_left mQ PP mQ h_cs1 (0≤mQ)]
    let step5 = c.mul_le_left(mq.clone(), pp.clone(), mq.clone(), h_cs1.clone(), nn_mq);
    // h6a : pow4(P) ≤ (m·Q)·(m·Q)
    let mq_mq = c.mul(mq.clone(), mq.clone());
    let h6a = c.le_trans(
        pow4_p.clone(),
        c.mul(mq.clone(), pp.clone()),
        mq_mq.clone(),
        step4,
        step5,
    );

    // eqQ : (m·Q)·(m·Q) = (m·m)·(Q·Q)   [mul_mul_mul_comm m Q m Q]
    let mm_qq = c.mul(m_sq.clone(), qq.clone());
    let eq_q = c.mul_mul_mul_comm(m.clone(), q.clone(), m.clone(), q.clone());
    // h6b : pow4(P) ≤ (m·m)·(Q·Q)   [subst h6a along eqQ]
    let h6b = {
        let motive = {
            let mut d = EnvDeclBuilder::child_of(b);
            let (t_id, t) = d.fresh_local(c.rat());
            let body = c.le(pow4_p.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        c.subst(motive, mq_mq.clone(), mm_qq.clone(), eq_q, h6a)
    };

    // step10 : (m·m)·(Q·Q) ≤ (m·m)·(m·R)   [mul_le_left mm QQ mR h_cs2 (0≤mm)]
    let mm_mr = c.mul(m_sq.clone(), mr.clone());
    let step10 = c.mul_le_left(m_sq.clone(), qq.clone(), mr.clone(), h_cs2, nn_mm.clone());
    // h6c : pow4(P) ≤ (m·m)·(m·R)
    let h6c = c.le_trans(pow4_p.clone(), mm_qq.clone(), mm_mr.clone(), h6b, step10);

    // ── R ≤ Σw⁴   (per-x: (chi·w²)² ≤ pow4(w)).
    let r_le_sumw4 = {
        let per = forall_x(c, b, n, false, |d, x| {
            let w2 = c.sq(w_of(x)); // w·w
            let pow4_w = c.pow4(w_of(x)); // (w·w)·(w·w) — note w²·w² IS pow4(w)
            let cw2 = c.mul(chi_of(x), w2.clone()); // chi·w²
            let cw2_sq = c.mul(cw2.clone(), cw2.clone()); // (chi·w²)²
            let chichi = c.mul(chi_of(x), chi_of(x)); // chi·chi
            let w2w2 = c.mul(w2.clone(), w2.clone()); // w²·w²  (≡ pow4(w))
            let chichi_w2w2 = c.mul(chichi.clone(), w2w2.clone());
            let chi_pow4 = c.mul(chi_of(x), pow4_w.clone()); // chi·pow4(w) (≡ chi·(w²·w²))

            // eqA : (chi·w²)² = (chi·chi)·(w²·w²)   [mul_mul_mul_comm chi w² chi w²]
            let eq_a = c.mul_mul_mul_comm(chi_of(x), w2.clone(), chi_of(x), w2.clone());
            // eqB : (chi·chi)·(w²·w²) = chi·(w²·w²)   [congrArg (·(w²·w²)) of H3 x]
            let h3x = Expr::app(h3.clone(), x.clone()); // chi·chi = chi
            let mul_w2w2 = {
                let mut dd = EnvDeclBuilder::child_of(d);
                let (t_id, t) = dd.fresh_local(c.rat());
                let body = c.mul(t, w2w2.clone());
                dd.finish_child(dd.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };
            let eq_b = c.congr_arg(chichi.clone(), chi_of(x), mul_w2w2, h3x);
            // eqAB : (chi·w²)² = chi·(w²·w²)  ( = chi·pow4(w) )
            let eq_ab = c.trans(
                cw2_sq.clone(),
                chichi_w2w2.clone(),
                chi_pow4.clone(),
                eq_a,
                eq_b,
            );

            // 0 ≤ pow4(w) := sq_nonneg (w·w).
            let nn_pow4w = c.sq_nonneg(w2.clone());
            // le1 : chi·pow4(w) ≤ 1·pow4(w)  [mul_le_right pow4(w) chi 1 (H4 x) (0≤pow4w)]
            let h4x = Expr::app(h4.clone(), x.clone()); // chi ≤ 1
            let one_pow4 = c.mul(c.one(), pow4_w.clone());
            let le1 = c.mul_le_right(pow4_w.clone(), chi_of(x), c.one(), h4x, nn_pow4w);
            // eq1 : 1·pow4(w) = pow4(w)   [mul_comm 1 pow4 ; mul_one pow4]
            let pow4_one = c.mul(pow4_w.clone(), c.one());
            let comm1 = c.mul_comm(c.one(), pow4_w.clone()); // 1·pow4 = pow4·1
            let mul_one = c.mul_one(pow4_w.clone()); // pow4·1 = pow4
            let eq1 = c.trans(one_pow4.clone(), pow4_one, pow4_w.clone(), comm1, mul_one);
            // le2 : chi·pow4(w) ≤ pow4(w)  [subst le1 along eq1]
            let le2 = {
                let motive = {
                    let mut dd = EnvDeclBuilder::child_of(d);
                    let (t_id, t) = dd.fresh_local(c.rat());
                    let body = c.le(chi_pow4.clone(), t);
                    dd.finish_child(dd.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
                };
                c.subst(motive, one_pow4, pow4_w.clone(), eq1, le1)
            };
            // goal : (chi·w²)² ≤ pow4(w)  [subst le2 along symm eqAB]
            let symm_ab = c.symm(cw2_sq.clone(), chi_pow4.clone(), eq_ab); // chi·pow4 = (chi·w²)²
            let motive = {
                let mut dd = EnvDeclBuilder::child_of(d);
                let (t_id, t) = dd.fresh_local(c.rat());
                let body = c.le(t, pow4_w.clone());
                dd.finish_child(dd.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };
            c.subst(motive, chi_pow4.clone(), cw2_sq.clone(), symm_ab, le2)
        });
        c.sum_le(n, r_fn.clone(), w4_fn.clone(), per)
    }; // : R ≤ Σw⁴

    // 0 ≤ m·R := mul_nonneg m R (0≤m) (0≤R) ; 0≤R via Fin.sum_nonneg of r_fn (sq_nonneg).
    // m·R ≤ m·Σw⁴  [mul_le_left m R Σw⁴ (R≤Σw⁴) (0≤m)]
    let m_sumw4 = c.mul(m.clone(), sum_w4.clone());
    let m_r_le = c.mul_le_left(m.clone(), r.clone(), sum_w4.clone(), r_le_sumw4, h5.clone());
    // step13 : (m·m)·(m·R) ≤ (m·m)·(m·Σw⁴)  [mul_le_left mm (m·R) (m·Σw⁴) m_r_le (0≤mm)]
    let mm_m_sumw4 = c.mul(m_sq.clone(), m_sumw4.clone());
    let step13 = c.mul_le_left(m_sq.clone(), mr.clone(), m_sumw4.clone(), m_r_le, nn_mm);
    // h6d : pow4(P) ≤ (m·m)·(m·Σw⁴)
    let h6d = c.le_trans(
        pow4_p.clone(),
        mm_mr.clone(),
        mm_m_sumw4.clone(),
        h6c,
        step13,
    );

    // eqF : (m·m)·(m·Σw⁴) = (m·(m·m))·Σw⁴
    //   (m·m)·(m·Σw⁴) = ((m·m)·m)·Σw⁴   [symm mul_assoc (m·m) m Σw⁴]
    //   ((m·m)·m)·Σw⁴ = (m·(m·m))·Σw⁴   [congrArg (·Σw⁴) of (mul_comm (m·m) m)]
    let mm_m = c.mul(m_sq.clone(), m.clone()); // (m·m)·m
    let mm_m_sumw4_assoc = c.mul(mm_m.clone(), sum_w4.clone()); // ((m·m)·m)·Σw⁴
    let assoc_f = c.mul_assoc(m_sq.clone(), m.clone(), sum_w4.clone()); // ((m·m)·m)·Σw⁴ = (m·m)·(m·Σw⁴)
                                                                        // symm(a, b, h:a=b) : b=a ⇒ symm(mm_m_sumw4_assoc, mm_m_sumw4, assoc_f) : mm_m_sumw4 = mm_m_sumw4_assoc
    let eq_f1 = c.symm(mm_m_sumw4_assoc.clone(), mm_m_sumw4.clone(), assoc_f); // (m·m)·(m·Σw⁴) = ((m·m)·m)·Σw⁴
    let comm_mm_m = c.mul_comm(m_sq.clone(), m.clone()); // (m·m)·m = m·(m·m)
    let mul_sumw4 = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (t_id, t) = d.fresh_local(c.rat());
        let body = c.mul(t, sum_w4.clone());
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
    };
    let eq_f2 = c.congr_arg(mm_m.clone(), m_cube.clone(), mul_sumw4, comm_mm_m); // ((m·m)·m)·Σw⁴ = (m·(m·m))·Σw⁴
    let eq_f = c.trans(
        mm_m_sumw4.clone(),
        c.mul(mm_m.clone(), sum_w4.clone()),
        c.mul(m_cube.clone(), sum_w4.clone()),
        eq_f1,
        eq_f2,
    );

    // final : pow4(P) ≤ (m·(m·m))·Σw⁴  [subst h6d along eqF]
    let motive = {
        let mut d = EnvDeclBuilder::child_of(b);
        let (t_id, t) = d.fresh_local(c.rat());
        let body = c.le(pow4_p.clone(), t);
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
    };
    c.subst(
        motive,
        mm_m_sumw4,
        c.mul(m_cube.clone(), sum_w4.clone()),
        eq_f,
        h6d,
    )
}
