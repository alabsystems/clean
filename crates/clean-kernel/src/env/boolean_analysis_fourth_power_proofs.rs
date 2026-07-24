// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner B5 fourth-power even-pair — proof-term builders.
//!
//! The equational layer feeding the (2,4)-hypercontractivity B5 step. Built on
//! the run-2/3 square identities (`Rat.add_sq`, `Rat.sub_sq`) plus the
//! constructive `Rat` additive surface (`Rat.add_assoc`, `Rat.add_comm`,
//! `Rat.add_neg_self`, `Rat.add_zero`, `Rat.mul_neg`). Every term is built from
//! genuinely-`Constructive` `Rat` lemmas, so each identity registered here is
//! itself `Constructive` (empty domain-axiom closure).
//!
//! ## The parallelogram law (this commit)
//!
//! `Rat.add_sq_add_sub_sq m c :
//!     (m+c)·(m+c) + (m−c)·(m−c) = (1+1)·(m·m) + (1+1)·(c·c)`
//!
//! Rewrite each square via `Rat.add_sq m c` / `Rat.sub_sq m c`:
//!   `(m+c)² = (m·m + 2·(m·c)) + c·c`
//!   `(m−c)² = (m·m + 2·(m·(−c))) + c·c`
//! Fold `2·(m·(−c)) = −(2·(m·c))` (via `Rat.mul_neg` lifted through `two_mul`),
//! then the additive-cancellation helper `even_collapse` collapses
//!   `((p + t) + r) + ((p + (−t)) + r) = 2·p + 2·r`
//! at `p := m·m`, `t := 2·(m·c)`, `r := c·c`.
//!
//! Split from the registrar (`boolean_analysis_fourth_power.rs`) to keep each
//! file under the 500-line limit.

use super::boolean_analysis_ring_identities_proofs::RingConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

// ---------------------------------------------------------------------------
// Shared additive helpers over the constructive Rat surface
// ---------------------------------------------------------------------------

/// `Rat.add_neg_self a : a + (−a) = 0`.
fn add_neg_self(a: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Rat.add_neg_self"), vec![]),
        a,
    )
}

/// `Rat.mul_neg a b : a·(−b) = −(a·b)`.
fn mul_neg(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_neg"), vec![]),
        [a, b],
    )
}

/// `even_collapse c b p t r`:
///   proof of `((p + t) + r) + ((p + (−t)) + r) = (1+1)·p + (1+1)·r`.
///
/// Pure additive identity (`p`, `t`, `r` free). Strategy: regroup so the `t`
/// and `−t` meet and cancel via `Rat.add_neg_self`, leaving `(p+r)+(p+r)`,
/// then fold `(p+r)+(p+r) → ...` is NOT what we want; instead we collapse to
/// `2·p + 2·r` by routing through `(p + p) + (r + r)` and the `two_mul`
/// expansions `2·p = p + p`, `2·r = r + r`.
///
/// We build it as an explicit `Eq.trans` chain. `b` is the parent builder whose
/// fvar scope `p`/`t`/`r` live in (needed for the `congrArg` motives).
pub(super) fn even_collapse(
    c: &RingConsts,
    b: &EnvDeclBuilder,
    p: &Expr,
    t: &Expr,
    r: &Expr,
) -> Expr {
    let add_c = c.add_const();
    let neg_t = c.neg(t.clone());

    // LHS = ((p+t)+r) + ((p+(−t))+r)
    let pt = c.add(p.clone(), t.clone()); // p+t
    let pnt = c.add(p.clone(), neg_t.clone()); // p+(−t)
    let l1 = c.add(pt.clone(), r.clone()); // (p+t)+r
    let l2 = c.add(pnt.clone(), r.clone()); // (p+(−t))+r
    let lhs = c.add(l1.clone(), l2.clone());

    // Target = 2·p + 2·r
    let two = c.two();
    let two_p = c.mul(two.clone(), p.clone());
    let two_r = c.mul(two.clone(), r.clone());
    let target = c.add(two_p.clone(), two_r.clone());

    // ── Step A: ((p+t)+r) = (p+r)+t   [commute t past r inside]
    // (p+t)+r = p+(t+r)            [add_assoc p t r]
    // t+r = r+t                    [add_comm t r] → p+(t+r) = p+(r+t)
    // p+(r+t) = (p+r)+t            [symm add_assoc p r t]
    let t_plus_r = c.add(t.clone(), r.clone());
    let r_plus_t = c.add(r.clone(), t.clone());
    let p_tr = c.add(p.clone(), t_plus_r.clone());
    let p_rt = c.add(p.clone(), r_plus_t.clone());
    let pr = c.add(p.clone(), r.clone());
    let pr_t = c.add(pr.clone(), t.clone());
    let a_a1 = c.aassoc(p.clone(), t.clone(), r.clone()); // (p+t)+r = p+(t+r)
    let h_tr = c.acomm(t.clone(), r.clone()); // t+r = r+t
    let a_a2 = c.cong_right(
        b,
        &add_c,
        t_plus_r.clone(),
        r_plus_t.clone(),
        p.clone(),
        h_tr,
    ); // p+(t+r)=p+(r+t)
    let a_a3_raw = c.aassoc(p.clone(), r.clone(), t.clone()); // (p+r)+t = p+(r+t)
    let a_a3 = c.symm(pr_t.clone(), p_rt.clone(), a_a3_raw); // p+(r+t)=(p+r)+t
    let s_a = c.trans(l1.clone(), p_tr.clone(), p_rt.clone(), a_a1, a_a2);
    let step_a = c.trans(l1.clone(), p_rt.clone(), pr_t.clone(), s_a, a_a3); // l1 = (p+r)+t

    // ── Step B: ((p+(−t))+r) = (p+r)+(−t)   [same shape with −t]
    let nt_plus_r = c.add(neg_t.clone(), r.clone());
    let r_plus_nt = c.add(r.clone(), neg_t.clone());
    let p_ntr = c.add(p.clone(), nt_plus_r.clone());
    let p_rnt = c.add(p.clone(), r_plus_nt.clone());
    let pr_nt = c.add(pr.clone(), neg_t.clone());
    let b_b1 = c.aassoc(p.clone(), neg_t.clone(), r.clone()); // (p+(−t))+r = p+((−t)+r)
    let h_ntr = c.acomm(neg_t.clone(), r.clone()); // (−t)+r = r+(−t)
    let b_b2 = c.cong_right(
        b,
        &add_c,
        nt_plus_r.clone(),
        r_plus_nt.clone(),
        p.clone(),
        h_ntr,
    );
    let b_b3_raw = c.aassoc(p.clone(), r.clone(), neg_t.clone()); // (p+r)+(−t) = p+(r+(−t))
    let b_b3 = c.symm(pr_nt.clone(), p_rnt.clone(), b_b3_raw);
    let s_b = c.trans(l2.clone(), p_ntr.clone(), p_rnt.clone(), b_b1, b_b2);
    let step_b = c.trans(l2.clone(), p_rnt.clone(), pr_nt.clone(), s_b, b_b3); // l2 = (p+r)+(−t)

    // ── lhs = ((p+r)+t) + ((p+r)+(−t))   [congr both summands]
    let lhs2 = c.add(pr_t.clone(), l2.clone());
    let c_l = c.cong_left(b, &add_c, l1.clone(), pr_t.clone(), l2.clone(), step_a);
    let lhs3 = c.add(pr_t.clone(), pr_nt.clone());
    let c_r = c.cong_right(b, &add_c, l2.clone(), pr_nt.clone(), pr_t.clone(), step_b);
    let s1 = c.trans(lhs.clone(), lhs2.clone(), lhs3.clone(), c_l, c_r);

    // ── ((p+r)+t) + ((p+r)+(−t)) = (p+r) + (t + (−t))   via the "X+t plus X+(−t)" regroup
    // Let X = p+r. (X+t)+(X+(−t)) = X + (t + (X+(−t)))      [add_assoc X t (X+(−t))]
    //   t + (X+(−t)) = t + (X+(−t)) ... we need to commute X out.
    // Cleaner: (X+t)+(X+(−t)) = ((X+t)+X) + (−t)            [symm add_assoc (X+t) X (−t)]
    //   (X+t)+X = X+(t+X) = X+(X+t) = (X+X)+t               [assoc/comm]
    // This is getting long; route through add_comm to pair t with −t directly:
    // (X+t)+(X+(−t)) = (X+(−t))+(X+t)        [add_comm]   -- not simpler.
    //
    // Use: (X+t)+(X+(−t)) = X + (t + (X + (−t)))   [aassoc X t (X+(−t))]
    let x = pr.clone();
    let x_nt = pr_nt.clone(); // X+(−t)
    let t_x_nt = c.add(t.clone(), x_nt.clone()); // t + (X+(−t))
    let x_t_x_nt = c.add(x.clone(), t_x_nt.clone()); // X + (t+(X+(−t)))
    let a1 = c.aassoc(x.clone(), t.clone(), x_nt.clone()); // (X+t)+(X+(−t)) = X+(t+(X+(−t)))

    //   t + (X+(−t)) = t + (X+(−t))   rewrite inner X+(−t) → (−t)+X (add_comm) ... then t+((−t)+X)
    let nt_x = c.add(neg_t.clone(), x.clone()); // (−t)+X
    let h_xnt = c.acomm(x.clone(), neg_t.clone()); // X+(−t) = (−t)+X
    let t_nt_x = c.add(t.clone(), nt_x.clone()); // t + ((−t)+X)
    let cinner = c.cong_right(b, &add_c, x_nt.clone(), nt_x.clone(), t.clone(), h_xnt); // t+(X+(−t)) = t+((−t)+X)
                                                                                        // lift over fixed X: X+(t+(X+(−t))) = X+(t+((−t)+X))
    let x_t_nt_x = c.add(x.clone(), t_nt_x.clone());
    let clift = c.cong_right(b, &add_c, t_x_nt.clone(), t_nt_x.clone(), x.clone(), cinner);

    //   t + ((−t)+X) = (t+(−t)) + X     [symm aassoc t (−t) X]
    let t_nt = c.add(t.clone(), neg_t.clone()); // t+(−t)
    let t_nt_xs = c.add(t_nt.clone(), x.clone()); // (t+(−t))+X
    let araw = c.aassoc(t.clone(), neg_t.clone(), x.clone()); // (t+(−t))+X = t+((−t)+X)
    let asym = c.symm(t_nt_xs.clone(), t_nt_x.clone(), araw);
    let x_tnt_xs = c.add(x.clone(), t_nt_xs.clone());
    let clift2 = c.cong_right(b, &add_c, t_nt_x.clone(), t_nt_xs.clone(), x.clone(), asym);

    //   (t+(−t)) = 0    [add_neg_self t]  → ((t+(−t))+X) = (0+X)
    let zero = c.o.rat_zero.clone();
    let h_tnt0 = add_neg_self(t.clone()); // t+(−t)=0
    let zero_xs = c.add(zero.clone(), x.clone()); // 0+X
    let ccancel = c.cong_left(b, &add_c, t_nt.clone(), zero.clone(), x.clone(), h_tnt0); // (t+(−t))+X = 0+X
    let x_zero_xs = c.add(x.clone(), zero_xs.clone());
    let clift3 = c.cong_right(
        b,
        &add_c,
        t_nt_xs.clone(),
        zero_xs.clone(),
        x.clone(),
        ccancel,
    );

    //   0+X = X    [zero_add X]
    let h_z_xs = Expr::app(
        Expr::const_(Name::from_string("Rat.zero_add"), vec![]),
        x.clone(),
    ); // 0+X=X
    let x_xs = c.add(x.clone(), x.clone()); // X+X
    let clift4 = c.cong_right(b, &add_c, zero_xs.clone(), x.clone(), x.clone(), h_z_xs); // X+(0+X)=X+X

    // chain s2: lhs3 → x_t_x_nt → x_t_nt_x → x_tnt_xs → x_zero_xs → x_xs
    let s2 = c.trans(lhs3.clone(), x_t_x_nt.clone(), x_t_nt_x.clone(), a1, clift);
    let s2 = c.trans(lhs3.clone(), x_t_nt_x.clone(), x_tnt_xs.clone(), s2, clift2);
    let s2 = c.trans(
        lhs3.clone(),
        x_tnt_xs.clone(),
        x_zero_xs.clone(),
        s2,
        clift3,
    );
    let s2 = c.trans(lhs3.clone(), x_zero_xs.clone(), x_xs.clone(), s2, clift4);
    // now lhs3 = X+X = (p+r)+(p+r)

    // ── (p+r)+(p+r) = 2·p + 2·r
    // First (p+r)+(p+r) = ((p+r)+p)+r       [symm aassoc (p+r) p r]
    let pr_p = c.add(pr.clone(), p.clone()); // (p+r)+p
    let pr_p_r = c.add(pr_p.clone(), r.clone()); // ((p+r)+p)+r
    let araw2 = c.aassoc(pr.clone(), p.clone(), r.clone()); // ((p+r)+p)+r = (p+r)+(p+r)
    let asym2 = c.symm(pr_p_r.clone(), x_xs.clone(), araw2);
    // (p+r)+p = p+(r+p) = p+(p+r) = (p+p)+r ... we want to reach (p+p)+(r+r).
    // Simpler target route: (p+r)+(p+r) = (p+p)+(r+r) via add_comm/assoc, then
    // fold each doubled term to 2··.
    // (p+r)+p = (p+r)+p ; rewrite to p+(p+r)? Use add_comm: (p+r)+p = p+(p+r).
    let p_pr = c.add(p.clone(), pr.clone()); // p+(p+r)
    let h_comm_prp = c.acomm(pr.clone(), p.clone()); // (p+r)+p = p+(p+r)
                                                     // ((p+r)+p)+r = (p+(p+r))+r   [cong_left]
    let p_pr_r = c.add(p_pr.clone(), r.clone());
    let cc1 = c.cong_left(b, &add_c, pr_p.clone(), p_pr.clone(), r.clone(), h_comm_prp);
    // p+(p+r) = (p+p)+r    [symm aassoc p p r]
    let pp = c.add(p.clone(), p.clone());
    let pp_r = c.add(pp.clone(), r.clone());
    let araw3 = c.aassoc(p.clone(), p.clone(), r.clone()); // (p+p)+r = p+(p+r)
    let asym3 = c.symm(pp_r.clone(), p_pr.clone(), araw3);
    // (p+(p+r))+r = ((p+p)+r)+r   [cong_left]
    let pp_r_r = c.add(pp_r.clone(), r.clone());
    let cc2 = c.cong_left(b, &add_c, p_pr.clone(), pp_r.clone(), r.clone(), asym3);
    // ((p+p)+r)+r = (p+p)+(r+r)   [aassoc (p+p) r r]
    let rr = c.add(r.clone(), r.clone());
    let pp_rr = c.add(pp.clone(), rr.clone());
    let aassoc_final = c.aassoc(pp.clone(), r.clone(), r.clone()); // ((p+p)+r)+r = (p+p)+(r+r)
                                                                   // fold p+p → 2·p  and  r+r → 2·r
    let h_two_p = c.two_mul(b, p.clone()); // 2·p = p+p
    let h_two_p_sym = c.symm(two_p.clone(), pp.clone(), h_two_p); // p+p = 2·p
    let two_p_rr = c.add(two_p.clone(), rr.clone());
    let cfp = c.cong_left(
        b,
        &add_c,
        pp.clone(),
        two_p.clone(),
        rr.clone(),
        h_two_p_sym,
    ); // (p+p)+(r+r)=(2·p)+(r+r)
    let h_two_r = c.two_mul(b, r.clone()); // 2·r = r+r
    let h_two_r_sym = c.symm(two_r.clone(), rr.clone(), h_two_r); // r+r = 2·r
    let cfr = c.cong_right(
        b,
        &add_c,
        rr.clone(),
        two_r.clone(),
        two_p.clone(),
        h_two_r_sym,
    ); // (2·p)+(r+r)=(2·p)+(2·r)

    // chain s3: x_xs → pr_p_r → p_pr_r → pp_r_r → pp_rr → two_p_rr → target
    let s3 = c.trans(x_xs.clone(), pr_p_r.clone(), p_pr_r.clone(), asym2, cc1);
    let s3 = c.trans(x_xs.clone(), p_pr_r.clone(), pp_r_r.clone(), s3, cc2);
    let s3 = c.trans(
        x_xs.clone(),
        pp_r_r.clone(),
        pp_rr.clone(),
        s3,
        aassoc_final,
    );
    let s3 = c.trans(x_xs.clone(), pp_rr.clone(), two_p_rr.clone(), s3, cfp);
    let s3 = c.trans(x_xs.clone(), two_p_rr.clone(), target.clone(), s3, cfr);

    // assemble: lhs = lhs3 (s1) = X+X (s2) = target (s3)
    let chain = c.trans(lhs.clone(), lhs3.clone(), x_xs.clone(), s1, s2);
    c.trans(lhs, x_xs, target, chain, s3)
}

// ---------------------------------------------------------------------------
// Rat.add_sq_add_sub_sq : (m+c)² + (m−c)² = 2·(m·m) + 2·(c·c)
// ---------------------------------------------------------------------------

/// Type of `Rat.add_sq_add_sub_sq`:
/// `∀ m c, ((m+c)·(m+c)) + ((m−c)·(m−c)) = (1+1)·(m·m) + (1+1)·(c·c)`.
pub(super) fn add_sq_add_sub_sq_type(c: &RingConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.rat());
    let (cc_id, cv) = b.fresh_local(c.rat());
    let m_plus_c = c.add(m.clone(), cv.clone());
    let m_minus_c = c.sub(m.clone(), cv.clone());
    let sq_add = c.mul(m_plus_c.clone(), m_plus_c);
    let sq_sub = c.mul(m_minus_c.clone(), m_minus_c);
    let lhs = c.add(sq_add, sq_sub);
    let mm = c.mul(m.clone(), m.clone());
    let cc2 = c.mul(cv.clone(), cv.clone());
    let rhs = c.add(c.nmul(c.two(), mm), c.nmul(c.two(), cc2));
    let body = c.eq(lhs, rhs);
    let e = b.mk_pi(cc_id, BinderInfo::Default, c.rat(), body);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}

/// Build the proof term for `Rat.add_sq_add_sub_sq`.
pub(super) fn build_add_sq_add_sub_sq_proof(c: &RingConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(c.rat());
    let (cc_id, cv) = b.fresh_local(c.rat());

    let add_c = c.add_const();
    let m_plus_c = c.add(m.clone(), cv.clone());
    let m_minus_c = c.sub(m.clone(), cv.clone());
    let sq_add = c.mul(m_plus_c.clone(), m_plus_c.clone()); // (m+c)²
    let sq_sub = c.mul(m_minus_c.clone(), m_minus_c.clone()); // (m−c)²
    let lhs = c.add(sq_add.clone(), sq_sub.clone());

    let mm = c.mul(m.clone(), m.clone());
    let cc2 = c.mul(cv.clone(), cv.clone());
    let mc = c.mul(m.clone(), cv.clone()); // m·c
    let neg_c = c.neg(cv.clone());
    let m_negc = c.mul(m.clone(), neg_c.clone()); // m·(−c)
    let two = c.two();
    let two_mc = c.nmul(two.clone(), mc.clone()); // 2·(m·c)
    let two_mnegc = c.nmul(two.clone(), m_negc.clone()); // 2·(m·(−c))
    let neg_two_mc = c.neg(two_mc.clone()); // −(2·(m·c))

    // h_add : (m+c)² = (m·m + 2·(m·c)) + c·c   [Rat.add_sq m c]
    let add_sq = Expr::const_(Name::from_string("Rat.add_sq"), vec![]);
    let h_add = Expr::apps(add_sq, [m.clone(), cv.clone()]);
    let add_rhs = {
        // (m·m + 2·(m·c)) + c·c
        let inner = c.add(mm.clone(), two_mc.clone());
        c.add(inner, cc2.clone())
    };

    // h_sub : (m−c)² = (m·m + 2·(m·(−c))) + c·c   [Rat.sub_sq m c]
    let sub_sq = Expr::const_(Name::from_string("Rat.sub_sq"), vec![]);
    let h_sub = Expr::apps(sub_sq, [m.clone(), cv.clone()]);
    let sub_rhs = {
        let inner = c.add(mm.clone(), two_mnegc.clone());
        c.add(inner, cc2.clone())
    };

    // Rewrite LHS summands: lhs = add_rhs + sub_rhs
    let lhs1 = c.add(add_rhs.clone(), sq_sub.clone());
    let c_l = c.cong_left(
        &b,
        &add_c,
        sq_add.clone(),
        add_rhs.clone(),
        sq_sub.clone(),
        h_add,
    );
    let lhs2 = c.add(add_rhs.clone(), sub_rhs.clone());
    let c_r = c.cong_right(
        &b,
        &add_c,
        sq_sub.clone(),
        sub_rhs.clone(),
        add_rhs.clone(),
        h_sub,
    );

    // Fold 2·(m·(−c)) → −(2·(m·c)) inside sub_rhs.
    //   m·(−c) = −(m·c)               [mul_neg m c]
    //   2·(m·(−c)) = 2·(−(m·c))       [cong_right mul over 2]  ... then
    //   2·(−(m·c)) = −(2·(m·c))       [mul_neg 2 (m·c)]
    let h_mneg = mul_neg(m.clone(), cv.clone()); // m·(−c) = −(m·c)
    let neg_mc = c.neg(mc.clone());
    let two_neg_mc = c.nmul(two.clone(), neg_mc.clone()); // 2·(−(m·c))
    let mul_c = c.mul_const();
    let c_fold1 = c.cong_right(
        &b,
        &mul_c,
        m_negc.clone(),
        neg_mc.clone(),
        two.clone(),
        h_mneg,
    ); // 2·(m·(−c)) = 2·(−(m·c))
    let h_mneg2 = mul_neg(two.clone(), mc.clone()); // 2·(−(m·c)) = −(2·(m·c))
    let h_two_mnegc_eq = c.trans(
        two_mnegc.clone(),
        two_neg_mc.clone(),
        neg_two_mc.clone(),
        c_fold1,
        h_mneg2,
    ); // 2·(m·(−c)) = −(2·(m·c))

    // sub_rhs = (m·m + 2·(m·(−c))) + c·c → (m·m + −(2·(m·c))) + c·c
    let mm_negtwo = c.add(mm.clone(), neg_two_mc.clone());
    let sub_rhs2 = c.add(mm_negtwo.clone(), cc2.clone());
    // lift over the inner add (cong_right on m·m), then over the outer add (cong_left on +c·c)
    let inner_sub = c.add(mm.clone(), two_mnegc.clone());
    let c_inner = c.cong_right(
        &b,
        &add_c,
        two_mnegc.clone(),
        neg_two_mc.clone(),
        mm.clone(),
        h_two_mnegc_eq,
    ); // (m·m + 2·(m·(−c))) = (m·m + −(2·(m·c)))
    let c_outer = c.cong_left(
        &b,
        &add_c,
        inner_sub.clone(),
        mm_negtwo.clone(),
        cc2.clone(),
        c_inner,
    ); // sub_rhs = sub_rhs2

    let lhs3 = c.add(add_rhs.clone(), sub_rhs2.clone());
    let c_sub_fold = c.cong_right(
        &b,
        &add_c,
        sub_rhs.clone(),
        sub_rhs2.clone(),
        add_rhs.clone(),
        c_outer,
    );

    // Now lhs3 = ((m·m + 2·(m·c)) + c·c) + ((m·m + −(2·(m·c))) + c·c)
    //         = even_collapse at p:=m·m, t:=2·(m·c), r:=c·c
    let collapse = even_collapse(c, &b, &mm, &two_mc, &cc2);
    // even_collapse target = 2·(m·m) + 2·(c·c) = the stated RHS.
    let target = c.add(
        c.nmul(two.clone(), mm.clone()),
        c.nmul(two.clone(), cc2.clone()),
    );

    // Chain: lhs → lhs1 → lhs2 → lhs3 → target
    let s = c.trans(lhs.clone(), lhs1.clone(), lhs2.clone(), c_l, c_r);
    let s = c.trans(lhs.clone(), lhs2.clone(), lhs3.clone(), s, c_sub_fold);
    let body = c.trans(lhs.clone(), lhs3.clone(), target.clone(), s, collapse);

    let e = b.mk_lam(cc_id, BinderInfo::Default, c.rat(), body);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.rat(), e);
    b.finish(e)
}
