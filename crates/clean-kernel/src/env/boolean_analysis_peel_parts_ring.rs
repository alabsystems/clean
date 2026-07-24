// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Included by `boolean_analysis_peel_parts.rs` — the closed-Rat ring chains for
// the two `peel_reconstruct` branches. Uses only the constructive Rat surface
// already in the env after `init_boolean_analysis_ring_identities` +
// `register_rat_q_structural` (Rat.one_mul, Rat.mul_one, Rat.mul_comm,
// Rat.mul_neg, Rat.neg_neg, Rat.add_comm, Rat.add_assoc, Rat.add_neg_self,
// Rat.add_left_neg, Rat.zero_add, Rat.add_zero, Rat.two_mul). All proof terms are
// inline (no new globals), so `peel_reconstruct`'s axiom closure stays empty.
//
// Every helper that builds a `fun z => …` lift takes the enclosing builder
// `parent` and nests via `child_of`/`finish_child`, so the lift's bound var never
// collides with the theorem's `n,f,x` FVars.

/// `Rat.mul_comm a b : a·b = b·a`.
fn rc_mul_comm(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_comm"), vec![]),
        [a, b],
    )
}
/// `Rat.mul_one a : a·1 = a`.
fn rc_mul_one(a: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Rat.mul_one"), vec![]), a)
}
/// `Rat.mul_neg a b : a·(−b) = −(a·b)`.
fn rc_mul_neg(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_neg"), vec![]),
        [a, b],
    )
}
/// `Rat.neg_neg a : −(−a) = a`.
fn rc_neg_neg(a: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Rat.neg_neg"), vec![]), a)
}
/// `Rat.one_mul a : 1·a = a`.
fn rc_one_mul(a: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Rat.one_mul"), vec![]), a)
}
/// `Rat.add_comm a b : a+b = b+a`.
fn rc_add_comm(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.add_comm"), vec![]),
        [a, b],
    )
}
/// `Rat.add_assoc a b c : (a+b)+c = a+(b+c)`.
fn rc_add_assoc(a: Expr, b: Expr, cc: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.add_assoc"), vec![]),
        [a, b, cc],
    )
}
/// `Rat.add_neg_self a : a + (−a) = 0`.
fn rc_add_neg_self(a: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Rat.add_neg_self"), vec![]),
        a,
    )
}
/// `Rat.add_left_neg a : (−a) + a = 0`.
fn rc_add_left_neg(a: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Rat.add_left_neg"), vec![]),
        a,
    )
}
/// `Rat.zero_add a : 0 + a = a`.
fn rc_zero_add(a: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Rat.zero_add"), vec![]), a)
}
/// `Rat.add_zero a : a + 0 = a`.
fn rc_add_zero(a: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Rat.add_zero"), vec![]), a)
}

/// `congrArg.{1,1} Rat Rat a b Rat.neg h : −a = −b`  from `h : a = b`.
fn cong_neg(rc: &RingConsts, a: Expr, b: Expr, h: Expr) -> Expr {
    let u1 = Level::succ(Level::zero());
    let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![u1.clone(), u1]);
    let neg_c = Expr::const_(Name::from_string("Rat.neg"), vec![]);
    Expr::apps(congr_arg, [rc.rat(), rc.rat(), a, b, neg_c, h])
}

/// `congrArg.{1,1} Rat Rat a b g h : g a = g b`.
fn cong_g(rc: &RingConsts, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
    let u1 = Level::succ(Level::zero());
    let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![u1.clone(), u1]);
    Expr::apps(congr_arg, [rc.rat(), rc.rat(), a, b, g, h])
}

/// `fun z => c + z` (nests under `parent`).
fn add_left_fixed(parent: &EnvDeclBuilder, rc: &RingConsts, cst: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let (z_id, z) = d.fresh_local(rc.rat());
    let body = rc.add(cst.clone(), z);
    d.finish_child(d.mk_lam(z_id, BinderInfo::Default, rc.rat(), body))
}

/// `fun z => z + c` (nests under `parent`).
fn add_right_fixed(parent: &EnvDeclBuilder, rc: &RingConsts, cst: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let (z_id, z) = d.fresh_local(rc.rat());
    let body = rc.add(z, cst.clone());
    d.finish_child(d.mk_lam(z_id, BinderInfo::Default, rc.rat(), body))
}

/// `fun z => (cst − z)` (nests under `parent`).
fn sub_right_fn(parent: &EnvDeclBuilder, rc: &RingConsts, cst: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let (z_id, z) = d.fresh_local(rc.rat());
    let body = rc.sub(cst.clone(), z);
    d.finish_child(d.mk_lam(z_id, BinderInfo::Default, rc.rat(), body))
}

/// `(−1)·x = −x`:  (−1)·x = x·(−1) [mul_comm] = −(x·1) [mul_neg] = −x [cong (mul_one)].
fn neg_one_mul_inline(rc: &RingConsts, x: &Expr) -> Expr {
    let one = rc.one();
    let neg_one = rc.neg(one.clone());
    let lhs = rc.mul(neg_one.clone(), x.clone());
    let x_neg_one = rc.mul(x.clone(), neg_one.clone());
    let neg_x_one = rc.neg(rc.mul(x.clone(), one.clone()));
    let neg_x = rc.neg(x.clone());
    let s1 = rc_mul_comm(neg_one.clone(), x.clone());
    let s2 = rc_mul_neg(x.clone(), one.clone());
    let s3 = cong_neg(
        rc,
        rc.mul(x.clone(), one.clone()),
        x.clone(),
        rc_mul_one(x.clone()),
    );
    let t12 = rc.trans(lhs.clone(), x_neg_one, neg_x_one.clone(), s1, s2);
    rc.trans(lhs, neg_x_one, neg_x, t12, s3)
}

// ───────────────────────── branch chains ─────────────────────────

/// false branch: `p·2 = (p+m) − 1·(m−p)`.
fn rc_recon_false(
    parent: &EnvDeclBuilder,
    rc: &RingConsts,
    _c: &PeelPartsConsts,
    p: &Expr,
    m: &Expr,
    twice_p: &Expr,
    gpart: &Expr,
    hpart: &Expr,
) -> Expr {
    let one = rc.one();
    let one_h = rc.mul(one.clone(), hpart.clone()); // 1·(m−p)
    let rhs = rc.sub(gpart.clone(), one_h.clone());
    // step A: (p+m) − 1·(m−p) = (p+m) − (m−p)   [congr (gpart − ·) (one_mul (m−p))]
    let h_one_mul = rc_one_mul(hpart.clone());
    let sub_fn = sub_right_fn(parent, rc, gpart);
    let cong_a = cong_g(rc, one_h.clone(), hpart.clone(), sub_fn, h_one_mul);
    let t_a = rc.sub(gpart.clone(), hpart.clone());
    // step B: (p+m) − (m−p) = p·2
    let ring = sub_double_eq(parent, rc, p, m, gpart, hpart, twice_p);
    let rhs_eq_double = rc.trans(rhs.clone(), t_a, twice_p.clone(), cong_a, ring);
    rc.symm(rhs, twice_p.clone(), rhs_eq_double)
}

/// true branch: `m·2 = (p+m) − (−1)·(m−p)`.
fn rc_recon_true(
    parent: &EnvDeclBuilder,
    rc: &RingConsts,
    _c: &PeelPartsConsts,
    p: &Expr,
    m: &Expr,
    twice_m: &Expr,
    gpart: &Expr,
    hpart: &Expr,
) -> Expr {
    let one = rc.one();
    let neg_one = rc.neg(one.clone());
    let negone_h = rc.mul(neg_one.clone(), hpart.clone()); // (−1)·(m−p)
    let rhs = rc.sub(gpart.clone(), negone_h.clone());
    // step A: (p+m) − (−1)·(m−p) = (p+m) − (−(m−p))   [congr (gpart − ·) (neg_one_mul)]
    let h_neg_one_mul = neg_one_mul_inline(rc, hpart);
    let neg_h = rc.neg(hpart.clone());
    let sub_fn = sub_right_fn(parent, rc, gpart);
    let cong_a = cong_g(rc, negone_h.clone(), neg_h.clone(), sub_fn, h_neg_one_mul);
    let t_a = rc.sub(gpart.clone(), neg_h.clone());
    // step B: (p+m) − (−(m−p)) = m·2
    let ring = sub_neg_double_eq(parent, rc, p, m, gpart, hpart, twice_m);
    let rhs_eq_double = rc.trans(rhs.clone(), t_a, twice_m.clone(), cong_a, ring);
    rc.symm(rhs, twice_m.clone(), rhs_eq_double)
}

/// `(p+m) − (m−p) = p·2`.  `Rat.sub` reducible ⇒ `(p+m) − (m−p) ≡ (p+m) + (−(m−p))`.
fn sub_double_eq(
    parent: &EnvDeclBuilder,
    rc: &RingConsts,
    p: &Expr,
    m: &Expr,
    gpart: &Expr,
    hpart: &Expr,
    twice_p: &Expr,
) -> Expr {
    let neg_hpart = rc.neg(hpart.clone());
    let neg_m = rc.neg(m.clone());
    let p_plus_negm = rc.add(p.clone(), neg_m.clone()); // p + (−m)
    let neg_mp_eq = neg_sub_eq(parent, rc, m, p); // −(m−p) = p + (−m)
    let lhs = rc.add(gpart.clone(), neg_hpart.clone());
    let mid = rc.add(gpart.clone(), p_plus_negm.clone());
    let add_fn = add_left_fixed(parent, rc, gpart);
    let cong = cong_g(rc, neg_hpart, p_plus_negm.clone(), add_fn, neg_mp_eq);
    // (p+m) + (p + (−m)) = p·2
    let ring = double_cancel_false(parent, rc, p, m, twice_p);
    rc.trans(lhs, mid, twice_p.clone(), cong, ring)
}

/// `(p+m) − (−(m−p)) = m·2`.  `(p+m) − (−(m−p)) ≡ (p+m) + (−(−(m−p)))` then neg_neg.
fn sub_neg_double_eq(
    parent: &EnvDeclBuilder,
    rc: &RingConsts,
    p: &Expr,
    m: &Expr,
    gpart: &Expr,
    hpart: &Expr,
    twice_m: &Expr,
) -> Expr {
    let neg_h = rc.neg(hpart.clone());
    let neg_neg_h = rc.neg(neg_h.clone());
    let lhs = rc.add(gpart.clone(), neg_neg_h.clone()); // (p+m) + (−(−(m−p)))
    let nn = rc_neg_neg(hpart.clone()); // −(−(m−p)) = (m−p)
    let add_fn = add_left_fixed(parent, rc, gpart);
    let cong = cong_g(rc, neg_neg_h, hpart.clone(), add_fn, nn);
    let mid = rc.add(gpart.clone(), hpart.clone()); // (p+m) + (m−p)
                                                    // (p+m) + (m−p) = m·2
    let ring = double_cancel_true(parent, rc, p, m, twice_m);
    rc.trans(lhs, mid, twice_m.clone(), cong, ring)
}

/// `−(m−p) = p + (−m)`  via additive-inverse uniqueness (`(m−p) + (p−m) = 0`).
fn neg_sub_eq(parent: &EnvDeclBuilder, rc: &RingConsts, m: &Expr, p: &Expr) -> Expr {
    let neg_p = rc.neg(p.clone());
    let neg_m = rc.neg(m.clone());
    let m_sub_p = rc.add(m.clone(), neg_p.clone()); // m + (−p) ≡ m − p
    let p_sub_m = rc.add(p.clone(), neg_m.clone()); // p + (−m) ≡ p − m
    let neg_msubp = rc.neg(m_sub_p.clone());
    let h1 = add_neg_pair_zero(parent, rc, m, p); // (m+(−p)) + (p+(−m)) = 0
    add_inv_unique(parent, rc, &m_sub_p, &p_sub_m, &neg_msubp, h1)
}

/// From `h1 : w + cand = 0`, prove `−w = cand`:
///   cand =[symm left]= ((−w)+w)+cand =[assoc]= (−w)+(w+cand) =[right]= −w, then symm.
fn add_inv_unique(
    parent: &EnvDeclBuilder,
    rc: &RingConsts,
    w: &Expr,
    cand: &Expr,
    neg_w: &Expr,
    h1: Expr,
) -> Expr {
    let _ = neg_w;
    let zero = rc.o.rat_zero.clone();
    let neg_w_e = rc.neg(w.clone());
    let assoc = rc_add_assoc(neg_w_e.clone(), w.clone(), cand.clone()); // ((−w)+w)+c = (−w)+(w+c)
    let neg_w_plus_w = rc.add(neg_w_e.clone(), w.clone());
    let lhs_assoc = rc.add(neg_w_plus_w.clone(), cand.clone());
    let rhs_assoc = rc.add(neg_w_e.clone(), rc.add(w.clone(), cand.clone()));
    // left: ((−w)+w)+c = 0+c = c
    let cong_left = cong_g(
        rc,
        neg_w_plus_w.clone(),
        zero.clone(),
        add_right_fixed(parent, rc, cand),
        rc_add_left_neg(w.clone()),
    );
    let zero_plus_cand = rc.add(zero.clone(), cand.clone());
    let left_eq = rc.trans(
        lhs_assoc.clone(),
        zero_plus_cand,
        cand.clone(),
        cong_left,
        rc_zero_add(cand.clone()),
    );
    // right: (−w)+(w+c) = (−w)+0 = −w
    let w_plus_cand = rc.add(w.clone(), cand.clone());
    let cong_right = cong_g(
        rc,
        w_plus_cand.clone(),
        zero.clone(),
        add_left_fixed(parent, rc, &neg_w_e),
        h1,
    );
    let negw_plus_zero = rc.add(neg_w_e.clone(), zero.clone());
    let right_eq = rc.trans(
        rhs_assoc.clone(),
        negw_plus_zero,
        neg_w_e.clone(),
        cong_right,
        rc_add_zero(neg_w_e.clone()),
    );
    // cand = lhs_assoc = rhs_assoc = −w
    let symm_left = rc.symm(lhs_assoc.clone(), cand.clone(), left_eq);
    let cand_to_rhs = rc.trans(cand.clone(), lhs_assoc, rhs_assoc.clone(), symm_left, assoc);
    let cand_eq_negw = rc.trans(
        cand.clone(),
        rhs_assoc,
        neg_w_e.clone(),
        cand_to_rhs,
        right_eq,
    );
    rc.symm(cand.clone(), neg_w_e, cand_eq_negw)
}

/// `(m + (−p)) + (p + (−m)) = 0`.
fn add_neg_pair_zero(parent: &EnvDeclBuilder, rc: &RingConsts, m: &Expr, p: &Expr) -> Expr {
    let zero = rc.o.rat_zero.clone();
    let neg_p = rc.neg(p.clone());
    let neg_m = rc.neg(m.clone());
    let m_np = rc.add(m.clone(), neg_p.clone()); // m + (−p)
    let p_nm = rc.add(p.clone(), neg_m.clone()); // p + (−m)
    let lhs = rc.add(m_np.clone(), p_nm.clone());
    // (m+(−p))+(p+(−m)) = m + ((−p)+(p+(−m)))   [assoc m (−p) (p+(−m))]
    let assoc1 = rc_add_assoc(m.clone(), neg_p.clone(), p_nm.clone());
    let inner1 = rc.add(neg_p.clone(), p_nm.clone()); // (−p)+(p+(−m))
    let step1_rhs = rc.add(m.clone(), inner1.clone());
    // (−p)+(p+(−m)) = ((−p)+p)+(−m)  [symm assoc] = 0+(−m) = −m
    let assoc2 = rc_add_assoc(neg_p.clone(), p.clone(), neg_m.clone()); // ((−p)+p)+(−m) = (−p)+(p+(−m))
    let np_plus_p = rc.add(neg_p.clone(), p.clone());
    let assoc2_lhs = rc.add(np_plus_p.clone(), neg_m.clone());
    let cong_npp = cong_g(
        rc,
        np_plus_p.clone(),
        zero.clone(),
        add_right_fixed(parent, rc, &neg_m),
        rc_add_left_neg(p.clone()),
    );
    let zero_plus_negm = rc.add(zero.clone(), neg_m.clone());
    let assoc2_lhs_to_negm = rc.trans(
        assoc2_lhs.clone(),
        zero_plus_negm,
        neg_m.clone(),
        cong_npp,
        rc_zero_add(neg_m.clone()),
    );
    let symm_assoc2 = rc.symm(assoc2_lhs.clone(), inner1.clone(), assoc2);
    let inner1_eq_negm = rc.trans(
        inner1.clone(),
        assoc2_lhs,
        neg_m.clone(),
        symm_assoc2,
        assoc2_lhs_to_negm,
    );
    // m + inner1 = m + (−m) = 0
    let cong_inner = cong_g(
        rc,
        inner1.clone(),
        neg_m.clone(),
        add_left_fixed(parent, rc, m),
        inner1_eq_negm,
    );
    let m_plus_negm = rc.add(m.clone(), neg_m.clone());
    let step1_rhs_to_zero = rc.trans(
        step1_rhs.clone(),
        m_plus_negm,
        zero.clone(),
        cong_inner,
        rc_add_neg_self(m.clone()),
    );
    rc.trans(lhs, step1_rhs, zero, assoc1, step1_rhs_to_zero)
}

/// `(p+m) + (p + (−m)) = p·2`.
fn double_cancel_false(
    parent: &EnvDeclBuilder,
    rc: &RingConsts,
    p: &Expr,
    m: &Expr,
    twice_p: &Expr,
) -> Expr {
    let neg_m = rc.neg(m.clone());
    let p_m = rc.add(p.clone(), m.clone()); // p+m
    let p_nm = rc.add(p.clone(), neg_m.clone()); // p+(−m)
    let lhs = rc.add(p_m.clone(), p_nm.clone());
    // (p+m)+(p+(−m)) = p + (m + (p+(−m)))   [assoc p m (p+(−m))]
    let assoc1 = rc_add_assoc(p.clone(), m.clone(), p_nm.clone());
    let inner = rc.add(m.clone(), p_nm.clone()); // m + (p+(−m))
    let step1 = rc.add(p.clone(), inner.clone());
    // m + (p + (−m)) = p
    let inner_eq_p = m_plus_p_minus_m_eq_p(parent, rc, p, m);
    let cong = cong_g(
        rc,
        inner.clone(),
        p.clone(),
        add_left_fixed(parent, rc, p),
        inner_eq_p,
    );
    let p_plus_p = rc.add(p.clone(), p.clone());
    // chain: lhs = step1 [assoc1] = p+p [cong] = p·2
    let lhs_to_step1 = assoc1;
    let lhs_to_pp = rc.trans(lhs.clone(), step1, p_plus_p.clone(), lhs_to_step1, cong);
    let pp_eq_double = p_plus_eq_double(parent, rc, p, twice_p);
    rc.trans(lhs, p_plus_p, twice_p.clone(), lhs_to_pp, pp_eq_double)
}

/// `(p+m) + (m + (−p)) = m·2`.
fn double_cancel_true(
    parent: &EnvDeclBuilder,
    rc: &RingConsts,
    p: &Expr,
    m: &Expr,
    twice_m: &Expr,
) -> Expr {
    let neg_p = rc.neg(p.clone());
    let p_m = rc.add(p.clone(), m.clone()); // p+m
    let m_p = rc.add(m.clone(), p.clone()); // m+p
    let m_np = rc.add(m.clone(), neg_p.clone()); // m+(−p)
    let lhs = rc.add(p_m.clone(), m_np.clone()); // (p+m)+(m+(−p))
                                                 // step0: (p+m)+(m+(−p)) = (m+p)+(m+(−p))   [congr (·+(m+(−p))) (add_comm p m)]
    let cong0 = cong_g(
        rc,
        p_m.clone(),
        m_p.clone(),
        add_right_fixed(parent, rc, &m_np),
        rc_add_comm(p.clone(), m.clone()),
    );
    let lhs2 = rc.add(m_p.clone(), m_np.clone()); // (m+p)+(m+(−p))
                                                  // (m+p)+(m+(−p)) = m + (p + (m+(−p)))   [assoc m p (m+(−p))]
    let assoc1 = rc_add_assoc(m.clone(), p.clone(), m_np.clone());
    let inner = rc.add(p.clone(), m_np.clone()); // p + (m+(−p))
    let step1 = rc.add(m.clone(), inner.clone());
    // p + (m + (−p)) = m
    let inner_eq_m = p_plus_m_minus_p_eq_m(parent, rc, m, p);
    let cong = cong_g(
        rc,
        inner.clone(),
        m.clone(),
        add_left_fixed(parent, rc, m),
        inner_eq_m,
    );
    let m_plus_m = rc.add(m.clone(), m.clone());
    // chain: lhs = lhs2 [cong0] = step1 [assoc1] = m+m [cong] = m·2
    let lhs_to_step1 = rc.trans(lhs.clone(), lhs2, step1.clone(), cong0, assoc1);
    let lhs_to_mm = rc.trans(lhs.clone(), step1, m_plus_m.clone(), lhs_to_step1, cong);
    let mm_eq_double = p_plus_eq_double(parent, rc, m, twice_m);
    rc.trans(lhs, m_plus_m, twice_m.clone(), lhs_to_mm, mm_eq_double)
}

/// `m + (p + (−m)) = p`.
fn m_plus_p_minus_m_eq_p(parent: &EnvDeclBuilder, rc: &RingConsts, p: &Expr, m: &Expr) -> Expr {
    let neg_m = rc.neg(m.clone());
    let p_nm = rc.add(p.clone(), neg_m.clone()); // p+(−m)
    let lhs = rc.add(m.clone(), p_nm.clone()); // m + (p+(−m))
                                               // = (m+p)+(−m)   [symm (assoc m p (−m))]
    let assoc = rc_add_assoc(m.clone(), p.clone(), neg_m.clone()); // (m+p)+(−m) = m+(p+(−m))
    let m_p = rc.add(m.clone(), p.clone());
    let mp_nm = rc.add(m_p.clone(), neg_m.clone());
    let symm_assoc = rc.symm(mp_nm.clone(), lhs.clone(), assoc);
    // (m+p)+(−m) = (p+m)+(−m)   [congr (·+(−m)) (add_comm m p)]
    let p_m = rc.add(p.clone(), m.clone());
    let cong = cong_g(
        rc,
        m_p.clone(),
        p_m.clone(),
        add_right_fixed(parent, rc, &neg_m),
        rc_add_comm(m.clone(), p.clone()),
    );
    let pm_nm = rc.add(p_m.clone(), neg_m.clone());
    // (p+m)+(−m) = p + (m+(−m))  [assoc] = p+0 = p
    let assoc2 = rc_add_assoc(p.clone(), m.clone(), neg_m.clone());
    let m_nm = rc.add(m.clone(), neg_m.clone());
    let p_plus_mnm = rc.add(p.clone(), m_nm.clone());
    let cong2 = cong_g(
        rc,
        m_nm.clone(),
        rc.o.rat_zero.clone(),
        add_left_fixed(parent, rc, p),
        rc_add_neg_self(m.clone()),
    );
    let p_plus_zero = rc.add(p.clone(), rc.o.rat_zero.clone());
    let p_plus_mnm_to_p = rc.trans(
        p_plus_mnm.clone(),
        p_plus_zero,
        p.clone(),
        cong2,
        rc_add_zero(p.clone()),
    );
    let pm_nm_to_p = rc.trans(
        pm_nm.clone(),
        p_plus_mnm,
        p.clone(),
        assoc2,
        p_plus_mnm_to_p,
    );
    let lhs_to_pmnm = rc.trans(lhs.clone(), mp_nm, pm_nm.clone(), symm_assoc, cong);
    rc.trans(lhs, pm_nm, p.clone(), lhs_to_pmnm, pm_nm_to_p)
}

/// `p + (m + (−p)) = m`.
fn p_plus_m_minus_p_eq_m(parent: &EnvDeclBuilder, rc: &RingConsts, m: &Expr, p: &Expr) -> Expr {
    let neg_p = rc.neg(p.clone());
    let m_np = rc.add(m.clone(), neg_p.clone()); // m+(−p)
    let np_m = rc.add(neg_p.clone(), m.clone()); // (−p)+m
    let lhs = rc.add(p.clone(), m_np.clone());
    // congr (p+·) (add_comm m (−p)) : p+(m+(−p)) = p+((−p)+m)
    let cong = cong_g(
        rc,
        m_np.clone(),
        np_m.clone(),
        add_left_fixed(parent, rc, p),
        rc_add_comm(m.clone(), neg_p.clone()),
    );
    let p_npm = rc.add(p.clone(), np_m.clone());
    // p+((−p)+m) = (p+(−p))+m  [symm assoc]
    let assoc = rc_add_assoc(p.clone(), neg_p.clone(), m.clone()); // (p+(−p))+m = p+((−p)+m)
    let p_np = rc.add(p.clone(), neg_p.clone());
    let pnp_m = rc.add(p_np.clone(), m.clone());
    let symm_assoc = rc.symm(pnp_m.clone(), p_npm.clone(), assoc);
    // (p+(−p))+m = 0+m = m
    let cong2 = cong_g(
        rc,
        p_np.clone(),
        rc.o.rat_zero.clone(),
        add_right_fixed(parent, rc, m),
        rc_add_neg_self(p.clone()),
    );
    let zero_m = rc.add(rc.o.rat_zero.clone(), m.clone());
    let pnpm_to_m = rc.trans(
        pnp_m.clone(),
        zero_m,
        m.clone(),
        cong2,
        rc_zero_add(m.clone()),
    );
    let lhs_to_pnpm = rc.trans(lhs.clone(), p_npm, pnp_m.clone(), cong, symm_assoc);
    rc.trans(lhs, pnp_m, m.clone(), lhs_to_pnpm, pnpm_to_m)
}

/// `p + p = p·2`  via `two_mul p : 2·p = p+p` and `mul_comm p 2 : p·2 = 2·p`.
fn p_plus_eq_double(parent: &EnvDeclBuilder, rc: &RingConsts, p: &Expr, twice_p: &Expr) -> Expr {
    let two = rc.two();
    let two_p = rc.mul(two.clone(), p.clone()); // 2·p
    let p_plus_p = rc.add(p.clone(), p.clone());
    let two_mul = rc.two_mul(parent, p.clone()); // 2·p = p+p
    let mul_comm = rc_mul_comm(p.clone(), two.clone()); // p·2 = 2·p
    let symm_two_mul = rc.symm(two_p.clone(), p_plus_p.clone(), two_mul); // p+p = 2·p
    let symm_mul_comm = rc.symm(twice_p.clone(), two_p.clone(), mul_comm); // 2·p = p·2
    rc.trans(
        p_plus_p,
        two_p,
        twice_p.clone(),
        symm_two_mul,
        symm_mul_comm,
    )
}
