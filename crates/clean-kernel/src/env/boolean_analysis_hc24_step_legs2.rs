// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// The `hc24_core_step` ring-equality legs (S6 assemble, S7/S8 close, product
// square). `include!`d into the step build module.

/// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
fn mmmc(_c: &StepConsts, a: &Expr, bv: &Expr, cc: &Expr, dd: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
        [a.clone(), bv.clone(), cc.clone(), dd.clone()],
    )
}

/// `(p·sg²)·(p·sh²) = (p·(sg·sh))·(p·(sg·sh))`.
///
/// LHS = (p·(sg·sg))·(p·(sh·sh))
///     = (p·p)·((sg·sg)·(sh·sh))            [mmmc p (sg·sg) p (sh·sh)]
///     = (p·p)·((sg·sh)·(sg·sh))            [cong_right ((p·p)·_) of mmmc sg sg sh sh]
///     = (p·(sg·sh))·(p·(sg·sh))            [symm (mmmc p (sg·sh) p (sg·sh))]
fn step_prod_sq_eq(
    c: &StepConsts,
    parent: &EnvDeclBuilder,
    p: &Expr,
    sg: &Expr,
    sh: &Expr,
) -> Expr {
    let mul_c = c.mul_c();
    let sg2 = c.sq(sg);
    let sh2 = c.sq(sh);
    let sgsh = c.mul(sg.clone(), sh.clone());
    let pp = c.mul(p.clone(), p.clone());

    let lhs = c.mul(c.mul(p.clone(), sg2.clone()), c.mul(p.clone(), sh2.clone()));
    // s1 : LHS = (p·p)·(sg²·sh²)
    let sg2_sh2 = c.mul(sg2.clone(), sh2.clone());
    let mid1 = c.mul(pp.clone(), sg2_sh2.clone());
    let s1 = mmmc(c, p, &sg2, p, &sh2);
    // s2 : (p·p)·(sg²·sh²) = (p·p)·((sg·sh)·(sg·sh))
    let sgsh_sgsh = c.mul(sgsh.clone(), sgsh.clone());
    let mid2 = c.mul(pp.clone(), sgsh_sgsh.clone());
    let h_inner = mmmc(c, sg, sg, sh, sh); // (sg·sg)·(sh·sh) = (sg·sh)·(sg·sh)
    let s2 = c.cong_right(
        parent,
        &mul_c,
        sg2_sh2.clone(),
        sgsh_sgsh.clone(),
        pp.clone(),
        h_inner,
    );
    // s3 : (p·p)·((sg·sh)·(sg·sh)) = (p·(sg·sh))·(p·(sg·sh))
    let rhs = c.mul(
        c.mul(p.clone(), sgsh.clone()),
        c.mul(p.clone(), sgsh.clone()),
    );
    let s3 = c.symm(rhs.clone(), mid2.clone(), mmmc(c, p, &sgsh, p, &sgsh));

    let t1 = c.trans(lhs.clone(), mid1.clone(), mid2.clone(), s1, s2);
    c.trans(lhs, mid2, rhs, t1, s3)
}

/// S6 : `(8^n SG² + 8^n SH²) + (1+1)·(8^n·(SG·SH)) = 8^n·(SG+SH)²`.
///
/// hc24Assemble p sg sh : `p·sg² + (2·(p·(sg·sh)) + p·sh²) = p·(sg+sh)²`.
/// We reshape our `bound = (p·sg² + p·sh²) + Z`  (Z := (1+1)·(p·(sg·sh)))
/// into the hc24Assemble LHS `p·sg² + (Z + p·sh²)`:
///   bound = p·sg² + (p·sh² + Z)        [add_assoc]
///         = p·sg² + (Z + p·sh²)        [cong_right (p·sg² + _) (add_comm p·sh² Z)]
///         = p·(sg+sh)²                 [hc24Assemble]
fn step_s6_assemble(
    c: &StepConsts,
    parent: &EnvDeclBuilder,
    pow8: &Expr,
    sg: &Expr,
    sh: &Expr,
    bnd_pq: &Expr,
    bnd_2r: &Expr,
) -> Expr {
    let add_c = c.add_c();
    let p_sg2 = c.mul(pow8.clone(), c.sq(sg)); // p·sg²
    let p_sh2 = c.mul(pow8.clone(), c.sq(sh)); // p·sh²
    let z = bnd_2r.clone(); // (1+1)·(p·(sg·sh))
                            // bnd_pq = p·sg² + p·sh²  (by construction).
    let bound = c.add(bnd_pq.clone(), z.clone()); // (p·sg² + p·sh²) + Z

    // s1 : (p·sg² + p·sh²) + Z = p·sg² + (p·sh² + Z)    [add_assoc p·sg² p·sh² Z]
    let assoc = Expr::apps(
        Expr::const_(Name::from_string("Rat.add_assoc"), vec![]),
        [p_sg2.clone(), p_sh2.clone(), z.clone()],
    );
    let mid1 = c.add(p_sg2.clone(), c.add(p_sh2.clone(), z.clone()));
    // s2 : p·sg² + (p·sh² + Z) = p·sg² + (Z + p·sh²)   [cong_right (p·sg² + _) (add_comm p·sh² Z)]
    let comm = Expr::apps(
        Expr::const_(Name::from_string("Rat.add_comm"), vec![]),
        [p_sh2.clone(), z.clone()],
    );
    let z_sh2 = c.add(z.clone(), p_sh2.clone());
    let s2 = c.cong_right(
        parent,
        &add_c,
        c.add(p_sh2.clone(), z.clone()),
        z_sh2.clone(),
        p_sg2.clone(),
        comm,
    );
    let mid2 = c.add(p_sg2.clone(), z_sh2.clone()); // hc24Assemble LHS shape
                                                    // s3 : hc24Assemble pow8 sg sh : mid2 = p·(sg+sh)²
    let s3 = c.assemble(pow8, sg, sh);
    let sg_plus_sh = c.add(sg.clone(), sh.clone());
    let rhs = c.mul(pow8.clone(), c.sq(&sg_plus_sh));

    let t1 = c.trans(bound.clone(), mid1.clone(), mid2.clone(), assoc, s2);
    c.trans(bound, mid2, rhs, t1, s3)
}

/// S7+S8 close : `(1+1)·(8^n·(SG+SH)²) = 8^{n+1}·SF'²`.
///
/// 1. hc24S7 n F : `SG+SH = (1+1)·SF'`; lift through `8^n·(_·_)` (two congrArgs)
///    to get `8^n·(SG+SH)² = 8^n·((1+1)SF'·(1+1)SF')`.
/// 2. lift through `(1+1)·_` : `(1+1)·(8^n·(SG+SH)²) = (1+1)·(8^n·((1+1)SF'·(1+1)SF'))`.
/// 3. `hc24_numeral 8^n SF'` (a closed Rat ring identity) :
///    `(1+1)·(8^n·((1+1)SF'·(1+1)SF')) = (8·8^n)·(SF'·SF')`.
/// 4. powNat_succ 8 n : `8^{n+1} = 8·8^n`; lift through `_·SF'²`:
///    `(8·8^n)·SF'² = 8^{n+1}·SF'²`  (symm).
fn step_s78_close(
    c: &StepConsts,
    parent: &EnvDeclBuilder,
    pow8: &Expr,
    n: &Expr,
    _sg: &Expr,
    _sh: &Expr,
    sf: &Expr,
    f: &Expr,
    sg_plus_sh: &Expr,
    _two_pow8_sgsh2: &Expr,
) -> Expr {
    let two = c.two();
    let mul_c = c.mul_c();
    let sn = c.succ(n);

    // h_s7 : SG+SH = (1+1)·SF'
    let two_sf = c.mul(two.clone(), sf.clone());
    let h_s7 = c.s7(n, f);

    // (SG+SH)² → ((1+1)SF')²  via two congruences on `_·_`.
    let ss = c.mul(sg_plus_sh.clone(), sg_plus_sh.clone()); // (SG+SH)·(SG+SH)
    let two_sf_sq = c.mul(two_sf.clone(), two_sf.clone()); // ((1+1)SF')·((1+1)SF')
                                                           // cong left:  (SG+SH)·(SG+SH) = (1+1)SF·(SG+SH)
    let mid_a = c.mul(two_sf.clone(), sg_plus_sh.clone());
    let cl = c.cong_left(
        parent,
        &mul_c,
        sg_plus_sh.clone(),
        two_sf.clone(),
        sg_plus_sh.clone(),
        h_s7.clone(),
    );
    // cong right: (1+1)SF·(SG+SH) = (1+1)SF·(1+1)SF
    let cr = c.cong_right(
        parent,
        &mul_c,
        sg_plus_sh.clone(),
        two_sf.clone(),
        two_sf.clone(),
        h_s7,
    );
    let ss_eq = c.trans(ss.clone(), mid_a, two_sf_sq.clone(), cl, cr);

    // 8^n·(SG+SH)² = 8^n·((1+1)SF')²   [cong_right (8^n·_)]
    let p_ss = c.mul(pow8.clone(), ss.clone());
    let p_tsf = c.mul(pow8.clone(), two_sf_sq.clone());
    let p_ss_eq = c.cong_right(
        parent,
        &mul_c,
        ss.clone(),
        two_sf_sq.clone(),
        pow8.clone(),
        ss_eq,
    );

    // (1+1)·(8^n·(SG+SH)²) = (1+1)·(8^n·((1+1)SF')²)   [cong_right ((1+1)·_)]
    let lhs = c.mul(two.clone(), p_ss.clone());
    let mid_num = c.mul(two.clone(), p_tsf.clone());
    let lhs_eq_mid = c.cong_right(
        parent,
        &mul_c,
        p_ss.clone(),
        p_tsf.clone(),
        two.clone(),
        p_ss_eq,
    );

    // hc24_numeral : (1+1)·(8^n·((1+1)SF'·(1+1)SF')) = (8·8^n)·(SF'·SF')
    let num = step_hc24_numeral(c, parent, pow8, sf);
    let eight_p = c.mul(c.eight_rat(), pow8.clone());
    let sf_sq = c.mul(sf.clone(), sf.clone());
    let eight_p_sfsq = c.mul(eight_p.clone(), sf_sq.clone());

    // (8·8^n)·SF'² = 8^{n+1}·SF'²   [cong_left (_·SF'²) (symm powNat_succ 8 n)]
    let pow8_sn = c.pow8(&sn); // 8^{n+1}
    let h_pow = c.pow_nat_succ(&c.eight_rat(), n); // 8^{n+1} = 8·8^n
    let h_pow_sym = c.symm(pow8_sn.clone(), eight_p.clone(), h_pow); // 8·8^n = 8^{n+1}
    let cl_pow = c.cong_left(
        parent,
        &mul_c,
        eight_p.clone(),
        pow8_sn.clone(),
        sf_sq.clone(),
        h_pow_sym,
    );
    let goal = c.mul(pow8_sn.clone(), sf_sq.clone()); // 8^{n+1}·SF'²

    // chain: lhs = mid_num = (8·8^n)·SF'² = 8^{n+1}·SF'²
    let t1 = c.trans(
        lhs.clone(),
        mid_num.clone(),
        eight_p_sfsq.clone(),
        lhs_eq_mid,
        num,
    );
    c.trans(lhs, eight_p_sfsq, goal, t1, cl_pow)
}

/// The closed Rat ring identity
/// `hc24_numeral p s : (1+1)·(p·(((1+1)·s)·((1+1)·s))) = (8·p)·(s·s)`,
/// built inline (free `p := 8^n`, `s := SF'`).
///
/// `((1+1)s)·((1+1)s) = ((1+1)·(1+1))·(s·s)`           [mmmc (1+1) s (1+1) s]
/// `p·(((1+1)(1+1))·(s·s)) = (p·((1+1)(1+1)))·(s·s)`    [symm mul_assoc]
/// `(1+1)·((p·((1+1)(1+1)))·(s·s)) = ((1+1)·(p·((1+1)(1+1))))·(s·s)`  [symm mul_assoc]
/// `(1+1)·(p·((1+1)(1+1))) = (((1+1)·(1+1))·(1+1))·p` reshape to `(8·p)`  [mul_comm/assoc + defeq 2·2·2=8]
fn step_hc24_numeral(c: &StepConsts, parent: &EnvDeclBuilder, p: &Expr, s: &Expr) -> Expr {
    let mul_c = c.mul_c();
    let two = c.two();
    let two_s = c.mul(two.clone(), s.clone()); // (1+1)·s
    let ss = c.mul(s.clone(), s.clone()); // s·s
    let two_two = c.mul(two.clone(), two.clone()); // (1+1)·(1+1)

    // step A : ((1+1)s)·((1+1)s) = ((1+1)(1+1))·(s·s)   [mmmc (1+1) s (1+1) s]
    let lhs_inner = c.mul(two_s.clone(), two_s.clone());
    let mid_a = c.mul(two_two.clone(), ss.clone());
    let a = mmmc(c, &two, s, &two, s);

    // step B : p·(((1+1)s)·((1+1)s)) = p·(((1+1)(1+1))·(s·s))   [cong_right (p·_) a]
    let p_lhs_inner = c.mul(p.clone(), lhs_inner.clone());
    let p_mid_a = c.mul(p.clone(), mid_a.clone());
    let b = c.cong_right(
        parent,
        &mul_c,
        lhs_inner.clone(),
        mid_a.clone(),
        p.clone(),
        a,
    );

    // step C : p·(((1+1)(1+1))·(s·s)) = (p·((1+1)(1+1)))·(s·s)   [symm mul_assoc p ((1+1)(1+1)) (s·s)]
    let p_tt = c.mul(p.clone(), two_two.clone());
    let pc_rhs = c.mul(p_tt.clone(), ss.clone());
    let assoc_c = c.massoc(p, &two_two, &ss); // (p·tt)·ss = p·(tt·ss)
    let c_step = c.symm(pc_rhs.clone(), p_mid_a.clone(), assoc_c);

    // step BC (combined, under p·_): p·lhs_inner = (p·tt)·ss
    let bc = c.trans(
        p_lhs_inner.clone(),
        p_mid_a.clone(),
        pc_rhs.clone(),
        b,
        c_step,
    );

    // lhs0 = (1+1)·(p·lhs_inner).
    let lhs0 = c.mul(two.clone(), p_lhs_inner.clone());
    let two_pc_rhs = c.mul(two.clone(), pc_rhs.clone());
    // step D : (1+1)·(p·lhs_inner) = (1+1)·((p·tt)·ss)   [cong_right ((1+1)·_) bc]
    let d = c.cong_right(
        parent,
        &mul_c,
        p_lhs_inner.clone(),
        pc_rhs.clone(),
        two.clone(),
        bc,
    );

    // step E : (1+1)·((p·tt)·ss) = ((1+1)·(p·tt))·ss   [symm mul_assoc (1+1) (p·tt) ss]
    let two_ptt = c.mul(two.clone(), p_tt.clone());
    let e_rhs = c.mul(two_ptt.clone(), ss.clone());
    let assoc_e = c.massoc(&two, &p_tt, &ss); // (2·(p·tt))·ss = 2·((p·tt)·ss)
    let e_step = c.symm(e_rhs.clone(), two_pc_rhs.clone(), assoc_e);

    // step F : ((1+1)·(p·tt))·ss = (8·p)·ss   [cong_left (_·ss) coeff_eq]
    let coeff = two_ptt.clone(); // (1+1)·(p·((1+1)(1+1)))
    let eight_p = c.mul(c.eight_rat(), p.clone());
    let coeff_eq = step_coeff_eq(c, parent, p, &two, &two_two, &p_tt); // coeff = 8·p
    let f_step = c.cong_left(
        parent,
        &mul_c,
        coeff.clone(),
        eight_p.clone(),
        ss.clone(),
        coeff_eq,
    );
    let target = c.mul(eight_p.clone(), ss.clone());

    // chain: lhs0 = (1+1)·((p·tt)·ss) = ((1+1)·(p·tt))·ss = (8·p)·ss
    let c1 = c.trans(lhs0.clone(), two_pc_rhs.clone(), e_rhs.clone(), d, e_step);
    c.trans(lhs0, e_rhs, target, c1, f_step)
}

/// `(1+1)·(p·((1+1)·(1+1))) = 8·p`.
///
/// `(1+1)·(p·((1+1)(1+1)))`
///   = (1+1)·(((1+1)(1+1))·p)   [cong_right ((1+1)·_) (mul_comm p ((1+1)(1+1)))]
///   = ((1+1)·((1+1)(1+1)))·p   [symm mul_assoc (1+1) ((1+1)(1+1)) p]
///   = 8·p                       [cong_left (_·p) (defeq (1+1)·((1+1)(1+1)) = 8)]
fn step_coeff_eq(
    c: &StepConsts,
    parent: &EnvDeclBuilder,
    p: &Expr,
    two: &Expr,
    two_two: &Expr,
    p_tt: &Expr,
) -> Expr {
    let mul_c = c.mul_c();
    let lhs = c.mul(two.clone(), p_tt.clone()); // (1+1)·(p·((1+1)(1+1)))
                                                // s1 : p·((1+1)(1+1)) = ((1+1)(1+1))·p   [mul_comm]
    let tt_p = c.mul(two_two.clone(), p.clone());
    let comm = c.mcomm(p, two_two);
    let s1 = c.cong_right(
        parent,
        &mul_c,
        p_tt.clone(),
        tt_p.clone(),
        two.clone(),
        comm,
    );
    let mid1 = c.mul(two.clone(), tt_p.clone());
    // s2 : (1+1)·(((1+1)(1+1))·p) = ((1+1)·((1+1)(1+1)))·p   [symm mul_assoc]
    let two_tt = c.mul(two.clone(), two_two.clone()); // (1+1)·((1+1)(1+1)) = 8 (defeq)
    let mid2 = c.mul(two_tt.clone(), p.clone());
    let assoc = c.massoc(two, two_two, p); // (2·tt)·p = 2·(tt·p)
    let s2 = c.symm(mid2.clone(), mid1.clone(), assoc);
    // s3 : ((1+1)·((1+1)(1+1)))·p = 8·p   [cong_left (_·p) (Eq.refl eight_rat, defeq)]
    let h_num = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![c.l1.clone()]),
        [c.rat(), c.eight_rat()],
    ); // two_tt = eight_rat  (defeq)
    let eight_p = c.mul(c.eight_rat(), p.clone());
    let s3 = c.cong_left(
        parent,
        &mul_c,
        two_tt.clone(),
        c.eight_rat(),
        p.clone(),
        h_num,
    );

    let t1 = c.trans(lhs.clone(), mid1.clone(), mid2.clone(), s1, s2);
    c.trans(lhs, mid2, eight_p, t1, s3)
}
