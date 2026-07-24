// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Proof-term builder for `Rat.two_point_fourth_moment` — the RATIONAL fourth
// moment of the dual `(4/3, 4)` two-point base.
//
// `include!`d into `boolean_analysis_two_point_base_moment.rs`; shares its `use`s
// and the `RingConsts` / `MomentConsts` surfaces.

/// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
fn mmmc(a: &Expr, b: &Expr, cc: &Expr, dd: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
        [a.clone(), b.clone(), cc.clone(), dd.clone()],
    )
}

/// Build the type + proof of `Rat.two_point_fourth_moment`.
fn build_two_point_fourth_moment(rc: &RingConsts, mc: &MomentConsts) -> (Expr, Expr) {
    let rat = rc.rat();

    // Shared per-(a,b) builder: returns (proof, lhs, rhs).
    let build = |bo: &EnvDeclBuilder, a: &Expr, b: &Expr| -> (Expr, Expr, Expr) {
        let add_c = rc.add_const();
        let mul_c = rc.mul_const();
        let half = mc.half();
        let rho = mc.one_third();
        let rb = rc.mul(rho.clone(), b.clone()); // ρ·b
        let two = rc.two();
        let two_two = rc.mul(two.clone(), two.clone());
        let coeff = rc.add(two_two.clone(), rc.nmul(two.clone(), two_two.clone())); // (2·2)+2·(2·2)

        // monomials.
        let aa = rc.mul(a.clone(), a.clone());
        let bb = rc.mul(b.clone(), b.clone());
        let a4 = rc.mul(aa.clone(), aa.clone());
        let b4 = rc.mul(bb.clone(), bb.clone());
        let a2b2 = rc.mul(aa.clone(), bb.clone());
        let rbrb = rc.mul(rb.clone(), rb.clone()); // (ρb)·(ρb)
        let rb4 = rc.mul(rbrb.clone(), rbrb.clone()); // (ρb)⁴
        let rho2 = rc.mul(rho.clone(), rho.clone()); // ρ·ρ
        let rho4 = rc.mul(rho2.clone(), rho2.clone()); // (ρ·ρ)·(ρ·ρ)

        // coefficient numerals.
        let one81 = mc.frac(1, 81);
        let two3 = mc.frac(2, 3);

        // Even-pair: M = E.
        let s = rc.add(a.clone(), rb.clone());
        let d = rc.sub(a.clone(), rb.clone());
        let even_lhs = rc.add(pow4_of(rc, &s), pow4_of(rc, &d)); // M
        let two_a4 = rc.nmul(two.clone(), a4.clone());
        let two_rb4 = rc.nmul(two.clone(), rb4.clone());
        let aa_rbrb = rc.mul(aa.clone(), rbrb.clone()); // a²·(ρb)²
        let e_cross = rc.mul(coeff.clone(), aa_rbrb.clone());
        let e_left = rc.add(two_a4.clone(), two_rb4.clone());
        let even_rhs = rc.add(e_left.clone(), e_cross.clone()); // E

        let h_ep = Expr::apps(
            Expr::const_(Name::from_string("Rat.fourth_power_rho_even_pair"), vec![]),
            [a.clone(), b.clone(), rho.clone()],
        ); // M = E

        // ½·M and ½·E.
        let half_m = rc.mul(half.clone(), even_lhs.clone());
        let half_e = rc.mul(half.clone(), even_rhs.clone());
        // stepA : ½·M = ½·E.
        let step_a = mc.cong_mul_right(bo, &half, even_lhs.clone(), even_rhs.clone(), h_ep);

        // stepB : ½·E = ½·e_left + ½·e_cross   (ldist half e_left e_cross).
        let half_eleft = rc.mul(half.clone(), e_left.clone());
        let half_ecross = rc.mul(half.clone(), e_cross.clone());
        let distr_e = rc.add(half_eleft.clone(), half_ecross.clone());
        let step_b = rc.ldist(half.clone(), e_left.clone(), e_cross.clone());

        // ── left part: ½·e_left = a4 + (1/81)·b4. ──
        // ldist half (2·a4) (2·rb4) : ½·(2a4+2rb4) = ½·(2a4) + ½·(2rb4).
        let half_2a4 = rc.mul(half.clone(), two_a4.clone());
        let half_2rb4 = rc.mul(half.clone(), two_rb4.clone());
        let il_distr = rc.add(half_2a4.clone(), half_2rb4.clone());
        let step_il = rc.ldist(half.clone(), two_a4.clone(), two_rb4.clone());

        // leg1 : ½·(2·a4) = a4.
        let leg1 = build_leg_a4(rc, mc, bo, &half, &two, &a4);

        // leg2 : ½·(2·rb4) = (1/81)·b4.
        let leg2 = build_leg_rb4(
            rc, mc, bo, &half, &two, &rho, b, &rb, &bb, &b4, &rho2, &rho4, &one81,
        );

        // congr the two legs over the il_distr sum.
        let mid_il = rc.add(a4.clone(), half_2rb4.clone());
        let one81_b4 = rc.mul(one81.clone(), b4.clone());
        let il_target = rc.add(a4.clone(), one81_b4.clone());
        let il_l = rc.cong_left(
            bo,
            &add_c,
            half_2a4.clone(),
            a4.clone(),
            half_2rb4.clone(),
            leg1,
        );
        let il_r = rc.cong_right(
            bo,
            &add_c,
            half_2rb4.clone(),
            one81_b4.clone(),
            a4.clone(),
            leg2,
        );
        let il_legs = rc.trans(
            il_distr.clone(),
            mid_il.clone(),
            il_target.clone(),
            il_l,
            il_r,
        );
        // left_part : ½·e_left = a4 + (1/81)·b4.
        let left_part = rc.trans(
            half_eleft.clone(),
            il_distr.clone(),
            il_target.clone(),
            step_il,
            il_legs,
        );

        // ── right part: ½·e_cross = (2/3)·a2b2. ──
        let two3_a2b2 = rc.mul(two3.clone(), a2b2.clone());
        let right_part = build_leg_cross(
            rc, mc, bo, &half, &coeff, a, b, &aa, &bb, &rbrb, &aa_rbrb, &a2b2, &rho2, &two3,
        );

        // ── assemble: ½·E = (a4 + (1/81)·b4) + (2/3)·a2b2. ──
        let asm_target = rc.add(il_target.clone(), two3_a2b2.clone());
        let asm_l = rc.cong_left(
            bo,
            &add_c,
            half_eleft.clone(),
            il_target.clone(),
            half_ecross.clone(),
            left_part,
        );
        let mid_asm = rc.add(il_target.clone(), half_ecross.clone());
        let asm_r = rc.cong_right(
            bo,
            &add_c,
            half_ecross.clone(),
            two3_a2b2.clone(),
            il_target.clone(),
            right_part,
        );
        let asm = rc.trans(
            distr_e.clone(),
            mid_asm.clone(),
            asm_target.clone(),
            asm_l,
            asm_r,
        );
        // ½·E = asm_target  (step_b then asm).
        let half_e_eq = rc.trans(
            half_e.clone(),
            distr_e.clone(),
            asm_target.clone(),
            step_b,
            asm,
        );

        // ── reorder asm_target → target  (X+Z)+Y = (X+Y)+Z. ──
        // X = a4, Z = (1/81)·b4, Y = (2/3)·a2b2.
        let target = rc.add(rc.add(a4.clone(), two3_a2b2.clone()), one81_b4.clone());
        let reorder = build_reorder(rc, bo, &a4, &one81_b4, &two3_a2b2);

        // chain: ½·M = ½·E = asm_target = target.
        let p1 = rc.trans(
            half_m.clone(),
            half_e.clone(),
            asm_target.clone(),
            step_a,
            half_e_eq,
        );
        let proof = rc.trans(
            half_m.clone(),
            asm_target.clone(),
            target.clone(),
            p1,
            reorder,
        );

        let _ = (&mul_c, &a2b2);
        (proof, half_m, target)
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(rat.clone());
        let (bv_id, bv) = b.fresh_local(rat.clone());
        let (_p, lhs, rhs) = build(&b, &a, &bv);
        let body = rc.eq(lhs, rhs);
        let e = b.mk_pi(bv_id, BinderInfo::Default, rat.clone(), body);
        let e = b.mk_pi(a_id, BinderInfo::Default, rat.clone(), e);
        b.finish(e)
    };
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(rat.clone());
        let (bv_id, bv) = b.fresh_local(rat.clone());
        let (proof, _l, _r) = build(&b, &a, &bv);
        let e = b.mk_lam(bv_id, BinderInfo::Default, rat.clone(), proof);
        let e = b.mk_lam(a_id, BinderInfo::Default, rat.clone(), e);
        b.finish(e)
    };
    (ty, value)
}

/// `leg1 : ½·(2·a4) = a4`.
///   `½·(2·a4) =[symm massoc] (½·2)·a4 =[bridge mk2,2=1] (mk 1 1)·a4 =[one_mul] a4`.
fn build_leg_a4(
    rc: &RingConsts,
    mc: &MomentConsts,
    bo: &EnvDeclBuilder,
    half: &Expr,
    two: &Expr,
    a4: &Expr,
) -> Expr {
    let half_2a4 = rc.mul(half.clone(), rc.mul(two.clone(), a4.clone()));
    let half2 = rc.mul(half.clone(), two.clone()); // ½·2  (defeq mk 2 2)
    let half2_a4 = rc.mul(half2.clone(), a4.clone());
    let one11 = mc.frac(1, 1);
    let one11_a4 = rc.mul(one11.clone(), a4.clone());

    // assoc : (½·2)·a4 = ½·(2·a4); symm.
    let assoc = rc.massoc(half.clone(), two.clone(), a4.clone());
    let leg_a = rc.symm(half2_a4.clone(), half_2a4.clone(), assoc); // ½·(2·a4) = (½·2)·a4
                                                                    // bridge : mk 2 2 = mk 1 1  (defeq ½·2 = mk 1 1); congr_left over a4.
    let bridge = mc.frac_bridge(2, 2, 1, 1, 2); // 2·1 = 1·2 = 2
    let c1 = mc.cong_mul_left(bo, a4, half2.clone(), one11.clone(), bridge);
    // (½·2)·a4 = (mk 1 1)·a4
    // one_mul a4 : 1·a4 = a4  (defeq (mk 1 1)·a4 = a4).
    let one_mul = rc.one_mul(a4.clone());
    let s = rc.trans(
        half_2a4.clone(),
        half2_a4.clone(),
        one11_a4.clone(),
        leg_a,
        c1,
    );
    rc.trans(half_2a4, one11_a4, a4.clone(), s, one_mul)
}

/// `leg2 : ½·(2·rb4) = (1/81)·b4`.
///   `rb4 = ρ⁴·b4`  (two mmmc regroups), then
///   `½·(2·rb4) =[symm massoc] (½·2)·rb4 =[cong rb4→ρ⁴b4] (½·2)·(ρ⁴·b4)
///             =[symm massoc] ((½·2)·ρ⁴)·b4 =[bridge mk2,162=1/81] (1/81)·b4`.
#[allow(clippy::too_many_arguments)]
fn build_leg_rb4(
    rc: &RingConsts,
    mc: &MomentConsts,
    bo: &EnvDeclBuilder,
    half: &Expr,
    two: &Expr,
    rho: &Expr,
    b: &Expr,
    rb: &Expr,
    bb: &Expr,
    b4: &Expr,
    rho2: &Expr,
    rho4: &Expr,
    one81: &Expr,
) -> Expr {
    let mul_c = rc.mul_const();
    let rbrb = rc.mul(rb.clone(), rb.clone());
    let rb4 = rc.mul(rbrb.clone(), rbrb.clone());

    // eq_rb4 : rb4 = ρ⁴·b4.
    //   (ρb)·(ρb) = (ρ·ρ)·(b·b)   [mmmc ρ b ρ b]  → rho2·bb.
    let rho2_bb = rc.mul(rho2.clone(), bb.clone());
    let step1 = mmmc(rho, b, rho, b); // rbrb = rho2·bb
                                      // rewrite left factor of rb4: rbrb·rbrb = (rho2·bb)·rbrb.
    let cl = rc.cong_left(
        bo,
        &mul_c,
        rbrb.clone(),
        rho2_bb.clone(),
        rbrb.clone(),
        step1.clone(),
    );
    let r2bb_rbrb = rc.mul(rho2_bb.clone(), rbrb.clone());
    // rewrite right factor: (rho2·bb)·rbrb = (rho2·bb)·(rho2·bb).
    let cr = rc.cong_right(
        bo,
        &mul_c,
        rbrb.clone(),
        rho2_bb.clone(),
        rho2_bb.clone(),
        step1,
    );
    let r2bb_r2bb = rc.mul(rho2_bb.clone(), rho2_bb.clone());
    let step_both = rc.trans(rb4.clone(), r2bb_rbrb.clone(), r2bb_r2bb.clone(), cl, cr);
    // (rho2·bb)·(rho2·bb) = (rho2·rho2)·(bb·bb) = ρ⁴·b4   [mmmc rho2 bb rho2 bb].
    let rho4_b4 = rc.mul(rho4.clone(), b4.clone());
    let step2 = mmmc(rho2, bb, rho2, bb);
    let eq_rb4 = rc.trans(
        rb4.clone(),
        r2bb_r2bb.clone(),
        rho4_b4.clone(),
        step_both,
        step2,
    );

    // ½·(2·rb4).
    let half_2rb4 = rc.mul(half.clone(), rc.mul(two.clone(), rb4.clone()));
    let half2 = rc.mul(half.clone(), two.clone()); // ½·2 (defeq mk 2 2)
    let half2_rb4 = rc.mul(half2.clone(), rb4.clone());
    // assoc symm : ½·(2·rb4) = (½·2)·rb4.
    let assoc = rc.massoc(half.clone(), two.clone(), rb4.clone());
    let s0 = rc.symm(half2_rb4.clone(), half_2rb4.clone(), assoc);
    // (½·2)·rb4 = (½·2)·(ρ⁴·b4)   [cong_right (½·2) eq_rb4].
    let half2_rho4b4 = rc.mul(half2.clone(), rho4_b4.clone());
    let c1 = mc.cong_mul_right(bo, &half2, rb4.clone(), rho4_b4.clone(), eq_rb4);
    // (½·2)·(ρ⁴·b4) = ((½·2)·ρ⁴)·b4   [symm massoc (½·2) ρ⁴ b4].
    let half2_rho4 = rc.mul(half2.clone(), rho4.clone()); // defeq mk 2 162
    let half2rho4_b4 = rc.mul(half2_rho4.clone(), b4.clone());
    let assoc2 = rc.massoc(half2.clone(), rho4.clone(), b4.clone()); // (s·ρ⁴)·b4 = s·(ρ⁴·b4)
    let s2 = rc.symm(half2rho4_b4.clone(), half2_rho4b4.clone(), assoc2);
    // ((½·2)·ρ⁴)·b4 = (1/81)·b4   [bridge mk 2 162 = mk 1 81, cong_left over b4].
    let bridge = mc.frac_bridge(2, 162, 1, 81, 162); // 2·81 = 1·162 = 162
    let one81_b4 = rc.mul(one81.clone(), b4.clone());
    let c2 = mc.cong_mul_left(bo, b4, half2_rho4.clone(), one81.clone(), bridge);

    // chain: half_2rb4 → half2_rb4 → half2_rho4b4 → half2rho4_b4 → one81_b4.
    let s = rc.trans(
        half_2rb4.clone(),
        half2_rb4.clone(),
        half2_rho4b4.clone(),
        s0,
        c1,
    );
    let s = rc.trans(
        half_2rb4.clone(),
        half2_rho4b4.clone(),
        half2rho4_b4.clone(),
        s,
        s2,
    );
    rc.trans(half_2rb4, half2rho4_b4, one81_b4, s, c2)
}

/// `leg_cross : ½·(coeff·(aa·rbrb)) = (2/3)·a2b2`.
///   inner `coeff·(aa·rbrb) = (coeff·ρ²)·a2b2`, then
///   `½·((coeff·ρ²)·a2b2) =[symm massoc] (½·(coeff·ρ²))·a2b2 =[bridge mk12,18=2/3] (2/3)·a2b2`.
#[allow(clippy::too_many_arguments)]
fn build_leg_cross(
    rc: &RingConsts,
    mc: &MomentConsts,
    bo: &EnvDeclBuilder,
    half: &Expr,
    coeff: &Expr,
    _a: &Expr,
    b: &Expr,
    aa: &Expr,
    bb: &Expr,
    rbrb: &Expr,
    aa_rbrb: &Expr,
    a2b2: &Expr,
    rho2: &Expr,
    two3: &Expr,
) -> Expr {
    let mul_c = rc.mul_const();
    let rho = mc.one_third();

    // eq_inner : coeff·(aa·rbrb) = (coeff·ρ²)·a2b2.
    // step_rbrb : rbrb = ρ²·bb  [mmmc ρ b ρ b].
    let rho2_bb = rc.mul(rho2.clone(), bb.clone());
    let step_rbrb = mmmc(&rho, b, &rho, b);
    // aa·rbrb = aa·(ρ²·bb)  [cong_right aa].
    let aa_r2bb = rc.mul(aa.clone(), rho2_bb.clone());
    let c_in = rc.cong_right(
        bo,
        &mul_c,
        rbrb.clone(),
        rho2_bb.clone(),
        aa.clone(),
        step_rbrb,
    );
    // aa·(ρ²·bb) = aa·(bb·ρ²)  [cong_right aa, mcomm ρ² bb].
    let bb_rho2 = rc.mul(bb.clone(), rho2.clone());
    let comm1 = rc.mcomm(rho2.clone(), bb.clone());
    let aa_bbr2 = rc.mul(aa.clone(), bb_rho2.clone());
    let c_comm = rc.cong_right(
        bo,
        &mul_c,
        rho2_bb.clone(),
        bb_rho2.clone(),
        aa.clone(),
        comm1,
    );
    // aa·(bb·ρ²) = (aa·bb)·ρ²  [symm massoc aa bb ρ²].
    let a2b2_rho2 = rc.mul(a2b2.clone(), rho2.clone());
    let assoc1 = rc.massoc(aa.clone(), bb.clone(), rho2.clone()); // (aa·bb)·ρ² = aa·(bb·ρ²)
    let s_assoc1 = rc.symm(a2b2_rho2.clone(), aa_bbr2.clone(), assoc1);
    // aa·rbrb = (aa·bb)·ρ² = a2b2·ρ².
    let inner_eq0 = rc.trans(
        aa_rbrb.clone(),
        aa_r2bb.clone(),
        aa_bbr2.clone(),
        c_in,
        c_comm,
    );
    let inner_eq = rc.trans(
        aa_rbrb.clone(),
        aa_bbr2.clone(),
        a2b2_rho2.clone(),
        inner_eq0,
        s_assoc1,
    );
    // lift over coeff: coeff·(aa·rbrb) = coeff·(a2b2·ρ²).
    let coeff_a2b2r2 = rc.mul(coeff.clone(), a2b2_rho2.clone());
    let c_lift = rc.cong_right(
        bo,
        &mul_c,
        aa_rbrb.clone(),
        a2b2_rho2.clone(),
        coeff.clone(),
        inner_eq,
    );
    // coeff·(a2b2·ρ²) = coeff·(ρ²·a2b2)  [cong_right coeff, mcomm a2b2 ρ²].
    let rho2_a2b2 = rc.mul(rho2.clone(), a2b2.clone());
    let comm2 = rc.mcomm(a2b2.clone(), rho2.clone());
    let coeff_r2a2b2 = rc.mul(coeff.clone(), rho2_a2b2.clone());
    let c_comm2 = rc.cong_right(
        bo,
        &mul_c,
        a2b2_rho2.clone(),
        rho2_a2b2.clone(),
        coeff.clone(),
        comm2,
    );
    // coeff·(ρ²·a2b2) = (coeff·ρ²)·a2b2  [symm massoc coeff ρ² a2b2].
    let coeff_rho2 = rc.mul(coeff.clone(), rho2.clone()); // defeq mk 12 9
    let coeffr2_a2b2 = rc.mul(coeff_rho2.clone(), a2b2.clone());
    let assoc2 = rc.massoc(coeff.clone(), rho2.clone(), a2b2.clone());
    let s_assoc2 = rc.symm(coeffr2_a2b2.clone(), coeff_r2a2b2.clone(), assoc2);
    // chain eq_inner: coeff·(aa·rbrb) → coeff·(a2b2·ρ²) → coeff·(ρ²·a2b2) → (coeff·ρ²)·a2b2.
    let coeff_inner = rc.mul(coeff.clone(), aa_rbrb.clone());
    let ei0 = rc.trans(
        coeff_inner.clone(),
        coeff_a2b2r2.clone(),
        coeff_r2a2b2.clone(),
        c_lift,
        c_comm2,
    );
    let eq_inner = rc.trans(
        coeff_inner.clone(),
        coeff_r2a2b2.clone(),
        coeffr2_a2b2.clone(),
        ei0,
        s_assoc2,
    );

    // ½·(coeff·(aa·rbrb)) = ½·((coeff·ρ²)·a2b2)  [cong_right half].
    let half_coeffinner = rc.mul(half.clone(), coeff_inner.clone());
    let half_coeffr2a2b2 = rc.mul(half.clone(), coeffr2_a2b2.clone());
    let c_half = mc.cong_mul_right(
        bo,
        half,
        coeff_inner.clone(),
        coeffr2_a2b2.clone(),
        eq_inner,
    );
    // ½·((coeff·ρ²)·a2b2) = (½·(coeff·ρ²))·a2b2  [symm massoc half (coeff·ρ²) a2b2].
    let half_coeffr2 = rc.mul(half.clone(), coeff_rho2.clone()); // defeq mk 12 18
    let halfcoeffr2_a2b2 = rc.mul(half_coeffr2.clone(), a2b2.clone());
    let assoc3 = rc.massoc(half.clone(), coeff_rho2.clone(), a2b2.clone());
    let s_assoc3 = rc.symm(halfcoeffr2_a2b2.clone(), half_coeffr2a2b2.clone(), assoc3);
    // (½·(coeff·ρ²))·a2b2 = (2/3)·a2b2  [bridge mk 12 18 = mk 2 3, cong_left a2b2].
    let bridge = mc.frac_bridge(12, 18, 2, 3, 36); // 12·3 = 2·18 = 36
    let two3_a2b2 = rc.mul(two3.clone(), a2b2.clone());
    let c_final = mc.cong_mul_left(bo, a2b2, half_coeffr2.clone(), two3.clone(), bridge);

    // chain: half_coeffinner → half_coeffr2a2b2 → halfcoeffr2_a2b2 → two3_a2b2.
    let s = rc.trans(
        half_coeffinner.clone(),
        half_coeffr2a2b2.clone(),
        halfcoeffr2_a2b2.clone(),
        c_half,
        s_assoc3,
    );
    rc.trans(half_coeffinner, halfcoeffr2_a2b2, two3_a2b2, s, c_final)
}

/// `reorder : (X + Z) + Y = (X + Y) + Z`.
///   `(X+Z)+Y =[aassoc] X+(Z+Y) =[cong_right X (acomm Z Y)] X+(Y+Z) =[symm aassoc] (X+Y)+Z`.
fn build_reorder(rc: &RingConsts, bo: &EnvDeclBuilder, x: &Expr, z: &Expr, y: &Expr) -> Expr {
    let add_c = rc.add_const();
    let xz = rc.add(x.clone(), z.clone());
    let xz_y = rc.add(xz.clone(), y.clone()); // (X+Z)+Y
    let zy = rc.add(z.clone(), y.clone());
    let x_zy = rc.add(x.clone(), zy.clone()); // X+(Z+Y)
    let yz = rc.add(y.clone(), z.clone());
    let x_yz = rc.add(x.clone(), yz.clone()); // X+(Y+Z)
    let xy = rc.add(x.clone(), y.clone());
    let xy_z = rc.add(xy.clone(), z.clone()); // (X+Y)+Z

    let aassoc1 = rc.aassoc(x.clone(), z.clone(), y.clone()); // (X+Z)+Y = X+(Z+Y)
    let acomm = rc.acomm(z.clone(), y.clone()); // Z+Y = Y+Z
    let cong = rc.cong_right(bo, &add_c, zy.clone(), yz.clone(), x.clone(), acomm); // X+(Z+Y) = X+(Y+Z)
    let aassoc2 = rc.aassoc(x.clone(), y.clone(), z.clone()); // (X+Y)+Z = X+(Y+Z)
    let s_aassoc2 = rc.symm(xy_z.clone(), x_yz.clone(), aassoc2); // X+(Y+Z) = (X+Y)+Z

    let s = rc.trans(xz_y.clone(), x_zy.clone(), x_yz.clone(), aassoc1, cong);
    rc.trans(xz_y, x_yz, xy_z, s, s_aassoc2)
}
