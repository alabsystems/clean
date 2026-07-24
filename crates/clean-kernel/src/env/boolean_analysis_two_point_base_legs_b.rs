// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Leg (B) of the two-point base: `S³ ≥ LHS`, a PURE RATIONAL inequality.
//
// `include!`d into `boolean_analysis_two_point_base_legs.rs`; shares its `use`s
// and the `TwoPointLegConsts` surface.
//
// With `bb := b·b`, `c := (2/9)·bb`, `S := 1 + c`:
//   LHS  := (1 + (2/3)·bb) + (1/81)·(bb·bb)        -- a=1 fourth moment
//   S³   := (S·S)·S                                 -- cube of the rational pivot
//   Δ    := (11/4)·(c·c) + ((c·c)·c)                -- nonneg remainder
//
// The identity `S³ = LHS + Δ` is proved entirely in the `c`-world:
//   (1) `Rat.add_cube 1 c` :  S³ = 1³ + (3·(1²·c) + (3·(1·c²) + c³)),
//   (2) collapse the unit factors                S³ = 1 + (3·c + (3·(c·c) + (c·c)·c)),
//   (3) re-split `3·(c·c) = (1/4)·(c·c) + (11/4)·(c·c)` and reassociate into
//       `LHS_c + Δ` with `LHS_c := (1 + 3·c) + (1/4)·(c·c)`,
//   (4) bridge the coefficients to the `bb`-form moment:
//       `3·c = (2/3)·bb`, `(1/4)·(c·c) = (1/81)·(bb·bb)`.
// Then `LHS ≤ LHS + Δ` (`le_add_of_nonneg_right`, `Δ ≥ 0`) and (the symm of)
// the identity give `LHS ≤ S³` by `Eq.subst`.

impl Environment {
    /// `BoolAnalysis.two_point_S_cube_ge_moment : ∀ b : Rat,
    ///   Rat.le ((1 + (2/3)·(b·b)) + (1/81)·((b·b)·(b·b)))
    ///          (((S·S)·S))`,  `S := 1 + (2/9)·(b·b)`.
    fn register_two_point_s_cube_ge_moment(
        &mut self,
        c: &TwoPointLegConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.two_point_S_cube_ge_moment");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_two_point_s_cube_ge_moment(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// The a=1 fourth moment `(1 + (2/3)·bb) + (1/81)·(bb·bb)`.
fn moment_lhs(c: &TwoPointLegConsts, bb: &Expr) -> Expr {
    let one = c.rat_one.clone();
    let term1 = c.add(one, c.mul(c.frac(2, 3), bb.clone()));
    let bb2 = c.mul(bb.clone(), bb.clone());
    c.add(term1, c.mul(c.frac(1, 81), bb2))
}

/// The nonneg remainder `Δ := (11/4)·(c·c) + ((c·c)·c)`.
fn delta(c: &TwoPointLegConsts, cc: &Expr) -> Expr {
    let cc_sq = c.mul(cc.clone(), cc.clone());
    let cc_cube = c.mul(cc_sq.clone(), cc.clone());
    c.add(c.mul(c.frac(11, 4), cc_sq), cc_cube)
}

/// Build `(type, value)` of leg (B).
fn build_two_point_s_cube_ge_moment(c: &TwoPointLegConsts) -> (Expr, Expr) {
    // ── type ──
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (bv_id, bv) = b.fresh_local(c.rat.clone());
        let bb = c.mul(bv.clone(), bv.clone());
        let cc = c.mul(c.frac(2, 9), bb.clone());
        let s = c.add(c.rat_one.clone(), cc);
        let lhs = moment_lhs(c, &bb);
        let concl = c.le(lhs, c.cube(&s));
        b.finish(b.mk_pi(bv_id, BinderInfo::Default, c.rat.clone(), concl))
    };

    // ── value ──
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (bv_id, bv) = b.fresh_local(c.rat.clone());

        let bb = c.mul(bv.clone(), bv.clone()); // b·b
        let cc = c.mul(c.frac(2, 9), bb.clone()); // c = (2/9)·bb
        let s = c.add(c.rat_one.clone(), cc.clone()); // S = 1 + c
        let s_cube = c.cube(&s); // (S·S)·S
        let lhs = moment_lhs(c, &bb);
        let dlt = delta(c, &cc);
        let lhs_plus_delta = c.add(lhs.clone(), dlt.clone());

        // h_id : S³ = LHS + Δ.
        let h_id = build_cube_identity(c, &b, &bb, &cc);

        // h_delta_nn : 0 ≤ Δ.
        let h_delta_nn = build_delta_nonneg(c, &bv, &bb, &cc);

        // h_le : LHS ≤ LHS + Δ.
        let h_le = c.le_add_of_nonneg_right(&lhs, &dlt, h_delta_nn);

        // Transport the RHS `LHS + Δ → S³` along `symm h_id : LHS+Δ = S³`.
        let motive = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = m.fresh_local(c.rat.clone());
            let body = c.le(lhs.clone(), t);
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_id_sym = c.symm_rat(s_cube.clone(), lhs_plus_delta.clone(), h_id);
        let body = c.subst_rat(motive, lhs_plus_delta, s_cube, h_id_sym, h_le);

        b.finish(b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), body))
    };

    (ty, value)
}

/// `0 ≤ Δ = (11/4)·(c·c) + ((c·c)·c)`, with `c = (2/9)·(b·b) ≥ 0`.
fn build_delta_nonneg(c: &TwoPointLegConsts, _bv: &Expr, bb: &Expr, cc: &Expr) -> Expr {
    let coeff_29 = c.frac(2, 9);
    // 0 ≤ b·b  (sq_nonneg of b is `0 ≤ b·b`; `bb = b·b`).
    let h_bb_nn = c.sq_nonneg(_bv); // Rat.sq_nonneg b : 0 ≤ b·b
                                    // 0 ≤ c = (2/9)·bb.
    let h_c_nn = c.mul_nonneg(&coeff_29, bb, c.lit_nonneg(2, 9), h_bb_nn);

    // 0 ≤ c·c.
    let cc_sq = c.mul(cc.clone(), cc.clone());
    let h_cc_nn = c.mul_nonneg(cc, cc, h_c_nn.clone(), h_c_nn.clone());

    // 0 ≤ (11/4)·(c·c).
    let term1 = c.mul(c.frac(11, 4), cc_sq.clone());
    let h_term1 = c.mul_nonneg(&c.frac(11, 4), &cc_sq, c.lit_nonneg(11, 4), h_cc_nn.clone());

    // 0 ≤ (c·c)·c.
    let term2 = c.mul(cc_sq.clone(), cc.clone());
    let h_term2 = c.mul_nonneg(&cc_sq, cc, h_cc_nn, h_c_nn);

    // 0 ≤ term1 + term2  via `term1 ≤ term1 + term2` and `le_trans 0 term1 (…)`.
    let h_t1_le_sum = c.le_add_of_nonneg_right(&term1, &term2, h_term2);
    let sum = c.add(term1.clone(), term2.clone());
    c.le_trans(&c.rat_zero.clone(), &term1, &sum, h_term1, h_t1_le_sum)
}

/// `S³ = LHS + Δ`. Pure ring identity (see module header).
fn build_cube_identity(
    c: &TwoPointLegConsts,
    parent: &EnvDeclBuilder,
    bb: &Expr,
    cc: &Expr,
) -> Expr {
    let one = c.rat_one.clone();
    let s = c.add(one.clone(), cc.clone()); // S = 1 + c
    let s_cube = c.cube(&s); // (S·S)·S

    // `3 := (1+1)+1` (matches `Rat.add_cube`'s coefficient).
    let three = c.add(c.add(one.clone(), one.clone()), one.clone());

    // ── (1) add_cube 1 c : S³ = RHS0 ──
    //   RHS0 = ((1·1)·1) + ( (3·((1·1)·c)) + ( (3·((1·c)·c)) + ((c·c)·c) ) ).
    let one_cube = c.mul(c.mul(one.clone(), one.clone()), one.clone()); // (1·1)·1
    let one2_c = c.mul(c.mul(one.clone(), one.clone()), cc.clone()); // (1·1)·c
    let one_c2 = c.mul(c.mul(one.clone(), cc.clone()), cc.clone()); // (1·c)·c
    let c_cube = c.mul(c.mul(cc.clone(), cc.clone()), cc.clone()); // (c·c)·c
    let three_one2_c = c.mul(three.clone(), one2_c.clone());
    let three_one_c2 = c.mul(three.clone(), one_c2.clone());
    let tail0 = c.add(three_one_c2.clone(), c_cube.clone());
    let mid0 = c.add(three_one2_c.clone(), tail0.clone());
    let rhs0 = c.add(one_cube.clone(), mid0.clone());
    let h_ac = c.add_cube(&one, cc); // S³ = RHS0

    // ── (2) collapse unit factors ──
    //   (1·1)·1 = 1 ; (1·1)·c = c ; (1·c)·c = c·c.
    let cc_sq = c.mul(cc.clone(), cc.clone());

    // e_onecube : (1·1)·1 = 1.   ((1·1)·1 =[mul_one] (1·1) =[mul_one] 1).
    let one_one = c.mul(one.clone(), one.clone()); // 1·1
    let e_oc_1 = c.mul_one(&one_one); // (1·1)·1 = 1·1
    let e_oc_2 = c.mul_one(&one); // 1·1 = 1
    let e_onecube = c.trans_rat(
        one_cube.clone(),
        one_one.clone(),
        one.clone(),
        e_oc_1,
        e_oc_2,
    );

    // e_one2c : (1·1)·c = c.   ((1·1)·c =[congr_left (1·1=1)] 1·c =[one_mul] c).
    let one_c = c.mul(one.clone(), cc.clone()); // 1·c
    let e11 = c.mul_one(&one); // 1·1 = 1
    let cl_one2c = c.congr_mul_left(parent, cc, one_one.clone(), one.clone(), e11.clone());
    let e_one2c = c.trans_rat(
        one2_c.clone(),
        one_c.clone(),
        cc.clone(),
        cl_one2c,
        c.one_mul(cc),
    );

    // e_onec2 : (1·c)·c = c·c.   ((1·c)·c =[congr_left (1·c=c)] c·c).
    let e_onemulc = c.one_mul(cc); // 1·c = c
    let e_onec2 = c.congr_mul_left(parent, cc, one_c.clone(), cc.clone(), e_onemulc);

    // Build U = 1 + (3·c + (3·(c·c) + (c·c)·c)).
    let three_c = c.mul(three.clone(), cc.clone());
    let three_cc_sq = c.mul(three.clone(), cc_sq.clone());
    let u_tail = c.add(three_cc_sq.clone(), c_cube.clone());
    let u_mid = c.add(three_c.clone(), u_tail.clone());
    let u = c.add(one.clone(), u_mid.clone());

    // Rewrite RHS0 → U by the three unit collapses (congr on the matching slot).
    //   step a: 3·((1·1)·c) = 3·c     (congr_mul_right three e_one2c).
    let ca = c.congr_mul_right(parent, &three, one2_c.clone(), cc.clone(), e_one2c);
    //   step b: 3·((1·c)·c) = 3·(c·c) (congr_mul_right three e_onec2).
    let cb = c.congr_mul_right(parent, &three, one_c2.clone(), cc_sq.clone(), e_onec2);

    // Assemble RHS0 = U via nested congrArg.
    //   tail: (3·(1·c²)) + c³  →  (3·c²) + c³   (congr_add_left over c³).
    let h_tail = c.congr_add_left(
        parent,
        &c_cube,
        three_one_c2.clone(),
        three_cc_sq.clone(),
        cb,
    );
    //   mid: (3·(1²·c)) + tail0  →  (3·c) + u_tail.
    //     first rewrite the left summand: congr_add_left over tail0 with ca,
    //     then rewrite the right summand: congr_add_right over (3·c) with h_tail.
    let mid_a = c.add(three_c.clone(), tail0.clone());
    let h_mid_1 = c.congr_add_left(parent, &tail0, three_one2_c.clone(), three_c.clone(), ca);
    let h_mid_2 = c.congr_add_right(parent, &three_c, tail0.clone(), u_tail.clone(), h_tail);
    let h_mid = c.trans_rat(mid0.clone(), mid_a.clone(), u_mid.clone(), h_mid_1, h_mid_2);
    //   rhs0: (1·1·1) + mid0  →  1 + u_mid.
    let rhs0_a = c.add(one.clone(), mid0.clone());
    let h_r_1 = c.congr_add_left(parent, &mid0, one_cube.clone(), one.clone(), e_onecube);
    let h_r_2 = c.congr_add_right(parent, &one, mid0.clone(), u_mid.clone(), h_mid);
    let h_collapse = c.trans_rat(rhs0.clone(), rhs0_a.clone(), u.clone(), h_r_1, h_r_2);

    // ── (3) split 3·(c·c) = (1/4)·(c·c) + (11/4)·(c·c), regroup to LHS_c + Δ ──
    // LHS_c := (1 + 3·c) + (1/4)·(c·c).   Δ := (11/4)·(c·c) + (c·c)·c.
    let q14 = c.frac(1, 4);
    let q114 = c.frac(11, 4);
    let q14_cc = c.mul(q14.clone(), cc_sq.clone());
    let q114_cc = c.mul(q114.clone(), cc_sq.clone());

    // e_split : 3·(c·c) = (1/4)·(c·c) + (11/4)·(c·c).
    //   RHS = ((1/4)+(11/4))·(c·c) [symm right_distrib] = 3·(c·c) [bridge (1/4)+(11/4)=3, congr_mul_left].
    let sum_coeff = c.add(q14.clone(), q114.clone()); // (1/4)+(11/4) (defeq mk … = 3)
    let rdist = Expr::apps(
        c.rat_right_distrib.clone(),
        [q14.clone(), q114.clone(), cc_sq.clone()],
    ); // ((1/4)+(11/4))·(c·c) = (1/4)(c·c)+(11/4)(c·c)
    let split_sum = c.add(q14_cc.clone(), q114_cc.clone());
    let sum_coeff_cc = c.mul(sum_coeff.clone(), cc_sq.clone());
    // bridge (1/4)+(11/4) = 3.  `Rat.add (mk 1 4)(mk 11 4)` ground-reduces (raw
    // `mk (n_a·d_b + n_b·d_a)(d_a·d_b)`) to `mk (1·4 + 11·4)(4·4) = mk 48 16`;
    // `three = (1+1)+1` defeq `mk 3 1`. bridge mk 48 16 = mk 3 1 (48·1 = 3·16 = 48).
    let e_coeff = build_coeff_eq(c, &sum_coeff, &three, 48, 16, 3, 1, 48);
    // congr_mul_left over (c·c): sum_coeff·(c·c) = three·(c·c).
    let cl_coeff = c.congr_mul_left(parent, &cc_sq, sum_coeff.clone(), three.clone(), e_coeff);
    // e_split : 3·(c·c) = (1/4)(c·c)+(11/4)(c·c).
    //   three·(c·c) =[symm cl_coeff] sum_coeff·(c·c) =[rdist] split_sum.
    let e_split = c.trans_rat(
        three_cc_sq.clone(),
        sum_coeff_cc.clone(),
        split_sum.clone(),
        c.symm_rat(sum_coeff_cc.clone(), three_cc_sq.clone(), cl_coeff),
        rdist,
    );

    // Now reassociate `U = 1 + (3c + (3cc + c³))` to the LEFT-associated
    // `((1 + 3c) + q14_cc) + Δ`, matching the PIN moment's `(X + Y) + …` shape,
    // with `Δ := q114_cc + c³` and the split `3cc = q14_cc + q114_cc`.
    let delta_e = c.add(q114_cc.clone(), c_cube.clone()); // Δ = (11/4)cc + c³

    // Target form T := ((1 + 3c) + q14_cc) + Δ.
    let one_plus_3c = c.add(one.clone(), three_c.clone()); // 1 + 3c
    let lhsc = c.add(one_plus_3c.clone(), q14_cc.clone()); // (1+3c) + q14_cc  = LHS_c (3·c form)
    let lhsc_plus_delta = c.add(lhsc.clone(), delta_e.clone());

    // We prove U = T directly by associativity normalisation, in steps:
    //   u_tail = 3cc + c³ → (q14_cc + q114_cc) + c³   [congr_add_left e_split]
    let split_plus_ccube = c.add(split_sum.clone(), c_cube.clone());
    let h_ut = c.congr_add_left(
        parent,
        &c_cube,
        three_cc_sq.clone(),
        split_sum.clone(),
        e_split,
    );
    //   (q14_cc + q114_cc) + c³ = q14_cc + (q114_cc + c³) = q14_cc + Δ   [add_assoc]
    let q14_plus_delta = c.add(q14_cc.clone(), delta_e.clone());
    let h_assoc_ut = Expr::apps(
        c.rat_add_assoc.clone(),
        [q14_cc.clone(), q114_cc.clone(), c_cube.clone()],
    ); // (q14+q114)+c³ = q14+(q114+c³)
    let h_ut2 = c.trans_rat(
        u_tail.clone(),
        split_plus_ccube.clone(),
        q14_plus_delta.clone(),
        h_ut,
        h_assoc_ut,
    );
    //   u_mid = 3c + u_tail → 3c + (q14_cc + Δ)   [congr_add_right]
    let three_c_plus_q14d = c.add(three_c.clone(), q14_plus_delta.clone());
    let h_um = c.congr_add_right(
        parent,
        &three_c,
        u_tail.clone(),
        q14_plus_delta.clone(),
        h_ut2,
    );
    //   U = 1 + u_mid → 1 + (3c + (q14_cc + Δ))   [congr_add_right]
    let one_plus_midform = c.add(one.clone(), three_c_plus_q14d.clone());
    let h_u_step1 = c.congr_add_right(parent, &one, u_mid.clone(), three_c_plus_q14d.clone(), h_um);
    //   Now associate `1 + (3c + (q14_cc + Δ))` to `((1+3c) + q14_cc) + Δ`.
    //   In three add_assoc rewrites (each (a+(b+x)) = (a+b)+x form):
    //   step A: 1 + (3c + (q14_cc+Δ)) = (1 + 3c) + (q14_cc + Δ)  [symm add_assoc 1 3c (q14+Δ)]
    let onep3c_plus_q14d = c.add(one_plus_3c.clone(), q14_plus_delta.clone());
    let h_assoc_a = Expr::apps(
        c.rat_add_assoc.clone(),
        [one.clone(), three_c.clone(), q14_plus_delta.clone()],
    ); // (1+3c)+(q14+Δ) = 1+(3c+(q14+Δ))
    let h_u_step2 = c.trans_rat(
        u.clone(),
        one_plus_midform.clone(),
        onep3c_plus_q14d.clone(),
        h_u_step1,
        c.symm_rat(
            onep3c_plus_q14d.clone(),
            one_plus_midform.clone(),
            h_assoc_a,
        ),
    );
    //   step B: (1+3c) + (q14_cc + Δ) = ((1+3c) + q14_cc) + Δ  [symm add_assoc (1+3c) q14_cc Δ]
    let h_assoc_b = Expr::apps(
        c.rat_add_assoc.clone(),
        [one_plus_3c.clone(), q14_cc.clone(), delta_e.clone()],
    ); // ((1+3c)+q14)+Δ = (1+3c)+(q14+Δ)
    let h_u2 = c.trans_rat(
        u.clone(),
        onep3c_plus_q14d.clone(),
        lhsc_plus_delta.clone(),
        h_u_step2,
        c.symm_rat(lhsc_plus_delta.clone(), onep3c_plus_q14d.clone(), h_assoc_b),
    );

    // ── (4) bridge LHS_c (left-assoc `(1+3c)+q14_cc`) → LHS_bb (the PIN moment) ──
    // LHS_c  = (1 + 3·c) + (1/4)·(c·c).
    // LHS_bb = (1 + (2/3)·bb) + (1/81)·(bb·bb).
    // Rewrite (a) 3·c → (2/3)·bb  and (b) (1/4)·(c·c) → (1/81)·(bb·bb).
    let bb2 = c.mul(bb.clone(), bb.clone());
    let two3_bb = c.mul(c.frac(2, 3), bb.clone());
    let one81_bb2 = c.mul(c.frac(1, 81), bb2.clone());

    // (a) e_3c : 3·c = (2/3)·bb.
    let e_3c = build_3c_eq(c, parent, &three, bb, cc);
    // (b) e_q14cc : (1/4)·(c·c) = (1/81)·(bb·bb).
    let e_q14cc = build_q14cc_eq(c, parent, bb, cc, &cc_sq);

    // LHS_c = (1+3c) + (1/4 cc).
    //   inner (1+3c) → (1+(2/3)bb)  [congr_add_right over 1, rewriting 3c]
    let one_plus_23bb = c.add(one.clone(), two3_bb.clone());
    let h_in = c.congr_add_right(parent, &one, three_c.clone(), two3_bb.clone(), e_3c);
    //   outer-left: (1+3c)+(1/4 cc) → (1+(2/3)bb)+(1/4 cc)  [congr_add_left over q14_cc]
    let lhs_step1 = c.add(one_plus_23bb.clone(), q14_cc.clone());
    let h_o1 = c.congr_add_left(
        parent,
        &q14_cc,
        one_plus_3c.clone(),
        one_plus_23bb.clone(),
        h_in,
    );
    //   outer-right: (1+(2/3)bb)+(1/4 cc) → (1+(2/3)bb)+(1/81 bb²) = LHS_bb  [congr_add_right]
    let lhs_bb = c.add(one_plus_23bb.clone(), one81_bb2.clone());
    let h_o2 = c.congr_add_right(
        parent,
        &one_plus_23bb,
        q14_cc.clone(),
        one81_bb2.clone(),
        e_q14cc,
    );
    let h_lhs = c.trans_rat(lhsc.clone(), lhs_step1.clone(), lhs_bb.clone(), h_o1, h_o2);
    //   lift to (…)+Δ: LHS_c + Δ → LHS_bb + Δ  [congr_add_left over Δ].
    let lhsbb_plus_delta = c.add(lhs_bb.clone(), delta_e.clone());
    let h_lift = c.congr_add_left(parent, &delta_e, lhsc.clone(), lhs_bb.clone(), h_lhs);

    // ── chain everything: S³ = RHS0 = U = LHS_c+Δ = LHS_bb+Δ ──
    let t1 = c.trans_rat(s_cube.clone(), rhs0.clone(), u.clone(), h_ac, h_collapse);
    let t2 = c.trans_rat(s_cube.clone(), u.clone(), lhsc_plus_delta.clone(), t1, h_u2);
    c.trans_rat(s_cube, lhsc_plus_delta, lhsbb_plus_delta, t2, h_lift)
}

/// `e : 3·c = (2/3)·bb`, with `c = (2/9)·bb`, `3 = (1+1)+1`.
///   `3·c = 3·((2/9)·bb) =[symm mul_assoc] (3·(2/9))·bb =[bridge 3·(2/9)=2/3] (2/3)·bb`.
fn build_3c_eq(
    c: &TwoPointLegConsts,
    parent: &EnvDeclBuilder,
    three: &Expr,
    bb: &Expr,
    cc: &Expr,
) -> Expr {
    let q29 = c.frac(2, 9);
    let q23 = c.frac(2, 3);
    let three_c = c.mul(three.clone(), cc.clone()); // 3·c   (cc = (2/9)·bb)
    let three_q29 = c.mul(three.clone(), q29.clone()); // 3·(2/9)  (defeq mk 6 9)
    let three_q29_bb = c.mul(three_q29.clone(), bb.clone());
    let q23_bb = c.mul(q23.clone(), bb.clone());
    // symm mul_assoc 3 (2/9) bb : (3·(2/9))·bb = 3·((2/9)·bb).
    let assoc = c.mul_assoc(three, &q29, bb); // (3·(2/9))·bb = 3·((2/9)·bb)
    let s0 = c.symm_rat(three_q29_bb.clone(), three_c.clone(), assoc); // 3·c = (3·(2/9))·bb
                                                                       // bridge 3·(2/9) = 2/3.  3·(2/9) defeq mk 6 9 ; 2/3 = mk 2 3 ; 6·3=2·9=18.
    let e_coeff = build_coeff_eq(c, &three_q29, &q23, 6, 9, 2, 3, 18);
    let cl = c.congr_mul_left(parent, bb, three_q29.clone(), q23.clone(), e_coeff);
    c.trans_rat(three_c, three_q29_bb, q23_bb, s0, cl)
}

/// `e : (1/4)·(c·c) = (1/81)·(bb·bb)`, with `c = (2/9)·bb`.
///   `c·c = ((2/9)·bb)·((2/9)·bb) =[mul_mul_mul_comm] ((2/9)·(2/9))·(bb·bb)`,
///   then `(1/4)·(c·c) =[congr] (1/4)·(((2/9)²)·(bb·bb))
///         =[symm mul_assoc] ((1/4)·(2/9)²)·(bb·bb) =[bridge] (1/81)·(bb·bb)`.
fn build_q14cc_eq(
    c: &TwoPointLegConsts,
    parent: &EnvDeclBuilder,
    bb: &Expr,
    cc: &Expr,
    cc_sq: &Expr,
) -> Expr {
    let q29 = c.frac(2, 9);
    let q14 = c.frac(1, 4);
    let q181 = c.frac(1, 81);
    let bb2 = c.mul(bb.clone(), bb.clone());

    // c·c = ((2/9)·bb)·((2/9)·bb) = ((2/9)·(2/9))·(bb·bb)   [mul_mul_mul_comm].
    let q29_sq = c.mul(q29.clone(), q29.clone()); // (2/9)·(2/9)  (defeq mk 4 81)
    let q29sq_bb2 = c.mul(q29_sq.clone(), bb2.clone());
    let mmmc = Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_mul_mul_comm"), vec![]),
        [q29.clone(), bb.clone(), q29.clone(), bb.clone()],
    ); // (cc)·(cc) = ((2/9)(2/9))·(bb·bb)  — note cc_sq defeq this LHS
       // (1/4)·(c·c) = (1/4)·(((2/9)²)·(bb·bb))   [congr_mul_right q14 mmmc].
    let q14_cc = c.mul(q14.clone(), cc_sq.clone());
    let q14_q29sq_bb2 = c.mul(q14.clone(), q29sq_bb2.clone());
    let c1 = c.congr_mul_right(parent, &q14, cc_sq.clone(), q29sq_bb2.clone(), mmmc);
    // = ((1/4)·(2/9)²)·(bb·bb)   [symm mul_assoc q14 q29sq bb2].
    let q14_q29sq = c.mul(q14.clone(), q29_sq.clone()); // (1/4)·(2/9)²  (defeq mk 4 324)
    let q14q29sq_bb2 = c.mul(q14_q29sq.clone(), bb2.clone());
    let assoc = c.mul_assoc(&q14, &q29_sq, &bb2); // (q14·q29sq)·bb2 = q14·(q29sq·bb2)
    let s2 = c.symm_rat(q14q29sq_bb2.clone(), q14_q29sq_bb2.clone(), assoc);
    // bridge (1/4)·(2/9)² = 1/81.  (1/4)·(4/81) defeq mk 4 324 ; 1/81 = mk 1 81 ; 4·81 = 1·324 = 324.
    let e_coeff = build_coeff_eq(c, &q14_q29sq, &q181, 4, 324, 1, 81, 324);
    let one81_bb2 = c.mul(q181.clone(), bb2.clone());
    let c3 = c.congr_mul_left(parent, &bb2, q14_q29sq.clone(), q181.clone(), e_coeff);
    // chain: q14_cc → q14_q29sq_bb2 → q14q29sq_bb2 → one81_bb2.
    let t1 = c.trans_rat(q14_cc, q14_q29sq_bb2.clone(), q14q29sq_bb2.clone(), c1, s2);
    c.trans_rat(
        c.mul(q14.clone(), cc_sq.clone()),
        q14q29sq_bb2,
        one81_bb2,
        t1,
        c3,
    )
}

/// A coefficient equality `coeff_a = coeff_b` between two `Rat` expressions that
/// are DEFEQ to `Rat.mk (Int.ofNat pn) pd` resp. `Rat.mk (Int.ofNat qn) qd`,
/// proved by a single lowest-terms `Quot.sound` bridge (`pn·qd = qn·pd = prod`).
///
/// `coeff_a` may be a SYMBOLIC product (e.g. `3·(2/9)`) that ground-reduces by
/// defeq to `mk pn pd`; the returned proof has type `coeff_a = coeff_b` because
/// the bridge's `mk pn pd = mk qn qd` type is defeq to it.
fn build_coeff_eq(
    c: &TwoPointLegConsts,
    coeff_a: &Expr,
    coeff_b: &Expr,
    pn: u64,
    pd: u64,
    qn: u64,
    qd: u64,
    prod: u64,
) -> Expr {
    // bridge : mk pn pd = mk qn qd  (defeq to coeff_a = coeff_b).
    let bridge = c.frac_bridge(pn, pd, qn, qd, prod);
    // Re-cast the endpoints to the symbolic coeff_a / coeff_b via refl trans
    // (defeq makes these the same proposition).
    let mk_p = c.frac(pn, pd);
    let mk_q = c.frac(qn, qd);
    let s1 = c.trans_rat(
        coeff_a.clone(),
        mk_p.clone(),
        mk_q.clone(),
        c.refl_rat(coeff_a.clone()),
        bridge,
    );
    c.trans_rat(
        coeff_a.clone(),
        mk_q,
        coeff_b.clone(),
        s1,
        c.refl_rat(coeff_b.clone()),
    )
}
