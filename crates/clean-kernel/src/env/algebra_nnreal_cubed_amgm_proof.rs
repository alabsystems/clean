// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Proof bodies for `algebra_nnreal_cubed_amgm.rs` (kept here for the 500-line
// cap). `include!`d into that module; shares its `use` imports and the
// `CubedAmGmConsts` / `NNConsts` helpers.

/// `E : Rat.mul N_n y = add_n(y)` (the numeral-to-additive bridge, `n ≥ 1`).
///
/// `N_1 = Rat.one`, `add_1(y) = y`; base is `Rat.one_mul y`. The step uses
/// `right_distrib N_k 1 y` (`mul (N_k+1) y = mul N_k y + mul 1 y`), `one_mul`
/// to clean the trailing `mul 1 y`, then `congrArg (·+y)` of the running eq.
fn build_mul_numeral_eq_add_n(
    c: &CubedAmGmConsts,
    parent: &EnvDeclBuilder,
    y: &Expr,
    n: u32,
) -> Expr {
    debug_assert!(n >= 1);
    // base : mul N_1 y = y  (one_mul). running LHS numeral N_k, running sum add_k.
    let mut num_k = c.rat_one.clone(); // N_1
    let mut sum_k = y.clone(); // add_1(y) = y
    let mut eq_k = c.one_mul(y); // mul N_1 y = y
    for _ in 1..n {
        let num_next = c.radd(&num_k, &c.rat_one); // N_{k+1} = N_k + 1
        let sum_next = c.radd(&sum_k, y); // add_{k+1}(y) = add_k(y) + y
        let mul_nk_y = c.rmul(&num_k, y); // mul N_k y
        let mul_1_y = c.rmul(&c.rat_one, y); // mul 1 y
                                             // d1 : mul N_{k+1} y = (mul N_k y) + (mul 1 y)   [right_distrib N_k 1 y].
        let d1 = c.right_distrib(&num_k, &c.rat_one, y);
        let rd_rhs = c.radd(&mul_nk_y, &mul_1_y); // (mul N_k y) + (mul 1 y)
                                                  // d2 : (mul N_k y)+(mul 1 y) = (mul N_k y)+y  [congr ((mul N_k y)+·)(one_mul y)].
        let add_left_fn = {
            let mut fb = EnvDeclBuilder::child_of(parent);
            let (v_id, v) = fb.fresh_local(c.rat.clone());
            let body = c.radd(&mul_nk_y, &v);
            fb.finish_child(fb.mk_lam(v_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let d2 = c.congr_arg(&mul_1_y, y, add_left_fn, c.one_mul(y));
        let nk_plus_y = c.radd(&mul_nk_y, y); // (mul N_k y) + y
                                              // d3 : (mul N_k y)+y = add_k(y)+y  [congr (·+y)(eq_k)].
        let add_right_fn = {
            let mut fb = EnvDeclBuilder::child_of(parent);
            let (v_id, v) = fb.fresh_local(c.rat.clone());
            let body = c.radd(&v, y);
            fb.finish_child(fb.mk_lam(v_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let d3 = c.congr_arg(&mul_nk_y, &sum_k, add_right_fn, eq_k);
        let sum_k_plus_y = c.radd(&sum_k, y); // add_k(y) + y  (= sum_next)
        let mul_next = c.rmul(&num_next, y); // mul N_{k+1} y
                                             // chain: mul N_{k+1} y = rd_rhs = nk_plus_y = sum_next.
        let ch = c.eq_trans(&mul_next, &rd_rhs, &nk_plus_y, d1, d2);
        let ch = c.eq_trans(&mul_next, &nk_plus_y, &sum_k_plus_y, ch, d3);
        eq_k = ch;
        num_k = num_next;
        sum_k = sum_next;
    }
    let _ = (num_k, sum_k);
    eq_k
}

/// `Rat.cube_amgm_additive` proof body.
fn build_rat_cube_amgm_additive(c: &CubedAmGmConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (p_id, p) = b.fresh_local(c.rat.clone());
    let (q_id, q) = b.fresh_local(c.rat.clone());
    let hp_ty = c.nonneg(&p);
    let (hp_id, hp) = b.fresh_local(hp_ty.clone());
    let hq_ty = c.nonneg(&q);
    let (hq_id, hq) = b.fresh_local(hq_ty.clone());

    // ── the multiplicative-numeral forms (exactly cube_amgm_two_one's) ──
    let two_num = c.rnumeral(2); // 1+1
    let tsv_num = c.rnumeral(AMGM_COEFF); // 27num
    let p2q = c.rsq_t(&p, &q); // (p·p)·q
    let mul27 = c.rmul(&tsv_num, &p2q); // mul 27num (p²q)
    let two_p = c.rmul(&two_num, &p); // mul 2num p
    let old_base = c.radd(&two_p, &q); // (mul 2num p) + q
    let old_cube = c.rcube(&old_base); // ((mul 2num p)+q)³

    // amgm : Rat.le (mul 27num p²q) (((mul 2num p)+q)³).
    let amgm = Expr::apps(
        c.cube_amgm_two_one.clone(),
        [p.clone(), q.clone(), hp.clone(), hq.clone()],
    );

    // ── the additive target forms ──
    let add27 = c.radd_n(&p2q, AMGM_COEFF); // add27(p²q)
    let new_base = c.radd(&c.radd(&p, &p), &q); // (p+p)+q
    let new_cube = c.rcube(&new_base);

    // E1 : mul 27num (p²q) = add27(p²q).
    let e1 = build_mul_numeral_eq_add_n(c, &b, &p2q, AMGM_COEFF);
    // E2 : mul 2num p = p+p.
    let e2 = build_mul_numeral_eq_add_n(c, &b, &p, 2);

    // E2 lifted to the cube base then the cube:
    //   (mul 2num p)+q = (p+p)+q   [congr (·+q) E2],
    //   ((mul 2num p)+q)³ = ((p+p)+q)³   [congr cube of the base eq].
    let base_eq = {
        let add_q_fn = {
            let mut fb = EnvDeclBuilder::child_of(&b);
            let (v_id, v) = fb.fresh_local(c.rat.clone());
            let body = c.radd(&v, &q);
            fb.finish_child(fb.mk_lam(v_id, BinderInfo::Default, c.rat.clone(), body))
        };
        c.congr_arg(&two_p, &c.radd(&p, &p), add_q_fn, e2)
    };
    let cube_eq = {
        let cube_fn = {
            let mut fb = EnvDeclBuilder::child_of(&b);
            let (v_id, v) = fb.fresh_local(c.rat.clone());
            let body = c.rcube(&v);
            fb.finish_child(fb.mk_lam(v_id, BinderInfo::Default, c.rat.clone(), body))
        };
        c.congr_arg(&old_base, &new_base, cube_fn, base_eq)
    };

    // Step A: rewrite the LHS  mul27 → add27  in amgm.
    //   motive_lhs t := Rat.le t old_cube.   subst along E1 (mul27 = add27).
    let motive_lhs = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.rle(&t, &old_cube);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let step_a = c.subst(motive_lhs, &mul27, &add27, e1, amgm); // Rat.le add27 old_cube

    // Step B: rewrite the cube  old_cube → new_cube.
    //   motive_rhs t := Rat.le add27 t.   subst along cube_eq (old_cube = new_cube).
    let motive_rhs = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.rle(&add27, &t);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let proof = c.subst(motive_rhs, &old_cube, &new_cube, cube_eq, step_a); // Rat.le add27 new_cube

    let e = b.mk_lam(hq_id, BinderInfo::Default, hq_ty, proof);
    let e = b.mk_lam(hp_id, BinderInfo::Default, hp_ty, e);
    let e = b.mk_lam(q_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(p_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// `NNReal.CauSeq.cubed_amgm` proof body — the pointwise lift.
///
/// `CauSeq.le L R = ∀ ε>0 ∃N ∀n≥N, vL n < vR n + ε`. We take `N := n` (any
/// witness; the predicate is closed under `≥`, but we discharge it for every
/// `n` directly via `Exists.intro` at a fixed cap and the `∀n≥cap` body). At
/// each index the carrier ops push through `Rat.add`/`Rat.mul` on `.val` by
/// `Eq.refl`, so `vL n ≡ add27 (vP n² vQ n)` and `vR n ≡ ((vP n+vP n)+vQ n)³`;
/// `Rat.cube_amgm_additive` gives `vL n ≤ vR n`, and `vR n < vR n + ε`
/// (`add_lt_add_left` + `add_zero`), chained by `Rat.lt_of_le_of_lt`.
fn build_causeq_cubed_amgm(c: &CubedAmGmConsts) -> Expr {
    let additive = Expr::const_(Name::from_string("Rat.cube_amgm_additive"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (f_id, f) = b.fresh_local(c.causeq.clone());
    let (g_id, g) = b.fresh_local(c.causeq.clone());

    // The CauSeq LHS/RHS (so the goal type unfolds to ∀ε∃N∀n, vL n < vR n + ε).
    let cau_lhs = cau_add_n(c, &cau_sq_t(c, &f, &g), AMGM_COEFF);
    let base = c.cau_add(&c.cau_add(&f, &f), &g);
    let cau_rhs = cau_cube(c, &base);

    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.rlt(&c.rat_zero, &eps);
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    // Witness cap `N := Nat.zero`; the body proves the pointwise `<` for all n.
    let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // body : ∀ n, Nat.le 0 n → vL n < vR n + ε.
    let body_fn = {
        let mut bn = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bn.fresh_local(c.nat.clone());
        let hle_ty = c.nat_le(&nat_zero, &m);
        let (hle_id, _hle) = bn.fresh_local(hle_ty.clone());

        // vP n, vQ n and the per-point nonneg facts.
        let vp = c.vseq(&f, &m);
        let vq = c.vseq(&g, &m);
        let h0vp = c.property_seq(&f, &m); // 0 ≤ vP n
        let h0vq = c.property_seq(&g, &m); // 0 ≤ vQ n

        // vL n ≡ add27 ((vP·vP)·vQ) ; vR n ≡ (((vP+vP)+vQ)·…)·… by val defeq.
        let vl = c.radd_n(&c.rsq_t(&vp, &vq), AMGM_COEFF);
        let vr_base = c.radd(&c.radd(&vp, &vp), &vq);
        let vr = c.rcube(&vr_base);

        // h_le : vL n ≤ vR n  := Rat.cube_amgm_additive vP vQ h0vP h0vQ.
        let h_le = Expr::apps(additive.clone(), [vp.clone(), vq.clone(), h0vp, h0vq]);

        // h_lt : vR n < vR n + ε.
        //   add_lt_add_left 0 ε (vR n) hpos : (vR n + 0) < (vR n + ε); then
        //   subst (vR n + 0) → vR n along Rat.add_zero (vR n).
        let vr_plus_eps = c.radd(&vr, &eps);
        let step = c.add_lt_add_left(&c.rat_zero, &eps, &vr, hpos.clone());
        let vr_plus_zero = c.radd(&vr, &c.rat_zero);
        let add_zero_vr = c.add_zero(&vr); // vR n + 0 = vR n
        let motive = {
            let mut m2 = EnvDeclBuilder::child_of(&bn);
            let (t_id, t) = m2.fresh_local(c.rat.clone());
            let body = c.rlt(&t, &vr_plus_eps);
            m2.finish_child(m2.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_lt = c.subst(motive, &vr_plus_zero, &vr, add_zero_vr, step); // vR n < vR n + ε

        // chain : vL n < vR n + ε  := lt_of_le_of_lt (vL n)(vR n)(vR n+ε) h_le h_lt.
        let proof = c.lt_of_le_of_lt(&vl, &vr, &vr_plus_eps, h_le, h_lt);

        let e = bn.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
        bn.finish_child(bn.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e))
    };

    // ∃ N, ∀ n, N≤n → vL n < vR n + ε   via Exists.intro at N := 0.
    let pred = build_pred_n(c, &b, &cau_lhs, &cau_rhs, &eps);
    let intro = Expr::apps(
        c.exists_intro.clone(),
        [c.nat.clone(), pred, nat_zero.clone(), body_fn],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, intro);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), e);
    b.finish(e)
}

/// The `Exists` predicate `fun N => ∀ n, Nat.le N n → vseq L n < vseq R n + ε`,
/// for the `CauSeq.le L R` unfolding.
fn build_pred_n(
    c: &CubedAmGmConsts,
    parent: &EnvDeclBuilder,
    cau_l: &Expr,
    cau_r: &Expr,
    eps: &Expr,
) -> Expr {
    let mut bn = EnvDeclBuilder::child_of(parent);
    let (cap_id, cap) = bn.fresh_local(c.nat.clone());
    let inner = {
        let mut bm = EnvDeclBuilder::child_of(&bn);
        let (m_id, m) = bm.fresh_local(c.nat.clone());
        let hle = c.nat_le(&cap, &m);
        let (hle_id, _h) = bm.fresh_local(hle.clone());
        let concl = c.rlt(&c.vseq(cau_l, &m), &c.radd(&c.vseq(cau_r, &m), eps));
        let e = bm.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        bm.finish_child(bm.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e))
    };
    bn.finish_child(bn.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), inner))
}

/// `NNReal.cubed_amgm` proof body — nested `Quot.ind`² over the `CauSeq` core.
fn build_nnreal_cubed_amgm(c: &CubedAmGmConsts, nn: &NNConsts) -> Expr {
    let core = Expr::const_(Name::from_string("NNReal.CauSeq.cubed_amgm"), vec![]);
    let nnreal = nn.nnreal.clone();

    let mut b = EnvDeclBuilder::new();
    let (p_id, p) = b.fresh_local(nnreal.clone());
    let (q_id, q) = b.fresh_local(nnreal.clone());

    // motive over P: M P := NNReal.le (add27 (P²Q)) (((P+P)+Q)³).
    let motive_p = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = mb.fresh_local(nnreal.clone());
        let lhs = nn.add_n(&nn.sq_t(&x, &q), AMGM_COEFF);
        let rhs = nn.cube(&nn.two_plus(&x, &q));
        let body = nn.le(&lhs, &rhs);
        mb.finish_child(mb.mk_lam(x_id, BinderInfo::Default, nnreal.clone(), body))
    };
    let minor_p = {
        let mut mf = EnvDeclBuilder::child_of(&b);
        let (f_id, f) = mf.fresh_local(c.causeq.clone());
        let mkf = c.quot_mk(f.clone());
        // descend on Q.
        let motive_q = {
            let mut mb = EnvDeclBuilder::child_of(&mf);
            let (y_id, y) = mb.fresh_local(nnreal.clone());
            let lhs = nn.add_n(&nn.sq_t(&mkf, &y), AMGM_COEFF);
            let rhs = nn.cube(&nn.two_plus(&mkf, &y));
            let body = nn.le(&lhs, &rhs);
            mb.finish_child(mb.mk_lam(y_id, BinderInfo::Default, nnreal.clone(), body))
        };
        let minor_q = {
            let mut mg = EnvDeclBuilder::child_of(&mf);
            let (g_id, g) = mg.fresh_local(c.causeq.clone());
            // leaf: goal NNReal.le (add27 ((mk f)²(mk g))) (((mk f+mk f)+mk g)³)
            //   reduces (Quot.lift β-rule) to CauSeq.le (add27 ((f·f)·g)) (((f+f)+g)³).
            let body = Expr::apps(core.clone(), [f.clone(), g.clone()]);
            mg.finish_child(mg.mk_lam(g_id, BinderInfo::Default, c.causeq.clone(), body))
        };
        let ind_q = Expr::apps(
            c.quot_ind.clone(),
            [
                c.causeq.clone(),
                c.causeq_equiv.clone(),
                motive_q,
                minor_q,
                q.clone(),
            ],
        );
        mf.finish_child(mf.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), ind_q))
    };
    let ind_p = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive_p,
            minor_p,
            p.clone(),
        ],
    );

    let e = b.mk_lam(q_id, BinderInfo::Default, nnreal.clone(), ind_p);
    let e = b.mk_lam(p_id, BinderInfo::Default, nnreal.clone(), e);
    b.finish(e)
}
