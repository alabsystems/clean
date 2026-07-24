// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Term builders for `BoolAnalysis.deriv_coeff_eq` (#4). `include!`d into
// `boolean_analysis_deriv_coeff.rs`; shares `DerivCoeffConsts` + imports.

fn deriv_coeff_type(c: &DerivCoeffConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let db = c.deriv(&b, &n, &bf, &i);
    let lhs = c.acoeff(&b, &n, &db, &s); // A(D_i b, S)
    let two_ind = c.mul(c.rat_two.clone(), c.ind_(Expr::app(s.clone(), i.clone())));
    let rhs = c.mul(two_ind, c.acoeff(&b, &n, &bf, &s)); // (2·ind(S i))·A(b,S)
    let concl = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(i_id, BinderInfo::Default, c.fin_of(&n), concl);
    let e = b.mk_pi(s_id, BinderInfo::Default, hcp, e);
    let e = b.mk_pi(bf_id, BinderInfo::Default, b_ty, e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn deriv_coeff_value(c: &DerivCoeffConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let b_ty = c.hcpoint_to_rat(&n);
    let (bf_id, bf) = b.fresh_local(b_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (i_id, i) = b.fresh_local(c.fin_of(&n));

    let si = Expr::app(s.clone(), i.clone());
    let fs = c.flip_sign_(si.clone());
    let two_ind = c.mul(c.rat_two.clone(), c.ind_(si.clone()));

    // ── named summand lambdas over HCPoint n ──
    // bchi  := fun y => (b y)·χ_S y           ; Σ bchi = A(b,S) = capA.
    let bchi = make_bchi(c, &b, &n, &bf, &s);
    // bfchi := fun y => (b(flip y))·χ_S y      ; the "second" term.
    let bfchi = make_bfchi(c, &b, &n, &bf, &s, &i);
    // split := fun y => (b y)·χ_S y − (b(flip y))·χ_S y
    let split = make_split(c, &b, &n, &bf, &s, &i);
    // db_chi := fun y => (D_i b y)·χ_S y  (= A(D_i b,S)'s summand, δ-eq to split's parent)
    let db = c.deriv(&b, &n, &bf, &i);
    let db_chi = {
        let mut yb = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let body = c.mul(Expr::app(db.clone(), y.clone()), c.chi_(&n, &s, &y));
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
    };

    let cap_a = c.ssum(&n, bchi.clone()); // A(b,S)
    let sum_split = c.ssum(&n, split.clone());
    let sum_db_chi = c.ssum(&n, db_chi.clone()); // = lhs, δ
    let sum_bfchi = c.ssum(&n, bfchi.clone());

    // ── STEP 1+2: sum_db_chi = sum_split   [subsetSum_congr, per-y distribute] ──
    let pw_split = {
        let mut yb = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let by = Expr::app(bf.clone(), y.clone());
        let bfy = Expr::app(bf.clone(), c.hc_flip_(&n, &y, &i));
        let chi = c.chi_(&n, &s, &y);
        let diff = c.sub(by.clone(), bfy.clone());
        // (b y − b(flip y))·χ = χ·(b y − b(flip y))            [mul_comm]
        let lhs0 = c.mul(diff.clone(), chi.clone());
        let chi_diff = c.mul(chi.clone(), diff.clone());
        let e_comm = Expr::apps(c.rat_mul_comm.clone(), [diff.clone(), chi.clone()]);
        // χ·(b y − b(flip y)) = χ·(b y) − χ·(b(flip y))        [Rat.mul_sub]
        let chi_by = c.mul(chi.clone(), by.clone());
        let chi_bfy = c.mul(chi.clone(), bfy.clone());
        let e_sub = Expr::apps(
            c.rat_mul_sub.clone(),
            [chi.clone(), by.clone(), bfy.clone()],
        );
        let chi_by_sub = c.sub(chi_by.clone(), chi_bfy.clone());
        // χ·(b y) − χ·(b(flip y)) = (b y)·χ − χ·(b(flip y))    [mul_comm on left term]
        let by_chi = c.mul(by.clone(), chi.clone());
        let comm_l = Expr::apps(c.rat_mul_comm.clone(), [chi.clone(), by.clone()]);
        // congrArg (· − χ·b(flip y)) comm_l
        let g_subl = {
            let mut d = EnvDeclBuilder::child_of(&yb);
            let (z_id, z) = d.fresh_local(c.rat.clone());
            let body = c.sub(z.clone(), chi_bfy.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let e_l = c.congr(chi_by.clone(), by_chi.clone(), g_subl, comm_l);
        let mid_l = c.sub(by_chi.clone(), chi_bfy.clone());
        // (b y)·χ − χ·(b(flip y)) = (b y)·χ − (b(flip y))·χ    [mul_comm on right term]
        let bfy_chi = c.mul(bfy.clone(), chi.clone());
        let comm_r = Expr::apps(c.rat_mul_comm.clone(), [chi.clone(), bfy.clone()]);
        let e_r = c.sub_right_congr(&yb, &by_chi, chi_bfy.clone(), bfy_chi.clone(), comm_r);
        let final_r = c.sub(by_chi.clone(), bfy_chi.clone());
        // chain: lhs0 = chi_diff = chi_by_sub = mid_l = final_r
        let p1 = c.trans(
            lhs0.clone(),
            chi_diff.clone(),
            chi_by_sub.clone(),
            e_comm,
            e_sub,
        );
        let p2 = c.trans(lhs0.clone(), chi_by_sub.clone(), mid_l.clone(), p1, e_l);
        let body = c.trans(lhs0, mid_l, final_r, p2, e_r);
        yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp.clone(), body))
    };
    // leg12 : sum_db_chi = sum_split
    let leg12 = Expr::apps(
        c.subset_sum_congr.clone(),
        [n.clone(), db_chi.clone(), split.clone(), pw_split],
    );

    // ── STEP 3: sum_split = capA − sum_bfchi   [subsetSum_sub] ──
    let leg3 = Expr::apps(
        c.subset_sum_sub.clone(),
        [n.clone(), bchi.clone(), bfchi.clone()],
    );
    let a_sub_bfchi = c.sub(cap_a.clone(), sum_bfchi.clone());

    // ── STEP 4: sum_bfchi = fs·capA ──
    let step4 = build_step4(
        c, &b, &n, &bf, &s, &i, &fs, &cap_a, &bchi, &bfchi, &sum_bfchi,
    );
    let fs_a = c.mul(fs.clone(), cap_a.clone());

    // congrArg (capA − ·) step4 : (capA − sum_bfchi) = (capA − fs·capA)
    let leg4 = c.sub_right_congr(&b, &cap_a, sum_bfchi.clone(), fs_a.clone(), step4);
    let a_sub_fsa = c.sub(cap_a.clone(), fs_a.clone());

    // ── STEP 5: capA − fs·capA = (1−fs)·capA = (2·ind)·capA ──
    // 5a: (capA − fs·capA) = (1·capA − fs·capA)   [congrArg (· − fs·capA) (one_mul capA).symm]
    let one_a = c.mul(c.rat_one.clone(), cap_a.clone());
    let one_mul_a = Expr::apps(
        Expr::const_(Name::from_string("Rat.one_mul"), vec![]),
        [cap_a.clone()],
    ); // 1·capA = capA
    let one_mul_a_sym = c.symm(one_a.clone(), cap_a.clone(), one_mul_a); // capA = 1·capA
    let g_subr_fsa = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.sub(z.clone(), fs_a.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let s5a = c.congr(cap_a.clone(), one_a.clone(), g_subr_fsa, one_mul_a_sym);
    let onea_sub_fsa = c.sub(one_a.clone(), fs_a.clone());
    // 5b: (1·capA − fs·capA) = (1−fs)·capA   [symm (Rat.sub_mul 1 fs capA)] — but we only
    //   have Rat.mul_sub (left).  Use: (1−fs)·capA = capA·(1−fs)? simpler: build via
    //   capA·(1−fs) path.  Instead use Rat.mul_sub with the factored side:
    //   (1−fs)·capA = ?  We want (1·capA − fs·capA) = (1−fs)·capA.
    //   Rat.mul_comm: (1−fs)·capA = capA·(1−fs); Rat.mul_sub capA 1 fs : capA·(1−fs)=capA·1−capA·fs;
    //   then commute each back.  Build the reverse chain and symm.
    let one_sub_fs = c.sub(c.rat_one.clone(), fs.clone());
    let factored = c.mul(one_sub_fs.clone(), cap_a.clone()); // (1−fs)·capA
                                                             // forward F : (1−fs)·capA = 1·capA − fs·capA
                                                             //   F1: (1−fs)·capA = capA·(1−fs)        [mul_comm]
    let a_one_sub_fs = c.mul(cap_a.clone(), one_sub_fs.clone());
    let f1 = Expr::apps(c.rat_mul_comm.clone(), [one_sub_fs.clone(), cap_a.clone()]);
    //   F2: capA·(1−fs) = capA·1 − capA·fs   [Rat.mul_sub capA 1 fs]
    let a_one = c.mul(cap_a.clone(), c.rat_one.clone());
    let a_fs = c.mul(cap_a.clone(), fs.clone());
    let f2 = Expr::apps(
        c.rat_mul_sub.clone(),
        [cap_a.clone(), c.rat_one.clone(), fs.clone()],
    );
    let a_one_sub_a_fs = c.sub(a_one.clone(), a_fs.clone());
    //   F3: capA·1 − capA·fs = 1·capA − capA·fs   [congrArg (· − capA·fs) (mul_comm capA 1)]
    let comm_a1 = Expr::apps(c.rat_mul_comm.clone(), [cap_a.clone(), c.rat_one.clone()]); // capA·1 = 1·capA
    let g_subl_afs = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.sub(z.clone(), a_fs.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let f3 = c.congr(a_one.clone(), one_a.clone(), g_subl_afs, comm_a1);
    let onea_sub_afs = c.sub(one_a.clone(), a_fs.clone());
    //   F4: 1·capA − capA·fs = 1·capA − fs·capA   [congrArg (1·capA − ·) (mul_comm capA fs)]
    let comm_afs = Expr::apps(c.rat_mul_comm.clone(), [cap_a.clone(), fs.clone()]); // capA·fs = fs·capA
    let f4 = c.sub_right_congr(&b, &one_a, a_fs.clone(), fs_a.clone(), comm_afs);
    // forward chain F : factored = onea_sub_fsa
    let ff1 = c.trans(
        factored.clone(),
        a_one_sub_fs.clone(),
        a_one_sub_a_fs.clone(),
        f1,
        f2,
    );
    let ff2 = c.trans(
        factored.clone(),
        a_one_sub_a_fs.clone(),
        onea_sub_afs.clone(),
        ff1,
        f3,
    );
    let f_fwd = c.trans(
        factored.clone(),
        onea_sub_afs.clone(),
        onea_sub_fsa.clone(),
        ff2,
        f4,
    );
    // 5b := symm F : onea_sub_fsa = factored
    let s5b = c.symm(factored.clone(), onea_sub_fsa.clone(), f_fwd);
    // 5c: (1−fs)·capA = (2·ind)·capA   [congrArg (·capA) (flip_coeff_absorb (S i))]
    let absorb = Expr::apps(c.flip_coeff_absorb.clone(), [si.clone()]); // (1−fs) = 2·ind
    let g_mulr_a = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = c.mul(z.clone(), cap_a.clone());
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let rhs_final = c.mul(two_ind.clone(), cap_a.clone());
    let s5c = c.congr(one_sub_fs.clone(), two_ind.clone(), g_mulr_a, absorb);

    // ── assemble the full chain ──
    // sum_db_chi = sum_split [leg12]
    //            = (capA − sum_bfchi) [leg3]
    //            = (capA − fs·capA)   [leg4]
    //            = (1·capA − fs·capA) [s5a]
    //            = (1−fs)·capA        [s5b]
    //            = (2·ind)·capA       [s5c]
    let c1 = c.trans(
        sum_db_chi.clone(),
        sum_split.clone(),
        a_sub_bfchi.clone(),
        leg12,
        leg3,
    );
    let c2 = c.trans(
        sum_db_chi.clone(),
        a_sub_bfchi.clone(),
        a_sub_fsa.clone(),
        c1,
        leg4,
    );
    // s5a : a_sub_fsa = onea_sub_fsa
    let c3 = c.trans(
        sum_db_chi.clone(),
        a_sub_fsa.clone(),
        onea_sub_fsa.clone(),
        c2,
        s5a,
    );
    let c4 = c.trans(
        sum_db_chi.clone(),
        onea_sub_fsa.clone(),
        factored.clone(),
        c3,
        s5b,
    );
    let proof = c.trans(
        sum_db_chi.clone(),
        factored.clone(),
        rhs_final.clone(),
        c4,
        s5c,
    );

    let e = b.mk_lam(i_id, BinderInfo::Default, c.fin_of(&n), proof);
    let e = b.mk_lam(s_id, BinderInfo::Default, hcp, e);
    let e = b.mk_lam(bf_id, BinderInfo::Default, b_ty, e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

include!("boolean_analysis_deriv_coeff_build2.rs");
