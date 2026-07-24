// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Proof builders for `BoolAnalysis.nnFinSumPow2SuccSplit` and
// `BoolAnalysis.norm43_cubed_succ_split` (premise (D) of §11.1). `include!`d into
// `boolean_analysis_hc43_norm_split.rs`.

/// `fun (i : Fin (2^m)) => F (castP (idx_map (2^m)(2^m) i))` — a split-half
/// summand (the `finSumPow2SuccSplit` RHS half), `low` selects `Fin.castAdd`.
fn pow2_half_fn(c: &NsConsts, parent: &EnvDeclBuilder, m: &Expr, f: &Expr, low: bool) -> Expr {
    let p2m = c.pow2(m);
    let fin = c.fin_of(&p2m);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = b.fresh_local(fin.clone());
    let idx = if low {
        Expr::apps(
            c.fin_cast_add.clone(),
            [p2m.clone(), p2m.clone(), i.clone()],
        )
    } else {
        Expr::apps(c.fin_add_nat.clone(), [p2m.clone(), p2m.clone(), i.clone()])
    };
    let casted = c.cast_p(&b, m, &idx);
    let body = Expr::app(f.clone(), casted);
    b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin, body))
}

/// `BoolAnalysis.nnFinSumPow2SuccSplit : ∀ (m : Nat) (F : Fin (2^(m+1)) → NNReal),`
/// `  finSum (2^(m+1)) F`
/// `    = add (finSum (2^m) (fun i => F (castP (castAdd (2^m)(2^m) i))))`
/// `          (finSum (2^m) (fun j => F (castP (addNat  (2^m)(2^m) j))))`.
/// Value: `Eq.trans (finSum_cast …) (finSum_split_add …)` — the NNReal dual of
/// the landed Rat `BoolAnalysis.finSumPow2SuccSplit`.
fn build_nn_pow2_succ_split(c: &NsConsts) -> (Expr, Expr) {
    let fin_to_nn = |n: &Expr| Expr::pi(BinderInfo::Default, c.fin_of(n), c.nnreal.clone());

    // concl(m, F) := lhs = add (finSum 2^m low) (finSum 2^m high).
    let concl = |parent: &EnvDeclBuilder, m: &Expr, f: &Expr| -> (Expr, Expr) {
        let sm = c.succ(m);
        let p2sm = c.pow2(&sm);
        let p2m = c.pow2(m);
        let lhs = c.finsum(&p2sm, f);
        let low = pow2_half_fn(c, parent, m, f, true);
        let high = pow2_half_fn(c, parent, m, f, false);
        let rhs = c.nnadd(&c.finsum(&p2m, &low), &c.finsum(&p2m, &high));
        (lhs, rhs)
    };

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let sm = c.succ(&m);
        let f_ty = fin_to_nn(&c.pow2(&sm));
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let (lhs, rhs) = concl(&b, &m, &f);
        let body = c.eq_nn(&lhs, &rhs);
        let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, body);
        b.finish(b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), r))
    };

    let value = {
        let mut vb = EnvDeclBuilder::new();
        let (m_id, m) = vb.fresh_local(c.nat.clone());
        let sm = c.succ(&m);
        let p2sm = c.pow2(&sm);
        let p2m = c.pow2(&m);
        let sum_pow = c.nat_add_(&p2m, &p2m);
        let f_ty = fin_to_nn(&p2sm);
        let (f_id, f) = vb.fresh_local(f_ty.clone());

        // e_sym : 2^m+2^m = 2^(m+1).
        let e_fwd = Expr::app(c.pow_two_succ.clone(), m.clone());
        let e_sym = Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![c.l1.clone()]),
            [c.nat.clone(), p2sm.clone(), sum_pow.clone(), e_fwd],
        );

        // F' : Fin (2^m+2^m) → NNReal := fun i => F (castP i).
        let f_prime = {
            let mut fb = EnvDeclBuilder::child_of(&vb);
            let (i_id, i) = fb.fresh_local(c.fin_of(&sum_pow));
            let casted = c.cast_p(&fb, &m, &i);
            let body = Expr::app(f.clone(), casted);
            fb.finish_child(fb.mk_lam(i_id, BinderInfo::Default, c.fin_of(&sum_pow), body))
        };

        // step1 : finSum (2^(m+1)) F = finSum (2^m+2^m) F'  (finSum_cast 2^(m+1) (2^m+2^m) e_sym F).
        let step1 = Expr::apps(
            c.nnreal_finsum_cast.clone(),
            [p2sm.clone(), sum_pow.clone(), e_sym.clone(), f.clone()],
        );
        // step2 : finSum (2^m+2^m) F' = add (finSum 2^m low') (finSum 2^m high')
        //   (finSum_split_add 2^m 2^m F').
        let step2 = Expr::apps(
            c.nnreal_finsum_split.clone(),
            [p2m.clone(), p2m.clone(), f_prime.clone()],
        );

        let lhs = c.finsum(&p2sm, &f);
        let mid = c.finsum(&sum_pow, &f_prime);
        // low'/high' : the split_add RHS summands (F' ∘ castAdd / F' ∘ addNat).
        let low_prime = {
            let mut lb = EnvDeclBuilder::child_of(&vb);
            let (i_id, i) = lb.fresh_local(c.fin_of(&p2m));
            let ca = Expr::apps(
                c.fin_cast_add.clone(),
                [p2m.clone(), p2m.clone(), i.clone()],
            );
            let body = Expr::app(f_prime.clone(), ca);
            lb.finish_child(lb.mk_lam(i_id, BinderInfo::Default, c.fin_of(&p2m), body))
        };
        let high_prime = {
            let mut hb = EnvDeclBuilder::child_of(&vb);
            let (j_id, j) = hb.fresh_local(c.fin_of(&p2m));
            let an = Expr::apps(c.fin_add_nat.clone(), [p2m.clone(), p2m.clone(), j.clone()]);
            let body = Expr::app(f_prime.clone(), an);
            hb.finish_child(hb.mk_lam(j_id, BinderInfo::Default, c.fin_of(&p2m), body))
        };
        let rhs = c.nnadd(&c.finsum(&p2m, &low_prime), &c.finsum(&p2m, &high_prime));

        let composed = c.trans_nn(&lhs, &mid, &rhs, step1, step2);
        let lam = vb.mk_lam(f_id, BinderInfo::Default, f_ty, composed);
        vb.finish(vb.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), lam))
    };

    (type_, value)
}

/// The merged per-low-coordinate summand `W := fun (k : Fin (2^m)) =>
///   NNReal.add (Φ (castP (castAdd k))) (Φ (castP (addNat k)))` where
/// `Φ := cube_summand (m+1) F s r hs`.
fn merged_w_fn(
    c: &NsConsts,
    parent: &EnvDeclBuilder,
    m: &Expr,
    f: &Expr,
    s: &Expr,
    r: &Expr,
    hs: &Expr,
) -> Expr {
    let sm = c.succ(m);
    let p2m = c.pow2(m);
    let fin = c.fin_of(&p2m);
    let mut b = EnvDeclBuilder::child_of(parent);
    let (k_id, k) = b.fresh_local(fin.clone());
    let lo_idx = Expr::apps(
        c.fin_cast_add.clone(),
        [p2m.clone(), p2m.clone(), k.clone()],
    );
    let hi_idx = Expr::apps(c.fin_add_nat.clone(), [p2m.clone(), p2m.clone(), k.clone()]);
    let lo_cast = c.cast_p(&b, m, &lo_idx);
    let hi_cast = c.cast_p(&b, m, &hi_idx);
    let phi_lo = c.contribution(f, s, r, hs, &c.decode(&sm, &lo_cast));
    let phi_hi = c.contribution(f, s, r, hs, &c.decode(&sm, &hi_cast));
    let body = c.nnadd(&phi_lo, &phi_hi);
    b.finish_child(b.mk_lam(k_id, BinderInfo::Default, fin, body))
}

/// `BoolAnalysis.norm43_cubed_succ_split` type + proof (premise (D)).
fn build_norm43_cubed_succ_split(c: &NsConsts) -> (Expr, Expr) {
    // TYPE.
    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let sm = c.succ(&m);
        let fn_ty = c.fn_type(&sm);
        let (f_id, f) = b.fresh_local(fn_ty.clone());
        let (s_id, s) = b.fresh_local(fn_ty.clone());
        let (r_id, r) = b.fresh_local(fn_ty.clone());
        let hs_ty = c.forall_scale_nonneg_ty(&b, &sm, &s);
        let (hs_id, hs) = b.fresh_local(hs_ty.clone());
        let w = merged_w_fn(c, &b, &m, &f, &s, &r, &hs);
        let sum_w = c.finsum(&c.pow2(&m), &w);
        let cube_sum_w = c.cube(&sum_w);
        let ncubed = c.norm43_cubed_app(&sm, &f, &s, &r, &hs);
        let concl = c.eq_nn(&ncubed, &cube_sum_w);
        let e = b.mk_pi(hs_id, BinderInfo::Default, hs_ty, concl);
        let e = b.mk_pi(r_id, BinderInfo::Default, fn_ty.clone(), e);
        let e = b.mk_pi(s_id, BinderInfo::Default, fn_ty.clone(), e);
        let e = b.mk_pi(f_id, BinderInfo::Default, fn_ty, e);
        b.finish(b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e))
    };

    // VALUE.
    let value = {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(c.nat.clone());
        let sm = c.succ(&m);
        let fn_ty = c.fn_type(&sm);
        let (f_id, f) = b.fresh_local(fn_ty.clone());
        let (s_id, s) = b.fresh_local(fn_ty.clone());
        let (r_id, r) = b.fresh_local(fn_ty.clone());
        let hs_ty = c.forall_scale_nonneg_ty(&b, &sm, &s);
        let (hs_id, hs) = b.fresh_local(hs_ty.clone());

        let p2m = c.pow2(&m);
        // Φ := cube_summand (m+1) F s r hs : Fin (2^(m+1)) → NNReal.
        let phi = c.cube_summand(&b, &sm, &f, &s, &r, &hs);
        // norm43 (m+1) ≡ finSum (2^(m+1)) Φ  (δ-defeq; both reducible).
        let n_sum = c.finsum(&c.pow2(&sm), &phi);

        // split : finSum (2^(m+1)) Φ = add (finSum 2^m low) (finSum 2^m high).
        let low = pow2_half_fn(c, &b, &m, &phi, true);
        let high = pow2_half_fn(c, &b, &m, &phi, false);
        let sum_low = c.finsum(&p2m, &low);
        let sum_high = c.finsum(&p2m, &high);
        let split_rhs = c.nnadd(&sum_low, &sum_high);
        let split = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.nnFinSumPow2SuccSplit"),
                vec![],
            ),
            [m.clone(), phi.clone()],
        );

        // merge : add (finSum 2^m low) (finSum 2^m high) = finSum 2^m W
        //   (symm (NNReal.finSum_add 2^m low high)).
        // W k = add (low k) (high k); low k = Φ (castP (castAdd k)) = Φ-applied;
        // NNReal.finSum_add 2^m low high : finSum 2^m (fun k => low k + high k)
        //   = add (finSum 2^m low) (finSum 2^m high). The summand fun k => low k +
        //   high k is δ-defeq to W (low k ≡ Φ (castP (castAdd k)), and W's Φ is the
        //   SAME cube_summand applied to decode (m+1) (castP …)).
        let w = merged_w_fn(c, &b, &m, &f, &s, &r, &hs);
        let sum_w = c.finsum(&p2m, &w);
        let finsum_add = Expr::apps(
            c.nnreal_finsum_add.clone(),
            [p2m.clone(), low.clone(), high.clone()],
        );
        // finsum_add : finSum 2^m (fun k => low k + high k) = add sum_low sum_high.
        // Its LHS summand fun k => low k + high k is defeq to W, so symm gives
        // add sum_low sum_high = finSum 2^m W.
        let merge = c.symm_nn(&sum_w, &split_rhs, finsum_add);

        // n_eq_sum_w : finSum (2^(m+1)) Φ = finSum 2^m W  (trans split merge).
        let n_eq_sum_w = c.trans_nn(&n_sum, &split_rhs, &sum_w, split, merge);

        // cube congruence: (((N)·N)·N) = (((ΣW)·ΣW)·ΣW) via congrArg of the cube.
        let cube_lam = {
            let mut cb = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = cb.fresh_local(c.nnreal.clone());
            let body = c.cube(&t);
            cb.finish_child(cb.mk_lam(t_id, BinderInfo::Default, c.nnreal.clone(), body))
        };
        let cube_sum_w = c.cube(&sum_w);
        // congrArg cube n_eq_sum_w : cube (finSum (2^(m+1)) Φ) = cube (finSum 2^m W).
        // cube (finSum (2^(m+1)) Φ) ≡ norm43_cubed (m+1) F s r hs by δ-unfold
        // (norm43_cubed ≡ ((norm43)·(norm43))·(norm43), norm43 ≡ finSum (2^(m+1)) Φ).
        let cube_congr = c.congr_arg_nn(&n_sum, &sum_w, cube_lam, n_eq_sum_w);
        // Re-target the LHS to norm43_cubed (m+1) via subst LEFT along the δ-defeq
        // identity. We use the kernel's defeq: `cube_congr` has type
        // `cube n_sum = cube_sum_w`, and `cube n_sum` is defeq to `norm43_cubed
        // (m+1) …`; the goal type is `norm43_cubed (m+1) … = cube_sum_w`. Since the
        // declared type uses `norm43_cubed_app` and the proof `cube_congr` has the
        // δ-equal `cube n_sum`, the kernel accepts `cube_congr` directly.
        let _ = c.norm43_cubed_app(&sm, &f, &s, &r, &hs);
        let _ = cube_sum_w;

        let proof = cube_congr;
        let e = b.mk_lam(hs_id, BinderInfo::Default, hs_ty, proof);
        let e = b.mk_lam(r_id, BinderInfo::Default, fn_ty.clone(), e);
        let e = b.mk_lam(s_id, BinderInfo::Default, fn_ty.clone(), e);
        let e = b.mk_lam(f_id, BinderInfo::Default, fn_ty, e);
        b.finish(b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e))
    };

    (ty, value)
}
