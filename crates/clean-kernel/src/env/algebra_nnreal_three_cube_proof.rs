// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Proof body for `algebra_nnreal_three_cube.rs` (`include!`d there).

/// `NNReal.three_cube_eq_add27` value: `Quot.ind` on `X` then `Quot.sound`.
fn build_three_cube_value(c: &ThreeCubeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.nnreal.clone());

    // motive M X := Eq NNReal (cube(three X)) (add27 (cube X)).
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = mb.fresh_local(c.nnreal.clone());
        let lhs = c.nn_cube(&c.nn_three(&y));
        let rhs = c.nn_add_n(&c.nn_cube(&y), AMGM_COEFF);
        let body = c.eq_nnreal(&lhs, &rhs);
        mb.finish_child(mb.mk_lam(y_id, BinderInfo::Default, c.nnreal.clone(), body))
    };
    // minor : ∀ f : CauSeq, M (mk f).
    //   goal `Eq NNReal (cube(three (mk f)))(add27 (cube (mk f)))` reduces (NNReal
    //   add/mul Quot.lift β) to `Eq NNReal (mk (cau_cube(cau_three f)))
    //   (mk (cau_add27 (cau_cube f)))`, closed by Quot.sound.
    let minor = {
        let mut mf = EnvDeclBuilder::child_of(&b);
        let (f_id, f) = mf.fresh_local(c.causeq.clone());
        let cau_l = c.cau_cube(&c.cau_three(&f)); // (3f)³ as CauSeq
        let cau_r = c.cau_add_n(&c.cau_cube(&f), AMGM_COEFF); // add27(f³) as CauSeq
        let equiv_pf = build_equiv_proof(c, &mf, &f);
        let sound = c.quot_sound(&cau_l, &cau_r, equiv_pf);
        let _ = (c.quot_mk(&cau_l), c.quot_mk(&cau_r)); // documents the reduced goal heads
        mf.finish_child(mf.mk_lam(f_id, BinderInfo::Default, c.causeq.clone(), sound))
    };
    let ind = Expr::apps(
        c.quot_ind.clone(),
        [
            c.causeq.clone(),
            c.causeq_equiv.clone(),
            motive,
            minor,
            x.clone(),
        ],
    );
    let e = b.mk_lam(x_id, BinderInfo::Default, c.nnreal.clone(), ind);
    b.finish(e)
}

/// `Equiv (cau_cube(cau_three f)) (cau_add27(cau_cube f))`:
///   `∀ ε, 0<ε → ∃ N, ∀ n, N≤n → bound_pair (vL n)(vR n) ε`,
/// where `vL n ≡ ((3·vf n)·(3·vf n))·(3·vf n)`, `vR n ≡ add27((vf n·vf n)·vf n)`
/// are POINTWISE-EQUAL (`RatPolyProver`), so each `<` is `vR n < vR n + ε`
/// transported by the pointwise `Eq`.
fn build_equiv_proof(c: &ThreeCubeConsts, parent: &EnvDeclBuilder, f: &Expr) -> Expr {
    let cau_l = c.cau_cube(&c.cau_three(f));
    let cau_r = c.cau_add_n(&c.cau_cube(f), AMGM_COEFF);

    let mut b = EnvDeclBuilder::child_of(parent);
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hpos_ty = c.rlt(&c.rat_zero, &eps);
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());

    // body : ∀ n, Nat.le 0 n → bound_pair (vL n)(vR n) ε.
    let body_fn = {
        let mut bn = EnvDeclBuilder::child_of(&b);
        let (m_id, m) = bn.fresh_local(c.nat.clone());
        let hle_ty = c.nat_le(&c.nat_zero, &m);
        let (hle_id, _hle) = bn.fresh_local(hle_ty.clone());

        // The reduced Rat forms at index m (defeq to vseq cau_l / cau_r).
        let vf = c.vseq(f, &m); // val(seq f m)
        let vl = c.rcube(&c.rthree(&vf)); // ((3vf)·(3vf))·(3vf)
        let vr = c.radd_n(&c.rcube(&vf), AMGM_COEFF); // add27((vf·vf)·vf)

        // eq_n : vL = vR  (RatPolyProver: both normalise to 27·vf³).
        let pr = RatPolyProver::new(vec![vf.clone()]);
        let eq_n = pr
            .prove_poly_eq(&bn, &vl, &vr)
            .expect("(3X)³ = 27X³ is a polynomial identity");

        // h_self : vR < vR + ε   (add_lt_add_left 0 ε vR hpos; subst vR+0→vR).
        let vr_eps = c.radd(&vr, &eps);
        let step = c.add_lt_add_left(&c.rat_zero, &eps, &vr, hpos.clone());
        let vr_zero = c.radd(&vr, &c.rat_zero);
        let motive_self = {
            let mut mb = EnvDeclBuilder::child_of(&bn);
            let (t_id, t) = mb.fresh_local(c.rat.clone());
            let body = c.rlt(&t, &vr_eps);
            mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let h_self = c.subst(motive_self, &vr_zero, &vr, c.add_zero(&vr), step); // vR < vR+ε

        // left conjunct : vL < vR + ε   (subst vR→vL in the `<` LHS along symm eq_n).
        let left = {
            let motive_l = {
                let mut mb = EnvDeclBuilder::child_of(&bn);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.rlt(&t, &vr_eps);
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            // symm eq_n : vR = vL ; subst transports `vR < vR+ε` to `vL < vR+ε`.
            c.subst(
                motive_l,
                &vr,
                &vl,
                c.eq_symm(&vl, &vr, eq_n.clone()),
                h_self.clone(),
            )
            // (eq_n cloned; the `right` conjunct reuses it via symm)
        };
        // right conjunct : vR < vL + ε   (subst vR→vL in the `+ε` base along symm eq_n).
        let right = {
            let motive_r = {
                let mut mb = EnvDeclBuilder::child_of(&bn);
                let (t_id, t) = mb.fresh_local(c.rat.clone());
                let body = c.rlt(&vr, &c.radd(&t, &eps));
                mb.finish_child(mb.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            // symm eq_n : vR = vL ; subst transports `vR < vR+ε` to `vR < vL+ε`.
            c.subst(motive_r, &vr, &vl, c.eq_symm(&vl, &vr, eq_n), h_self)
        };

        let conj_left = c.rlt(&vl, &vr_eps);
        let conj_right = c.rlt(&vr, &c.radd(&vl, &eps));
        let proof = c.and_intro(&conj_left, &conj_right, left, right);

        let e = bn.mk_lam(hle_id, BinderInfo::Default, hle_ty, proof);
        bn.finish_child(bn.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e))
    };

    // ∃ N, ∀ n, N≤n → bound_pair (vL n)(vR n) ε   via Exists.intro at N := 0.
    let pred = build_equiv_pred(c, &b, &cau_l, &cau_r, &eps);
    let intro = Expr::apps(
        c.exists_intro.clone(),
        [c.nat.clone(), pred, c.nat_zero.clone(), body_fn],
    );

    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, intro);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish_child(e)
}

/// `fun N => ∀ n, Nat.le N n → bound_pair (vseq L n)(vseq R n) ε`.
fn build_equiv_pred(
    c: &ThreeCubeConsts,
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
        let concl = c.bound_pair(&c.vseq(cau_l, &m), &c.vseq(cau_r, &m), eps);
        let e = bm.mk_pi(hle_id, BinderInfo::Default, hle, concl);
        bm.finish_child(bm.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e))
    };
    bn.finish_child(bn.mk_lam(cap_id, BinderInfo::Default, c.nat.clone(), inner))
}
